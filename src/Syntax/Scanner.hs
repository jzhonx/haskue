{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax.Scanner where

import Control.Monad (void, when)
import Control.Monad.State.Strict
import Data.ByteString.Builder (Builder, charUtf8, toLazyByteString, word8)
import Data.ByteString.Char8 (toStrict)
import qualified Data.ByteString.Char8 as BC
import Data.Char (chr, digitToInt, isAlpha, isDigit, isHexDigit, isOctDigit)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as Seq
import Debug.Trace (trace)
import Syntax.Token
import Text.Printf (printf)

-- | Scanner state using State monad
newtype Scanner a = Scanner
  { runScanner :: State ScannerState a
  }
  deriving (Functor, Applicative, Monad, MonadState ScannerState)

-- | Scanner state containing input and position information
data ScannerState = ScannerState
  { source :: BC.ByteString
  , startLoc :: Location
  -- ^ Starting location of the current scanning session. Token will use this as the base location.
  , loc :: Location
  -- ^ Current location in the source code.
  , current :: !Int
  -- ^ Current offset in the input source.
  , tokens :: Seq.Seq Token
  -- ^ Accumulated tokens.
  , invalids :: Seq.Seq Token
  -- ^ Accumulated invalid tokens.
  , lparens :: [Location]
  }
  deriving (Show)

-- | Create initial scanner state
initialState :: FilePath -> BC.ByteString -> ScannerState
initialState fname dataInput =
  let loc = Location 1 1 (Just fname)
   in ScannerState
        { source = dataInput
        , startLoc = loc
        , loc = loc
        , current = 0
        , tokens = Seq.empty
        , invalids = Seq.empty
        , lparens = []
        }

-- | Peek the next character without consuming it.
peek :: Scanner (Maybe Char)
peek = do
  inputBytes <- getSource
  current <- gets current
  return $ BC.indexMaybe inputBytes current

peekNext :: Scanner (Maybe Char)
peekNext = do
  inputBytes <- getSource
  current <- gets current
  return $ BC.indexMaybe inputBytes (current + 1)

peek2 :: Scanner (Maybe Char, Maybe Char)
peek2 = do
  first <- peek
  second <- peekNext
  return (first, second)

getLastScannedToken :: Scanner (Maybe Token)
getLastScannedToken = do
  ts <- gets tokens
  return $ case Seq.viewr ts of
    Seq.EmptyR -> Nothing
    _ Seq.:> lastToken -> Just lastToken

popLastScannedToken :: Scanner ()
popLastScannedToken = modify $ \s ->
  case Seq.viewr (tokens s) of
    Seq.EmptyR -> s
    ts Seq.:> _ -> s{tokens = ts}

-- | Advance the source by one character.
advance :: Scanner (Maybe Char)
advance = do
  inputBytes <- getSource
  cur <- gets current
  let nextChar = BC.indexMaybe inputBytes cur
  case nextChar of
    Nothing -> return ()
    Just c -> do
      -- We only insert comma when there is a next character. EOF is handled separately in scanAll.
      insertComma nextChar
      -- Update location and current position.
      -- Also handle automatic comma insertion at line breaks.
      modify $ \s ->
        let l = loc s
            newLoc = case c of
              '\n' -> l{line = line l + 1, column = 1}
              _ -> l{column = column l + 1}
         in s{loc = newLoc, current = current s + 1}
  return nextChar

insertComma :: Maybe Char -> Scanner ()
insertComma cM = do
  let isNextCharNewline = case cM of
        Just '\n' -> True
        -- EOF, handles the automatic comma insertion at the end of file if needed.
        Nothing -> True
        _ -> False
  s <- get
  let l = loc s
      shouldInsert = isNextCharNewline && endLineInsertCond s
  when shouldInsert $
    let newTokens =
          tokens s
            Seq.|> Token
              { tkType = Comma
              , -- Comma is added after the last token on the line, which is non-existent in source.
                tkLoc = (loc s){line = line l, column = column l + 1}
              , tkLiteral = BC.pack ","
              }
     in put s{tokens = newTokens}
 where
  -- According to spec The formal grammar uses commas , as terminators in a number of productions. CUE programs may omit
  -- most of these commas using the following rules:
  --
  -- When the input is broken into tokens, a comma is automatically inserted into the token stream immediately after a
  -- line’s final token if that token is
  --
  -- an identifier, keyword, or bottom
  -- a number or string literal, including an interpolation
  -- one of the characters ), ], }, or ?
  -- an ellipsis ...
  -- Although commas are automatically inserted, the parser will require explicit commas between two list elements.
  --
  -- Another case is that
  -- > Also, a newline or end of file may trigger the insertion of a comma.
  endLineInsertCond :: ScannerState -> Bool
  endLineInsertCond s = do
    case Seq.viewr (tokens s) of
      Seq.EmptyR -> False
      _ Seq.:> lastToken -> case tkType lastToken of
        Identifier -> True
        Bool -> True
        Bottom -> True
        Null -> True
        Int -> True
        Float -> True
        String -> True
        MultiLineString -> True
        Bytes -> True
        MultiLineBytes -> True
        InterpolationEnd -> True -- Interpolation end is part of string literals.
        RParen -> True
        RBrace -> True
        RSquare -> True
        QuestionMark -> True
        Ellipsis -> True
        _
          | isTokenKeyword (tkType lastToken) -> True
          | otherwise -> False

-- Helper functions for state manipulation
updateSource :: BC.ByteString -> Scanner ()
updateSource newInput = modify $ \s -> s{source = newInput}

getSource :: Scanner BC.ByteString
getSource = gets source

-- | Create a token with current position.
addToken :: TokenType -> Scanner ()
addToken tokenType = addTokenWith (const tokenType)

-- | Create a token with a function to determine its type.
addTokenWith :: (BC.ByteString -> TokenType) -> Scanner ()
addTokenWith f = addTokenTransLit f id

{- | Create a token with a function to determine its type and a function to transform its literal.

It also tracks left parentheses. Both left parenthesis and interpolation will increase the left parenthesis count.
-}
addTokenTransLit :: (BC.ByteString -> TokenType) -> (BC.ByteString -> BC.ByteString) -> Scanner ()
addTokenTransLit f g = modify $ \s ->
  let
    literal = BC.take (current s) (source s)
    tType = f literal
    tk =
      Token
        { tkType = tType
        , tkLoc = startLoc s
        , tkLiteral = g literal
        }
   in
    s
      { tokens = tokens s Seq.|> tk
      , lparens = case tType of
          LParen -> tk.tkLoc : lparens s
          Interpolation -> tk.tkLoc : lparens s
          RParen -> case lparens s of
            [] -> lparens s -- We will report the missing left parenthesis in the parser.
            (_ : ls) -> ls
          _ -> lparens s
      }

addInvalidToken :: (BC.ByteString -> BC.ByteString) -> Scanner ()
addInvalidToken msgF = modify $ \s ->
  let
    literal = BC.take (current s) (source s)
    tk =
      Token
        { tkType = Illegal
        , tkLoc = startLoc s
        , tkLiteral = msgF literal
        }
   in
    s{invalids = invalids s Seq.|> tk}

{- | Reset the current scanning position.

Reset the current offset to zero so that the next token can have the correct literal.
Set the starting location to the current location.
-}
resetCurPosLoc :: Scanner ()
resetCurPosLoc = modify $ \s -> s{source = BC.drop (current s) (source s), current = 0, startLoc = loc s}

-- | Scan all tokens from input.
scanTokens :: BC.ByteString -> Either Token [Token]
scanTokens = scanTokensFromFile ""

-- | Scan tokens with filename information.
scanTokensFromFile :: FilePath -> BC.ByteString -> Either Token [Token]
scanTokensFromFile fname dataInput =
  let final = execState (runScanner scanAll) (initialState fname dataInput)
   in case toList (invalids final) of
        [] -> Right (toList (tokens final))
        (errToken : _) -> Left errToken

-- | Scan all tokens until end of input.
scanAll :: Scanner ()
scanAll = go
 where
  go = do
    scanToken
    isEnd <- gets (BC.null . source)
    if isEnd
      then return ()
      else go

-- | Scan a single token from the input.
scanToken :: Scanner ()
scanToken = do
  skipWhitespaceAndComments
  -- If some whitespace or comments were skipped, we need to reset the current offset.
  resetCurPosLoc

  charM <- advance
  case charM of
    Nothing -> do
      insertComma Nothing -- Handle automatic comma insertion at the end of file if needed.
      addToken EOF
    Just c -> case c of
      '(' -> addToken LParen
      ')' -> addToken RParen
      '{' -> addToken LBrace
      '}' -> addToken RBrace
      '[' -> addToken LSquare
      ']' -> addToken RSquare
      ':' -> addToken Colon
      ',' -> addToken Comma
      '?' -> addToken QuestionMark
      '+' -> addToken Plus
      '-' -> addToken Minus
      '*' -> addToken Multiply
      '&' -> addToken Unify
      '|' -> addToken Disjoin
      _ -> compound c
 where
  compound c
    | c == '!' = scanBang
    | c == '/' = scanSlash
    | c == '<' = scanLess
    | c == '>' = scanGreater
    | c == '=' = scanEqual
    | c == '.' = scanEllipsis
    | c == '"' = scanStringLit
    | c == '\'' = scanBytesLit
    | isDigit c = scanNumber
    | isAlpha c || c `elem` ("_$#" :: String) = do
        (second, third) <- peek2
        case (c, second, third) of
          ('_', Just '|', Just '_') -> advance >> advance >> addToken Bottom
          _ -> scanIdentifierOrKeyword c
    | otherwise = addInvalidToken ("Illegal character: " <>)

-- | Skip whitespace and comments
skipWhitespaceAndComments :: Scanner ()
skipWhitespaceAndComments = do
  ch <- peek
  case ch of
    Nothing -> return ()
    Just c -> case c of
      ' ' -> advance >> skipWhitespaceAndComments
      '\t' -> advance >> skipWhitespaceAndComments
      '\n' -> advance >> skipWhitespaceAndComments
      '\r' -> advance >> skipWhitespaceAndComments
      '/' -> do
        nextCh <- peekNext
        case nextCh of
          Just '/' -> advance >> advance >> skipLineComment >> skipWhitespaceAndComments
          _ -> return ()
      _ -> return ()

-- | Skip line comment
skipLineComment :: Scanner ()
skipLineComment = do
  nextChar <- peek
  case nextChar of
    Nothing -> return ()
    Just c ->
      if c == '\n'
        then void advance
        else advance >> skipLineComment

-- | Scan exclamation-based operators (!, !=, !~)
scanBang :: Scanner ()
scanBang = do
  c <- peek
  case c of
    Just '=' -> advance >> addToken NotEqual
    Just '~' -> advance >> addToken NotMatch
    _ -> addToken Exclamation

-- | Scan slash operator and comments (/ and //)
scanSlash :: Scanner ()
scanSlash = do
  c <- peek
  case c of
    Just '/' -> advance >> skipLineComment
    _ -> addToken Divide

-- | Scan less-than operators (< and <=)
scanLess :: Scanner ()
scanLess = do
  c <- peek
  case c of
    Just '=' -> advance >> addToken LessEqual
    _ -> addToken Less

-- | Scan greater-than operators (> and >=)
scanGreater :: Scanner ()
scanGreater = do
  c <- peek
  case c of
    Just '=' -> advance >> addToken GreaterEqual
    _ -> addToken Greater

-- | Scan equal operators (=, ==, =~)
scanEqual :: Scanner ()
scanEqual = do
  c <- peek
  case c of
    Just '=' -> advance >> addToken Equal
    Just '~' -> advance >> addToken Match
    _ -> addToken Assign

-- | Scan ellipsis operator (...)
scanEllipsis :: Scanner ()
scanEllipsis = do
  -- We've already consumed the first '.'
  (second, third) <- peek2
  case (second, third) of
    (Just '.', Just '.') -> advance >> advance >> addToken Ellipsis
    -- If the second character is not '.' or third is not, just add a single Dot token.
    _ -> addToken Dot

-- | Scan string literal (handles both simple and multiline)
scanStringLit :: Scanner ()
scanStringLit = do
  -- We've already consumed the first '"'.
  (second, third) <- peek2
  case (second, third) of
    (Just '"', Just '"') ->
      advance >> advance >> do
        ch <- peek
        case ch of
          Just '\n' -> advance >> scanMultiline
          _ -> addInvalidToken (const "Invalid multiline string")
    _ -> scanString

-- | Scan string content.
scanString :: Scanner ()
scanString = scanByteSeq tryClose String mempty
 where
  tryClose closeType c b
    | c == '\n' = addInvalidToken (const "Unterminated string literal") >> return True
    | c == '"' = addTokenTransLit (const closeType) (const $ toStrict $ toLazyByteString b) >> return True
    | otherwise = return False

-- | Scan multiline string content.
scanMultiline :: Scanner ()
scanMultiline = scanByteSeq tryClose MultiLineString mempty
 where
  tryClose closeType c b
    | c == '"' = do
        (first, second) <- peek2
        case (first, second) of
          (Just '"', Just '"') -> do
            void $ advance >> advance
            case stripMultilineIndent $ toStrict $ toLazyByteString b of
              Left err -> addInvalidToken (const err)
              Right stripped -> addTokenTransLit (const closeType) (const stripped)
            return True
          _ -> return False
    | otherwise = return False

-- | Scan bytes literal (handles both simple and multiline)
scanBytesLit :: Scanner ()
scanBytesLit = do
  -- We've already consumed the first '\''.
  (second, third) <- peek2
  case (second, third) of
    (Just '\'', Just '\'') ->
      advance >> advance >> do
        ch <- peek
        case ch of
          Just '\n' -> advance >> scanMLBytes
          _ -> addInvalidToken (const "Invalid multiline bytes literal")
    _ -> scanBytes

-- | Scan simple bytes content.
scanBytes :: Scanner ()
scanBytes = scanByteSeq tryClose Bytes mempty
 where
  tryClose closeType c b
    | c == '\n' = addInvalidToken (const "Unterminated bytes literal") >> return True
    | c == '\'' = addTokenTransLit (const closeType) (const $ toStrict $ toLazyByteString b) >> return True
    | otherwise = return False

-- | Scan multiline bytes content.
scanMLBytes :: Scanner ()
scanMLBytes = scanByteSeq tryClose MultiLineBytes mempty
 where
  tryClose closeType c b
    | c == '\'' = do
        (first, second) <- peek2
        case (first, second) of
          (Just '\'', Just '\'') -> do
            void $ advance >> advance
            case stripMultilineIndent $ toStrict $ toLazyByteString b of
              Left err -> addInvalidToken (const err)
              Right stripped -> addTokenTransLit (const closeType) (const stripped)
            return True
          _ -> return False
    | otherwise = return False

stripMultilineIndent :: BC.ByteString -> Either BC.ByteString BC.ByteString
stripMultilineIndent content =
  let ls = BC.split '\n' content
      (contentLines, indent) =
        if not (null ls) && BC.all (\c -> c == ' ' || c == '\t') (last ls)
          then (init ls, last ls) -- last line is whitespace-only: it's the closing indent
          else (ls, BC.empty) -- last line is content: no indent to strip
      stripLine l
        | BC.isPrefixOf indent l = Right $ BC.drop (BC.length indent) l
        | BC.null l = Right l -- allow empty lines without the indent
        | otherwise =
            Left
              "Indentation error in multiline literal: all lines must have the same indentation as the closing line"
   in fmap (BC.intercalate "\n") (mapM stripLine contentLines)

scanByteSeq :: (TokenType -> Char -> Builder -> Scanner Bool) -> TokenType -> Builder -> Scanner ()
scanByteSeq tryClose closeTkType b = do
  ch <- peek
  case ch of
    -- EOF, there might be some non-empty string characters to add.
    Nothing -> addInvalidToken (const "Unterminated string literal")
    Just c | c == '\\' -> do
      nextCh <- peekNext
      let isBytes = closeTkType == Bytes || closeTkType == MultiLineBytes
      case nextCh of
        Nothing -> addInvalidToken (const "Unterminated escape sequence")
        Just nextC -> case nextC of
          'a' -> escapeNamed '\a'
          'b' -> escapeNamed '\b'
          'f' -> escapeNamed '\f'
          'n' -> escapeNamed '\n'
          'r' -> escapeNamed '\r'
          't' -> escapeNamed '\t'
          'v' -> escapeNamed '\v'
          '/' -> escapeNamed '/'
          '\\' -> escapeNamed '\\'
          '\'' -> escapeNamed '\''
          '"' -> escapeNamed '"'
          '(' -> do
            void $ advance >> advance
            addTokenTransLit (const Interpolation) (const $ toStrict $ toLazyByteString b)
            curLParens <- gets lparens
            scanItplEnd (length curLParens)
            -- After finishing the interpolation, we need to start a new partition.
            scanByteSeq tryClose InterpolationEnd mempty
          'u' -> do
            void $ advance >> advance
            readHexDigits 4 >>= \case
              Just n -> scanByteSeq tryClose closeTkType (b <> (charUtf8 . chr) n)
              Nothing -> addInvalidToken (const "Invalid unicode escape sequence")
          'U' -> do
            void $ advance >> advance
            readHexDigits 8 >>= \case
              Just n -> scanByteSeq tryClose closeTkType (b <> (charUtf8 . chr) n)
              Nothing -> addInvalidToken (const "Invalid unicode escape sequence")
          'x' | isBytes -> do
            void $ advance >> advance
            readHexDigits 2 >>= \case
              Just n -> scanByteSeq tryClose closeTkType (b <> (word8 . fromIntegral) n)
              Nothing -> addInvalidToken (const "Invalid hex escape sequence")
          _ | isBytes && isOctDigit nextC -> do
            void $ advance >> advance
            let d1 = digitToInt nextC
            readOctalDigits2 >>= \case
              Just (d2, d3) -> do
                let byte = fromIntegral (d1 * 64 + d2 * 8 + d3)
                trace ("Octal escape sequence: " ++ show byte ++ " from digits " ++ show [d1, d2, d3]) $ return ()
                scanByteSeq tryClose closeTkType (b <> word8 byte)
              Nothing -> addInvalidToken (const "Invalid octal escape sequence")
          _ -> addInvalidToken (const $ "Invalid escape character: \\" <> BC.singleton nextC)
    Just c -> do
      void advance
      -- The char is not appended to the builder.
      shouldStop <- tryClose closeTkType c b
      if shouldStop
        then return ()
        else scanByteSeq tryClose closeTkType (b <> word8 (fromIntegral (fromEnum c)))
 where
  escapeNamed c = advance >> advance >> scanByteSeq tryClose closeTkType (b <> word8 (fromIntegral (fromEnum c)))

  readHexDigits :: Int -> Scanner (Maybe Int)
  readHexDigits n = go n 0
   where
    go 0 acc = return $ Just acc
    go k acc = do
      ch' <- peek
      case ch' of
        Just c' | isHexDigit c' -> do
          void advance
          go (k - 1) (acc * 16 + fromIntegral (digitToInt c'))
        _ -> return Nothing

  readOctalDigits2 :: Scanner (Maybe (Int, Int))
  readOctalDigits2 = do
    (d1M, d2M) <- peek2
    case (d1M, d2M) of
      (Just c1, Just c2) | isOctDigit c1 && isOctDigit c2 -> do
        trace ("Octal digits: " ++ show [digitToInt c1, digitToInt c2]) $ return ()
        void advance >> void advance
        return $ Just (digitToInt c1, digitToInt c2)
      _ -> return Nothing

scanItplEnd :: Int -> Scanner ()
scanItplEnd lparenDepth = do
  next <- peek
  case next of
    Nothing -> addInvalidToken (const "Unterminated interpolation")
    Just _ -> do
      scanToken
      lastTk <- getLastScannedToken
      case lastTk of
        Just tk | tk.tkType == RParen -> do
          curLParens <- gets lparens
          -- The last token is a right paren, which just matches the left paren of the interpolation.
          if length curLParens == lparenDepth - 1
            -- Pop the last scanned right parenthesis token because the interpolation end token will be added later to
            -- have the same semantic meaning as the right parenthesis.
            then popLastScannedToken
            else scanItplEnd lparenDepth
        _ -> scanItplEnd lparenDepth

-- | Scan number literal (int or float).
scanNumber :: Scanner ()
scanNumber = do
  digits
  (first, second) <- peek2
  -- consume the '.'.
  hasDot <- case (first, second) of
    (Just '.', Just digit) | isDigit digit -> advance >> return True
    _ -> return False
  digits
  addToken $ if hasDot then Float else Int
 where
  digits :: Scanner ()
  digits = do
    c <- peek
    case c of
      Just digit | isDigit digit -> advance >> digits
      _ -> return ()

{- | Scan identifier or keyword.

The first character is already consumed and it is of the form [a-zA-Z_$#].
-}
scanIdentifierOrKeyword :: Char -> Scanner ()
scanIdentifierOrKeyword first = do
  case first of
    '_' -> do
      secondChar <- peek
      case secondChar of
        Just '_' -> addInvalidToken (const "Invalid identifier starting with __")
        Just '#' -> advance >> mustLetterChar
        _ -> return ()
    '#' -> mustLetterChar
    _ -> return ()
  letterNums
  addTokenWith getIdentifierType
 where
  isLetter c = isAlpha c || c == '_' || c == '$'
  mustLetterChar = do
    ch <- advance
    case ch of
      Just c | isLetter c -> return ()
      _ -> addInvalidToken (const "Identifier must have a letter, _, $, or # after initial _ or #")
  letterNums = do
    ch <- peek
    case ch of
      Just c | isLetter c || isDigit c -> advance >> letterNums
      _ -> return ()

-- | Determine token type for identifier text
getIdentifierType :: BC.ByteString -> TokenType
getIdentifierType text = case text of
  "package" -> Package
  "import" -> Import
  "for" -> For
  "in" -> In
  "if" -> If
  "let" -> Let
  "null" -> Null
  "true" -> Bool
  "false" -> Bool
  "_|_" -> Bottom
  _ -> Identifier

debugSState :: Scanner ()
debugSState = do
  s <- get
  trace ("source: " ++ show (source s) ++ ", current: " ++ show (current s)) (return ())

isByteStringIdentifier :: BC.ByteString -> Bool
isByteStringIdentifier bs = case scanTokens bs of
  Right [Token{tkType = Identifier, tkLiteral = lit}] | lit == bs -> True
  _ -> False