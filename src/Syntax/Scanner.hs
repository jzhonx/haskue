{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Syntax.Scanner where

import Control.Monad (void, when)
import Control.Monad.State.Strict
import Data.ByteString.Builder (Builder, char7, toLazyByteString)
import Data.ByteString.Char8 (toStrict)
import qualified Data.ByteString.Char8 as BC
import Data.Char (isAlpha, isDigit)
import Data.Foldable (toList)
import qualified Data.Sequence as Seq
import Debug.Trace (trace)
import Syntax.Token

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

-- | Advance the source by one character.
advance :: Scanner (Maybe Char)
advance = do
  inputBytes <- getSource
  cur <- gets current
  case BC.indexMaybe inputBytes cur of
    Just c -> do
      -- Update location and current position.
      -- Also handle automatic comma insertion at line breaks.
      modify $ \s ->
        let l = loc s
            newLoc = case c of
              '\n' -> l{line = line l + 1, column = 1}
              _ -> l{column = column l + 1}
            newTokens =
              if c == '\n' && shouldInsertComma s
                then
                  tokens s
                    Seq.|> Token
                      { tkType = Comma
                      , -- Comma is added after the last token on the line, which is non-existent in source.
                        tkLoc = (loc s){line = line l, column = column l + 1}
                      , tkLiteral = BC.pack ","
                      }
                else tokens s
         in s{loc = newLoc, current = current s + 1, tokens = newTokens}
      return (Just c)
    Nothing -> return Nothing
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
  shouldInsertComma :: ScannerState -> Bool
  shouldInsertComma s = do
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

-- | Create a token with a function to determine its type and a function to transform its literal.
addTokenTransLit :: (BC.ByteString -> TokenType) -> (BC.ByteString -> BC.ByteString) -> Scanner ()
addTokenTransLit f g = modify $ \s ->
  let
    literal = BC.take (current s) (source s)
    tk =
      Token
        { tkType = f literal
        , tkLoc = startLoc s
        , tkLiteral = g literal
        }
   in
    s{tokens = tokens s Seq.|> tk}

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
    -- Before scanning the next token, reset the current offset.
    resetCurPosLoc
    isEnd <- gets (BC.null . source)
    if isEnd
      then addToken EOF
      else scanToken >> go

-- | Scan a single token from the input.
scanToken :: Scanner ()
scanToken = do
  skipWhitespaceAndComments
  -- If some whitespace or comments were skipped, we need to reset the current offset.
  resetCurPosLoc

  charM <- advance
  case charM of
    Nothing -> return ()
    Just c -> case c of
      '(' -> addToken LParen
      ')' -> addToken RParen
      '{' -> addToken LBrace
      '}' -> addToken RBrace
      '[' -> addToken LSquare
      ']' -> addToken RSquare
      ':' -> addToken Colon
      ',' -> addToken Comma
      '\\' -> addToken Backslash
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
scanString = chars
 where
  chars = do
    ch <- advance
    case ch of
      Nothing -> addInvalidToken (const "Unterminated string literal")
      -- From spec, unicode_char: /* an arbitrary Unicode code point except newline */ .
      Just c -> case c of
        '\n' -> addInvalidToken (const "Unterminated string literal")
        '"' -> addTokenTransLit (const String) (BC.tail . BC.init) -- remove the surrounding quotes
        _ -> chars

-- | Scan multiline string content.
scanMultiline :: Scanner ()
scanMultiline = chars
 where
  chars = do
    ch <- advance
    case ch of
      Nothing -> addInvalidToken (const "Unterminated multiline string literal")
      Just c -> case c of
        -- If we see a quote, we can proceed to check if it's the closing triple quotes without checking newline before
        -- the closing quotes.
        '"' -> close
        _ -> chars
  close = do
    (first, second) <- peek2
    case (first, second) of
      (Just '"', Just '"') ->
        advance
          >> advance
          >>
          -- Remove the first newline plus the triple quotes in the beginning.
          addTokenTransLit (const MultiLineString) (BC.drop 4 . BC.dropEnd 3)
      _ -> addInvalidToken (const "Unterminated multiline string literal")

partitionUnquotedStr :: Token -> Either Token [Token]
partitionUnquotedStr tk = do
  let final =
        execState
          (runScanner $ scanPartitions mempty)
          ( ScannerState
              { source = tk.tkLiteral
              , startLoc = tk.tkLoc
              , loc = tk.tkLoc
              , current = 0
              , tokens = Seq.empty
              , invalids = Seq.empty
              }
          )
  case toList (invalids final) of
    [] -> Right (toList (tokens final))
    (errToken : _) -> Left errToken

{- | Scan string partitions inside an unquoted string.

The discovered token list might be a list of tokens including the string token and the interpolation token.

It also handles escaped characters like \n, \t, etc.
-}
scanPartitions :: Builder -> Scanner ()
scanPartitions b = do
  ch <- peek
  case ch of
    -- EOF, there might be some non-empty string characters to add.
    Nothing -> addNonEmptyChars
    Just c | c == '\\' -> do
      nextCh <- peekNext
      case nextCh of
        Nothing -> addInvalidToken (const "Unterminated escape sequence")
        Just '(' -> do
          -- We have detected an interpolation. There might be some non-empty string characters before it.
          addNonEmptyChars
          advance
            >> advance
            >> scanInterEnd
            >>
            -- Remove the surrounding \(...).
            addTokenTransLit (const Interpolation) (BC.drop 2 . BC.init)
          scanPartitions mempty
        -- It is an escaped character, continue scanning interpolation.
        Just nextC -> handleChar nextC True
    -- Regular character, continue scanning.
    Just c -> handleChar c False
 where
  scanInterEnd = do
    ch <- advance
    case ch of
      Nothing -> addInvalidToken (const "Unterminated interpolation")
      Just c -> case c of
        ')' -> return ()
        '\n' -> addInvalidToken (const "Unterminated interpolation")
        _ -> scanInterEnd

  handleChar :: Char -> Bool -> Scanner ()
  handleChar c True = do
    void advance -- consume the backslash
    void advance -- consume the escaped character
    let m = case c of
          'a' -> Just '\a'
          'b' -> Just '\b'
          'f' -> Just '\f'
          'n' -> Just '\n'
          'r' -> Just '\r'
          't' -> Just '\t'
          'v' -> Just '\v'
          '/' -> Just '/'
          _ -> Nothing

    case m of
      Nothing -> addInvalidToken (const $ "Invalid escape character: \\" <> BC.singleton c)
      Just escapedC -> scanPartitions (b <> char7 escapedC)
  handleChar c False = advance >> scanPartitions (b <> char7 c)

  -- Add string token if there are non-empty characters consumed.
  addNonEmptyChars = do
    cur <- gets current
    when (cur > 0) $
      addTokenTransLit (const String) (const $ let x = toStrict $ toLazyByteString b in x)
        >> resetCurPosLoc

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