{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Syntax.AST where

import Control.DeepSeq (NFData (..))
import Control.Monad (foldM)
import Control.Monad.State.Strict (MonadState, evalState, gets, modify')
import Data.ByteString.Builder (Builder, byteString, char7, string7, toLazyByteString)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import GHC.Generics (Generic)
import Syntax.Token
import Prelude hiding (GT, LT)

newtype SourceFile = SourceFile
  { sfDecls :: [Declaration]
  }
  deriving (Eq, Show)

class ASTNode a where
  getNodeLoc :: a -> Location

data Expression
  = Unary UnaryExpr
  | Binary Token Expression Expression
  deriving (Eq, Show, Generic, NFData)

instance ASTNode Expression where
  getNodeLoc (Unary ue) = getNodeLoc ue
  getNodeLoc (Binary op _ _) = op.tkLoc

data UnaryExpr
  = Primary PrimaryExpr
  | UnaryOp Token UnaryExpr
  deriving (Eq, Show, Generic, NFData)

instance ASTNode UnaryExpr where
  getNodeLoc (Primary pe) = getNodeLoc pe
  getNodeLoc (UnaryOp op _) = op.tkLoc

data PrimaryExpr
  = PrimExprOperand Operand
  | -- | Field selection, e.g., `a.b`. The location is that of the dot.
    PrimExprSelector PrimaryExpr Location Selector
  | -- | Indexing, e.g., `a[0]`. The locations are that of the square brackets.
    PrimExprIndex PrimaryExpr Location Expression Location
  | -- | Function call arguments, e.g., `f(x, y)`. The locations are that of the parentheses.
    PrimExprArguments PrimaryExpr Location [Expression] Location
  deriving (Eq, Show, Generic, NFData)

instance ASTNode PrimaryExpr where
  getNodeLoc (PrimExprOperand op) = getNodeLoc op
  getNodeLoc (PrimExprSelector pe _ _) = getNodeLoc pe
  getNodeLoc (PrimExprIndex pe _ _ _) = getNodeLoc pe
  getNodeLoc (PrimExprArguments pe _ _ _) = getNodeLoc pe

data Selector
  = IDSelector Token
  | StringSelector SimpleStringLit
  deriving (Eq, Show, Generic, NFData)

data Operand
  = OpLiteral Literal
  | OpName OperandName
  | -- | Parenthesized expression. The locations are that of the parentheses.
    OpExpression Location Expression Location
  deriving (Eq, Show, Generic, NFData)

instance ASTNode Operand where
  getNodeLoc (OpLiteral lit) = getNodeLoc lit
  getNodeLoc (OpName on) = getNodeLoc on
  getNodeLoc (OpExpression loc _ _) = loc

data Literal
  = LitBasic BasicLit
  | LitStruct StructLit
  | LitList ListLit
  deriving (Eq, Show, Generic, NFData)

instance ASTNode Literal where
  getNodeLoc (LitBasic b) = getNodeLoc b
  getNodeLoc (LitStruct s) = getNodeLoc s
  getNodeLoc (LitList l) = getNodeLoc l

data ListLit
  = -- | Locations are that of the brackets.
    ListLit Location ElementList Location
  deriving (Eq, Show, Generic, NFData)

instance ASTNode ListLit where
  getNodeLoc (ListLit loc _ _) = loc

data StructLit
  = -- | Locations are that of the braces.
    StructLit Location [Declaration] Location
  deriving (Eq, Show, Generic, NFData)

instance ASTNode StructLit where
  getNodeLoc (StructLit loc _ _) = loc

data BasicLit
  = IntLit Token
  | FloatLit Token
  | BoolLit Token
  | NullLit Token
  | BottomLit Token
  | StringLit StringLit
  deriving (Eq, Show, Generic, NFData)

instance ASTNode BasicLit where
  getNodeLoc (IntLit t) = t.tkLoc
  getNodeLoc (FloatLit t) = t.tkLoc
  getNodeLoc (BoolLit t) = t.tkLoc
  getNodeLoc (NullLit t) = t.tkLoc
  getNodeLoc (BottomLit t) = t.tkLoc
  getNodeLoc (StringLit s) = getNodeLoc s

data StringLit
  = SimpleStringL SimpleStringLit
  | MultiLineStringL MultiLineStringLit
  deriving (Eq, Show, Generic, NFData)

instance ASTNode StringLit where
  getNodeLoc (SimpleStringL s) = getNodeLoc s
  getNodeLoc (MultiLineStringL s) = getNodeLoc s

data SimpleStringLit = SimpleStringLit Location [StringLitSeg]
  deriving (Eq, Show, Generic, NFData)

instance ASTNode SimpleStringLit where
  getNodeLoc (SimpleStringLit loc _) = loc

data MultiLineStringLit = MultiLineStringLit Location [StringLitSeg]
  deriving (Eq, Show, Generic, NFData)

instance ASTNode MultiLineStringLit where
  getNodeLoc (MultiLineStringLit loc _) = loc

data StringLitSeg
  = UnicodeChars T.Text
  | Interpolation Location Expression
  deriving (Eq, Show, Generic, NFData)

newtype Label = Label LabelExpr deriving (Eq, Show, Generic, NFData)

data Declaration
  = FieldDecl FieldDecl
  | EllipsisDecl EllipsisDecl
  | Embedding Embedding
  | DeclLet LetClause
  deriving (Eq, Show, Generic, NFData)

data FieldDecl
  = Field [Label] Expression
  deriving (Eq, Show, Generic, NFData)

data EllipsisDecl
  = -- | Location is that of the ellipsis token.
    Ellipsis Location (Maybe Expression)
  deriving (Eq, Show, Generic, NFData)

newtype ElementList = EmbeddingList [Embedding] deriving (Eq, Show, Generic, NFData)

newtype OperandName = OperandName Token deriving (Eq, Show, Generic, NFData)

instance ASTNode OperandName where
  getNodeLoc (OperandName tk) = tk.tkLoc

data LabelExpr
  = -- | A label name with an optional constraint. The constraint is either question mark (?) for optional labels or
    -- exclamation mark (!) for required labels.
    LabelName LabelName (Maybe TokenType)
  | -- | A label expression. The location is that of the square brackets.
    LabelExpr Location Expression Location
  deriving (Eq, Show, Generic, NFData)

data LabelName
  = LabelID Token
  | LabelString SimpleStringLit
  | -- | Parenthesized expression. The locations are that of the parentheses.
    LabelNameExpr Location Expression Location
  deriving (Eq, Show, Generic, NFData)

data Embedding = EmbedComprehension Comprehension | AliasExpr Expression
  deriving (Eq, Show, Generic, NFData)

data Comprehension = Comprehension Clauses StructLit
  deriving (Eq, Show, Generic, NFData)

data Clauses = Clauses StartClause [Clause] deriving (Eq, Show, Generic, NFData)

data StartClause
  = -- | GuardClause is an "if" expression
    -- The location is that of the "if" token.
    GuardClause Location Expression
  | -- | ForClause is a "for" expression
    -- The location is that of the "for" token.
    -- The first Token is the identifier.
    -- The Maybe Token is the optional second identifier.
    ForClause Location Token (Maybe Token) Expression
  deriving (Eq, Show, Generic, NFData)

data Clause
  = ClauseStart StartClause
  | ClauseLet LetClause
  deriving (Eq, Show, Generic, NFData)

data LetClause
  = -- | The location is that of the "let" token.
    LetClause Location Token Expression
  deriving (Eq, Show, Generic, NFData)

binaryOpPrec :: TokenType -> Int
binaryOpPrec Unify = 2
binaryOpPrec Disjoin = 1
binaryOpPrec Plus = 6
binaryOpPrec Minus = 6
binaryOpPrec Multiply = 7
binaryOpPrec Divide = 7
binaryOpPrec Equal = 4
binaryOpPrec NotEqual = 4
binaryOpPrec Less = 4
binaryOpPrec LessEqual = 4
binaryOpPrec Greater = 4
binaryOpPrec GreaterEqual = 4
binaryOpPrec Match = 4
binaryOpPrec NotMatch = 4
binaryOpPrec _ = 0

textToSimpleStrLiteral :: T.Text -> Literal
textToSimpleStrLiteral s = LitBasic $ Syntax.AST.StringLit $ SimpleStringL $ textToSimpleStrLit s

textToMultiLineLiteral :: T.Text -> Literal
textToMultiLineLiteral s =
  LitBasic $ Syntax.AST.StringLit $ MultiLineStringL $ MultiLineStringLit emptyLoc [UnicodeChars s]

textToSimpleStrLit :: T.Text -> SimpleStringLit
textToSimpleStrLit s = SimpleStringLit emptyLoc [UnicodeChars s]

litCons :: Literal -> Expression
litCons x = Unary $ Primary $ PrimExprOperand $ OpLiteral x

idCons :: T.Text -> Expression
idCons x = Unary $ Primary $ idToPrimExpr x

idToPrimExpr :: T.Text -> PrimaryExpr
idToPrimExpr x = PrimExprOperand $ OpName $ OperandName $ Token Identifier emptyLoc (TE.encodeUtf8 x)

-- == Below are functions for pretty printing the AST ==

exprToStr :: Expression -> String
exprToStr e = show $ toLazyByteString $ exprToBuilder False e

exprToOneLinerStr :: Expression -> String
exprToOneLinerStr e = show $ toLazyByteString $ exprToBuilder True e

exprToBuilder :: Bool -> Expression -> Builder
exprToBuilder oneLiner e = evalState (exprBld e) (ASTBuilderState 0 oneLiner)

exprToOneLinerBuilder :: Expression -> Builder
exprToOneLinerBuilder = exprToBuilder True

declsToBuilder :: [Declaration] -> Builder
declsToBuilder decls = evalState (declsBld decls) (ASTBuilderState 0 False)

data ASTBuilderState = ASTBuilderState
  { absIndent :: Int
  , absOneLiner :: Bool
  }
  deriving (Eq, Show)

type M = MonadState ASTBuilderState

getIndent :: (M m) => m Int
getIndent = gets absIndent

getOneLiner :: (M m) => m Bool
getOneLiner = gets absOneLiner

withIncIndent :: (M m) => m a -> m a
withIncIndent action = do
  indent <- getIndent
  modify' (\s -> s{absIndent = indent + 1})
  r <- action
  modify' (\s -> s{absIndent = indent})
  return r

exprBld :: (M m) => Expression -> m Builder
exprBld e = case e of
  Unary ue -> unaryBld ue
  Binary op e1 e2 -> do
    b1 <- wrapParensIfNeeded e1 op
    b2 <- wrapParensIfNeeded e2 op
    return $
      b1 <> char7 ' ' <> tokenBuilder op <> char7 ' ' <> b2
 where
  wrapParensIfNeeded operand@((Binary op1 _ _)) op = do
    operandB <- exprBld operand
    return $
      if binaryOpPrec op1.tkType < binaryOpPrec op.tkType
        then char7 '(' <> operandB <> char7 ')'
        else operandB
  wrapParensIfNeeded operand _ = exprBld operand

tokenBuilder :: Token -> Builder
tokenBuilder tk = byteString tk.tkLiteral

unaryBld :: (M m) => UnaryExpr -> m Builder
unaryBld e = case e of
  Primary pe -> primBld pe
  UnaryOp op ue -> do
    b <- unaryBld ue
    return $ tokenBuilder op <> b

primBld :: (M m) => PrimaryExpr -> m Builder
primBld e = case e of
  PrimExprOperand op -> opndBld op
  PrimExprSelector pe _ sel -> do
    b <- primBld pe
    b2 <- selBld sel
    return $ b <> string7 "." <> b2
  PrimExprIndex pe _ ie _ -> do
    b1 <- primBld pe
    b2 <- exprBld ie
    return $ b1 <> string7 "[" <> b2 <> string7 "]"
  PrimExprArguments pe _ es _ -> do
    b <- primBld pe
    (argsB, _) <-
      foldM
        ( \(acc, started) x -> do
            xb <- exprBld x
            return (if not started then xb else acc <> string7 ", " <> xb, True)
        )
        (mempty, False)
        es
    return $ b <> string7 "(" <> argsB <> string7 ")"

selBld :: (M m) => Selector -> m Builder
selBld e = case e of
  IDSelector is -> return $ byteString is.tkLiteral
  StringSelector s -> simpleStrLitBld s

opndBld :: (M m) => Operand -> m Builder
opndBld op = case op of
  OpLiteral lit -> litBld lit
  OpName on -> return $ opNameBld on
  OpExpression _ e _ -> exprBld e

opNameBld :: OperandName -> Builder
opNameBld (OperandName tk) = byteString tk.tkLiteral

litBld :: (M m) => Literal -> m Builder
litBld (LitBasic b) = case b of
  Syntax.AST.IntLit t -> return $ tokenBuilder t
  Syntax.AST.FloatLit t -> return $ tokenBuilder t
  Syntax.AST.BoolLit t -> return $ tokenBuilder t
  Syntax.AST.BottomLit t -> return $ tokenBuilder t
  Syntax.AST.NullLit t -> return $ tokenBuilder t
  Syntax.AST.StringLit s -> strLitBld s
litBld (LitStruct l) = structLitBld l
litBld (LitList (ListLit _ l _)) = listBld l

strLitBld :: (M m) => StringLit -> m Builder
strLitBld (SimpleStringL s) = do
  b <- simpleStrLitBld s
  return $ char7 '"' <> b <> char7 '"'
strLitBld (MultiLineStringL s) = do
  b <- multilineStrLitBld s
  return $ string7 "\"\"\"\n" <> b <> string7 "\"\"\""

-- | TODO: efficiency
simpleStrLitBld :: (M m) => SimpleStringLit -> m Builder
simpleStrLitBld (SimpleStringLit _ segs) =
  foldM
    ( \acc seg -> do
        b <- strLitSegBld seg
        return $ acc <> b
    )
    mempty
    segs

multilineStrLitBld :: (M m) => MultiLineStringLit -> m Builder
multilineStrLitBld (Syntax.AST.MultiLineStringLit _ segs) =
  foldM
    ( \acc seg -> do
        b <- strLitSegBld seg
        return $ acc <> b
    )
    mempty
    segs

strLitSegBld :: (M m) => StringLitSeg -> m Builder
strLitSegBld (UnicodeChars chs) = return $ string7 (T.unpack chs)
strLitSegBld (Syntax.AST.Interpolation _ e) = do
  b <- exprBld e
  return $ string7 "\\(" <> b <> char7 ')'

structLitBld :: (M m) => StructLit -> m Builder
structLitBld (StructLit _ decls _)
  | null decls = return $ string7 "{}"
  | otherwise = do
      indent <- getIndent
      oneLiner <- getOneLiner
      if oneLiner
        then do
          -- When one-liner is set, we do not add new lines or indentation.
          declsB <- declsBld decls
          return $ string7 "{" <> declsB <> string7 "}"
        else do
          declsB <- withIncIndent $ declsBld decls
          return $ string7 "{\n" <> declsB <> indentBld indent <> char7 '}'

declsBld :: (M m) => [Declaration] -> m Builder
declsBld [] = return $ string7 ""
declsBld (x : xs) = do
  b <- declBld x
  rest <- declsBld xs
  oneLiner <- getOneLiner
  if oneLiner
    then
      -- When one-liner is set, we do not add new lines or indentation.
      return $ b <> (if null xs then mempty else string7 ",") <> rest
    else do
      indent <- getIndent
      return $ indentBld indent <> b <> char7 '\n' <> rest

declBld :: (M m) => Declaration -> m Builder
declBld e = case e of
  FieldDecl f -> fieldDeclBld f
  EllipsisDecl (Syntax.AST.Ellipsis _ eM) -> case eM of
    Nothing -> return $ string7 "..."
    Just e' -> do
      b <- exprBld e'
      return $ string7 "..." <> char7 ' ' <> b
  Embedding eb -> embeddingBld eb
  DeclLet (LetClause _ ident binde) -> do
    b <- exprBld binde
    return $ string7 "let " <> byteString ident.tkLiteral <> string7 " = " <> b

fieldDeclBld :: (M m) => FieldDecl -> m Builder
fieldDeclBld e = case e of
  Field ls fe -> do
    declB <- exprBld fe
    labels <-
      foldM
        ( \acc l -> do
            lb <- labelBld l
            return $ acc <> lb <> string7 ": "
        )
        mempty
        ls
    return $ labels <> declB

embeddingBld :: (M m) => Embedding -> m Builder
embeddingBld e = case e of
  EmbedComprehension _ -> return $ string7 "<undefined>"
  AliasExpr ex -> exprBld ex

listBld :: (M m) => ElementList -> m Builder
listBld (EmbeddingList l) = do
  b <- goList l
  return $ string7 "[" <> b
 where
  goList [] = return $ string7 "]"
  goList [x] = do
    b <- embeddingBld x
    return $ b <> string7 "]"
  goList (x : xs) = do
    b <- embeddingBld x
    rest <- goList xs
    return $ b <> string7 ", " <> rest

labelBld :: (M m) => Label -> m Builder
labelBld (Label e) = labelExprBld e

labelExprBld :: (M m) => LabelExpr -> m Builder
labelExprBld e = case e of
  LabelName ln cnstr -> case cnstr of
    Nothing -> labelNameBld ln
    Just QuestionMark -> do
      b <- labelNameBld ln
      return $ b <> string7 "?"
    Just Exclamation -> do
      b <- labelNameBld ln
      return $ b <> string7 "!"
    _ -> error "Unsupported label constraint"
  -- The LabelPattern should not be exported.
  LabelExpr _ le _ -> do
    b <- exprBld le
    return $ string7 "[" <> b <> string7 "]"

labelNameBld :: (M m) => LabelName -> m Builder
labelNameBld e = case e of
  LabelID ident -> return $ byteString ident.tkLiteral
  LabelString s -> simpleStrLitBld s
  LabelNameExpr _ ex _ -> do
    b <- exprBld ex
    return $ char7 '(' <> b <> char7 ')'

indentBld :: Int -> Builder
indentBld indent = string7 (replicate (indent * tabSize) ' ')

tabSize :: Int
tabSize = 4
