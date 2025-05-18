{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Comprehension where

import qualified AST
import qualified Common
import Exception (throwErrSt)

data Comprehension t = Comprehension
  { cphIsListCompreh :: Bool
  , cphIterClauses :: [IterClause t]
  , cphStruct :: t
  , cphIterBindings :: [ComprehIterBinding t]
  -- ^ Bindings are temporary on each iteration.
  , cphIterVal :: Maybe t
  , cphValue :: Maybe t
  }
  deriving (Eq, Show)

buildComprehASTExpr :: (Common.Env r s m, Common.BuildASTExpr t) => Bool -> Comprehension t -> m AST.Comprehension
buildComprehASTExpr c cph = do
  start <- buildStartClause (head (cphIterClauses cph))
  rest <- mapM buildIterClause (tail (cphIterClauses cph))

  e <- Common.buildASTExpr c (cphStruct cph)
  sl <- case e of
    AST.ExprUnaryExpr (AST.UnaryExprPrimaryExpr (AST.PrimExprOperand (AST.OpLiteral (AST.LitStructLit l)))) -> return l
    _ -> throwErrSt "struct lit is not found"
  return $ AST.Comprehension (AST.Clauses start rest) sl
 where
  buildStartClause clause = case clause of
    IterClauseIf val -> do
      ve <- Common.buildASTExpr c val
      return (AST.GuardClause ve)
    IterClauseFor varName secVarM val -> do
      ve <- Common.buildASTExpr c val
      return (AST.ForClause varName secVarM ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    IterClauseLet varName val -> do
      ve <- Common.buildASTExpr c val
      return $ AST.ClauseLetClause (AST.LetClause varName ve)
    _ -> do
      start <- buildStartClause clause
      return $ AST.ClauseStartClause start

data IterClause t = IterClauseLet String t | IterClauseIf t | IterClauseFor String (Maybe String) t
  deriving (Eq, Show, Functor)

mkComprehension :: Bool -> [IterClause t] -> t -> Comprehension t
mkComprehension isListCompreh clauses sv =
  Comprehension
    { cphIsListCompreh = isListCompreh
    , cphIterClauses = clauses
    , cphStruct = sv
    , cphIterBindings = []
    , cphIterVal = Nothing
    , cphValue = Nothing
    }

getValFromIterClause :: IterClause t -> t
getValFromIterClause (IterClauseLet _ v) = v
getValFromIterClause (IterClauseIf v) = v
getValFromIterClause (IterClauseFor _ _ v) = v

data ComprehIterBinding t = ComprehIterBinding
  { cphBindName :: String
  , cphBindValue :: t
  }
  deriving (Eq, Show)