{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ViewPatterns #-}

module Value.Comprehension where

import qualified AST
import qualified Common
import Control.DeepSeq (NFData (..))
import qualified Data.Text as T
import Exception (throwErrSt)
import GHC.Generics (Generic)

data Comprehension t = Comprehension
  { cphIsListCompreh :: !Bool
  , cphIterClauses :: [IterClause t]
  , cphStruct :: t
  , cphIterBindings :: [ComprehIterBinding t]
  -- ^ Bindings are temporary on each iteration.
  , cphIterVal :: Maybe t
  , cphValue :: Maybe t
  }
  deriving (Eq, Show, Generic, NFData)

buildComprehASTExpr :: (Common.Env r s m, Common.BuildASTExpr t) => Bool -> Comprehension t -> m AST.Comprehension
buildComprehASTExpr c cph = do
  start <- buildStartClause (head (cphIterClauses cph))
  rest <- mapM buildIterClause (tail (cphIterClauses cph))

  e <- Common.buildASTExpr c (cphStruct cph)
  sl <- case AST.wpVal e of
    AST.ExprUnaryExpr
      ( AST.wpVal ->
          AST.UnaryExprPrimaryExpr
            ( AST.wpVal ->
                AST.PrimExprOperand
                  ( AST.wpVal ->
                      AST.OpLiteral
                        (AST.wpVal -> AST.LitStructLit l)
                    )
              )
        ) -> return l
    _ -> throwErrSt "struct lit is not found"
  return $
    pure $
      AST.Comprehension (pure $ AST.Clauses (pure start) (map pure rest)) sl
 where
  buildStartClause clause = case clause of
    IterClauseIf val -> do
      ve <- Common.buildASTExpr c val
      return (AST.GuardClause ve)
    IterClauseFor varName secVarM val -> do
      ve <- Common.buildASTExpr c val
      return (AST.ForClause (pure varName) (pure <$> secVarM) ve)
    _ -> throwErrSt "start clause should not be let clause"

  buildIterClause clause = case clause of
    IterClauseLet varName val -> do
      ve <- Common.buildASTExpr c val
      return $ AST.ClauseLetClause (pure $ AST.LetClause (pure varName) ve)
    _ -> do
      start <- buildStartClause clause
      return $ AST.ClauseStartClause (pure start)

data IterClause t = IterClauseLet T.Text t | IterClauseIf t | IterClauseFor T.Text (Maybe T.Text) t
  deriving (Eq, Show, Functor, Generic, NFData)

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
  { cphBindName :: T.Text
  , cphBindValue :: t
  }
  deriving (Eq, Show, Generic, NFData)