module Query (
  prettyConstraints,
  queryValue,
  renderExplanation,
  renderVNode,
)
where

import Control.Monad.Except (runExcept, runExceptT, throwError)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.RWS.Strict (runRWST)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import Data.Foldable (toList)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Sequence as Seq
import EvalAddr (fileTopEvalAddr)
import Reduce.Core (reduceConstraintPass)
import Reduce.Monad (RM, getRMContext, modifyRMContext)
import qualified Reduce.Monad as Reduce
import Reduce.Reference (concreteRefSels, descend)
import Reduce.Store (fetchValMust)
import qualified Semant.Semant as Semant
import StringIndex (TextIndexer)
import Syntax.AST (
  Expression (..),
  Operand (..),
  OperandName (..),
  PrimaryExpr (..),
  UnaryExpr (..),
  exprToOneLinerStr,
  getNodeLoc,
 )
import Syntax.Parser (parseExpr)
import Syntax.Scanner (scanTokens)
import Syntax.Token (Location (..), Token)
import Value

queryValue :: B.ByteString -> RM VNode
queryValue source = do
  tokens <- either (throwError . show) return (scanTokens source)
  expr <- either throwError return (parseExpr tokens)
  rootIdent <-
    maybe
      (throwError "query must be a reference rooted at a file-level identifier")
      return
      (queryRootIdent expr)
  queryVNode <- translateQuery rootIdent expr
  ref <- case queryVNode of
    IsValSoleStaticOp (Ref r) -> return r
    _ -> throwError "query expression did not translate to a reference"

  identAddr <- case ref.identLocator of
    AbsoluteIdentAddr addr -> return addr
    LexicalIdent _ -> throwError "query identifier did not resolve to an absolute address"
  identValue <- fetchValMust "queryValue" identAddr

  reducedSelectors <- traverse (reduceConstraintPass fileTopEvalAddr) ref.selectors
  selectorsM <- concreteRefSels ref{selectors = reducedSelectors}
  selectors <- maybe (throwError "query selectors are not concrete") return selectorsM
  (_, targetM) <- descend identAddr identValue selectors
  maybe (throwError "query value not found") return targetM

translateQuery :: Token -> Expression -> RM VNode
translateQuery rootIdent expr = do
  context <- getRMContext
  let initialState = Semant.mkTransState (Reduce.tIndexer context)
  translated <-
    liftIO $
      runExceptT $
        runRWST
          (Semant.transQueryExprToVal rootIdent expr fileTopEvalAddr)
          ()
          initialState
  case translated of
    Left (Semant.SemantErr msg) -> throwError msg
    Left (Semant.FatalErr msg) -> throwError msg
    Right (vnode, transState, _) -> do
      modifyRMContext $ \ctx -> ctx{Reduce.tIndexer = Semant.tIndexer transState}
      return vnode

queryRootIdent :: Expression -> Maybe Token
queryRootIdent (Unary (Primary primary)) = primaryRootIdent primary
queryRootIdent _ = Nothing

primaryRootIdent :: PrimaryExpr -> Maybe Token
primaryRootIdent primary = case primary of
  PrimExprOperand (OpName (OperandName ident)) -> Just ident
  PrimExprOperand (OpExpression _ expr _) -> queryRootIdent expr
  PrimExprSelector base _ _ -> primaryRootIdent base
  PrimExprIndex base _ _ _ -> primaryRootIdent base
  _ -> Nothing

prettyConstraints :: TextIndexer -> VNode -> IO ()
prettyConstraints textIndexer = putStr . renderConstraints textIndexer

renderExplanation :: TextIndexer -> B.ByteString -> VNode -> String
renderExplanation textIndexer query vnode =
  BC.unpack query
    ++ " = "
    ++ renderVNode textIndexer (removeConstraints vnode)
    ++ "\n\n"
    ++ renderConstraints textIndexer vnode

renderConstraints :: TextIndexer -> VNode -> String
renderConstraints textIndexer vnode =
  let cnstrs =
        toList vnode.constraints.static
          ++ concatMap toList (IntMap.elems vnode.constraints.dynamic)
      renderedCnstrs = map (renderConstraint textIndexer) cnstrs
      maxConstraintWidth = maximum (0 : map length renderedCnstrs)
      renderLine i cnstr rendered =
        let branch = if i == length cnstrs - 1 then "└─" else "├─"
            padding = replicate (maxConstraintWidth - length rendered + 4) ' '
         in branch ++ " " ++ rendered ++ padding ++ formatLocation (getNodeLoc cnstr)
      renderedLines = case zip3 [0 ..] cnstrs renderedCnstrs of
        [] -> ["└─ (none)"]
        xs -> map (\(i, cnstr, rendered) -> renderLine i cnstr rendered) xs
   in unlines $
        ["Conjuncts:"]
          ++ renderedLines

renderConstraint :: TextIndexer -> Constraint -> String
renderConstraint textIndexer cnstr =
  renderVNode
    textIndexer
    emptyVNode
      { constraints = emptyConstraintsSet{static = Seq.singleton cnstr}
      }

renderVNode :: TextIndexer -> VNode -> String
renderVNode textIndexer vnode =
  case runExcept $ buildExpr vnode textIndexer of
    Left err -> "<unable to render: " ++ err ++ ">"
    Right (expr, _) -> exprToOneLinerStr expr

formatLocation :: Location -> String
formatLocation Location{line, column, filePath} =
  maybe "-" (\path -> if null path then "-" else path) filePath ++ ":" ++ show line ++ ":" ++ show column
