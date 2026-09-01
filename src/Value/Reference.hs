{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}

module Value.Reference where

import Control.DeepSeq (NFData)
import qualified Data.Sequence as Seq
import EvalAddr (EvalAddr, Feature)
import GHC.Generics (Generic)
import StringIndex (TextIndex)
import {-# SOURCE #-} Value.Val

-- | Reference denotes a reference starting with an identifier.
data Reference = Reference
  { ident :: TextIndex
  , identFeat :: Feature
  , selectors :: Seq.Seq VNode
  , selectorTypes :: Seq.Seq Bool
  -- ^ selectorTypes stores the type of each selector, where True means index select (e.g. `a[0]`) and False means field
  --   select (e.g. `a.b`).
  , resolvedIdentType :: RefIdentType
  , identLocator :: IdentLocator
  -- ^ The absolute or deferred locator of the identifier.
  , resolvedFullAddr :: Maybe EvalAddr
  -- ^ The resolved full address of the reference.
  , resolvedComprehClauseIdx :: Maybe Int
  -- ^ The resolved comprehension binding of the reference, represented as (comprehension depth, identifier).
  , isRefCycle :: !Bool
  }
  deriving (Generic)

data RefIdentType
  = ITField
  | ITLetBinding
  | ITIterBinding
  deriving (Eq, Show, Generic, NFData)

{- | A normalized relative path from an identifier's defining scope down to
the lexical scope containing its reference.

Transient constraint and operation segments are removed before a 'ScopeDiff'
is stored. The path remains relative and is not itself an absolute evaluator
address.
-}
newtype ScopeDiff = ScopeDiff {getScopeDiff :: EvalAddr}
  deriving (Eq, Show, Generic, NFData)

{- | How to locate the identifier from which a reference starts.

'AbsoluteIdentAddr' records an address that is already absolute in an evaluator
namespace. 'LexicalIdent' is a deferred lexical relocation used
when an identifier is defined inside a comprehension-generated scope. Its
payload is the reduced path from the identifier's defining scope down to the
scope containing the reference. At evaluation time that suffix is removed from
the reference's actual containing scope, and 'identFeat' is appended to recover
the identifier's absolute address.

For example:

@
data: {x: 1}
for k, _ in data {
    (k): {
        a: 1
        nested: {b: a}
    }
}
@

During translation the generated label @(k)@ is not yet known, so the reference
@a@ in @b@ cannot be assigned an absolute address such as @/x/a@. The defining
scope of @a@ is one surviving segment above the scope of @b@, so the stored
difference is @nested@. Once the comprehension materializes the structure at
@/x@, the evaluator resolves the reference from its actual scope
@/x/nested@ by removing @nested@ and appending @a@, producing @/x/a@.

Iteration bindings such as @k@ are handled separately through the comprehension
binding stack; this deferred locator is for ordinary fields, let bindings, and
other lexical identifiers declared in generated scopes.
-}
data IdentLocator
  = -- | An identifier whose absolute evaluator address is already known.
    AbsoluteIdentAddr EvalAddr
  | -- | A deferred identifier whose absolute address depends on its eventual
    -- location in a generated value.
    LexicalIdent ScopeDiff
  deriving (Eq, Show, Generic, NFData)

mapRefSels :: (Seq.Seq VNode -> Seq.Seq VNode) -> Reference -> Reference
mapRefSels f ref = ref{selectors = f (selectors ref)}

singletonIdentRef :: TextIndex -> Feature -> RefIdentType -> IdentLocator -> Reference
singletonIdentRef ident identFeat typ locator =
  Reference
    { ident = ident
    , identFeat
    , selectors = Seq.empty
    , selectorTypes = Seq.empty
    , resolvedIdentType = typ
    , identLocator = locator
    , resolvedFullAddr = Nothing
    , resolvedComprehClauseIdx = Nothing
    , isRefCycle = False
    }

comprehensionIdentRef :: TextIndex -> Feature -> Int -> IdentLocator -> Reference
comprehensionIdentRef ident identFeat cIdx locator =
  Reference
    { ident = ident
    , identFeat
    , selectors = Seq.empty
    , selectorTypes = Seq.empty
    , resolvedIdentType = ITIterBinding
    , identLocator = locator
    , resolvedFullAddr = Nothing
    , resolvedComprehClauseIdx = Just cIdx
    , isRefCycle = False
    }

appendRefArg :: VNode -> Bool -> Reference -> Reference
appendRefArg v typ ref = ref{selectors = selectors ref Seq.|> v, selectorTypes = selectorTypes ref Seq.|> typ}

{- | ValueSelect denotes a select operation with a base and multiple selectors.

The base (receiver) is a value instead of an identifier.
-}
data ValueSelect = ValueSelect
  { bvID :: !Int
  , base :: VNode
  , iSelectors :: Seq.Seq VNode
  , iSelectorTypes :: Seq.Seq Bool
  }
  deriving (Generic)

appendValueSelectArg :: VNode -> Bool -> ValueSelect -> ValueSelect
appendValueSelectArg y typ vs = vs{iSelectors = iSelectors vs Seq.|> y, iSelectorTypes = iSelectorTypes vs Seq.|> typ}
