module VTermTest (tests) where

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Feature
import StringIndex (TextIndex (..))
import Syntax.Token (emptyLoc)
import Test.Tasty
import Test.Tasty.HUnit
import Value

tests :: TestTree
tests =
  testGroup
    "VTerm immediate children"
    [ testCase "VNode unwraps and rebuilds static constraints" testStaticConstraints
    , testCase "VNode exposes dynamic and embedded constraint sequences" testConstraintSequences
    , testCase "struct exposes VNode, Val, and constraint-sequence children" testStructChildren
    , testCase "operations use their structural segment tags" testOpChildren
    , testCase "VNode forwards direct operation children through its sole constraint" testDirectOpChildren
    , testCase "missing and mismatched children are rejected" testInvalidChildren
    ]

testStaticConstraints :: Assertion
testStaticConstraints = do
  assertVTVal oldValue $ getChildVT staticValueSegment (VTVNode constraintRoot)
  assertVTOp regularOp $ getChildVT staticOpSegment (VTVNode constraintRoot)

  updatedTerm <- requireJust $ setChildVT staticValueSegment (VTVal newValue) (VTVNode constraintRoot)
  updated <- requireVNode updatedTerm
  updated.version @?= constraintRoot.version
  updated.constraints.allResolved @?= True
  case updated.constraints.static Seq.!? 0 of
    Just (ValCnstr valConstraint) -> do
      valConstraint.vcLoc @?= emptyLoc
      valConstraint.vcVal @?= newValue
    _ -> assertFailure "static value constraint changed its constructor"

  assertVTVal newValue $ getChildVT staticValueSegment updatedTerm

testConstraintSequences :: Assertion
testConstraintSequences = do
  assertVTConstraintSeq embeddedSequence $ getChildVT staticEmbedSegment (VTVNode constraintRoot)
  assertVTConstraintSeq dynamicSequence $ getChildVT dynamicSegment (VTVNode constraintRoot)
  assertVTVal oldValue $ getChildVT sequenceItemSegment (VTConstraintSeq dynamicSequence)

  let replacementSequence = Seq.singleton $ ValCnstr $ ValConstraint emptyLoc newValue
  updatedTerm <- requireJust $ setChildVT dynamicSegment (VTConstraintSeq replacementSequence) (VTVNode constraintRoot)
  assertVTConstraintSeq replacementSequence $ getChildVT dynamicSegment updatedTerm

  updatedSequence <- requireJust $ setChildVT sequenceItemSegment (VTVal newValue) (VTConstraintSeq dynamicSequence)
  assertVTVal newValue $ getChildVT sequenceItemSegment updatedSequence

testStructChildren :: Assertion
testStructChildren = do
  let term = VTVal $ VStruct fixtureStruct
  assertVNode oldNode $ getChildVT fieldSegment term
  assertVTVal oldValue $ getChildVT embedValueSegment term
  assertVNode labelNode $ getChildVT dynamicLabelSegment term
  assertVTConstraintSeq dynamicSequence $ getChildVT dynamicValueSegment term
  assertVNode patternNode $ getChildVT patternNodeSegment term
  assertVTConstraintSeq embeddedSequence $ getChildVT patternValueSegment term

  updated <- requireJust $ setChildVT dynamicValueSegment (VTConstraintSeq embeddedSequence) term
  assertVTConstraintSeq embeddedSequence $ getChildVT dynamicValueSegment updated

testOpChildren :: Assertion
testOpChildren = do
  assertVNode oldNode $ getChildVT opArgSegment (VTOp regularOp)
  updatedRegular <- requireJust $ setChildVT opArgSegment (VTVNode newNode) (VTOp regularOp)
  assertVNode newNode $ getChildVT opArgSegment updatedRegular

  assertVNode oldNode $ getChildVT sequenceItemSegment (VTOp comprehensionOp)
  assertNothing $ getChildVT opArgSegment (VTOp comprehensionOp)

  assertVNode selectBase $ getChildVT objectSegment (VTOp selectOp)
  updatedSelect <- requireJust $ setChildVT objectSegment (VTVNode newNode) (VTOp selectOp)
  assertVNode newNode $ getChildVT objectSegment updatedSelect

testDirectOpChildren :: Assertion
testDirectOpChildren = do
  let regularNode = (mkOpVN emptyLoc regularOp){version = 8}
  assertVNode oldNode $ getChildVT opArgSegment (VTVNode regularNode)
  updatedRegular <- requireJust $ setChildVT opArgSegment (VTVNode newNode) (VTVNode regularNode)
  assertVNode newNode $ getChildVT opArgSegment updatedRegular
  updatedRegularNode <- requireVNode updatedRegular
  updatedRegularNode.version @?= regularNode.version

  let selectNode = mkOpVN emptyLoc selectOp
  assertVNode selectBase $ getChildVT objectSegment (VTVNode selectNode)

testInvalidChildren :: Assertion
testInvalidChildren = do
  assertNothing $ getChildVT missingFieldSegment (VTVal $ VStruct fixtureStruct)
  assertNothing $ getChildVT missingConstraintSegment (VTConstraintSeq dynamicSequence)
  assertNothing $ setChildVT fieldSegment (VTVal newValue) (VTVal $ VStruct fixtureStruct)
  assertNothing $ setChildVT dynamicSegment (VTVNode newNode) (VTVNode constraintRoot)

assertVNode :: VNode -> Maybe VTermNode -> Assertion
assertVNode expected actual = case actual of
  Just (VTVNode node) -> do
    node.value @?= expected.value
    node.version @?= expected.version
  _ -> assertFailure "expected a VTVNode child"

assertVTVal :: Val -> Maybe VTermNode -> Assertion
assertVTVal expected actual = case actual of
  Just (VTVal value) -> value @?= expected
  _ -> assertFailure "expected a VTVal child"

assertVTOp :: Op -> Maybe VTermNode -> Assertion
assertVTOp expected actual = case actual of
  Just (VTOp op) -> op @?= expected
  _ -> assertFailure "expected a VTOp child"

assertVTConstraintSeq :: ConstraintSeq -> Maybe VTermNode -> Assertion
assertVTConstraintSeq expected actual = case actual of
  Just (VTConstraintSeq constraints) -> constraints @?= expected
  _ -> assertFailure "expected a VTConstraintSeq child"

requireJust :: Maybe a -> IO a
requireJust (Just value) = return value
requireJust Nothing = assertFailure "expected child reconstruction to succeed"

assertNothing :: Maybe a -> Assertion
assertNothing Nothing = return ()
assertNothing (Just _) = assertFailure "expected child operation to fail"

requireVNode :: VTermNode -> IO VNode
requireVNode (VTVNode node) = return node
requireVNode _ = assertFailure "expected a reconstructed VTVNode"

fieldKey, missingFieldKey :: TextIndex
fieldKey = TextIndex 1
missingFieldKey = TextIndex 999

dynamicID, patternID, selectID :: Int
dynamicID = 2
patternID = 3
selectID = 4

fieldSegment, missingFieldSegment, embedValueSegment :: AddrSegment
fieldSegment = featureToAddrSegment $ mkStringFeature fieldKey
missingFieldSegment = featureToAddrSegment $ mkStringFeature missingFieldKey
embedValueSegment = termStepToAddrSegment embedValueTermStep

staticValueSegment, staticOpSegment, staticEmbedSegment, sequenceItemSegment, missingConstraintSegment :: AddrSegment
staticValueSegment = termStepToAddrSegment $ mkRegCnstrTermStep 0
staticOpSegment = termStepToAddrSegment $ mkRegCnstrTermStep 1
staticEmbedSegment = termStepToAddrSegment $ mkRegCnstrTermStep 2
sequenceItemSegment = termStepToAddrSegment $ mkRegCnstrTermStep 0
missingConstraintSegment = termStepToAddrSegment $ mkRegCnstrTermStep 99

dynamicSegment, dynamicLabelSegment, dynamicValueSegment, patternNodeSegment, patternValueSegment :: AddrSegment
dynamicSegment = termStepToAddrSegment $ mkDynCnstrTermStep dynamicID
dynamicLabelSegment = termStepToAddrSegment $ mkDynFieldTermStep dynamicID 0
dynamicValueSegment = termStepToAddrSegment $ mkDynFieldTermStep dynamicID 1
patternNodeSegment = termStepToAddrSegment $ mkPatternTermStep patternID 0
patternValueSegment = termStepToAddrSegment $ mkPatternTermStep patternID 1

opArgSegment, objectSegment :: AddrSegment
opArgSegment = termStepToAddrSegment $ mkOpArgTermStep 0
objectSegment = termStepToAddrSegment $ mkObjectTermStep selectID

oldValue, newValue :: Val
oldValue = VAtom $ Int 10
newValue = VAtom $ Int 20

oldNode, newNode, labelNode, patternNode, selectBase :: VNode
oldNode = (mkAtomVN $ Int 1){version = 1}
newNode = (mkAtomVN $ Int 2){version = 2}
labelNode = (mkAtomVN $ String "dynamic"){version = 3}
patternNode = (mkAtomVN $ String "pattern"){version = 4}
selectBase = (mkAtomVN $ Int 5){version = 5}

regularOp, comprehensionOp, selectOp :: Op
regularOp = RegOp emptyRegularOp{ropArgs = Seq.singleton oldNode}
comprehensionOp = Compreh $ mkComprehension 5 False [ComprehArgIf oldNode] newNode
selectOp =
  VSelect
    ValueSelect
      { bvID = selectID
      , base = selectBase
      , iSelectors = Seq.singleton oldNode
      , iSelectorTypes = Seq.singleton False
      }

dynamicSequence, embeddedSequence :: ConstraintSeq
dynamicSequence = Seq.singleton $ ValCnstr $ ValConstraint emptyLoc oldValue
embeddedSequence = Seq.singleton $ ValCnstr $ ValConstraint emptyLoc newValue

constraintRoot :: VNode
constraintRoot =
  emptyVNode
    { version = 7
    , constraints =
        emptyConstraintsSet
          { static =
              Seq.fromList
                [ ValCnstr $ ValConstraint emptyLoc oldValue
                , OpCnstr $ OpConstraint emptyLoc regularOp
                , StructEmbedCnstr embeddedSequence
                ]
          , dynamic = IntMap.singleton dynamicID dynamicSequence
          , allResolved = True
          }
    }

fixtureStruct :: Struct
fixtureStruct =
  emptyStruct
    { stcFields = Map.singleton fieldKey (mkdefaultField oldNode)
    , stcDynFields =
        IntMap.singleton
          dynamicID
          DynamicField
            { dsfID = dynamicID
            , dsfAttr = defaultLabelAttr
            , dsfLabel = labelNode
            , dsfLabelIsInterp = False
            , dsfValue = dynamicSequence
            }
    , stcCnstrs =
        IntMap.singleton
          patternID
          StructCnstr
            { scsID = patternID
            , scsPattern = patternNode
            , scsPatAlias = Nothing
            , scsValue = embeddedSequence
            }
    , stcEmbedVal = Just oldValue
    }
