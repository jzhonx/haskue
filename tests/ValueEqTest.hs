module ValueEqTest (tests) where

import qualified Data.Sequence as Seq
import Test.Tasty
import Test.Tasty.HUnit
import Value

tests :: TestTree
tests =
  testGroup
    "Value Eq"
    [ testCase "identical unresolved disjunctions are equal" testIdenticalDisjunctions
    , testCase "a disjunction is not equal to its default" testDefaultIsNotDisjunction
    , testCase "default indexes are part of disjunction equality" testDefaultIndexesMatter
    , testCase "equality is transitive for default-bearing values" testDefaultEqualityIsTransitive
    ]

testIdenticalDisjunctions :: Assertion
testIdenticalDisjunctions =
  defaultDisjunction 2 @?= defaultDisjunction 2

testDefaultIsNotDisjunction :: Assertion
testDefaultIsNotDisjunction = do
  let disjunction = defaultDisjunction 2
      defaultValue = intValue 1
  assertNotEqual disjunction defaultValue
  assertNotEqual defaultValue disjunction

testDefaultIndexesMatter :: Assertion
testDefaultIndexesMatter =
  assertNotEqual (defaultDisjunction 2) (disjunctionWithDefaultIndex 1 2)

testDefaultEqualityIsTransitive :: Assertion
testDefaultEqualityIsTransitive = do
  let left = defaultDisjunction 2
      middle = intValue 1
      right = defaultDisjunction 3
  assertBool
    "if left == middle and middle == right, then left must equal right"
    (not (left == middle && middle == right) || left == right)

defaultDisjunction :: Integer -> Val
defaultDisjunction alternative = disjunctionWithDefaultIndex 0 alternative

disjunctionWithDefaultIndex :: Int -> Integer -> Val
disjunctionWithDefaultIndex defaultIndex alternative =
  VDisj
    emptyDisj
      { dsjDefIndexes = [defaultIndex]
      , dsjDisjuncts = Seq.fromList [mkAtomVN (Int 1), mkAtomVN (Int alternative)]
      }

intValue :: Integer -> Val
intValue = VAtom . Int

assertNotEqual :: Val -> Val -> Assertion
assertNotEqual left right =
  assertBool "expected values to be unequal" (left /= right)
