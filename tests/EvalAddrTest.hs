module EvalAddrTest (tests) where

import EvalAddr
import StringIndex (TextIndex (..))
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "EvalAddr"
    [ testCase "converts an address to selectors" testAddrToSelectors
    , testCase "rejects an address containing an internal term step" testRejectTermStep
    ]

testAddrToSelectors :: Assertion
testAddrToSelectors = do
  let selectors = Selectors [StringSel (TextIndex 3), IntSel 2, StringSel (TextIndex 7)]
  addrToSelectors (fieldPathToAddr selectors) @?= Just selectors

testRejectTermStep :: Assertion
testRejectTermStep = do
  let selectorAddr = fieldPathToAddr $ Selectors [StringSel (TextIndex 3)]
      internalAddr = appendTermStep selectorAddr (mkDisjTermStep 0)
  addrToSelectors internalAddr @?= Nothing
