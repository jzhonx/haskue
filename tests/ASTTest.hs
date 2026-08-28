module ASTTest (tests) where

import qualified Data.ByteString as BS
import Data.ByteString.Builder (toLazyByteString)
import qualified Data.ByteString.Char8 as BC
import Syntax.AST
import Syntax.Parser (parseExpr, parseSourceFile)
import Syntax.Scanner (scanTokens)
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "AST Tests"
    [ testCase "renders a multiline comprehension" $ do
        actual <- renderSource multilineComprehension
        actual @?= multilineExpected
    , testCase "renders a nested comprehension at its current indentation" $ do
        actual <- renderSource nestedComprehension
        actual @?= nestedExpected
    , testCase "renders a list comprehension on one line" $ do
        expr <- parseExpression "[for _, v in src let doubled = v * 2 if doubled > 2 {doubled}]"
        exprToOneLinerStr expr
          @?= "[for _, v in src let doubled = v * 2 if doubled > 2 {doubled}]"
    ]

renderSource :: BC.ByteString -> IO BC.ByteString
renderSource input = do
  tokens <- either (assertFailure . show) return (scanTokens input)
  SourceFile _ decls <- either assertFailure return (parseSourceFile tokens)
  return $ BS.toStrict $ toLazyByteString $ declsToBuilder decls

parseExpression :: BC.ByteString -> IO Expression
parseExpression input = do
  tokens <- either (assertFailure . show) return (scanTokens input)
  either assertFailure return (parseExpr tokens)

multilineComprehension :: BC.ByteString
multilineComprehension =
  "for k, v in data\n\
  \let selected = v.enabled\n\
  \if selected {\n\
  \  result: v\n\
  \}\n"

multilineExpected :: BC.ByteString
multilineExpected =
  "for k, v in data\n\
  \let selected = v.enabled\n\
  \if selected {\n\
  \    result: v\n\
  \}\n"

nestedComprehension :: BC.ByteString
nestedComprehension =
  "outer: {\n\
  \  for k in data\n\
  \  if k {\n\
  \    (k): k\n\
  \  }\n\
  \}\n"

nestedExpected :: BC.ByteString
nestedExpected =
  "outer: {\n\
  \    for k in data\n\
  \    if k {\n\
  \        (k): k\n\
  \    }\n\
  \}\n"
