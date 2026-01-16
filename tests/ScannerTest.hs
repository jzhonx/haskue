module ScannerTest (tests) where

import qualified Data.ByteString.Char8 as BC
import Syntax.Scanner
import Syntax.Token
import Test.Tasty
import Test.Tasty.HUnit

-- | Create a test tree with all scanner tests
tests :: TestTree
tests =
  testGroup
    "Scanner Tests"
    [ basicTokenTests
    , operatorTests
    , stringLiteralTests
    , commaInsertionTests
    , commentTests
    , multilineStringTests
    , complexExampleTests
    , edgeCaseTests
    , errorCaseTests
    ]

-- Helper to create tokens for comparison
mkT :: TokenType -> BC.ByteString -> Token
mkT t lit = Token t (Location 1 1 Nothing) lit

-- Helper to compare tokens ignoring location
assertTokensEqual :: String -> [Token] -> [Token] -> Assertion
assertTokensEqual msg actual expected =
  let
    -- Only compare type and literal, ignore location
    actual' = map (\t -> Token (tkType t) (Location 0 0 Nothing) (tkLiteral t)) actual
    expected' = map (\t -> Token (tkType t) (Location 0 0 Nothing) (tkLiteral t)) expected
   in
    assertEqual msg expected' actual'

getTokens :: BC.ByteString -> [Token]
getTokens input =
  case scanTokens input of
    Right tokens -> tokens
    Left errToken -> [errToken]

-- Basic token tests
basicTokenTests :: TestTree
basicTokenTests =
  testGroup
    "Basic Tokens"
    [ testCase "Identifiers" $
        let actual = getTokens (BC.pack "hello world")
            expected =
              [ mkT Identifier "hello"
              , mkT Identifier "world"
              , mkT EOF ""
              ]
         in assertTokensEqual "Identifiers" actual expected
    , testCase "Keywords" $
        let actual = getTokens (BC.pack "package import for if let")
            expected =
              [ mkT Package "package"
              , mkT Import "import"
              , mkT For "for"
              , mkT If "if"
              , mkT Let "let"
              , mkT EOF ""
              ]
         in assertTokensEqual "Keywords" actual expected
    , testCase "Numbers" $
        let actual = getTokens (BC.pack "42 3.14")
            expected =
              [ mkT Int "42"
              , mkT Float "3.14"
              , mkT EOF ""
              ]
         in assertTokensEqual "Numbers" actual expected
    , testCase "Booleans" $
        let actual = getTokens (BC.pack "true false")
            expected =
              [ mkT Bool "true"
              , mkT Bool "false"
              , mkT EOF ""
              ]
         in assertTokensEqual "Booleans" actual expected
    , testCase "Special values" $
        let actual = getTokens (BC.pack "null _|_ _")
            expected =
              [ mkT Null "null"
              , mkT Bottom "_|_"
              , mkT Identifier "_"
              , mkT EOF ""
              ]
         in assertTokensEqual "Special values" actual expected
    ]

-- Operator tests
operatorTests :: TestTree
operatorTests =
  testGroup
    "Operators"
    [ testCase "Single char operators" $
        let actual = getTokens (BC.pack "(){}[]:,.?+-*/&|=!")
            expected =
              [ mkT LParen "("
              , mkT RParen ")"
              , mkT LBrace "{"
              , mkT RBrace "}"
              , mkT LSquare "["
              , mkT RSquare "]"
              , mkT Colon ":"
              , mkT Comma ","
              , mkT Dot "."
              , mkT QuestionMark "?"
              , mkT Plus "+"
              , mkT Minus "-"
              , mkT Multiply "*"
              , mkT Divide "/"
              , mkT Unify "&"
              , mkT Disjoin "|"
              , mkT Assign "="
              , mkT Exclamation "!"
              , mkT EOF ""
              ]
         in assertTokensEqual "Single char operators" actual expected
    , testCase "Compound operators" $
        let actual = getTokens (BC.pack "!= == <= >= !~ =~ ...")
            expected =
              [ mkT NotEqual "!="
              , mkT Equal "=="
              , mkT LessEqual "<="
              , mkT GreaterEqual ">="
              , mkT NotMatch "!~"
              , mkT Match "=~"
              , mkT Ellipsis "..."
              , mkT EOF ""
              ]
         in assertTokensEqual "Compound operators" actual expected
    ]

-- String literal tests
stringLiteralTests :: TestTree
stringLiteralTests =
  testGroup
    "String Literals"
    [ testCase "Simple strings" $
        let actual = getTokens (BC.pack "\"hello\" \"world\"")
            expected =
              [ mkT String "hello"
              , mkT String "world"
              , mkT EOF ""
              ]
         in assertTokensEqual "Simple strings" actual expected
    , testCase "Empty string" $
        let actual = getTokens (BC.pack "\"\"")
            expected =
              [ mkT String ""
              , mkT EOF ""
              ]
         in assertTokensEqual "Empty string" actual expected
    , testCase "String with escapes" $
        let actual = getTokens (BC.pack "\"hello\\nworld\"")
            expected =
              [ mkT String "hello\\nworld"
              , mkT EOF ""
              ]
         in assertTokensEqual "String with escapes" actual expected
    ]

-- Comma insertion tests
commaInsertionTests :: TestTree
commaInsertionTests =
  testGroup
    "Comma Insertion"
    [ testCase "Identifiers at line endings" $
        let actual = getTokens (BC.pack "a: 1\nb: 2\nc: 3")
            expected =
              [ mkT Identifier "a"
              , mkT Colon ":"
              , mkT Int "1"
              , mkT Comma ","
              , mkT Identifier "b"
              , mkT Colon ":"
              , mkT Int "2"
              , mkT Comma ","
              , mkT Identifier "c"
              , mkT Colon ":"
              , mkT Int "3"
              , mkT EOF ""
              ]
         in assertTokensEqual "Identifiers at line endings" actual expected
    , testCase "No comma on same line" $
        let actual = getTokens (BC.pack "a: 1, b: 2, c: 3")
            expected =
              [ mkT Identifier "a"
              , mkT Colon ":"
              , mkT Int "1"
              , mkT Comma ","
              , mkT Identifier "b"
              , mkT Colon ":"
              , mkT Int "2"
              , mkT Comma ","
              , mkT Identifier "c"
              , mkT Colon ":"
              , mkT Int "3"
              , mkT EOF ""
              ]
         in assertTokensEqual "No comma on same line" actual expected
    , testCase "Keywords at line endings" $
        let actual = getTokens (BC.pack "package foo\nimport bar")
            expected =
              [ mkT Package "package"
              , mkT Identifier "foo"
              , mkT Comma ","
              , mkT Import "import"
              , mkT Identifier "bar"
              , mkT EOF ""
              ]
         in assertTokensEqual "Keywords at line endings" actual expected
    ]

-- Comment tests
commentTests :: TestTree
commentTests =
  testGroup
    "Comments"
    [ testCase "Line comments" $
        let actual = getTokens (BC.pack "a: 1 // comment\nb: 2")
            expected =
              [ mkT Identifier "a"
              , mkT Colon ":"
              , mkT Int "1"
              , mkT Comma ","
              , mkT Identifier "b"
              , mkT Colon ":"
              , mkT Int "2"
              , mkT EOF ""
              ]
         in assertTokensEqual "Line comments" actual expected
    , testCase "Comments at EOF" $
        let actual = getTokens (BC.pack "a: 1 // comment")
            expected =
              [ mkT Identifier "a"
              , mkT Colon ":"
              , mkT Int "1"
              , mkT EOF ""
              ]
         in assertTokensEqual "Comments at EOF" actual expected
    ]

-- Multiline string tests
multilineStringTests :: TestTree
multilineStringTests =
  testGroup
    "Multiline Strings"
    [ testCase "Simple multiline string" $
        let actual = getTokens (BC.pack "\"\"\"\nhello\"\"\"")
            expected =
              [ mkT MultiLineString "hello"
              , mkT EOF ""
              ]
         in assertTokensEqual "Simple multiline string" actual expected
    , testCase "Multiline with newlines" $
        let actual = getTokens (BC.pack "\"\"\"\nhello\nworld\"\"\"")
            expected =
              [ mkT MultiLineString "hello\nworld"
              , mkT EOF ""
              ]
         in assertTokensEqual "Multiline with newlines" actual expected
    ]

-- Complex example tests
complexExampleTests :: TestTree
complexExampleTests =
  testGroup
    "Complex Examples"
    [ testCase "CUE-like structure" $
        let actual = getTokens (BC.pack "package example\n\na: 1\nb: 2\nc: \"hello\"")
            expected =
              [ mkT Package "package"
              , mkT Identifier "example"
              , mkT Comma ","
              , mkT Identifier "a"
              , mkT Colon ":"
              , mkT Int "1"
              , mkT Comma ","
              , mkT Identifier "b"
              , mkT Colon ":"
              , mkT Int "2"
              , mkT Comma ","
              , mkT Identifier "c"
              , mkT Colon ":"
              , mkT String "hello"
              , mkT EOF ""
              ]
         in assertTokensEqual "CUE-like structure" actual expected
    , testCase "Nested structure" $
        let actual = getTokens (BC.pack "{\n  x: 1\n  y: \"test\"\n  z: [1, 2, 3]\n}")
            expected =
              [ mkT LBrace "{"
              , mkT Identifier "x"
              , mkT Colon ":"
              , mkT Int "1"
              , mkT Comma ","
              , mkT Identifier "y"
              , mkT Colon ":"
              , mkT String "test"
              , mkT Comma ","
              , mkT Identifier "z"
              , mkT Colon ":"
              , mkT LSquare "["
              , mkT Int "1"
              , mkT Comma ","
              , mkT Int "2"
              , mkT Comma ","
              , mkT Int "3"
              , mkT RSquare "]"
              , mkT Comma ","
              , mkT RBrace "}"
              , mkT EOF ""
              ]
         in assertTokensEqual "Nested structure" actual expected
    ]

-- Edge case tests
edgeCaseTests :: TestTree
edgeCaseTests =
  testGroup
    "Edge Cases"
    [ testCase "Empty input" $
        let actual = getTokens (BC.pack "")
            expected = [mkT EOF ""]
         in assertTokensEqual "Empty input" actual expected
    , testCase "Only whitespace" $
        let actual = getTokens (BC.pack "   \n  \t  \n")
            expected = [mkT EOF ""]
         in assertTokensEqual "Only whitespace" actual expected
    , testCase "Only comments" $
        let actual = getTokens (BC.pack "// comment 1\n// comment 2")
            expected = [mkT EOF ""]
         in assertTokensEqual "Only comments" actual expected
    ]

-- Error case tests
errorCaseTests :: TestTree
errorCaseTests =
  testGroup
    "Error Cases"
    [ testCase "Unclosed string" $
        let actual = getTokens (BC.pack "\"unclosed")
            expected =
              [ mkT Illegal "Unterminated string literal"
              ]
         in assertTokensEqual "Unclosed string" actual expected
    , testCase "Unknown character" $
        let actual = getTokens (BC.pack "@#$")
            expected =
              [ mkT Illegal "Illegal character: @"
              ]
         in assertTokensEqual "Unknown character" actual expected
    ]