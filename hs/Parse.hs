module Parse where
-- TODO: Export only (parseGrammar, parseRules)

import Prelude hiding (const)
import Text.ParserCombinators.Parsec hiding (label)
import qualified Text.ParserCombinators.Parsec.Token as P
import Control.Monad (liftM, liftM2, liftM3)

import Pattern
import Grammar
import Show


lexer = P.makeTokenParser $ P.LanguageDef {
  P.commentStart = "(*",
  P.commentEnd = "*)",
  P.commentLine = "",
  P.nestedComments = True,
  P.identStart = lower,
  P.identLetter = letter,
  P.opStart = upper,
  P.opLetter = letter,
  P.reservedNames = [grammarStr, rulesStr],
  P.reservedOpNames = [macHeadStr, macBodyStr],
  P.caseSensitive = True
  }
stringLiteral = P.stringLiteral lexer
natural = P.natural lexer
integer = P.integer lexer
float = P.float lexer
space = P.whiteSpace lexer
symbol = P.symbol lexer
upperId = P.operator lexer
lowerId = P.identifier lexer
reservedOp = P.reservedOp lexer

commaSep = P.commaSep lexer
parens = P.parens lexer
brackets = P.brackets lexer
braces = P.braces lexer

parse = Text.ParserCombinators.Parsec.parse

--parseGrammar = parse grammar
--parseRules = parse rules

grammar :: Parser Grammar
grammar = do
  symbol "grammar"
  ps <- many production
  return (Grammar ps)

production :: Parser Production
production = do
  l <- label
  symbol hasTypeStr
  ss <- esort `sepBy` (symbol typeProdStr)
  symbol typeArrowStr
  s <- sort
  symbol terminalStr
  return (Production l ss s)

sort :: Parser Sort
sort = liftM Sort upperId

esort :: Parser ESort
esort = esortList <|> esortScalar
  where
    esortScalar = liftM ESort sort
    esortList = liftM EList (brackets esort)

rules :: Parser Rules
rules = do
  symbol "rules"
  rs <- many rule
  return (Rules rs)

rule :: Parser Rule
rule = do
  p <- pattern
  symbol rewriteStr
  q <- pattern
  symbol terminalStr
  return (Rule p q)

pattern :: Parser Pattern
pattern = do
  p <- untaggedPattern
  ts <- optionMaybe tags
  case ts of
    Nothing -> return p
    Just ts -> return (addTags ts p)
  where
    untaggedPattern :: Parser Pattern
    untaggedPattern = pVar <|> pConst <|> pNode <|> pList
      where
        pVar = liftM PVar var
        pConst = liftM PConst const
        pList = liftM PList (brackets pattern)
        pNode = liftM2 PNode label (parens (commaSep pattern))
    addTags [] p = p
    addTags (o:os) p = addTags os (PTag o p)

term :: Parser Term
term = do
  t <- untaggedTerm
  os <- optionMaybe tags
  case os of
    Nothing -> return t
    Just os -> return (addTags os t)
  where    
    untaggedTerm = tConst <|> tNode
      where
        tConst = liftM TConst const
        tNode = liftM2 TNode label (parens (commaSep term))
    addTags [] t = t
    addTags (o:os) t = addTags os (TTag o t)

tags :: Parser [Origin]
tags = braces (brackets (commaSep origin))

const :: Parser Const
const = try parseInt <|> parseDbl <|> parseStr
  where
    parseInt = liftM (CInt . fromIntegral) integer
    parseDbl = liftM CDbl float
    parseStr = liftM CStr stringLiteral

var :: Parser Var
var = do
  symbol "'"
  t <- lowerId
  return (Var t)

origin :: Parser Origin
origin = origBody <|> origHead
  where
    origBody = reservedOp macBodyStr >> return MacBody
    origHead = do
      symbol macHeadStr
      symbol "("
      m <- label
      symbol ","
      i <- natural
      symbol ","
      t <- term
      symbol ")"
      return (MacHead m (fromIntegral i) t)

label :: Parser Label
label = liftM Label upperId
