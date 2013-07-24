module Parse where
-- TODO: Export only (parseModule, parseTerm)

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
  P.reservedNames = [rulesStr, surfaceStr, coreStr],
  P.reservedOpNames = [intSortStr, floatSortStr, stringSortStr,
                       macHeadStr, macBodyStr],
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

parseModule = Parse.parse top
parseTerm = Parse.parse term

top :: Parser Module
top = do
  symbol coreStr
  l1 <- language
  symbol surfaceStr
  l2 <- language
  rs <- rules
  return (Module l1 l2 rs)

language :: Parser Language
language = do
  symbol startStr
  s <- upperId
  symbol constrStr
  g <- grammar
  return (Language g s)

grammar :: Parser Grammar
grammar = do
  ps <- many production
  return (Grammar ps)

production :: Parser Production
production = do
  l <- label
  symbol hasTypeStr
  ss <- sort `sepBy` (symbol typeProdStr)
  symbol typeArrowStr
  s <- upperId
  symbol terminalStr
  return (Production (Constructor l ss) s)

sort :: Parser Sort
sort = intSort <|> floatSort <|> stringSort <|> sortList <|> sortName
  where
    sortName = liftM SortName upperId
    sortList = liftM SortList (brackets sort)
    intSort = reservedOp intSortStr >> return IntSort
    floatSort = reservedOp floatSortStr >> return FloatSort
    stringSort = reservedOp stringSortStr >> return StringSort

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
  symbol varStr
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
