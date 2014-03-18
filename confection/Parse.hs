module Parse where

import Prelude hiding (const)
import Text.ParserCombinators.Parsec hiding (label)
import qualified Text.ParserCombinators.Parsec.Token as P
import Control.Monad (liftM, liftM2, liftM3)
import Data.Maybe (maybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Pattern
import Grammar
import Show


lexer = P.makeTokenParser $ P.LanguageDef {
  P.commentStart = "(*",
  P.commentEnd = "*)",
  P.commentLine = "#",
  P.nestedComments = True,
  P.identStart = upper,
  P.identLetter = letter <|> digit <|> char '_',
  P.opStart = lower,
  P.opLetter = letter <|> digit <|> char '_',
  P.reservedNames = [rulesStr, surfaceStr, coreStr,
                     intSortStr, floatSortStr, stringSortStr,
                     macHeadStr, macBodyStr, freshStr],
  P.reservedOpNames = [],
  P.caseSensitive = True
  }
stringLiteral = P.stringLiteral lexer
natural = P.natural lexer
integer = P.integer lexer
float = P.float lexer
space = P.whiteSpace lexer
symbol = P.symbol lexer
iden = P.identifier lexer
op = P.operator lexer
reservedOp = P.reservedOp lexer

commaSep = P.commaSep lexer
commaSep1 = P.commaSep1 lexer
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
  return $ compile $ Module l1 l2 rs

compile :: Module -> Module
-- Fill in pattern `Info`s.
compile (Module l1@(Language (Grammar v1) _)
                l2@(Language (Grammar v2) _) (Rules rs)) =
  Module l1 l2 (Rules (map fillRuleInfo rs))
    where
      ls = prodLabels (v1 ++ v2)
      
      prodLabels :: [Production] -> Set Label
      prodLabels = Set.fromList . map getLabel
        where getLabel (Production (Constructor l _) _) = l
    
      fillRuleInfo :: Rule -> Rule
      fillRuleInfo (Rule p q fs i) =
        Rule (fillPattInfo p) (fillPattInfo q) fs i
    
      fillPattInfo :: Pattern -> Pattern
      fillPattInfo (PVar v) = PVar v
      fillPattInfo (PConst c) = PConst c
      fillPattInfo (PNode (Info z _) l ps) =
        PNode (Info z (Set.member l ls)) l (map fillPattInfo ps)
      fillPattInfo (PRep ps p) =
        PRep (map fillPattInfo ps) (fillPattInfo p)
      fillPattInfo (PList ps) = PList (map fillPattInfo ps)
      fillPattInfo (PTag o p) = PTag o (fillPattInfo p)

language :: Parser Language
language = do
  symbol valueStr
  g1 <- grammar
  symbol constrStr
  g2 <- grammar
  return (Language g1 g2)

grammar :: Parser Grammar
grammar = do
  ps <- many production
  return (Grammar ps)

production :: Parser Production
production = try shortProduction <|> longProduction
  where
    longProduction :: Parser Production
    longProduction = do
      l <- label
      symbol hasTypeStr
      ss <- sort `sepBy` (symbol typeProdStr)
      symbol typeArrowStr
      s <- iden
      symbol terminalStr
      return (Production (Constructor l ss) (SortN s))

    shortProduction :: Parser Production
    shortProduction = do
      l <- label
      symbol hasTypeStr
      s <- iden
      symbol terminalStr
      return (Production (Constructor l []) (SortN s))


sort :: Parser Sort
sort = intSort <|> floatSort <|> stringSort <|> sortList <|> simpleSort
  where
    simpleSort = liftM SortName sortName
    sortList = liftM SortList (brackets sort)
    intSort = reservedOp intSortStr >> return IntSort
    floatSort = reservedOp floatSortStr >> return FloatSort
    stringSort = reservedOp stringSortStr >> return StringSort

rules :: Parser Rules
rules = do
  symbol rulesStr
  rs <- many rule
  return (Rules rs)

rule :: Parser Rule
rule = do
  p <- pattern
  symbol rewriteStr
  q <- pattern
  fs <- many fresh
  overlapFlag <- optionBool (symbol "unsafe_overlap")
  symbol terminalStr
  return (Rule p q fs (RuleFlags overlapFlag))

fresh :: Parser Var
fresh = do
  symbol freshStr
  f <- op
  return (Var f)

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
        pList = brackets pListElems
        pNode = do
          transp <- optionBool (symbol transpStr)
          l <- label
          args <- optionMaybe (parens (commaSep pattern))
          let nodeArgs = maybe [] id args
          return (PNode (Info transp False) l nodeArgs) -- v filled in later
        pListElems = do
          xs <- commaSep pattern
          r <- optionMaybe (symbol repStr)
          case r of
            Nothing -> return (PList xs)
            Just _ -> case xs of
              [] -> fail "Invalid list."
              _:_ -> return (PRep (init xs) (last xs))

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
    untaggedTerm = tConst <|> tNode <|> tList
      where
        tConst = liftM TConst const
        tNode = liftM2 TNode label (parens (commaSep term))
        tList = liftM TList (brackets (commaSep term))
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
  t <- op
  return (Var t)

sortName :: Parser SortName
sortName = liftM SortN iden

origin :: Parser Origin
origin = origBody <|> origTransp <|> origAlien <|> origHead
  where
    origBody = reservedOp macBodyStr >> return MacBody
    origTransp = reservedOp macTranspBodyStr >> return MacTranspBody
    origAlien = reservedOp macAlienStr >> return MacAlien
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
label = liftM Label iden

optionBool :: Parser a -> Parser Bool
optionBool p = do
  m <- optionMaybe p
  return (maybe False (\_ -> True) m)
