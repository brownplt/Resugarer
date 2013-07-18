module Parse where

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as P
import Control.Monad (liftM, liftM2, liftM3)

import Pattern


lexer = P.makeTokenParser $ P.LanguageDef {
  P.commentStart = "(*",
  P.commentEnd = "*)",
  P.commentLine = "",
  P.nestedComments = True,
  P.identStart = lower,
  P.identLetter = letter,
  P.opStart = upper,
  P.opLetter = letter,
  P.reservedNames = [],
  P.reservedOpNames = ["Head", "Body"],
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

var :: Parser Var
var = do
  symbol "'"
  t <- lowerId
  return (Var t)

cst :: Parser Const
cst = try parseInt <|> parseDbl <|> parseStr
  where
    parseInt = liftM (CInt . fromIntegral) integer
    parseDbl = liftM CDbl float
    parseStr = liftM CStr stringLiteral

parens :: Parser a -> Parser a
parens p = do
  string "("
  x <- p
  string ")"
  return x

origin :: Parser Origin
origin = origBody <|> origHead
  where
    origBody = reservedOp macBodyStr >> return MacBody
    origHead = do
      reservedOp macHeadStr
      m <- upperId
      i <- natural
      t <- term
      return (MacHead m (fromIntegral i) t)

term :: Parser Term
term = liftM TCst cst <|> tLst <|> tMac <|> tTag
  where
    tLst = parens (liftM2 TLst lowerId (many term))
    tMac = parens (liftM2 TMac upperId (many term))
    tTag = parens (liftM2 TTag origin term)

patt :: Parser Pattern
patt = liftM PVar var <|> liftM PCst cst <|>
       pLst <|> pMac <|> pLstRep <|> pMacRep <|> pTag
  where
    pLst = parens (liftM2 PLst lowerId (many patt))
    pMac = parens (liftM2 PMac upperId (many patt))
    pTag = parens (liftM2 PTag origin patt)
    pLstRep = parens (liftM3 PLstRep lowerId (many patt) (rep patt))
    pMacRep = parens (liftM3 PMacRep upperId (many patt) (rep patt))
  
rep :: Parser a -> Parser a
rep p = do
  x <- p
  symbol repStr
  return x
