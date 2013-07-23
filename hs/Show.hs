module Show (grammarStr, rulesStr,
             repStr, varStr, rewriteStr, assignStr, terminalStr,
             hasTypeStr, typeProdStr, typeArrowStr,
             macBodyStr, macHeadStr, tagStr) where

import Pattern
import Grammar


{- Easy-to-change Syntax -}

grammarStr = "grammar"
rulesStr = "rules"

repStr = "..."
varStr = "'"
rewriteStr = "=>"
assignStr = "="
terminalStr = ";"

hasTypeStr = ":"
typeProdStr = "*"
typeArrowStr = "->"

macBodyStr = "Body"
macHeadStr = "Head"
tagStr = "Tag"


{- Printing -}


str = showString

sep :: String -> [ShowS] -> ShowS
sep _ []       = id
sep _ [x]      = x
sep s (x:y:ys) = x . str s . sep s (y:ys)

commaSep = sep ", "
spaceSep = sep " "
newlineSep = sep "\n"

surround :: String -> String -> ShowS -> ShowS
surround l r x = str l . x . str r

parens   = surround "(" ")"
brackets = surround "[" "]"
braces   = surround "{" "}"

instance Show Pattern where
  showsPrec _ (PVar v) = shows v
  showsPrec _ (PConst c) = shows c
  showsPrec _ (PList p) = brackets (shows p)
  showsPrec _ (PTag o p) = showTags [o] p
    where
      showTags os (PTag o p) = showTags (o:os) p
      showTags os p          =
        shows p . braces (brackets (commaSep (map shows os)))
  showsPrec _ (PNode l ps) = shows l . parens (commaSep (map shows ps))

instance Show Term where
  showsPrec _ = shows . termToPattern

instance Show Const where
  showsPrec _ (CInt x) = shows x
  showsPrec _ (CDbl x) = shows x
  showsPrec _ (CStr x) = shows x

instance Show Var where
  showsPrec _ (Var v) = str varStr . str v

instance Show Origin where
  showsPrec _ (MacHead m i t) =
    str macHeadStr . parens (commaSep [shows m, shows i, shows t])
  showsPrec _ MacBody = str macBodyStr

instance Show Binding where
  showsPrec _ (BList bs) = brackets (commaSep (map shows bs))
  showsPrec _ (BTerm t) = shows t

instance Show Macro where
  showsPrec _ (Macro m cs) =
    spaceSep [shows m, str assignStr, braces (commaSep (map shows cs))]

instance Show Rule where
  showsPrec _ (Rule p q) =
    spaceSep [shows p, str rewriteStr, shows q] . str terminalStr

instance Show Sort where
  showsPrec _ (Sort s) = str s

instance Show ESort where
  showsPrec _ (ESort s) = shows s
  showsPrec _ (EList s) = brackets (shows s)

instance Show Production where
  showsPrec _ (Production l ss s) =
    spaceSep [shows l, str hasTypeStr,
              sep (" " ++ typeProdStr ++ " ") (map shows ss),
              str typeArrowStr, shows s]
    . str terminalStr

instance Show Grammar where
  showsPrec _ (Grammar ps) =
    newlineSep (str grammarStr : map shows ps)

instance Show Rules where
  showsPrec _ (Rules rs) =
    newlineSep (str rulesStr : map shows rs)