module Show (rulesStr, surfaceStr, coreStr, startStr, valueStr, constrStr,
             varStr, rewriteStr, assignStr, terminalStr,
             hasTypeStr, typeProdStr, typeArrowStr,
             intSortStr, floatSortStr, stringSortStr, repStr,
             macBodyStr, macAlienStr, macHeadStr, tagStr) where

import Pattern
import Grammar


{- Syntax Parameters -}

surfaceStr = "surface"
coreStr = "core"
startStr = "start"
valueStr = "values"
constrStr = "constructors"
rulesStr = "rules"

varStr = ""
rewriteStr = "->"
assignStr = "="
terminalStr = ";"
hasTypeStr = ":"
typeProdStr = "*"
typeArrowStr = "->"
repStr = "..."

macBodyStr = "Body"
macHeadStr = "Head"
macAlienStr = "Alien"
tagStr = "Tag"

intSortStr = "Int"
floatSortStr = "Float"
stringSortStr = "String"


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
  showsPrec _ (PList ps) = brackets (commaSep (map shows ps))
  showsPrec _ (PRep ps p) =
    brackets (commaSep (map shows ps ++ [shows p]) . str repStr)
  showsPrec _ (PTag o p) = showTags [o] p
    where
      showTags os (PTag o p) = showTags (o:os) p
      showTags os p          =
        shows p . braces (brackets (commaSep (map shows os)))
  showsPrec _ (PNode l []) = shows l
  showsPrec _ (PNode l ps) = shows l . parens (commaSep (map shows ps))

instance Show Term where
  showsPrec _ (TConst c) = shows c
  showsPrec _ (TList ts) = brackets (commaSep (map shows ts))
  showsPrec _ (TNode l ts) = shows l . parens (commaSep (map shows ts))
  showsPrec _ (TTag o t) = showTags [o] t
    where
      showTags os (TTag o t) = showTags (o:os) t
      showTags os t =
        shows t . braces (brackets (commaSep (map shows os)))

instance Show Const where
  showsPrec _ (CInt x) = shows x
  showsPrec _ (CDbl x) = shows x
  showsPrec _ (CStr x) = shows x

instance Show Var where
  showsPrec _ (Var v) = str varStr . str v

instance Show Origin where
  showsPrec _ (MacHead m i t) =
    str macHeadStr . parens (commaSep [shows m, shows i, shows t])
  showsPrec _ MacAlien = str macAlienStr
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

instance Show SortName where
  showsPrec _ (SortN s) = str s

instance Show Sort where
  showsPrec _ (SortName s) = shows s
  showsPrec _ (SortList s) = brackets (shows s)
  showsPrec _ IntSort = str intSortStr
  showsPrec _ FloatSort = str floatSortStr
  showsPrec _ StringSort = str stringSortStr

instance Show Constructor where
  showsPrec _ (Constructor l ss) =
    spaceSep [shows l, str hasTypeStr,
              sep (" " ++ typeProdStr ++ " ") (map shows ss)]

instance Show Production where
  showsPrec _ (Production c s) =
    spaceSep [shows c, str typeArrowStr, shows s] . str terminalStr

instance Show Grammar where
  showsPrec _ (Grammar ps) =
    newlineSep (map shows ps)

instance Show Rules where
  showsPrec _ (Rules rs) =
    newlineSep (str rulesStr : map shows rs)

instance Show Language where
  showsPrec _ (Language g s) =
    newlineSep [str startStr, shows s, str constrStr, shows g]

instance Show Module where
  showsPrec _ (Module l1 l2 rs) =
    newlineSep [str coreStr, shows l1, str surfaceStr, shows l2, shows rs]

instance Show ResugarError where
  showsPrec _ (NoMatchingCase l t) =
    str "No matching case in macro " . shows l . str " for term " . shows t
  showsPrec _ (NoSuchMacro l) =
    str "The label " . shows l . str (" appears in a core term tag," ++
      "but there is no corresponding desugaring rule.")
  showsPrec _ (NoSuchCase l i) =
    str "A tag refers to case " . shows i . str " in macro " .
    shows l . str ", but no such case exists."
  showsPrec _ (UnboundSubsVar v) =
    str "Unbound variable " . shows v
  showsPrec _ (DepthMismatch v) =
    str "The variable " . shows v . str " appears at an inappropriate depth."

instance Show ResugarFailure where
  showsPrec _ (MatchFailure t p) =
    str "Could not match " . shows t . str " against " . shows p
  showsPrec _ TermIsOpaque =
    str "The term being unexpanded is opaque"
  showsPrec _ (ResugarError err) = shows err

