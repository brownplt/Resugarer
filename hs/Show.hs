module Show (rulesStr, surfaceStr, coreStr, startStr, constrStr,
             varStr, rewriteStr, assignStr, terminalStr,
             hasTypeStr, typeProdStr, typeArrowStr,
             intSortStr, floatSortStr, stringSortStr,
             macBodyStr, macHeadStr, tagStr) where

import Pattern
import Grammar


{- Syntax Parameters -}

surfaceStr = "surface"
coreStr = "core"
startStr = "start"
constrStr = "constructors"
rulesStr = "rules"

varStr = ""
rewriteStr = "=>"
assignStr = "="
terminalStr = ";"
hasTypeStr = ":"
typeProdStr = "*"
typeArrowStr = "->"

macBodyStr = "Body"
macHeadStr = "Head"
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
  showsPrec _ (SortName s) = str s
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
    spaceSep [shows c, str typeArrowStr, str s] . str terminalStr

instance Show Grammar where
  showsPrec _ (Grammar ps) =
    newlineSep (map shows ps)

instance Show Rules where
  showsPrec _ (Rules rs) =
    newlineSep (str rulesStr : map shows rs)

instance Show Language where
  showsPrec _ (Language g s) =
    newlineSep [str startStr, str s, str constrStr, shows g]

instance Show Module where
  showsPrec _ (Module l1 l2 rs) =
    newlineSep [str coreStr, shows l1, str surfaceStr, shows l2, shows rs]

instance Show ResugarError where
  showsPrec _ (NoMatchingCase l t) =
    str "No matching case in macro " . shows l . str " for term " . shows t
  showsPrec _ (NoSuchMacro l) =
    str "The label " . shows l . str (" appears in a core term tag," ++
      "but there is no corresponding desugaring rule.")

instance Show ResugarFailure where
  showsPrec _ (MatchFailure t p) =
    str "Could not match " . shows t . str " against " . shows p
  showsPrec _ TermIsOpaque =
    str "The term being unexpanded is opaque"
  showsPrec _ (ResugarError err) = shows err

