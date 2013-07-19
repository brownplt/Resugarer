module Show () where

import Pattern


str = showString

showsList :: [ShowS] -> ShowS
showsList [] = id
showsList [x] = x
showsList (x:y:ys) = x . str " " . showsList (y:ys)

showsParens :: [ShowS] -> ShowS
showsParens xs = str "(" . showsList xs . str ")"

instance Show Pattern where
  showsPrec _ (PVar v) = shows v
  showsPrec _ (PCst c) = shows c
  showsPrec _ (PNod l ps) = showsParens (shows l : map shows ps)
  showsPrec _ (PRep l ps r) =
    showsParens ([shows l] ++ map shows ps ++ [shows r, str repStr])
  showsPrec _ (PTag o p) = showsParens [str tagStr, shows o, shows p]

instance Show NodeType where
  showsPrec _ (NLst l) = str l
  showsPrec _ (NMac m) = str m

instance Show Term where
  showsPrec _ = shows . termToPattern

instance Show Const where
  showsPrec _ (CInt x) = shows x
  showsPrec _ (CDbl x) = shows x
  showsPrec _ (CStr x) = shows x

instance Show Var where
  showsPrec _ (Var v) = str "'" . str v

instance Show Origin where
  showsPrec _ (MacHead m i t) =
    showsList [str macHeadStr, str m, shows i, shows t]
  showsPrec _ MacBody = str macBodyStr
