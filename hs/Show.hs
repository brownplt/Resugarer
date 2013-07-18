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
  showsPrec _ (PLst l ps) = showsParens (str l : map shows ps)
  showsPrec _ (PMac m ps) = showsParens (str m : map shows ps)
  showsPrec _ (PLstRep l ps r) =
    showsParens ([str l] ++ map shows ps ++ [shows r, str repStr])
  showsPrec _ (PMacRep m ps r) =
    showsParens ([str m] ++ map shows ps ++ [shows r, str repStr])
  showsPrec _ (PTag o p) = showsParens [str tagStr, shows o, shows p]

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
