module Pattern where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad (liftM, liftM2, zipWithM, when)


newtype Var = Var String deriving (Eq, Ord)
type Label = String
type MacroName = String

type MacroTable = Map MacroName Macro

data Macro = Macro MacroName [MacroCase]

data MacroCase = MacroCase Pattern Pattern

data Pattern =
    PVar Var
  | PCst Const
  | PNod NodeType [Pattern]
  | PRep NodeType [Pattern] Pattern
  | PTag Origin Pattern
    deriving (Eq)

data Term =
    TCst Const
  | TNod NodeType [Term]
  | TTag Origin Term
    deriving (Eq)

data NodeType =
    NLst Label
  | NMac MacroName
    deriving (Eq, Ord)

data Origin =
    MacHead MacroName Int Term
  | MacBody

data Const =
    CInt Int
  | CDbl Double
  | CStr String
    deriving (Eq, Ord)

instance Eq Origin where
  MacBody == MacBody = True
  MacHead m _ _ == MacHead m' _ _ = m == m'
  _ == _ = False

data Binding =
    BList [Binding]
  | BTerm Term

type Env = Map Var Binding


data UnifyError = UnifyError Pattern Pattern

data ResugarError = MatchError Term Pattern
                  | NoMatchingCase MacroName Term
                  | NoSuchMacro MacroName
                  | TermIsOpaque

data WFError = CasesOverlap MacroName Pattern Pattern Pattern
             | UnboundVar Var
             | EmptyEllipsis MacroName


internalError msg = error ("Internal error: " ++ msg)

termToPattern :: Term -> Pattern
termToPattern (TCst c) = PCst c
termToPattern (TNod l ts) = PNod l (map termToPattern ts)
termToPattern (TTag o t) = PTag o (termToPattern t)

varName :: Var -> String
varName (Var name) = name

fvars :: Pattern -> Set Var
fvars (PVar v) = Set.singleton v
fvars (PCst _) = Set.empty
fvars (PNod _ ps) = Set.unions (map fvars ps)
fvars (PRep _ ps r) = Set.unions (map fvars ps) `Set.union` fvars r
fvars (PTag _ p) = fvars p

repStr = "..."
macBodyStr = "Body"
macHeadStr = "Head"
tagStr = "Tag"


{- Matching -}

match :: Term -> Pattern -> Either ResugarError Env
match (TCst c)    (PCst c')      | c == c' = return mtEnv
match t           (PVar v)                 = return (singletonEnv v t)
match (TTag o t)  (PTag o' p)    | o == o' = match t p
match (TNod l ts) (PNod l' ps)   | l == l' = matches l ts ps
match (TNod l ts) (PRep l' ps r) | l == l' = matchRep l ts ps r
match t           p                        = Left (MatchError t p)

matches _ [] [] = return mtEnv
matches l (t:ts) (p:ps) = liftM2 unifyEnv (match t p) (matches l ts ps)
matches l ts ps = Left (MatchError (TNod l ts) (PNod l ps))

matchRep _ []     []     r = return $ Map.fromList $
  map (\v -> (v, BList [])) (Set.toList (fvars r))
matchRep l (t:ts) (p:ps) r = liftM2 unifyEnv (match t p) (matchRep l ts ps r)
matchRep _ (t:ts) []     r = liftM mergeEnvs (zipWithM match (t:ts) (repeat r))
matchRep l []     ps     r = Left (MatchError (TNod l []) (PRep l ps r))

mergeEnvs :: [Env] -> Env
mergeEnvs [] = internalError "Unexpected empty env list"
mergeEnvs es = foldl1 merge (map singletonWrap es)
  where
    singletonWrap = Map.map (\t -> BList [t])
    merge e1 e2 = Map.intersectionWith concatBindings e1 e2
    concatBindings (BList bs) (BList bs') = BList (bs ++ bs')


{- Substitution -}

subs :: Env -> Pattern -> Term
subs e (PVar v@(Var name)) = case (lookupVar v e) of
  Nothing -> internalError ("Unbound variable: " ++ name)
  Just t -> t
subs e (PCst c)      = TCst c
subs e (PNod l ps)   = TNod l (map (subs e) ps)
subs e (PRep l ps r) = TNod l (map (subs e) ps ++ subsRep e r)
subs e (PTag o p)    = TTag o (subs e p)

subsRep e r = map (\e -> subs e r) (splitEnv e (Set.toList (fvars r)))

mtEnv = Map.empty
singletonEnv v t = Map.singleton v (BTerm t)
unifyEnv = Map.union

lookupVar :: Var -> Env -> Maybe Term
lookupVar v@(Var name) e = case Map.lookup v e of
  Nothing -> Nothing
  Just (BList _) -> internalError ("Unexpected binding list")
  Just (BTerm t) -> Just t

composeEnvs :: Env -> Env -> Env
composeEnvs e1 e2 = Map.union e2 e1

splitEnv :: Env -> [Var] -> [Env]
splitEnv e vs =
  map (\i -> Map.mapWithKey (split i) e) [0 .. n-1]
  where
    n = case Map.lookup (head vs) e of
      Nothing -> internalError "SplitEnv: unbound var"
      Just (BTerm _) -> internalError "SplitEnv: non-binding-list"
      Just (BList bs) -> length bs
    split i v b =
      if elem v vs
      then case b of
        BTerm _ -> internalError "splitEnv/split: non-binding-list"
        BList bs -> bs !! i
      else b


{- Unification -}

unify :: Pattern -> Pattern -> Either UnifyError Pattern
unify (PCst c)    (PCst c')          | c == c' = return (PCst c)
unify (PVar v)    p                            = return p
unify p           (PVar v)                     = return p
unify (PTag o p)  (PTag o' p')       | o == o' = liftM (PTag o) (unify p p')
unify (PNod l ps) (PNod l' ps')      | l == l' && length ps == length ps'
  = liftM (PNod l) (zipWithM unify ps ps')
unify (PNod l ps) (PRep l' ps' r)    | l == l' && length ps >= length ps'
  = liftM (PNod l) (zipWithM unify ps (ps' ++ repeat r))
unify (PRep l' ps' r) (PNod l ps)    | l == l' && length ps >= length ps'
  = liftM (PNod l) (zipWithM unify ps (ps' ++ repeat r))
unify (PRep l ps r) (PRep l' ps' r') | l == l' && isLeft (unify r r')
  = if length ps >= length ps'
    then liftM (PNod l) (zipWithM unify ps (ps' ++ repeat r'))
    else liftM (PNod l) (zipWithM unify ps' (ps ++ repeat r))
unify (PRep l ps r) (PRep l' ps' r') | l == l' && isRight (unify r r')
  = if length ps >= length ps'
    then liftM2 (PRep l) (zipWithM unify ps (ps' ++ repeat r'))
                         (unify r r')
    else liftM2 (PRep l) (zipWithM unify ps' (ps ++ repeat r))
                         (unify r r')
unify p q = Left (UnifyError p q)


{- Macros -}

expandMacro :: Macro -> Term -> Either ResugarError (Int, Term)
expandMacro (Macro name cs) t = expandCases 0 cs
  where
    expandCases _ [] = Left (NoMatchingCase name t)
    expandCases i (c:cs) = eitherOr (expandCase i c) (expandCases (i + 1) cs)
    
    expandCase i (MacroCase p p') = do
      e <- match t p
      return (i, subs e p')

unexpandMacro :: Macro -> (Int, Term) -> Term -> Either ResugarError Term
unexpandMacro (Macro m cs) (i, t') t =
  if i >= length cs
  then internalError ("Macro index out of range in " ++ m)
  else unexpandCase (cs !! i)
    where
      unexpandCase (MacroCase p p') = do
        e <- match t p
        e' <- match t' p'
        return (subs (composeEnvs e e') p)


{- Well-formedness Checking -}

wellFormedMacro :: Macro -> Either WFError ()
wellFormedMacro (Macro m cs) = do
  mapM_ disjointCases (allDistinctPairs cs)
  mapM_ (wellFormedCase m) cs
  where
    disjointCases ((MacroCase p _), (MacroCase q _)) = case unify p q of
      Left _ -> return ()
      Right r -> Left (CasesOverlap m p q r)

wellFormedCase :: MacroName -> MacroCase -> Either WFError ()
wellFormedCase m (MacroCase p q) = do
  wellFormedPattern m p
  wellFormedPattern m q
  varSubset p q
  where
    varSubset p q =
      case (Set.toList (Set.difference (fvars q) (fvars p))) of
        [] -> return ()
        (v:_) -> Left (UnboundVar v)

wellFormedPattern :: MacroName -> Pattern -> Either WFError ()
wellFormedPattern _ (PVar _) = return ()
wellFormedPattern _ (PCst _) = return ()
wellFormedPattern m (PTag _ p) = wellFormedPattern m p
wellFormedPattern m (PNod _ ps) = mapM_ (wellFormedPattern m) ps
wellFormedPattern m (PRep _ ps r) = do
  mapM_ (wellFormedPattern m) ps
  wellFormedPattern m r
  when (Set.null (fvars r)) (Left (EmptyEllipsis m))


{- Expansion and Unexpansion -}

lookupMacro :: MacroName -> MacroTable -> Either ResugarError Macro
lookupMacro m ms = case Map.lookup m ms of
  Nothing -> Left (NoSuchMacro m)
  Just m -> return m

expand :: MacroTable -> Term -> Either ResugarError Term
expand _ (TCst c) = return (TCst c)
expand ms t@(TNod (NMac m) ts) = do
  (i, t') <- lookupMacro m ms >>= flip expandMacro t
  expand ms (TTag (MacHead m i (TNod (NMac m) ts)) t')
expand ms (TNod (NLst l) ts) = liftM (TNod (NLst l)) (mapM (expand ms) ts)
expand ms (TTag o t) = liftM (TTag o) ((expand ms) t)

unexpand :: MacroTable -> Term -> Either ResugarError Term
unexpand _ (TCst c) = return (TCst c)
unexpand ms (TNod l ts) = liftM (TNod l) (mapM (unexpand ms) ts)
unexpand ms (TTag MacBody _) = Left TermIsOpaque
unexpand ms (TTag (MacHead m i t) t') =
  lookupMacro m ms >>= (\m -> unexpandMacro m (i, t') t) >>= unexpand ms


{- Errors as Eithers -}

instance Monad (Either a) where
  return x = Right x
  e >>= f = case e of 
    Left err -> Left err
    Right x -> f x

eitherOr :: Either e a -> Either e a -> Either e a
eitherOr e1 e2 = case e1 of
  Left _ -> e2
  Right x -> Right x

isLeft e  = case e of Left _ -> True;  Right _ -> False
isRight e = case e of Left _ -> False; Right _ -> True


{- Utility -}

allDistinctPairs :: [a] -> [(a, a)]
allDistinctPairs [] = []
allDistinctPairs [_] = []
allDistinctPairs (x:xs) = map (\y -> (x, y)) xs ++ allDistinctPairs xs


{- Printing -}


str = showString

showsList :: [ShowS] -> ShowS
showsList [] = id
showsList [x] = x
showsList (x:y:ys) = x . str " " . showsList (y:ys)

showsParens :: [ShowS] -> ShowS
showsParens xs = str "(" . showsList xs . str ")"

showsBrackets :: [ShowS] -> ShowS
showsBrackets xs = str "[" . showsList xs . str "]"

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

instance Show Binding where
  showsPrec _ (BList bs) = showsBrackets (map shows bs)
  showsPrec _ (BTerm t) = shows t

instance Show Macro where
  showsPrec _ (Macro m cs) = showsList ([str m, str ":"] ++ map shows cs)

instance Show MacroCase where
  showsPrec _ (MacroCase p q) =
    showsParens [shows p, str "=>", shows q]