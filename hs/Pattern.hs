module Pattern where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad (liftM, liftM2, zipWithM, when)


newtype Var = Var String deriving (Eq, Ord)
newtype Label = Label String deriving (Eq, Ord)

type MacroTable = Map Label Macro

data Macro = Macro Label [Rule]

data Rule = Rule Pattern Pattern deriving (Eq)

data Pattern =
    PVar Var
  | PConst Const
  | PNode Label [Pattern]
  | PList Pattern
  | PTag Origin Pattern
    deriving (Eq)

data Term =
    TConst Const
  | TNode Label [Term]
  | TList [Term]
  | TTag Origin Term
    deriving (Eq)

data Origin =
    MacHead Label Int Term
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


data UnifyFailure = UnifyFailure Pattern Pattern

-- This means something really went wrong
data ResugarError = NoMatchingCase Label Term
                  | NoSuchMacro Label

-- Except for `ResugarError`, this just means the term couldn't be resugared.
data ResugarFailure = MatchFailure Term Pattern
                    | TermIsOpaque
                    | ResugarError ResugarError

data WFError = CasesOverlap Label Pattern Pattern Pattern
             | UnboundVar Var
             | EmptyEllipsis Label

instance Show Label where
  show (Label l) = l


internalError msg = error ("Internal error: " ++ msg)

termToPattern :: Term -> Pattern
termToPattern (TConst c) = PConst c
termToPattern (TNode l ts) = PNode l (map termToPattern ts)
termToPattern (TTag o t) = PTag o (termToPattern t)

varName :: Var -> String
varName (Var name) = name

fvars :: Pattern -> Set Var
fvars (PVar v) = Set.singleton v
fvars (PConst _) = Set.empty
fvars (PNode _ ps) = Set.unions (map fvars ps)
fvars (PList p) = fvars p
fvars (PTag _ p) = fvars p


{- Matching -}

match :: Term -> Pattern -> Either ResugarFailure Env
match (TConst c)   (PConst c')    | c == c' = return mtEnv
match t            (PVar v)                 = return (singletonEnv v t)
match (TTag o t)   (PTag o' p)    | o == o' = match t p
match (TNode l ts) (PNode l' ps)  | l == l' = matchNode l ts ps
match (TList ts)   (PList p)                = matchList ts p
match t            p                        = Left (MatchFailure t p)

matchNode :: Label -> [Term] -> [Pattern] -> Either ResugarFailure Env
matchNode _ [] [] = return mtEnv
matchNode l (t:ts) (p:ps) = liftM2 unifyEnv (match t p) (matchNode l ts ps)
matchNode l ts ps = Left (MatchFailure (TNode l ts) (PNode l ps))

matchList :: [Term] -> Pattern -> Either ResugarFailure Env
matchList []     p = return $ Map.fromList $
  map (\v -> (v, BList [])) (Set.toList (fvars p))
matchList (t:ts) p = liftM mergeEnvs (zipWithM match (t:ts) (repeat p))

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
subs e (PConst c)    = TConst c
subs e (PNode l ps)  = TNode l (map (subs e) ps)
subs e (PList p)     = TList (subsList e p)
subs e (PTag o p)    = TTag o (subs e p)

subsList e p = map (\e -> subs e p) (splitEnv e (Set.toList (fvars p)))

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

unify :: Pattern -> Pattern -> Either UnifyFailure Pattern
unify (PConst c)   (PConst c')       | c == c' = return (PConst c)
unify (PVar v)     p                           = return p
unify p            (PVar v)                    = return p
unify (PTag o p)   (PTag o' p')      | o == o' = liftM (PTag o) (unify p p')
unify (PList p)    (PList p')                  = liftM PList (unify p p')
unify (PNode l ps) (PNode l' ps')    | l == l' && length ps == length ps'
  = liftM (PNode l) (zipWithM unify ps ps')
unify p q = Left (UnifyFailure p q)

subsumed :: Pattern -> Pattern -> Bool
subsumed _            (PVar _)                 = True
subsumed (PConst c)   (PConst c')    | c == c' = True
subsumed (PTag o p)   (PTag o' p')   | o == o' = subsumed p p'
subsumed (PList p)    (PList p')               = subsumed p p'
subsumed (PNode l ps) (PNode l' ps') | l == l' && length ps == length ps'
  = and (zipWith subsumed ps ps')
subsumed _            _                        = False


{- Macros -}

expandMacro :: Macro -> Term -> Either ResugarFailure (Int, Term)
expandMacro (Macro name cs) t = expandCases 0 cs
  where
    expandCases _ [] = Left (ResugarError (NoMatchingCase name t))
    expandCases i (c:cs) = eitherOr (expandCase i c) (expandCases (i + 1) cs)
    
    expandCase i (Rule p p') = do
      e <- match t p
      return (i, subs e p')

unexpandMacro :: Macro -> (Int, Term) -> Term -> Either ResugarFailure Term
unexpandMacro (Macro l cs) (i, t') t =
  if i >= length cs
  then internalError ("Macro index out of range in " ++ show l)
  else unexpandCase (cs !! i)
    where
      unexpandCase (Rule p p') = do
        e <- match t p
        e' <- match t' p'
        return (subs (composeEnvs e e') p)


{- Well-formedness Checking -}

wellFormedMacro :: Macro -> Either WFError ()
wellFormedMacro (Macro l cs) = do
  mapM_ disjointCases (allDistinctPairs cs)
  mapM_ (wellFormedCase l) cs
  where
    disjointCases ((Rule p _), (Rule q _)) = case unify p q of
      Left _ -> return ()
      Right r -> Left (CasesOverlap l p q r)

wellFormedCase :: Label -> Rule -> Either WFError ()
wellFormedCase l (Rule p q) = do
  wellFormedPattern l p
  wellFormedPattern l q
  varSubset p q
  where
    varSubset p q =
      case (Set.toList (Set.difference (fvars q) (fvars p))) of
        [] -> return ()
        (v:_) -> Left (UnboundVar v)

wellFormedPattern :: Label -> Pattern -> Either WFError ()
wellFormedPattern _ (PVar _) = return ()
wellFormedPattern _ (PConst _) = return ()
wellFormedPattern l (PTag _ p) = wellFormedPattern l p
wellFormedPattern l (PNode _ ps) = mapM_ (wellFormedPattern l) ps
wellFormedPattern l (PList p) = do
  wellFormedPattern l p
  when (Set.null (fvars p)) (Left (EmptyEllipsis l))


{- Expansion and Unexpansion -}

lookupMacro :: Label -> MacroTable -> Maybe Macro
lookupMacro l ms = Map.lookup l ms

expand :: MacroTable -> Term -> Either ResugarFailure Term
expand _ (TConst c) = return (TConst c)
expand ms (TTag o t) = liftM (TTag o) ((expand ms) t)
expand ms t@(TNode l ts) =
  case lookupMacro l ms of
    Nothing -> liftM (TNode l) (mapM (expand ms) ts)
    Just m -> do
      (i, t') <- expandMacro m t
      expand ms (TTag (MacHead l i (TNode l ts)) t')

unexpand :: MacroTable -> Term -> Either ResugarFailure Term
unexpand _ (TConst c) = return (TConst c)
unexpand ms (TNode l ts) = liftM (TNode l) (mapM (unexpand ms) ts)
unexpand ms (TTag MacBody _) = Left TermIsOpaque
unexpand ms (TTag (MacHead l i t) t') =
  case lookupMacro l ms of
    Nothing -> Left (ResugarError (NoSuchMacro l))
    Just l -> unexpandMacro l (i, t') t >>= unexpand ms


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
