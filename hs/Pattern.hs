module Pattern where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (liftM, liftM2, zipWithM)
import Data.Maybe (isNothing, isJust)


newtype Var = Var String deriving (Eq, Ord)
type Label = String
type Macro = String

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
  | NMac Macro
    deriving (Eq, Ord)

data Const =
    CInt Int
  | CDbl Double
  | CStr String
    deriving (Eq, Ord)

data Origin =
    MacHead Macro Int Term
  | MacBody

instance Eq Origin where
  MacBody == MacBody = True
  MacHead m _ _ == MacHead m' _ _ = m == m'
  _ == _ = False

data Binding =
    BList [Binding]
  | BTerm Term

type Env = Map Var Binding

internalError msg = error ("Internal error: " ++ msg)

termToPattern :: Term -> Pattern
termToPattern (TCst c) = PCst c
termToPattern (TNod l ts) = PNod l (map termToPattern ts)
termToPattern (TTag o t) = PTag o (termToPattern t)

-- TODO: Remove duplicates
fvars :: Pattern -> [Var]
fvars (PVar v) = [v]
fvars (PCst _) = []
fvars (PNod _ ps) = concat (map fvars ps)
fvars (PRep _ ps r) = concat (map fvars ps) ++ fvars r
fvars (PTag _ p) = fvars p

repStr = "..."
macBodyStr = "Body"
macHeadStr = "Head"
tagStr = "Tag"

match :: Term -> Pattern -> Maybe Env
match (TCst c)    (PCst c')      | c == c' = Just mtEnv
match t           (PVar v)                 = Just (singletonEnv v t)
match (TTag o t)  (PTag o' p)    | o == o' = match t p
match (TNod l ts) (PNod l' ps)   | l == l' = matches ts ps
match (TNod l ts) (PRep l' ps r) | l == l' = matchRep ts ps r
match _           _                        = Nothing

matches [] [] = Just mtEnv
matches (t:ts) (p:ps) = liftM2 unionEnv (match t p) (matches ts ps)
matches _ _ = Nothing

matchRep [] [] _ = Just mtEnv
matchRep (t:ts) (p:ps) r = liftM2 unionEnv (match t p) (matchRep ts ps r)
matchRep (t:ts) [] r = liftM mergeEnvs (zipWithM match (t:ts) (repeat r))
matchRep [] _ _ = Nothing

subs :: Env -> Pattern -> Term
subs e (PVar v)      = lookupVar v e
subs e (PCst c)      = TCst c
subs e (PNod l ps)   = TNod l (map (subs e) ps)
subs e (PRep l ps r) = TNod l (map (subs e) ps ++ subsRep e r)
subs e (PTag o p)    = TTag o (subs e p)

subsRep e r = map (\e -> subs e r) (splitEnv e (fvars r))

mtEnv = Map.empty
singletonEnv v t = Map.singleton v (BTerm t)
unionEnv = Map.union
lookupVar v@(Var name) e = case Map.lookup v e of
  Nothing -> internalError ("Unbound variable: " ++ name)
  Just (BList _) -> internalError ("Unexpected binding list")
  Just (BTerm t) -> t

mergeEnvs :: [Env] -> Env
mergeEnvs [] = internalError "Unexpected empty env list"
mergeEnvs es = foldl1 merge (map singletonWrap es)
  where
    singletonWrap = Map.map (\t -> BList [t])
    merge e1 e2 = Map.intersectionWith concatBindings e1 e2
    concatBindings (BList bs) (BList bs') = BList (bs ++ bs')

splitEnv :: Env -> [Var] -> [Env]
splitEnv e vs =
  map (\i -> Map.mapWithKey (split i) e) [0 .. n-1]
  where
    -- TODO: Give error msg
    n = case Map.lookup (head vs) e of Just (BList bs) -> length bs
    split i v b = if elem v vs
                  then case b of
                    -- TODO: Give error msg
                    BList bs -> bs !! i
                  else b

union :: Pattern -> Pattern -> Maybe Pattern
union (PCst c)    (PCst c')          | c == c' = Just (PCst c)
union (PVar v)    p                            = Just p
union p           (PVar v)                     = Just p
union (PTag o p)  (PTag o' p')       | o == o' = liftM (PTag o) (union p p')
union (PNod l ps) (PNod l' ps')      | l == l' && length ps == length ps'
  = liftM (PNod l) (zipWithM union ps ps')
union (PNod l ps) (PRep l' ps' r)    | l == l' && length ps >= length ps'
  = liftM (PNod l) (zipWithM union ps (ps' ++ repeat r))
union (PRep l' ps' r) (PNod l ps)    | l == l' && length ps >= length ps'
  = liftM (PNod l) (zipWithM union ps (ps' ++ repeat r))
union (PRep l ps r) (PRep l' ps' r') | l == l' && isNothing (union r r')
  = if length ps >= length ps'
    then liftM (PNod l) (zipWithM union ps (ps' ++ repeat r'))
    else liftM (PNod l) (zipWithM union ps' (ps ++ repeat r))
union (PRep l ps r) (PRep l' ps' r') | l == l' && isJust (union r r')
  = if length ps >= length ps'
    then liftM2 (PRep l) (zipWithM union ps (ps' ++ repeat r'))
                         (union r r')
    else liftM2 (PRep l) (zipWithM union ps' (ps ++ repeat r))
                         (union r r')
