module Pattern where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (liftM, liftM2, zipWithM)


newtype Var = Var String deriving (Eq, Ord)
type Label = String
type Macro = String

data Pattern =
    PVar Var
  | PCst Const
  | PNod NodeType [Pattern]
  | PRep NodeType [Pattern] Pattern
  | PTag Origin Pattern

data Term =
    TCst Const
  | TLst ListType [Term]
  | TTag Origin Term

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
  _ == _ = internalError "Pattern: origin eq: unexpected MacHead"

data Binding =
    BList [Binding]
  | BTerm Term

type Env = Map Var Binding

internalError msg = error ("Internal error: " ++ msg)

termToPattern :: Term -> Pattern
termToPattern (TCst c) = PCst c
termToPattern (TNod l ts) = PNod l (map termToPattern ts)
termToPattern (TTag o t) = PTag o (termToPattern t)

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

subs :: Env -> Pattern -> Pattern
subs e (PVar v)      = lookupVar v e
subs e (PCst c)      = PCst c
subs e (PNod l ps)   = PNod l (map (subs e) ps)
subs e (PRep l ps r) = PNod l (subs e ps ++ subsRep e r)
subs e (PTag o p)    = PTag o (subs e p)

subsRep e r = (splitEnv e (fvars r))

mtEnv = Map.empty
singletonEnv v t = Map.singleton v (BTerm t)
unionEnv = Map.union
lookupVar v e = case Map.lookup v e of
  Nothing -> internalError ("Unbound variable: " ++ show v)
  Just (BList _) = internalError ("Unexpected binding list")
  Just (BTerm t) = t

mergeEnvs :: [Env] -> Env
mergeEnvs [] = internalError "Unexpected empty env list"
mergeEnvs es = foldl1 merge (map singletonWrap es)
  where
    singletonWrap = Map.map (\t -> BList [t])
    merge e1 e2 = Map.intersectionWith concatBindings e1 e2
    concatBindings (BList bs) (BList bs') = BList (bs ++ bs')

union (PCst c)    (PCst c')       | c == c' = Just c
union (PVar v)    p                         = Just p
union p           (PVar v)                  = Just p
union (PTag o p)  (PTag o' p')    | o == o' = liftM (PTag o) (union p p')
union (PLst l ps) (