{-# LANGUAGE CPP #-}
module Pattern where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad (liftM, liftM2, zipWithM, when, replicateM)
import System.Random (randomIO)
import System.IO.Unsafe (unsafePerformIO) -- it's only to generate nonces, I swear!
import Data.Char (chr)
import Debug.Trace (trace)


newtype Var = Var String deriving (Eq, Ord)
newtype Label = Label String deriving (Eq, Ord)

type MacroTable = Map Label Macro

data Macro = Macro Label [Rule]
            
data Rule = Rule Pattern Pattern [Var] RuleFlags
            deriving (Eq) -- from, to, fresh vars

data RuleFlags = RuleFlags Bool -- overlap override
                 deriving (Eq)

data Info = Info Bool Bool -- transp marked, always transparent
noInfo = Info False False

data Pattern =
    PVar Var
  | PConst Const
  | PNode Info Label [Pattern]
  | PRep [Pattern] Pattern
  | PList [Pattern]
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
  | MacAlien

data Const =
    CInt Int
  | CDbl Double
  | CStr String
    deriving (Eq, Ord)

instance Eq Info where
  (==) = const (const True)

instance Eq Origin where
  MacBody == MacBody = True
  MacHead m _ _ == MacHead m' _ _ = m == m'
  _ == _ = False

data Binding =
    BList [Binding]
  | BTerm Term

type Env = Map Var Binding


data UnifyFailure = UnifyFailure Pattern Pattern

-- This means something really went wrong;
-- should never occur on good-faith user input.
data ResugarError = NoMatchingCase Label Term [Rule]
                  | NoSuchMacro Label
                  | NoSuchCase Label Int
                  | UnboundSubsVar Var
                  | DepthMismatch Var
                  deriving (Eq)

-- Except for `ResugarError`, this just means the term couldn't be resugared.
data ResugarFailure = MatchFailure Term Pattern
                    | TermIsOpaque
                    | ResugarError ResugarError
                    deriving (Eq)

data WFError = CasesOverlap Label Pattern Pattern Pattern
             | UnboundVar Var
             | EmptyEllipsis Label
             | DuplicateVar Var

instance Show Label where
  show (Label l) = l


-- These should never occur, even on malformed or malicious user input.
internalError msg = error ("Internal error: " ++ msg)

varName :: Var -> String
varName (Var name) = name

fvarList :: Pattern -> [Var]
fvarList (PVar v) = [v]
fvarList (PConst _) = []
fvarList (PNode _ _ ps) = concat (map fvarList ps)
fvarList (PRep ps p) = (concat (map fvarList ps)) ++ fvarList p
fvarList (PList ps) = concat (map fvarList ps)
fvarList (PTag _ p) = fvarList p

findDuplicate :: Ord a => [a] -> Maybe a
findDuplicate xs = findDup xs Set.empty
  where
    findDup [] _ = Nothing
    findDup (x:xs) s =
      if Set.member x s
      then Just x
      else findDup xs (Set.insert x s)

fvars :: Pattern -> Set Var
fvars (PVar v) = Set.singleton v
fvars (PConst _) = Set.empty
fvars (PNode _ _ ps) = Set.unions (map fvars ps)
fvars (PRep ps p) = Set.union (Set.unions (map fvars ps)) (fvars p)
fvars (PList ps) = Set.unions (map fvars ps)
fvars (PTag _ p) = fvars p

bodyWrap :: Bool -> Pattern -> Pattern
-- Enclose all of a pattern's subpatterns in MacBody tags.
bodyWrap z p = wrap p
  where
    wrap :: Pattern -> Pattern
    wrap (PVar v) = PVar v
    wrap (PConst c) = PConst c
    wrap (PNode i@(Info z' v) l ps) =
      if z'
      then opacify (not z) (PNode i l (map (bodyWrap (not z)) ps))
      else opacify z (PNode i l (map wrap ps))
    wrap (PRep ps p) = PRep (map wrap ps) (wrap p)
    wrap (PList ps) = PList (map wrap ps)
    wrap (PTag o p) = opacify z (skipTags (PTag o p))
      where
        skipTags (PTag o p) = PTag o (skipTags p)
        skipTags p = wrap p
    
    opacify :: Bool -> Pattern -> Pattern
    opacify z n@(PNode (Info _ True) _ _) = n -- never, ever tag these nodes
    opacify z p = if z then PTag MacBody p else p


{- Matching -}

match :: Term -> Pattern -> Either ResugarFailure Env
match (TConst c)   (PConst c')    | c == c' = return mtEnv
match t            (PVar v)                 = return (singletonEnv v t)
match (TTag o t)   (PTag o' p)    | o == o' = match t p
match (TNode l ts) (PNode i l' ps)| l == l' = matchNode i l ts ps
match (TList ts)   (PList ps)     | length ts == length ps =
  liftM Map.unions (zipWithM match ts ps)
match (TList ts)   (PRep ps p)    | length ts >= length ps = do
  e1 <- liftM Map.unions (zipWithM match (take (length ps) ts) ps)
  e2 <- matchList (drop (length ps) ts) p
  return (unifyEnv e1 e2)
match t            p                        = Left (MatchFailure t p)

matchNode :: Info -> Label -> [Term] -> [Pattern] -> Either ResugarFailure Env
matchNode _ _ [] [] = return mtEnv
matchNode i l (t:ts) (p:ps) = liftM2 unifyEnv (match t p) (matchNode i l ts ps)
matchNode i l ts ps = Left (MatchFailure (TNode l ts) (PNode i l ps))

matchList :: [Term] -> Pattern -> Either ResugarFailure Env
matchList []     p = return $ Map.fromList $
  map (\v -> (v, BList [])) (Set.toList (fvars p))
matchList (t:ts) p = liftM mergeEnvs (zipWithM match (t:ts) (repeat p))

mergeEnvs :: [Env] -> Env
mergeEnvs [] = internalError "mergeEnvs: Unexpected empty env list"
mergeEnvs es = foldl1 merge (map singletonWrap es)
  where
    singletonWrap = Map.map (\t -> BList [t])
    merge e1 e2 = Map.intersectionWith concatBindings e1 e2
    concatBindings (BList bs) (BList bs') = BList (bs ++ bs')
    concatBindings _ _ = internalError "concatBindings: unexpected"


{- Substitution -}

subs :: Env -> Pattern -> Either ResugarFailure Term
subs e (PVar v) = case Map.lookup v e of
  Nothing -> Left (ResugarError (UnboundSubsVar v))
  Just (BTerm t) -> return t
  Just (BList _) -> Left (ResugarError (DepthMismatch v))
subs e (PConst c)     = return (TConst c)
subs e (PNode _ l ps) = liftM (TNode l) (mapM (subs e) ps)
subs e (PList ps)     = liftM TList (mapM (subs e) ps)
subs e (PRep ps p)    = liftM TList (liftM2 (++) (mapM (subs e) ps) (subsList e p))
subs e (PTag o p)     = liftM (TTag o) (subs e p)

subsList e p = do
  let vs = Set.toList (fvars p)
  if null vs
    then internalError
         "Empty ellipsis: should have been caught by wf check"
    else do
    es <- splitEnv e (Set.toList (fvars p))
    mapM (\e -> subs e p) es

mtEnv = Map.empty
singletonEnv v t = Map.singleton v (BTerm t)
unifyEnv = Map.union

composeEnvs :: Env -> Env -> Env
composeEnvs e1 e2 = Map.union e2 e1

splitEnv :: Env -> [Var] -> Either ResugarFailure [Env]
splitEnv e vs = do
  n <- n
  mapM (\i -> mapWithKeyM (split i) e) [0 .. n-1]
  where
    -- Caller must check that vs nonempty!
    n = case Map.lookup (head vs) e of
      Nothing -> Left (ResugarError (UnboundSubsVar (head vs)))
      Just (BTerm _) -> Left (ResugarError (DepthMismatch (head vs)))
      Just (BList bs) -> return (length bs)
    split i v b =
      if elem v vs
      then case b of
        BTerm _ -> Left (ResugarError (DepthMismatch v))
        BList bs -> return (bs !! i)
      else return b


{- Unification (incomplete) -}

unify :: Pattern -> Pattern -> Either UnifyFailure Pattern
unify (PConst c)   (PConst c')       | c == c' = return (PConst c)
unify (PVar v)     p                           = return p
unify p            (PVar v)                    = return p
unify (PTag o p)   (PTag o' p')      | o == o' = liftM (PTag o) (unify p p')
unify (PRep ps p)  (PRep ps' p')              = undefined
unify (PNode i l ps) (PNode _ l' ps')    | l == l' && length ps == length ps'
  = liftM (PNode i l) (zipWithM unify ps ps')
unify p q = Left (UnifyFailure p q)

subsumed :: Pattern -> Pattern -> Bool
subsumed _            (PVar _)                 = True
subsumed (PConst c)   (PConst c')    | c == c' = True
subsumed (PTag o p)   (PTag o' p')   | o == o' = subsumed p p'
subsumed (PRep ps p)  (PRep ps' p')            = undefined
subsumed (PNode _ l ps) (PNode _ l' ps') | l == l' && length ps == length ps'
  = and (zipWith subsumed ps ps')
subsumed _            _                        = False


{- Macros -}

gensym :: String -> String
gensym prefix =
  prefix ++ unsafePerformIO (replicateM 8 randLetter)
  where
    randLetter :: IO Char
    randLetter = do
      c <- randomIO :: IO Int
      return (chr ((c `mod` 26) + 65))

addFreshVars :: [Var] -> Env -> Env
addFreshVars [] env = env
addFreshVars (Var f:fs) env =
  addFreshVars fs $
  Map.insert (Var f) (BTerm (TConst (CStr (gensym f)))) env

expandMacro :: Macro -> Term -> Either ResugarFailure (Int, Term)
expandMacro (Macro name cs) t = expandCases 0 cs
  where
    expandCases _ [] = Left (ResugarError (NoMatchingCase name t cs))
    expandCases i (c:cs) = eitherOr (expandCase i c) (expandCases (i + 1) cs)
    
    expandCase i (Rule p p' fs _) = do
      e <- match t (bodyWrap False p)
      t <- subs (addFreshVars fs e) (bodyWrap True p')
      return (i, t)

unexpandMacro :: Macro -> (Int, Term) -> Term -> Either ResugarFailure Term
unexpandMacro (Macro l cs) (i, t') t =
  if i >= length cs
  then Left (ResugarError (NoSuchCase l i))
  else unexpandCase (cs !! i)
    where
      unexpandCase (Rule p p' _ _) = do
        e <- match t (bodyWrap False p)
        e' <- match t' (bodyWrap True p')
        subs (composeEnvs e e') p


{- Well-formedness Checking -}

checkDuplicateVar :: Pattern -> Either WFError ()
checkDuplicateVar p = case findDuplicate (fvarList p) of
  Nothing -> return ()
  Just v -> Left (DuplicateVar v)

wellFormedMacro :: Macro -> Either WFError ()
wellFormedMacro (Macro l cs) = do
  mapM_ disjointCases (allDistinctPairs cs)
  mapM_ (wellFormedCase l) cs
  where
    disjointCases ((Rule p _ _ (RuleFlags True)), _) =
      return ()
    disjointCases ((Rule p _ _ _), (Rule q _ _ _)) =
      case unify p q of
        Left _ -> return ()
        Right r -> Left (CasesOverlap l p q r)

wellFormedCase :: Label -> Rule -> Either WFError ()
wellFormedCase l (Rule p q fs _) = do
  checkDuplicateVar p
  -- TODO: figure out how to handle dup vars systematically
  -- checkDuplicateVar q
  wellFormedPattern l p
  wellFormedPattern l q
  varSubset p q
  where
    varSubset p q =
      let pVars = Set.union (fvars p) (Set.fromList fs)
          qVars = fvars q in
      case Set.toList (Set.difference qVars pVars) of
        [] -> return ()
        (v:_) -> Left (UnboundVar v)

wellFormedPattern :: Label -> Pattern -> Either WFError ()
wellFormedPattern _ (PVar _) = return ()
wellFormedPattern _ (PConst _) = return ()
wellFormedPattern l (PTag _ p) = wellFormedPattern l p
wellFormedPattern l (PNode _ _ ps) = mapM_ (wellFormedPattern l) ps
wellFormedPattern l (PList ps) = mapM_ (wellFormedPattern l) ps
wellFormedPattern l (PRep ps p) = do
  mapM_ (wellFormedPattern l) ps
  wellFormedPattern l p
  when (Set.null (fvars p)) (Left (EmptyEllipsis l))


{- Expansion and Unexpansion -}

lookupMacro :: Label -> MacroTable -> Maybe Macro
lookupMacro l ms = Map.lookup l ms

expand :: MacroTable -> Term -> Either ResugarFailure Term
expand _ (TConst c) = return (TConst c)
expand ms (TTag o t) = liftM (TTag o) ((expand ms) t)
expand ms (TList ts) = liftM TList (mapM (expand ms) ts)
expand ms t@(TNode l ts) =
  case lookupMacro l ms of
    Nothing -> liftM (TNode l) (mapM (expand ms) ts)
    Just m -> do
      (i, t') <- expandMacro m t
      expand ms (TTag (MacHead l i (TNode l ts)) t')
 
unexpand :: MacroTable -> Term -> Either ResugarFailure Term
unexpand ms t = do
  t' <- rec t
  if unlittered t'
    then return t'
    else Left TermIsOpaque
  where
    unlittered :: Term -> Bool
    unlittered (TConst c) = True
    unlittered (TList ts) = and (map unlittered ts)
    unlittered (TNode _ ts) = and (map unlittered ts)
    unlittered (TTag _ _) = False
    
    rec :: Term -> Either ResugarFailure Term
    rec (TConst c) = return (TConst c)
    rec (TList ts) = liftM TList (mapM rec ts)
    rec (TNode l ts) = liftM (TNode l) (mapM rec ts)
    rec (TTag (MacHead l i t) t') =
      case lookupMacro l ms of
        Nothing -> Left (ResugarError (NoSuchMacro l))
        Just l -> do
          t' <- rec t'
          unexpandMacro l (i, t') t
    rec (TTag o t') = liftM (TTag o) (rec t')


{- Errors as Eithers -}
#if __GLASGOW_HASKELL__ < 700
instance Monad (Either a) where
  return x = Right x
  e >>= f = case e of 
    Left err -> Left err
    Right x -> f x
#endif

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

mapWithKeyM :: (Monad m, Ord k) => (k -> a -> m b) -> Map k a -> m (Map k b)
mapWithKeyM f m = liftM Map.fromList (mapM f' (Map.toList m))
  where
    f' (k, x) = f k x >>= return . (\x -> (k, x))

