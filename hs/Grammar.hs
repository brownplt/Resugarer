module Grammar where

import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad (liftM, zipWithM_)


import Pattern hiding (unify)


newtype SortName = SortN String
                 deriving (Eq, Ord)

data Sort = SortName SortName
          | SortList Sort
          | IntSort
          | FloatSort
          | StringSort
          | AnySort
          deriving (Eq)

data Grammar = Grammar [Production]
             deriving (Eq)

data Production = Production Constructor SortName
                  deriving (Eq)

data Constructor = Constructor Label [Sort]
                   deriving (Eq)

data Rules = Rules [Rule]
           deriving (Eq)

data Language = Language Grammar Grammar
              deriving (Eq)

data Module = Module Language Language Rules
            deriving (Eq)

data CompiledModule =
  CompiledModule CompiledLanguage CompiledLanguage MacroTable

data CompiledLanguage =
  CompiledLanguage ProductionTable

type ProductionTable = Map Label Production

data SortError = SortUnifyFailure Sort Sort
               | NoSuchConstructor Label
               | WrongArity Pattern Int
               | InvalidRule Rule
               | SortErrorInRule SortError Rule

data CompilationError = SortError SortError
                      | WFError WFError

data ConformanceError = NonConformant Term Sort
                      | NonConformantC Label


rulesToMacros :: Rules -> MacroTable
rulesToMacros (Rules rs) = f (reverse rs) Map.empty
  where
    f [] ms = ms
    f (c@(Rule (PNode _ l _) _) : rs) ms =
      let ms' = case Map.lookup l ms of
            Nothing ->
              Map.insert l (Macro l [c]) ms
            Just (Macro l cs) ->
              Map.insert l (Macro l (c : cs)) ms
      in f rs ms'
    f _ _ = internalError
            "rulesToMacros: invalid rule not caught by sort checking."

-- TODO: check for duplicates
grammarToProductionTable :: Grammar -> ProductionTable
grammarToProductionTable (Grammar ps) =
  convert ps Map.empty
    where
      convert [] m = m
      convert (p@(Production (Constructor l ss) s) : ps) m =
        convert ps (Map.insert l p m)

compileModule :: Module -> Either CompilationError CompiledModule
compileModule (Module l1 l2 rs) =
  let l1' = compileLanguage l1
      l2' = compileLanguage l2
      Language (Grammar g1) (Grammar g2) = l1
      Language (Grammar g3) (Grammar g4) = l2
      wholeGrammar = Grammar (g1 ++ g2 ++ g3 ++ g4)
      ms = rulesToMacros rs
      table = grammarToProductionTable wholeGrammar in do
  sortCheckRules table rs
  wfCheck (Map.elems ms)
  return (CompiledModule l1' l2' ms)
    where
      wfCheck ms = case mapM_ wellFormedMacro ms of
        Left err -> Left (WFError err)
        Right () -> Right ()

compileLanguage :: Language -> CompiledLanguage
compileLanguage (Language (Grammar g1) (Grammar g2)) =
  let g = Grammar (g1 ++ g2) in
  CompiledLanguage (grammarToProductionTable g)

constToSort :: Const -> Sort
constToSort (CInt _) = IntSort
constToSort (CDbl _) = FloatSort
constToSort (CStr _) = StringSort

termConforms :: ProductionTable -> Sort -> Term ->
                Either ConformanceError ()
termConforms g s t =
  let nonconformant = Left (NonConformant t s)
      noSuchConstructor l = Left (NonConformantC l) in
  case t of
    TConst c -> if constToSort c == s
                then return ()
                else nonconformant
    TList ts -> case s of
      SortList s -> mapM_ (termConforms g s) ts
      _ -> nonconformant
    TTag _ t -> termConforms g s t
    TNode l ts -> case Map.lookup l g of
      Nothing -> noSuchConstructor l
      Just (Production (Constructor l' ss) s') ->
        if l == l' && length ts == length ss && s == SortName s'
        then zipWithM_ (termConforms g) ss ts
        else nonconformant

sortCheckRules :: ProductionTable -> Rules -> Either CompilationError ()
sortCheckRules g (Rules rs) = mapM_ checkRule rs
  where
    checkRule r = case sortCheckRule g r of
      Left err -> Left (SortError (SortErrorInRule err r))
      Right () -> return ()

sortCheckRule :: ProductionTable -> Rule -> Either SortError ()
sortCheckRule g (Rule p q) = do
  case p of
    PNode _ l _ -> do
      case Map.lookup l g of
        Nothing -> Left (NoSuchConstructor l)
        Just (Production c s0) -> do
          s <- sortInfer g p
          s' <- sortInfer g q
          unify s (SortName s0)
          unify s' (SortName s0)
          return ()
    _ -> Left (InvalidRule (Rule p q))

sortInfer :: ProductionTable -> Pattern -> Either SortError Sort
-- Infer the sort of a pattern.
sortInfer _ (PVar v) = return AnySort -- no duplicate vars, so no unification
sortInfer _ (PConst (CInt _)) = return IntSort
sortInfer _ (PConst (CDbl _)) = return FloatSort
sortInfer _ (PConst (CStr _)) = return StringSort
sortInfer g (PList ps) =
  liftM SortList (unifies =<< (mapM (sortInfer g) ps))
sortInfer g (PRep ps p) =
  liftM SortList (unifies =<< (mapM (sortInfer g) (p:ps)))
sortInfer g (PNode _ l ps) =
  case Map.lookup l g of
    Nothing -> Left (NoSuchConstructor l)
    Just (Production (Constructor _ ss) s) ->
      if length ss /= length ps
      then Left (WrongArity (PNode noInfo l ps) (length ss))
      else do
        zipWithM_ (sortCheck g) ps ss
        return (SortName s)
sortInfer _ (PTag _ _) =
  internalError "Tag encountered while checking sorts."

sortCheck :: ProductionTable -> Pattern -> Sort -> Either SortError Sort
-- Ensure that a pattern has a given sort.
sortCheck g p s = do
  s' <- sortInfer g p
  unify s s'

unifies :: [Sort] -> Either SortError Sort
unifies [] = return AnySort
unifies [s] = return s
unifies (s1:s2:ss) = do
  s <- unify s1 s2
  unifies (s:ss)
    
unify :: Sort -> Sort -> Either SortError Sort
unify AnySort      s                       = return s
unify s            AnySort                 = return s
unify (SortName n) (SortName n') | n == n' = return (SortName n)
unify (SortList s) (SortList s')           = liftM SortList (unify s s')
unify IntSort      IntSort                 = return IntSort
unify FloatSort    FloatSort               = return FloatSort
unify StringSort   StringSort              = return StringSort
unify s            s'                      = Left (SortUnifyFailure s s')
