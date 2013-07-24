module Grammar where

import qualified Data.Map as Map
import Data.Map (Map)
import Pattern

type SortName = String

data Sort = SortName SortName
          | SortList Sort
          | IntSort
          | FloatSort
          | StringSort
          deriving (Eq)

data Grammar = Grammar [Production]
             deriving (Eq)

data Production = Production Constructor SortName
                  deriving (Eq)

data Constructor = Constructor Label [Sort]
                   deriving (Eq)

data Rules = Rules [Rule]
           deriving (Eq)

data Language = Language Grammar SortName
              deriving (Eq)

data Module = Module Language Language Rules
            deriving (Eq)

type ConstructorTable = Map SortName [Constructor]

-- How to check?
data RulesError = IncompleteSugarError Production


rulesToMacros :: Rules -> MacroTable
rulesToMacros (Rules rs) = f (reverse rs) Map.empty
  where
    f [] ms = ms
    f (c@(Rule (PNode l _) _) : rs) ms =
      case Map.lookup l ms of
        Nothing ->
          Map.insert l (Macro l [c]) ms
        Just (Macro l cs) ->
          Map.insert l (Macro l (c : cs)) ms

grammarToConstructorTable :: Grammar -> ConstructorTable
grammarToConstructorTable (Grammar ps) =
  convert ps Map.empty
    where
      convert [] m = m
      convert (Production c s : ps) m =
        convert ps (Map.insertWith (++) s [c] m)

constToSort :: Const -> Sort
constToSort (CInt _) = IntSort
constToSort (CDbl _) = FloatSort
constToSort (CStr _) = StringSort

termConforms :: ConstructorTable -> Sort -> Term -> Bool
termConforms g s t =
  case t of
    TConst c -> s == constToSort c
    TList ts -> case s of
      SortList s -> and (map (termConforms g s) ts)
      _ -> False
    TTag _ t -> termConforms g s t
    TNode l ts -> case s of
      SortName name -> case Map.lookup name g of
        Nothing -> False
        Just cs -> or (map conforms cs)
      where
        conforms (Constructor l' ss) =
          (l == l') &&
          (length ss == length ts) &&
          and (zipWith (termConforms g) ss ts)
