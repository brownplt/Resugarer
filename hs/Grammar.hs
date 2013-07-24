module Grammar where

import qualified Data.Map as Map
import Data.Map (Map)
import Pattern

newtype Sort = Sort String
             deriving (Eq)

data ESort = ESort Sort
           | EList ESort
           deriving (Eq)

data Grammar = Grammar [Production]
             deriving (Eq)

data Production = Production Label [ESort] Sort
                  deriving (Eq)

data Rules = Rules [Rule]
           deriving (Eq)

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
