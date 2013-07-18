module Env where

import qualified Data.Map as Map
import Data.Map (Map)

import Term

match :: Term -> Pattern -> Maybe Env
newtype Env = Env (Map String Term)

