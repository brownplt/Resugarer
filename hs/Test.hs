{-# LANGUAGE TypeSynonymInstances #-}
module Main where

import Pattern
import Grammar
import Show
import Parse
import Debug.Trace (trace)
import Prelude hiding (const)
import Test.QuickCheck hiding (label)
import Control.Monad (liftM, liftM2, liftM3)
import Data.Maybe (isJust)

smallList :: Arbitrary a => Gen [a]
smallList = oneof (map (\i -> vectorOf i arbitrary)
                   [1, 1, 2, 2, 3])

mediumList :: Arbitrary a => Gen [a]
mediumList = oneof (map (\i -> vectorOf i arbitrary)
                    [1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 6, 7])

instance Arbitrary Label where
  arbitrary = oneof (map (return . Label) ["Plus", "Times", "M", "MM"])

instance Arbitrary Macro where
  arbitrary = liftM (Macro (Label "M")) (vectorOf 3 arbitrary)

instance Arbitrary Rule where
  arbitrary = liftM2 Rule arbitrary arbitrary

instance Arbitrary Rules where
  arbitrary = liftM Rules mediumList

instance Arbitrary Grammar where
  arbitrary = liftM Grammar mediumList

instance Arbitrary ConstructorTable where
  arbitrary = liftM grammarToConstructorTable arbitrary

instance Arbitrary Language where
  arbitrary = liftM (flip Language "Expr") arbitrary

instance Arbitrary Module where
  arbitrary = liftM3 Module arbitrary arbitrary arbitrary

instance Arbitrary Production where
  arbitrary = liftM2 Production (liftM2 Constructor arbitrary smallList)
                                (oneof sorts)
    where
      sorts = [return "Expr", return "Struct", return "Other"]

instance Arbitrary Sort where
  arbitrary = oneof [return (SortName "Expr"),
                     return (SortName "Expr"),
                     return (SortName "Struct"),
                     return (SortName "Struct"),
                     return IntSort,
                     return StringSort,
                     liftM SortList arbitrary,
                     liftM SortList arbitrary]

instance Arbitrary Var where
  arbitrary = oneof $ map (return . Var) ["x", "y", "z"]

instance Arbitrary Pattern where
  arbitrary = sized $ \n ->
    let smaller = resize (n `div` 2 - 1) in
    if n == 0
    then oneof [liftM PVar arbitrary,
                liftM PVar arbitrary,
                liftM PConst arbitrary]
    else oneof [liftM PVar arbitrary,
                liftM PVar arbitrary,
                liftM PConst arbitrary,
                liftM2 PNode (smaller arbitrary) (smaller arbitrary),
                liftM2 PNode (smaller arbitrary) (smaller arbitrary),
                liftM PList (smaller arbitrary),
                liftM2 PTag arbitrary (smaller arbitrary)]

termGen :: Gen Term
termGen = arbitrary

instance Arbitrary Term where
  arbitrary = sized $ \n ->
    let n' = n `div` 2 - 1 in
    if n == 0
    then oneof [return (TConst (CInt 2)),
                return (TConst (CInt 3))]
    else oneof [liftM2 TTag  (resize n' arbitrary)
                             (resize n' arbitrary),
                liftM2 TNode (resize n' arbitrary)
                             (resize n' arbitrary)]

instance Arbitrary Const where
  -- No need to check doubles and strings
  arbitrary = oneof $ map return [CInt 2, CInt 3, CInt 4]

instance Arbitrary Origin where
  arbitrary = oneof [return MacBody,
                     return MacBody,
                     return (MacHead (Label "M") 0 (TConst (CStr "t")))]

data CoreTerm = CoreTerm Int Term
              deriving Show

instance Arbitrary CoreTerm where
  arbitrary = oneof [makeCoreTerm 0, makeCoreTerm 1, makeCoreTerm 2]
    where
      makeCoreTerm i = do
        t <- arbitrary
        return (CoreTerm i t)

deepCheck x n = quickCheckWith stdArgs {maxSuccess = n} x

prop_parse p x =
  case parse p "(quickcheck-test)" (show x) of
    Left _ -> False
    Right y -> x == y

prop_match t p =
  if isLeft (wellFormedPattern (Label "M") p)
  then True
  else case match t p of
    Left _ -> True
    Right e -> case (subs e p) of
      Left _ -> False
      Right t' -> t == t'

prop_get_put m t =
  if isLeft (wellFormedMacro m)
  then True
  else trace "." $ case expandMacro m t of
    Left _ -> True
    Right t' -> case unexpandMacro m t' t of
      Left _ -> False
      Right t2 -> t2 == t
  where types = t :: Term

prop_put_get :: Macro -> Term -> CoreTerm -> Bool
prop_put_get m t (CoreTerm i t') =
  if isLeft (wellFormedMacro m)
  then True
  else case unexpandMacro m (i, t') t of
    Left _ -> True
    Right t -> trace "." $ case expandMacro m t of
      Left _ -> False
      Right t2' -> t2' == (i, t')

main = do
--  sample (arbitrary :: Gen Grammar)
--  sample (arbitrary :: Gen Pattern)
--  sample (arbitrary :: Gen Rules)
--  sample (arbitrary :: Gen Pattern)
--  sample (arbitrary :: Gen Module)
  putStrLn "Testing parsing..."
  quickCheck (prop_parse label)
  quickCheck (prop_parse sort)
  quickCheck (prop_parse const)
  quickCheck (prop_parse origin)
  quickCheck (prop_parse term)
  quickCheck (prop_parse pattern)
  quickCheck (prop_parse grammar)
  quickCheck (prop_parse rule)
  quickCheck (prop_parse language)
  quickCheck (prop_parse top)
  putStrLn "Testing algorithms..."
  deepCheck prop_match    1000
  -- useless (precondition rarely ever satisfied):
--  deepCheck prop_get_put 1000
--  deepCheck prop_put_get 1000
