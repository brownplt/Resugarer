{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Pattern
import Show
import Test.QuickCheck
import Control.Monad (liftM, liftM2, liftM3)
import Data.Maybe (isJust)

instance Arbitrary Macro where
  arbitrary = liftM (Macro "M") (vectorOf 3 arbitrary)

instance Arbitrary MacroCase where
  arbitrary = liftM2 MacroCase arbitrary arbitrary

instance Arbitrary Var where
  arbitrary = oneof $ map (return . Var) ["x", "y", "z"]

instance Arbitrary Pattern where
  arbitrary = sized $ \n ->
    let smaller = resize (n `div` 2 - 1) in
    if n == 0
    then oneof [liftM PVar arbitrary,
                liftM PVar arbitrary,
                liftM PCst arbitrary]
    else oneof [liftM2 PNod (smaller arbitrary) (smaller arbitrary),
                liftM3 PRep (smaller arbitrary) (smaller arbitrary) (smaller arbitrary),
                liftM2 PTag arbitrary (smaller arbitrary)]

termGen :: Gen Term
termGen = arbitrary

instance Arbitrary Term where
  arbitrary = sized $ \n ->
    let n' = n `div` 2 - 1 in
    if n == 0
    then oneof [return (TCst (CInt 2)),
                return (TCst (CInt 3))]
    else oneof [liftM2 TTag (resize n' arbitrary)
                            (resize n' arbitrary),
                liftM2 TNod (resize n' arbitrary)
                            (resize n' arbitrary)]

instance Arbitrary NodeType where
  arbitrary = oneof [return (NLst "plus"),
                     return (NLst "times"),
                     return (NLst "if"),
                     return (NMac "M"),
                     return (NMac "MM")]

instance Arbitrary Const where
  -- No need to check doubles and strings
  arbitrary = oneof $ map return [CInt 2, CInt 3, CInt 4]

instance Arbitrary Origin where
  arbitrary = oneof [return MacBody,
                     return MacBody,
                     return (MacHead "mac" 0 (TCst (CStr "t")))]

--deepCheck p = check (defaultConfig { configMaxTest = 10000}) p

deepCheck x = quickCheckWith stdArgs {maxSuccess = 10000} x

prop_subs t p =
  if isLeft (wellFormedPattern "m" p)
  then True
  else case match t p of
    Left _ -> True
    Right e -> subs e p == t

prop_get_put m t =
  if isLeft (wellFormedMacro m)
  then True
  else case expandMacro m t of
    Left _ -> True
    Right t' -> case unexpandMacro m t' t of
      Left _ -> False
      Right t2 -> t2 == t
  where types = t :: Term

prop_put_get :: Macro -> Int -> Term -> (Int, Term) -> Property
prop_put_get m i t t' = i < 3 && i >= 0 ==>
  if isLeft (wellFormedMacro m)
  then True
  else case unexpandMacro m t' t of
    Left _ -> True
    Right t -> case expandMacro m t of
      Left _ -> False
      Right t2' -> t2' == t'

main = do
  deepCheck prop_subs
  deepCheck prop_get_put
  deepCheck prop_put_get
--  sample (arbitrary :: Gen Pattern)
