module Main where

import Pattern
import Show
import Test.QuickCheck
import Control.Monad (liftM, liftM2, liftM3)
import Data.Maybe (isJust)

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

prop_subs p q =
  let e = match p q in
  case e of
    Nothing -> True
    Just e -> subs e q == p

prop_subs' p q = isJust (match p q) ==> prop_subs p q

prop_RevRev xs = xs == xs
  where types = xs::[Term]

main = do
--  quickCheck prop_subs
  deepCheck prop_subs
--  sample (arbitrary :: Gen Pattern)
