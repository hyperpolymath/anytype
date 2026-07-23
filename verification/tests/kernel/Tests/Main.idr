||| Golden matrix for the anytype kernel: the same terms, checked under
||| the affine and the exact grade algebras, must produce the recorded
||| verdicts. The drop row (grade-1 binder, body TT) is the load-bearing
||| demonstration: affine ACCEPTS (0 <= 1), exact REJECTS (0 /= 1) —
||| same rules, distinct disciplines.
module Tests.Main

import Data.Fin
import System
import Anytype.Kernel

%default total

-- Data.Fin.Equality's Pointwise constructors shadow Fin's FZ/FS.
%hide Data.Fin.Equality.FZ
%hide Data.Fin.Equality.FS

two : TNat
two = NS (NS NZ)

three : TNat
three = NS two

four : TNat
four = NS three

five : TNat
five = NS four

accepts : Either CheckError a -> Bool
accepts (Right _) = True
accepts (Left _) = False

||| (name, expected-accept, actual-accept)
Case : Type
Case = (String, Bool, Bool)

dup : Term g (S n)
dup = Pair (Var FZ) (Var FZ)

affineCases : List Case
affineCases =
  [ ("affine: use once at 1",
     True,  accepts (checkClosed AffineAlgebra (Lam Q1 TBool (Var FZ))))
  , ("affine: drop at 1 (weakening allowed)",
     True,  accepts (checkClosed AffineAlgebra (Lam Q1 TBool TT)))
  , ("affine: double use at 1",
     False, accepts (checkClosed AffineAlgebra (Lam Q1 TBool dup)))
  , ("affine: double use at omega",
     True,  accepts (checkClosed AffineAlgebra (Lam QW TBool dup)))
  , ("affine: erased binder unused",
     True,  accepts (checkClosed AffineAlgebra (Lam Q0 TBool TT)))
  , ("affine: erased binder used",
     False, accepts (checkClosed AffineAlgebra (Lam Q0 TBool (Var FZ))))
  , ("affine: omega-arrow scales usage past 1 (BUG-001 rule)",
     False, accepts (checkClosed AffineAlgebra
              (Lam Q1 TBool (App (Lam QW TBool dup) (Var FZ)))))
  , ("affine: omega-arrow scaling admitted at omega",
     True,  accepts (checkClosed AffineAlgebra
              (Lam QW TBool (App (Lam QW TBool dup) (Var FZ)))))
  , ("affine: let-pair, each component once",
     True,  accepts (checkClosed AffineAlgebra
              (Lam Q1 (TProd TBool TUnit)
                 (LetPair (Var FZ) (Pair (Var (FS FZ)) (Var FZ))))))
  , ("affine: let-pair, first component twice",
     False, accepts (checkClosed AffineAlgebra
              (Lam Q1 (TProd TBool TUnit)
                 (LetPair (Var FZ) (Pair (Var (FS FZ)) (Var (FS FZ)))))))
  , ("affine: conversion Bits(2+3) against Bits 5",
     True,  accepts (checkAgainst AffineAlgebra (WordLit (NPlus two three))
                                  (TBits five)))
  , ("affine: conversion Bits(2+2) against Bits 5",
     False, accepts (checkAgainst AffineAlgebra (WordLit (NPlus two two))
                                  (TBits five)))
  , ("affine: application converts Bits(2+3) argument at Bits 5",
     True,  accepts (checkClosed AffineAlgebra
              (App (Lam Q1 (TBits five) (Var FZ)) (WordLit (NPlus two three)))))
  ]

exactCases : List Case
exactCases =
  [ ("exact: use once at 1",
     True,  accepts (checkClosed ExactAlgebra (Lam 1 TBool (Var FZ))))
  , ("exact: drop at 1 REJECTED (the discipline split)",
     False, accepts (checkClosed ExactAlgebra (Lam 1 TBool TT)))
  , ("exact: double use at 1",
     False, accepts (checkClosed ExactAlgebra (Lam 1 TBool dup)))
  , ("exact: double use at exactly 2",
     True,  accepts (checkClosed ExactAlgebra (Lam 2 TBool dup)))
  , ("exact: zero binder unused",
     True,  accepts (checkClosed ExactAlgebra (Lam 0 TBool TT)))
  , ("exact: zero binder used",
     False, accepts (checkClosed ExactAlgebra (Lam 0 TBool (Var FZ))))
  ]

report : Case -> IO Bool
report (name, expected, actual) =
  if expected == actual
    then putStrLn ("  PASS  " ++ name) $> True
    else putStrLn ("  FAIL  " ++ name
                   ++ " (expected accept=" ++ show expected
                   ++ ", got accept=" ++ show actual ++ ")") $> False

main : IO ()
main = do
  putStrLn "=== anytype kernel golden matrix ==="
  results <- traverse report (affineCases ++ exactCases)
  let bad = length (filter not results)
  putStrLn ("=== " ++ show (length results) ++ " cases, "
            ++ show bad ++ " failure(s) ===")
  when (bad > 0) exitFailure
