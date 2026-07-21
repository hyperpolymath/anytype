||| anytype L1: conversion is normalise-and-compare — one primitive
||| relation (equality of normal forms), no coercion machinery. Grades
||| on arrows are compared with the algebra's decidable equality; there
||| is no grade subtyping in conversion.
module Anytype.Core.Conversion

import Anytype.Grade.Algebra
import Anytype.Core.Syntax
import Anytype.Core.Normalise

%default total

||| Structural equality of canonical type-level naturals.
tnatEq : TNat -> TNat -> Bool
tnatEq NZ NZ = True
tnatEq (NS a) (NS b) = tnatEq a b
tnatEq _ _ = False

||| Structural equality of normalised types.
structEq : GradeAlgebra g -> Ty g -> Ty g -> Bool
structEq _ TUnit TUnit = True
structEq _ TBool TBool = True
structEq _ (TBits v) (TBits w) = tnatEq v w
structEq alg (TArr q a b) (TArr q' a' b') =
  case alg.gdec q q' of
    Yes _ => structEq alg a a' && structEq alg b b'
    No _  => False
structEq alg (TProd a b) (TProd a' b') =
  structEq alg a a' && structEq alg b b'
structEq _ _ _ = False

||| Are two types equal up to type-level computation?
public export
convertible : GradeAlgebra g -> Ty g -> Ty g -> Bool
convertible alg s t = structEq alg (normalise s) (normalise t)
