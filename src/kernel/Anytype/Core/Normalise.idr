||| anytype L1: normalisation of type-level computation.
|||
||| `TNat` has no recursion constructor, so evaluation is structural and
||| this whole module is `%default total` with no escape hatches — this
||| machine-checked totality IS the MVP totality gate: conversion below
||| is decidable because everything here terminates by construction.
module Anytype.Core.Normalise

import Anytype.Core.Syntax

%default total

||| Evaluate a type-level natural.
public export
nval : TNat -> Nat
nval NZ = 0
nval (NS t) = S (nval t)
nval (NPlus a b) = nval a + nval b
nval (NMul a b) = nval a * nval b

||| Canonical (NZ/NS-only) form of a Nat.
public export
tnatOfNat : Nat -> TNat
tnatOfNat Z = NZ
tnatOfNat (S k) = NS (tnatOfNat k)

||| Canonical form of a type-level natural: normalise-and-compare's
||| "normalise" half at the index level.
public export
nnorm : TNat -> TNat
nnorm = tnatOfNat . nval

||| Normalise a type: canonicalise every `TBits` index, recurse
||| structurally everywhere else.
public export
normalise : Ty g -> Ty g
normalise TUnit = TUnit
normalise TBool = TBool
normalise (TBits w) = TBits (nnorm w)
normalise (TArr q a b) = TArr q (normalise a) (normalise b)
normalise (TProd a b) = TProd (normalise a) (normalise b)
