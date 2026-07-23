||| The exact-usage grade algebra over Nat: `gleq` is *equality*, so a
||| binder's computed usage must equal its declared grade — dropping a
||| grade-1 value is rejected, unlike the affine order where 0 <= 1.
|||
||| This instance is systemet's required demonstration that the same
||| checking rules instantiate distinct disciplines: the checker code
||| never changes, only the algebra passed to it.
module Anytype.Grade.Exact

import Data.Nat
import Data.So
import Decidable.Equality
import Anytype.Grade.Algebra

%default total

natEqRefl : (n : Nat) -> (n == n) = True
natEqRefl Z = Refl
natEqRefl (S k) = natEqRefl k

natEqSound : (a, b : Nat) -> (a == b) = True -> a = b
natEqSound Z Z _ = Refl
natEqSound Z (S _) prf = absurd prf
natEqSound (S _) Z prf = absurd prf
natEqSound (S a) (S b) prf = cong S (natEqSound a b prf)

soSound : (a, b : Nat) -> So (a == b) -> a = b
soSound a b s = natEqSound a b (soToEq s)

eqRefl : (a : Nat) -> So (a == a)
eqRefl a = rewrite natEqRefl a in Oh

eqTrans : (a, b, c : Nat) -> So (a == b) -> So (b == c) -> So (a == c)
eqTrans a b c s1 s2 =
  rewrite soSound a b s1 in rewrite soSound b c s2 in eqRefl c

addMono' : (a, b, c, d : Nat) ->
           So (a == b) -> So (c == d) -> So ((a + c) == (b + d))
addMono' a b c d s1 s2 =
  rewrite soSound a b s1 in rewrite soSound c d s2 in eqRefl (b + d)

mulMono' : (a, b, c, d : Nat) ->
           So (a == b) -> So (c == d) -> So ((a * c) == (b * d))
mulMono' a b c d s1 s2 =
  rewrite soSound a b s1 in rewrite soSound c d s2 in eqRefl (b * d)

||| Exact usage: semiring laws come from Data.Nat; the order is equality.
public export
ExactAlgebra : GradeAlgebra Nat
ExactAlgebra = MkGradeAlgebra
  0 1 (+) (*) (==) decEq
  (\a, b, c => plusAssociative a b c)
  plusCommutative
  plusZeroLeftNeutral
  (\a, b, c => multAssociative a b c)
  multOneLeftNeutral
  multOneRightNeutral
  multZeroLeftZero
  multZeroRightZero
  (\a, b, c => multDistributesOverPlusRight a b c)
  (\a, b, c => multDistributesOverPlusLeft a b c)
  eqRefl
  eqTrans
  (\a, b, s1, _ => soSound a b s1)
  addMono'
  mulMono'
