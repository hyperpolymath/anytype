||| anytype L2: the grade-algebra interface.
|||
||| systemet's resource layer (L2) requires an ordered semiring: the
||| discipline of a language is chosen by choosing this algebra. The laws
||| are proof fields, so a `GradeAlgebra` value cannot be constructed
||| without discharging every one of them — an unlawful algebra is
||| unrepresentable, which is how "pins systemet upstream" is enforced
||| mechanically rather than by policy.
|||
||| The carrier is a record *parameter* (not an erased field): erased
||| carrier fields projected into value positions are the documented
||| failure mode of the quarantined template proofs.
module Anytype.Grade.Algebra

import Data.So

%default total

public export
record GradeAlgebra (g : Type) where
  constructor MkGradeAlgebra
  ||| Additive identity: the grade of an unused variable.
  gzero : g
  ||| Multiplicative identity: the grade of a single use.
  gone  : g
  ||| Combine usages from independent subterms.
  gadd  : g -> g -> g
  ||| Scale a usage through an application at a graded arrow.
  gmul  : g -> g -> g
  ||| Decidable order: `gleq computed declared` admits a binder.
  gleq  : g -> g -> Bool
  ||| Decidable equality, used by conversion on arrow grades.
  gdec  : (a, b : g) -> Dec (a = b)

  -- Semiring laws (systemet L2: the stated algebra laws).
  addAssoc : (a, b, c : g) -> gadd a (gadd b c) = gadd (gadd a b) c
  addComm  : (a, b : g)    -> gadd a b = gadd b a
  addZeroL : (a : g)       -> gadd gzero a = a
  mulAssoc : (a, b, c : g) -> gmul a (gmul b c) = gmul (gmul a b) c
  mulOneL  : (a : g)       -> gmul gone a = a
  mulOneR  : (a : g)       -> gmul a gone = a
  mulZeroL : (a : g)       -> gmul gzero a = gzero
  mulZeroR : (a : g)       -> gmul a gzero = gzero
  distribL : (a, b, c : g) -> gmul a (gadd b c) = gadd (gmul a b) (gmul a c)
  distribR : (a, b, c : g) -> gmul (gadd a b) c = gadd (gmul a c) (gmul b c)

  -- Order laws, and compatibility of the order with the semiring ops.
  leqRefl    : (a : g) -> So (gleq a a)
  leqTrans   : (a, b, c : g) -> So (gleq a b) -> So (gleq b c) -> So (gleq a c)
  leqAntisym : (a, b : g) -> So (gleq a b) -> So (gleq b a) -> a = b
  addMono    : (a, b, c, d : g) ->
               So (gleq a b) -> So (gleq c d) -> So (gleq (gadd a c) (gadd b d))
  mulMono    : (a, b, c, d : g) ->
               So (gleq a b) -> So (gleq c d) -> So (gleq (gmul a c) (gmul b d))
