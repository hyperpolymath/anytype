||| The affine+erasure grade algebra {0, 1, omega} — AffineScript's
||| discipline, mirrored cell-for-cell from affinescript/lib/quantity.ml
||| (q_add / q_mul / q_le): addition saturates (1+1 = omega), omega
||| absorbs, multiplication scales usage through application (the
||| omega*1 = omega rule, AffineScript's BUG-001 fix). `QVar` from the
||| AffineScript elaborator is unification machinery, not part of the
||| algebra, and is deliberately absent here.
|||
||| Law proofs are exhaustive constructor enumerations; the coverage
||| checker forces completeness and `%default total` forbids escape
||| hatches.
module Anytype.Grade.Affine

import Data.So
import Anytype.Grade.Algebra

%default total

public export
data Q = Q0 | Q1 | QW

public export
Show Q where
  show Q0 = "0"
  show Q1 = "1"
  show QW = "w"

||| quantity.ml q_add: 0 identity; 1+1 saturates to omega; omega absorbs.
public export
qadd : Q -> Q -> Q
qadd Q0 Q0 = Q0
qadd Q0 Q1 = Q1
qadd Q0 QW = QW
qadd Q1 Q0 = Q1
qadd Q1 Q1 = QW
qadd Q1 QW = QW
qadd QW Q0 = QW
qadd QW Q1 = QW
qadd QW QW = QW

||| quantity.ml q_mul: 0 annihilates; 1 identity; omega*omega = omega.
public export
qmul : Q -> Q -> Q
qmul Q0 Q0 = Q0
qmul Q0 Q1 = Q0
qmul Q0 QW = Q0
qmul Q1 Q0 = Q0
qmul Q1 Q1 = Q1
qmul Q1 QW = QW
qmul QW Q0 = Q0
qmul QW Q1 = QW
qmul QW QW = QW

||| quantity.ml q_le: the total order 0 <= 1 <= omega.
public export
qleq : Q -> Q -> Bool
qleq Q0 Q0 = True
qleq Q0 Q1 = True
qleq Q0 QW = True
qleq Q1 Q0 = False
qleq Q1 Q1 = True
qleq Q1 QW = True
qleq QW Q0 = False
qleq QW Q1 = False
qleq QW QW = True

q0NotQ1 : Q0 = Q1 -> Void
q0NotQ1 Refl impossible

q0NotQW : Q0 = QW -> Void
q0NotQW Refl impossible

q1NotQW : Q1 = QW -> Void
q1NotQW Refl impossible

public export
qdec : (a, b : Q) -> Dec (a = b)
qdec Q0 Q0 = Yes Refl
qdec Q0 Q1 = No q0NotQ1
qdec Q0 QW = No q0NotQW
qdec Q1 Q0 = No (\p => q0NotQ1 (sym p))
qdec Q1 Q1 = Yes Refl
qdec Q1 QW = No q1NotQW
qdec QW Q0 = No (\p => q0NotQW (sym p))
qdec QW Q1 = No (\p => q1NotQW (sym p))
qdec QW QW = Yes Refl

-- Exhaustive law proofs (generated; verified by the typechecker).

qaddAssoc : (a, b, c : Q) -> qadd a (qadd b c) = qadd (qadd a b) c
qmulAssoc : (a, b, c : Q) -> qmul a (qmul b c) = qmul (qmul a b) c
qdistribL : (a, b, c : Q) -> qmul a (qadd b c) = qadd (qmul a b) (qmul a c)
qdistribR : (a, b, c : Q) -> qmul (qadd a b) c = qadd (qmul a c) (qmul b c)
qaddComm : (a, b : Q) -> qadd a b = qadd b a
qaddZeroL : (a : Q) -> qadd Q0 a = a
qmulOneL : (a : Q) -> qmul Q1 a = a
qmulOneR : (a : Q) -> qmul a Q1 = a
qmulZeroL : (a : Q) -> qmul Q0 a = Q0
qmulZeroR : (a : Q) -> qmul a Q0 = Q0
qleqRefl : (a : Q) -> So (qleq a a)
qleqTrans : (a, b, c : Q) -> So (qleq a b) -> So (qleq b c) -> So (qleq a c)
qleqAntisym : (a, b : Q) -> So (qleq a b) -> So (qleq b a) -> a = b
qaddMono : (a, b, c, d : Q) ->
           So (qleq a b) -> So (qleq c d) -> So (qleq (qadd a c) (qadd b d))
qmulMono : (a, b, c, d : Q) ->
           So (qleq a b) -> So (qleq c d) -> So (qleq (qmul a c) (qmul b d))

qaddAssoc Q0 Q0 Q0 = Refl
qaddAssoc Q0 Q0 Q1 = Refl
qaddAssoc Q0 Q0 QW = Refl
qaddAssoc Q0 Q1 Q0 = Refl
qaddAssoc Q0 Q1 Q1 = Refl
qaddAssoc Q0 Q1 QW = Refl
qaddAssoc Q0 QW Q0 = Refl
qaddAssoc Q0 QW Q1 = Refl
qaddAssoc Q0 QW QW = Refl
qaddAssoc Q1 Q0 Q0 = Refl
qaddAssoc Q1 Q0 Q1 = Refl
qaddAssoc Q1 Q0 QW = Refl
qaddAssoc Q1 Q1 Q0 = Refl
qaddAssoc Q1 Q1 Q1 = Refl
qaddAssoc Q1 Q1 QW = Refl
qaddAssoc Q1 QW Q0 = Refl
qaddAssoc Q1 QW Q1 = Refl
qaddAssoc Q1 QW QW = Refl
qaddAssoc QW Q0 Q0 = Refl
qaddAssoc QW Q0 Q1 = Refl
qaddAssoc QW Q0 QW = Refl
qaddAssoc QW Q1 Q0 = Refl
qaddAssoc QW Q1 Q1 = Refl
qaddAssoc QW Q1 QW = Refl
qaddAssoc QW QW Q0 = Refl
qaddAssoc QW QW Q1 = Refl
qaddAssoc QW QW QW = Refl

qmulAssoc Q0 Q0 Q0 = Refl
qmulAssoc Q0 Q0 Q1 = Refl
qmulAssoc Q0 Q0 QW = Refl
qmulAssoc Q0 Q1 Q0 = Refl
qmulAssoc Q0 Q1 Q1 = Refl
qmulAssoc Q0 Q1 QW = Refl
qmulAssoc Q0 QW Q0 = Refl
qmulAssoc Q0 QW Q1 = Refl
qmulAssoc Q0 QW QW = Refl
qmulAssoc Q1 Q0 Q0 = Refl
qmulAssoc Q1 Q0 Q1 = Refl
qmulAssoc Q1 Q0 QW = Refl
qmulAssoc Q1 Q1 Q0 = Refl
qmulAssoc Q1 Q1 Q1 = Refl
qmulAssoc Q1 Q1 QW = Refl
qmulAssoc Q1 QW Q0 = Refl
qmulAssoc Q1 QW Q1 = Refl
qmulAssoc Q1 QW QW = Refl
qmulAssoc QW Q0 Q0 = Refl
qmulAssoc QW Q0 Q1 = Refl
qmulAssoc QW Q0 QW = Refl
qmulAssoc QW Q1 Q0 = Refl
qmulAssoc QW Q1 Q1 = Refl
qmulAssoc QW Q1 QW = Refl
qmulAssoc QW QW Q0 = Refl
qmulAssoc QW QW Q1 = Refl
qmulAssoc QW QW QW = Refl

qdistribL Q0 Q0 Q0 = Refl
qdistribL Q0 Q0 Q1 = Refl
qdistribL Q0 Q0 QW = Refl
qdistribL Q0 Q1 Q0 = Refl
qdistribL Q0 Q1 Q1 = Refl
qdistribL Q0 Q1 QW = Refl
qdistribL Q0 QW Q0 = Refl
qdistribL Q0 QW Q1 = Refl
qdistribL Q0 QW QW = Refl
qdistribL Q1 Q0 Q0 = Refl
qdistribL Q1 Q0 Q1 = Refl
qdistribL Q1 Q0 QW = Refl
qdistribL Q1 Q1 Q0 = Refl
qdistribL Q1 Q1 Q1 = Refl
qdistribL Q1 Q1 QW = Refl
qdistribL Q1 QW Q0 = Refl
qdistribL Q1 QW Q1 = Refl
qdistribL Q1 QW QW = Refl
qdistribL QW Q0 Q0 = Refl
qdistribL QW Q0 Q1 = Refl
qdistribL QW Q0 QW = Refl
qdistribL QW Q1 Q0 = Refl
qdistribL QW Q1 Q1 = Refl
qdistribL QW Q1 QW = Refl
qdistribL QW QW Q0 = Refl
qdistribL QW QW Q1 = Refl
qdistribL QW QW QW = Refl

qdistribR Q0 Q0 Q0 = Refl
qdistribR Q0 Q0 Q1 = Refl
qdistribR Q0 Q0 QW = Refl
qdistribR Q0 Q1 Q0 = Refl
qdistribR Q0 Q1 Q1 = Refl
qdistribR Q0 Q1 QW = Refl
qdistribR Q0 QW Q0 = Refl
qdistribR Q0 QW Q1 = Refl
qdistribR Q0 QW QW = Refl
qdistribR Q1 Q0 Q0 = Refl
qdistribR Q1 Q0 Q1 = Refl
qdistribR Q1 Q0 QW = Refl
qdistribR Q1 Q1 Q0 = Refl
qdistribR Q1 Q1 Q1 = Refl
qdistribR Q1 Q1 QW = Refl
qdistribR Q1 QW Q0 = Refl
qdistribR Q1 QW Q1 = Refl
qdistribR Q1 QW QW = Refl
qdistribR QW Q0 Q0 = Refl
qdistribR QW Q0 Q1 = Refl
qdistribR QW Q0 QW = Refl
qdistribR QW Q1 Q0 = Refl
qdistribR QW Q1 Q1 = Refl
qdistribR QW Q1 QW = Refl
qdistribR QW QW Q0 = Refl
qdistribR QW QW Q1 = Refl
qdistribR QW QW QW = Refl

qaddComm Q0 Q0 = Refl
qaddComm Q0 Q1 = Refl
qaddComm Q0 QW = Refl
qaddComm Q1 Q0 = Refl
qaddComm Q1 Q1 = Refl
qaddComm Q1 QW = Refl
qaddComm QW Q0 = Refl
qaddComm QW Q1 = Refl
qaddComm QW QW = Refl

qaddZeroL Q0 = Refl
qaddZeroL Q1 = Refl
qaddZeroL QW = Refl

qmulOneL Q0 = Refl
qmulOneL Q1 = Refl
qmulOneL QW = Refl

qmulOneR Q0 = Refl
qmulOneR Q1 = Refl
qmulOneR QW = Refl

qmulZeroL Q0 = Refl
qmulZeroL Q1 = Refl
qmulZeroL QW = Refl

qmulZeroR Q0 = Refl
qmulZeroR Q1 = Refl
qmulZeroR QW = Refl

qleqRefl Q0 = Oh
qleqRefl Q1 = Oh
qleqRefl QW = Oh

qleqTrans Q0 Q0 Q0 _ _ = Oh
qleqTrans Q0 Q0 Q1 _ _ = Oh
qleqTrans Q0 Q0 QW _ _ = Oh
qleqTrans Q0 Q1 Q0 _ y = absurd y
qleqTrans Q0 Q1 Q1 _ _ = Oh
qleqTrans Q0 Q1 QW _ _ = Oh
qleqTrans Q0 QW Q0 _ y = absurd y
qleqTrans Q0 QW Q1 _ y = absurd y
qleqTrans Q0 QW QW _ _ = Oh
qleqTrans Q1 Q0 Q0 x _ = absurd x
qleqTrans Q1 Q0 Q1 x _ = absurd x
qleqTrans Q1 Q0 QW x _ = absurd x
qleqTrans Q1 Q1 Q0 _ y = absurd y
qleqTrans Q1 Q1 Q1 _ _ = Oh
qleqTrans Q1 Q1 QW _ _ = Oh
qleqTrans Q1 QW Q0 _ y = absurd y
qleqTrans Q1 QW Q1 _ y = absurd y
qleqTrans Q1 QW QW _ _ = Oh
qleqTrans QW Q0 Q0 x _ = absurd x
qleqTrans QW Q0 Q1 x _ = absurd x
qleqTrans QW Q0 QW x _ = absurd x
qleqTrans QW Q1 Q0 x _ = absurd x
qleqTrans QW Q1 Q1 x _ = absurd x
qleqTrans QW Q1 QW x _ = absurd x
qleqTrans QW QW Q0 _ y = absurd y
qleqTrans QW QW Q1 _ y = absurd y
qleqTrans QW QW QW _ _ = Oh

qleqAntisym Q0 Q0 _ _ = Refl
qleqAntisym Q0 Q1 _ y = absurd y
qleqAntisym Q0 QW _ y = absurd y
qleqAntisym Q1 Q0 x _ = absurd x
qleqAntisym Q1 Q1 _ _ = Refl
qleqAntisym Q1 QW _ y = absurd y
qleqAntisym QW Q0 x _ = absurd x
qleqAntisym QW Q1 x _ = absurd x
qleqAntisym QW QW _ _ = Refl

qaddMono Q0 Q0 Q0 Q0 _ _ = Oh
qaddMono Q0 Q0 Q0 Q1 _ _ = Oh
qaddMono Q0 Q0 Q0 QW _ _ = Oh
qaddMono Q0 Q0 Q1 Q0 _ y = absurd y
qaddMono Q0 Q0 Q1 Q1 _ _ = Oh
qaddMono Q0 Q0 Q1 QW _ _ = Oh
qaddMono Q0 Q0 QW Q0 _ y = absurd y
qaddMono Q0 Q0 QW Q1 _ y = absurd y
qaddMono Q0 Q0 QW QW _ _ = Oh
qaddMono Q0 Q1 Q0 Q0 _ _ = Oh
qaddMono Q0 Q1 Q0 Q1 _ _ = Oh
qaddMono Q0 Q1 Q0 QW _ _ = Oh
qaddMono Q0 Q1 Q1 Q0 _ y = absurd y
qaddMono Q0 Q1 Q1 Q1 _ _ = Oh
qaddMono Q0 Q1 Q1 QW _ _ = Oh
qaddMono Q0 Q1 QW Q0 _ y = absurd y
qaddMono Q0 Q1 QW Q1 _ y = absurd y
qaddMono Q0 Q1 QW QW _ _ = Oh
qaddMono Q0 QW Q0 Q0 _ _ = Oh
qaddMono Q0 QW Q0 Q1 _ _ = Oh
qaddMono Q0 QW Q0 QW _ _ = Oh
qaddMono Q0 QW Q1 Q0 _ y = absurd y
qaddMono Q0 QW Q1 Q1 _ _ = Oh
qaddMono Q0 QW Q1 QW _ _ = Oh
qaddMono Q0 QW QW Q0 _ y = absurd y
qaddMono Q0 QW QW Q1 _ y = absurd y
qaddMono Q0 QW QW QW _ _ = Oh
qaddMono Q1 Q0 Q0 Q0 x _ = absurd x
qaddMono Q1 Q0 Q0 Q1 x _ = absurd x
qaddMono Q1 Q0 Q0 QW x _ = absurd x
qaddMono Q1 Q0 Q1 Q0 x _ = absurd x
qaddMono Q1 Q0 Q1 Q1 x _ = absurd x
qaddMono Q1 Q0 Q1 QW x _ = absurd x
qaddMono Q1 Q0 QW Q0 x _ = absurd x
qaddMono Q1 Q0 QW Q1 x _ = absurd x
qaddMono Q1 Q0 QW QW x _ = absurd x
qaddMono Q1 Q1 Q0 Q0 _ _ = Oh
qaddMono Q1 Q1 Q0 Q1 _ _ = Oh
qaddMono Q1 Q1 Q0 QW _ _ = Oh
qaddMono Q1 Q1 Q1 Q0 _ y = absurd y
qaddMono Q1 Q1 Q1 Q1 _ _ = Oh
qaddMono Q1 Q1 Q1 QW _ _ = Oh
qaddMono Q1 Q1 QW Q0 _ y = absurd y
qaddMono Q1 Q1 QW Q1 _ y = absurd y
qaddMono Q1 Q1 QW QW _ _ = Oh
qaddMono Q1 QW Q0 Q0 _ _ = Oh
qaddMono Q1 QW Q0 Q1 _ _ = Oh
qaddMono Q1 QW Q0 QW _ _ = Oh
qaddMono Q1 QW Q1 Q0 _ y = absurd y
qaddMono Q1 QW Q1 Q1 _ _ = Oh
qaddMono Q1 QW Q1 QW _ _ = Oh
qaddMono Q1 QW QW Q0 _ y = absurd y
qaddMono Q1 QW QW Q1 _ y = absurd y
qaddMono Q1 QW QW QW _ _ = Oh
qaddMono QW Q0 Q0 Q0 x _ = absurd x
qaddMono QW Q0 Q0 Q1 x _ = absurd x
qaddMono QW Q0 Q0 QW x _ = absurd x
qaddMono QW Q0 Q1 Q0 x _ = absurd x
qaddMono QW Q0 Q1 Q1 x _ = absurd x
qaddMono QW Q0 Q1 QW x _ = absurd x
qaddMono QW Q0 QW Q0 x _ = absurd x
qaddMono QW Q0 QW Q1 x _ = absurd x
qaddMono QW Q0 QW QW x _ = absurd x
qaddMono QW Q1 Q0 Q0 x _ = absurd x
qaddMono QW Q1 Q0 Q1 x _ = absurd x
qaddMono QW Q1 Q0 QW x _ = absurd x
qaddMono QW Q1 Q1 Q0 x _ = absurd x
qaddMono QW Q1 Q1 Q1 x _ = absurd x
qaddMono QW Q1 Q1 QW x _ = absurd x
qaddMono QW Q1 QW Q0 x _ = absurd x
qaddMono QW Q1 QW Q1 x _ = absurd x
qaddMono QW Q1 QW QW x _ = absurd x
qaddMono QW QW Q0 Q0 _ _ = Oh
qaddMono QW QW Q0 Q1 _ _ = Oh
qaddMono QW QW Q0 QW _ _ = Oh
qaddMono QW QW Q1 Q0 _ y = absurd y
qaddMono QW QW Q1 Q1 _ _ = Oh
qaddMono QW QW Q1 QW _ _ = Oh
qaddMono QW QW QW Q0 _ y = absurd y
qaddMono QW QW QW Q1 _ y = absurd y
qaddMono QW QW QW QW _ _ = Oh

qmulMono Q0 Q0 Q0 Q0 _ _ = Oh
qmulMono Q0 Q0 Q0 Q1 _ _ = Oh
qmulMono Q0 Q0 Q0 QW _ _ = Oh
qmulMono Q0 Q0 Q1 Q0 _ y = absurd y
qmulMono Q0 Q0 Q1 Q1 _ _ = Oh
qmulMono Q0 Q0 Q1 QW _ _ = Oh
qmulMono Q0 Q0 QW Q0 _ y = absurd y
qmulMono Q0 Q0 QW Q1 _ y = absurd y
qmulMono Q0 Q0 QW QW _ _ = Oh
qmulMono Q0 Q1 Q0 Q0 _ _ = Oh
qmulMono Q0 Q1 Q0 Q1 _ _ = Oh
qmulMono Q0 Q1 Q0 QW _ _ = Oh
qmulMono Q0 Q1 Q1 Q0 _ y = absurd y
qmulMono Q0 Q1 Q1 Q1 _ _ = Oh
qmulMono Q0 Q1 Q1 QW _ _ = Oh
qmulMono Q0 Q1 QW Q0 _ y = absurd y
qmulMono Q0 Q1 QW Q1 _ y = absurd y
qmulMono Q0 Q1 QW QW _ _ = Oh
qmulMono Q0 QW Q0 Q0 _ _ = Oh
qmulMono Q0 QW Q0 Q1 _ _ = Oh
qmulMono Q0 QW Q0 QW _ _ = Oh
qmulMono Q0 QW Q1 Q0 _ y = absurd y
qmulMono Q0 QW Q1 Q1 _ _ = Oh
qmulMono Q0 QW Q1 QW _ _ = Oh
qmulMono Q0 QW QW Q0 _ y = absurd y
qmulMono Q0 QW QW Q1 _ y = absurd y
qmulMono Q0 QW QW QW _ _ = Oh
qmulMono Q1 Q0 Q0 Q0 x _ = absurd x
qmulMono Q1 Q0 Q0 Q1 x _ = absurd x
qmulMono Q1 Q0 Q0 QW x _ = absurd x
qmulMono Q1 Q0 Q1 Q0 x _ = absurd x
qmulMono Q1 Q0 Q1 Q1 x _ = absurd x
qmulMono Q1 Q0 Q1 QW x _ = absurd x
qmulMono Q1 Q0 QW Q0 x _ = absurd x
qmulMono Q1 Q0 QW Q1 x _ = absurd x
qmulMono Q1 Q0 QW QW x _ = absurd x
qmulMono Q1 Q1 Q0 Q0 _ _ = Oh
qmulMono Q1 Q1 Q0 Q1 _ _ = Oh
qmulMono Q1 Q1 Q0 QW _ _ = Oh
qmulMono Q1 Q1 Q1 Q0 _ y = absurd y
qmulMono Q1 Q1 Q1 Q1 _ _ = Oh
qmulMono Q1 Q1 Q1 QW _ _ = Oh
qmulMono Q1 Q1 QW Q0 _ y = absurd y
qmulMono Q1 Q1 QW Q1 _ y = absurd y
qmulMono Q1 Q1 QW QW _ _ = Oh
qmulMono Q1 QW Q0 Q0 _ _ = Oh
qmulMono Q1 QW Q0 Q1 _ _ = Oh
qmulMono Q1 QW Q0 QW _ _ = Oh
qmulMono Q1 QW Q1 Q0 _ y = absurd y
qmulMono Q1 QW Q1 Q1 _ _ = Oh
qmulMono Q1 QW Q1 QW _ _ = Oh
qmulMono Q1 QW QW Q0 _ y = absurd y
qmulMono Q1 QW QW Q1 _ y = absurd y
qmulMono Q1 QW QW QW _ _ = Oh
qmulMono QW Q0 Q0 Q0 x _ = absurd x
qmulMono QW Q0 Q0 Q1 x _ = absurd x
qmulMono QW Q0 Q0 QW x _ = absurd x
qmulMono QW Q0 Q1 Q0 x _ = absurd x
qmulMono QW Q0 Q1 Q1 x _ = absurd x
qmulMono QW Q0 Q1 QW x _ = absurd x
qmulMono QW Q0 QW Q0 x _ = absurd x
qmulMono QW Q0 QW Q1 x _ = absurd x
qmulMono QW Q0 QW QW x _ = absurd x
qmulMono QW Q1 Q0 Q0 x _ = absurd x
qmulMono QW Q1 Q0 Q1 x _ = absurd x
qmulMono QW Q1 Q0 QW x _ = absurd x
qmulMono QW Q1 Q1 Q0 x _ = absurd x
qmulMono QW Q1 Q1 Q1 x _ = absurd x
qmulMono QW Q1 Q1 QW x _ = absurd x
qmulMono QW Q1 QW Q0 x _ = absurd x
qmulMono QW Q1 QW Q1 x _ = absurd x
qmulMono QW Q1 QW QW x _ = absurd x
qmulMono QW QW Q0 Q0 _ _ = Oh
qmulMono QW QW Q0 Q1 _ _ = Oh
qmulMono QW QW Q0 QW _ _ = Oh
qmulMono QW QW Q1 Q0 _ y = absurd y
qmulMono QW QW Q1 Q1 _ _ = Oh
qmulMono QW QW Q1 QW _ _ = Oh
qmulMono QW QW QW Q0 _ y = absurd y
qmulMono QW QW QW Q1 _ y = absurd y
qmulMono QW QW QW QW _ _ = Oh

||| AffineScript's discipline as a lawful algebra: an instance of this
||| record exists, therefore every law above is discharged.
public export
AffineAlgebra : GradeAlgebra Q
AffineAlgebra = MkGradeAlgebra
  Q0 Q1 qadd qmul qleq qdec
  qaddAssoc qaddComm qaddZeroL
  qmulAssoc qmulOneL qmulOneR qmulZeroL qmulZeroR
  qdistribL qdistribR
  qleqRefl qleqTrans qleqAntisym qaddMono qmulMono
