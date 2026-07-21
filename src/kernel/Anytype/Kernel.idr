||| anytype public API: pick the algebra, get the discipline.
|||
||| `checkClosed AffineAlgebra t` and `checkClosed ExactAlgebra t'`
||| run the identical rules under different grade algebras — the
||| discipline is an input, not something hardwired.
module Anytype.Kernel

import Data.Vect
import public Anytype.Grade.Algebra
import public Anytype.Grade.Affine
import public Anytype.Grade.Exact
import public Anytype.Core.Syntax
import public Anytype.Core.Normalise
import public Anytype.Core.Conversion
import public Anytype.Core.Check

%default total

||| Type a closed term under the chosen grade algebra.
public export
checkClosed : GradeAlgebra g -> Term g 0 -> Either CheckError (Ty g)
checkClosed alg t = map (normalise . fst) (infer alg (the (Ctx g 0) []) t)

||| Check a closed term against an expected type (conversion included).
public export
checkAgainst : GradeAlgebra g -> Term g 0 -> Ty g -> Either CheckError ()
checkAgainst alg t ty = map (const ()) (check alg (the (Ctx g 0) []) t ty)

||| Render a type, given a renderer for grades.
public export
showTy : (g -> String) -> Ty g -> String
showTy _ TUnit = "Unit"
showTy _ TBool = "Bool"
showTy _ (TBits w) = "Bits " ++ show (nval w)
showTy sg (TArr q a b) =
  "(" ++ showTy sg a ++ " " ++ sg q ++ "-> " ++ showTy sg b ++ ")"
showTy sg (TProd a b) = "(" ++ showTy sg a ++ " * " ++ showTy sg b ++ ")"
