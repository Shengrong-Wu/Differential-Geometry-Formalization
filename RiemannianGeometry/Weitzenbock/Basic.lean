import Mathlib.Algebra.Group.Basic

namespace Weitzenbock

universe u

/--
Minimal algebraic package for the one-form Weitzenbock identity
`Δ_H α = ∇*∇ α + ℛ α`.

The data records the two first-order pieces `dδ`, `δd`, the rough Laplacian,
and the zeroth-order curvature term, together with the standard decomposition
of `δd`.
-/
structure OneFormHodgeAlgebra where
  Ω1 : Type u
  [instAddCommGroupΩ1 : AddCommGroup Ω1]
  dDelta : Ω1 → Ω1
  deltaD : Ω1 → Ω1
  rough : Ω1 → Ω1
  curvatureTerm : Ω1 → Ω1
  deltaD_eq_rough_plus_curvature_minus_dDelta :
    ∀ α, deltaD α = rough α + curvatureTerm α - dDelta α

attribute [instance] OneFormHodgeAlgebra.instAddCommGroupΩ1

def hodgeLaplacian (A : OneFormHodgeAlgebra) (α : A.Ω1) : A.Ω1 :=
  A.dDelta α + A.deltaD α

end Weitzenbock
