import Mathlib.Data.Real.Basic
import Weitzenbock.ComponentBridge
import Bochner.CoordinateBochner

namespace Weitzenbock.Coordinate

open Bochner.Coordinate

variable (n : ℕ)

abbrev OneForm := Covector n

structure HodgeData (n : ℕ) where
  dDelta : OneForm n → OneForm n
  deltaD : OneForm n → OneForm n
  rough : OneForm n → OneForm n
  curvatureTerm : OneForm n → OneForm n
  deltaD_eq_rough_plus_curvature_minus_dDelta :
    ∀ α, deltaD α = rough α + curvatureTerm α - dDelta α

def coordHodgeAlgebra (D : HodgeData n) : OneFormHodgeAlgebra where
  Ω1 := OneForm n
  dDelta := D.dDelta
  deltaD := D.deltaD
  rough := D.rough
  curvatureTerm := D.curvatureTerm
  deltaD_eq_rough_plus_curvature_minus_dDelta := D.deltaD_eq_rough_plus_curvature_minus_dDelta

def coordProjection (D : HodgeData n) :
    ComponentProjection (coordHodgeAlgebra n D) (Fin n) ℝ where
  proj := fun ω j => ω j

theorem classical_weitzenbock
    (D : HodgeData n) :
    ∀ α j, hodgeLaplacian (coordHodgeAlgebra n D) α j = D.rough α j + D.curvatureTerm α j := by
  intro α j
  simpa [coordProjection, Pi.add_apply] using
    weitzenbock_in_components (coordHodgeAlgebra n D) α (coordProjection n D) j

end Weitzenbock.Coordinate
