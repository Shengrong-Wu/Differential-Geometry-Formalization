import Mathlib.Tactic.Abel
import Weitzenbock.Basic

namespace Weitzenbock

theorem weitzenbock_identity
    (A : OneFormHodgeAlgebra) (α : A.Ω1) :
    hodgeLaplacian A α = A.rough α + A.curvatureTerm α := by
  rw [hodgeLaplacian, A.deltaD_eq_rough_plus_curvature_minus_dDelta]
  abel

end Weitzenbock
