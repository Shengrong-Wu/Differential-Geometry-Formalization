import Mathlib.Tactic.Abel
import Bochner.Basic

namespace Bochner

theorem covariant_square_eq_curvature_action
    (A : BundleConnectionAlgebra) (conn : ConnectionForm A) (s : A.ΩE0) :
    covariantDeriv1 A conn (covariantDeriv0 A conn s) = curvatureAction A conn s := by
  simp only [covariantDeriv1, covariantDeriv0, curvatureAction, curvature]
  rw [A.dE1_add, A.dE1_dE0_eq_zero, A.dE1_act0]
  rw [A.act1_add_right, A.act_assoc, A.act2_add_left]
  abel

end Bochner
