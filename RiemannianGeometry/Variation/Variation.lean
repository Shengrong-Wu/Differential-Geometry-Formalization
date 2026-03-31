import Mathlib.Tactic.Abel
import Variation.Basic

namespace Variation

theorem curvature_variation_identity
    (A : LocalConnectionVariationAlgebra) (conn : ConnectionForm A) :
    A.deriv2 (curvature A conn) = covariantVariation A conn (connectionVariation A conn) := by
  simp only [curvature, covariantVariation, connectionVariation]
  rw [A.deriv2_add, A.deriv2_d1, A.deriv2_wedge11]
  abel

end Variation
