import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Variation.CoordinateVariation

open BigOperators Finset

namespace Variation.Coordinate

variable {n : ℕ}

noncomputable section

abbrev InverseMetric (n : ℕ) := Fin n → Fin n → ℝ
abbrev MetricVariation (n : ℕ) := Fin n → Fin n → ℝ
abbrev CovariantMetricDerivative (n : ℕ) := Fin n → Fin n → Fin n → ℝ

/-- Coordinate form of the Levi-Civita connection variation formula. -/
def leviCivitaVariation
    (gInv : InverseMetric n) (nablaH : CovariantMetricDerivative n) : Form1 n :=
  fun k i j =>
    (1 / 2 : ℝ) * ∑ l : Fin n, gInv k l * (nablaH i j l + nablaH j i l - nablaH l i j)

theorem curvature_variation_of_leviCivita_bridge
    (D : CoordVariationData n) (A : Form1 n)
    (gInv : InverseMetric n) (nablaH : CovariantMetricDerivative n)
    (hdotA : D.deriv1 A = leviCivitaVariation gInv nablaH) :
    ∀ i j μ ν : Fin n,
      D.deriv2 (curvature (coordAlgebra n D) ⟨A⟩) i j μ ν =
        D.d1 (leviCivitaVariation gInv nablaH) i j μ ν
          + (∑ k : Fin n,
              (leviCivitaVariation gInv nablaH i k μ * A k j ν
                - leviCivitaVariation gInv nablaH i k ν * A k j μ))
          + ∑ k : Fin n,
              (A i k μ * leviCivitaVariation gInv nablaH k j ν
                - A i k ν * leviCivitaVariation gInv nablaH k j μ) := by
  intro i j μ ν
  simpa [connectionVariation, coordAlgebra, hdotA] using
    classical_curvature_variation (n := n) D A i j μ ν

end

end Variation.Coordinate
