import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Variation.LeviCivitaVariationBridge

open BigOperators Finset

namespace Variation.Coordinate

variable {n : ℕ}

abbrev Tensor2 (n : ℕ) := Fin n → Fin n → ℝ

def ricciVariationFromCurvature (dotR : Form2 n) : Tensor2 n :=
  fun j ν => ∑ i : Fin n, dotR i j i ν

def scalarVariationFromRicci (gInv : InverseMetric n) (dotRic : Tensor2 n) : ℝ :=
  ∑ j : Fin n, ∑ ν : Fin n, gInv j ν * dotRic j ν

def inverseMetricVariationTerm (h Ric : Tensor2 n) : ℝ :=
  -∑ j : Fin n, ∑ ν : Fin n, h j ν * Ric j ν

def scalarVariationFormulaValue
    (gInv h Ric : Tensor2 n) (dotRic : Tensor2 n) : ℝ :=
  inverseMetricVariationTerm h Ric + scalarVariationFromRicci gInv dotRic

theorem ricci_variation_formula
    (D : CoordVariationData n) (A : Form1 n) :
    let conn : ConnectionForm (coordAlgebra n D) := ⟨A⟩
    let dotA := connectionVariation (coordAlgebra n D) conn
    ∀ j ν : Fin n,
      ricciVariationFromCurvature (D.deriv2 (curvature (coordAlgebra n D) conn)) j ν =
        ∑ i : Fin n,
          (D.d1 dotA i j i ν
            + (∑ k : Fin n, (dotA i k i * A k j ν - dotA i k ν * A k j i))
            + ∑ k : Fin n, (A i k i * dotA k j ν - A i k ν * dotA k j i)) := by
  intro conn dotA j ν
  unfold ricciVariationFromCurvature
  apply Finset.sum_congr rfl
  intro i hi
  simpa using classical_curvature_variation (n := n) D A i j i ν

theorem scalar_variation_formula
    (D : CoordVariationData n) (A : Form1 n) (gInv h Ric : Tensor2 n) :
    let conn : ConnectionForm (coordAlgebra n D) := ⟨A⟩
    let dotA := connectionVariation (coordAlgebra n D) conn
    scalarVariationFormulaValue gInv h Ric
        (ricciVariationFromCurvature (D.deriv2 (curvature (coordAlgebra n D) conn))) =
      inverseMetricVariationTerm h Ric
        + ∑ j : Fin n, ∑ ν : Fin n,
            gInv j ν *
              (∑ i : Fin n,
                (D.d1 dotA i j i ν
                  + (∑ k : Fin n, (dotA i k i * A k j ν - dotA i k ν * A k j i))
                  + ∑ k : Fin n, (A i k i * dotA k j ν - A i k ν * dotA k j i))) := by
  intro conn dotA
  unfold scalarVariationFormulaValue scalarVariationFromRicci
  apply congrArg ((inverseMetricVariationTerm h Ric) + ·)
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ν hν
  rw [ricci_variation_formula (n := n) D A j ν]

theorem scalar_variation_formula_of_leviCivita_bridge
    (D : CoordVariationData n) (A : Form1 n)
    (gInv : InverseMetric n) (h Ric : Tensor2 n)
    (nablaH : CovariantMetricDerivative n)
    (hdotA : D.deriv1 A = leviCivitaVariation gInv nablaH) :
    scalarVariationFormulaValue gInv h Ric
        (ricciVariationFromCurvature (D.deriv2 (curvature (coordAlgebra n D) ⟨A⟩))) =
      inverseMetricVariationTerm h Ric
        + ∑ j : Fin n, ∑ ν : Fin n,
            gInv j ν *
              (∑ i : Fin n,
                (D.d1 (leviCivitaVariation gInv nablaH) i j i ν
                  + (∑ k : Fin n,
                      (leviCivitaVariation gInv nablaH i k i * A k j ν
                        - leviCivitaVariation gInv nablaH i k ν * A k j i))
                  + ∑ k : Fin n,
                      (A i k i * leviCivitaVariation gInv nablaH k j ν
                        - A i k ν * leviCivitaVariation gInv nablaH k j i))) := by
  simpa [connectionVariation, coordAlgebra, hdotA] using
    scalar_variation_formula (n := n) D A gInv h Ric

end Variation.Coordinate
