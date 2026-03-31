import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Variation.CurveVariation

namespace Variation.Curve

open scoped BigOperators

variable {n : ℕ}

/-- Squared speed of a coordinate velocity field. -/
def speedSq (T : ℝ → Vector n) (t : ℝ) : ℝ :=
  pairing n (T t) (T t)

@[simp] theorem speedSq_eq_pairing
    (T : ℝ → Vector n) (t : ℝ) :
    speedSq (n := n) T t = pairing n (T t) (T t) :=
  rfl

theorem speedSq_nonneg
    (T : ℝ → Vector n) (t : ℝ) :
    0 ≤ speedSq (n := n) T t :=
  pairing_self_nonneg (n := n) (T t)

/-- Energy of a coordinate curve from its velocity field. -/
noncomputable def curveEnergy (a b : ℝ) (T : ℝ → Vector n) : ℝ :=
  (1 / 2 : ℝ) * ∫ t in a..b, speedSq (n := n) T t

@[simp] theorem curveEnergy_zero
    (a b : ℝ) :
    curveEnergy (n := n) a b (fun _ => 0) = 0 := by
  simp [curveEnergy, speedSq]

/-- Energy of the `s`-slice of a variation. -/
noncomputable def variationEnergy (Gamma : CurveVariation n) (a b s : ℝ) : ℝ :=
  curveEnergy (n := n) a b (Gamma.tangentField s)

@[simp] theorem variationEnergy_eq_curveEnergy
    (Gamma : CurveVariation n) (a b s : ℝ) :
    variationEnergy (n := n) Gamma a b s =
      curveEnergy (n := n) a b (Gamma.tangentField s) :=
  rfl

end Variation.Curve
