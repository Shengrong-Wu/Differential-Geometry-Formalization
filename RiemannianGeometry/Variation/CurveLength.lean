import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Variation.CurveVariation
import Variation.CurveEnergy

namespace Variation.Curve

open scoped BigOperators

variable {n : ℕ}

/-- Speed of a coordinate velocity field. -/
noncomputable def speed (T : ℝ → Vector n) (t : ℝ) : ℝ :=
  Real.sqrt (pairing n (T t) (T t))

theorem speed_eq_sqrt_speedSq
    (T : ℝ → Vector n) (t : ℝ) :
    speed (n := n) T t = Real.sqrt (speedSq (n := n) T t) :=
  rfl

theorem speed_nonneg
    (T : ℝ → Vector n) (t : ℝ) :
    0 ≤ speed (n := n) T t :=
  Real.sqrt_nonneg _

@[simp] theorem speed_zero
    (t : ℝ) :
    speed (n := n) (fun _ => 0) t = 0 := by
  simp [speed]

/-- Length of a coordinate curve from its velocity field. -/
noncomputable def curveLength (a b : ℝ) (T : ℝ → Vector n) : ℝ :=
  ∫ t in a..b, speed (n := n) T t

@[simp] theorem curveLength_zero
    (a b : ℝ) :
    curveLength (n := n) a b (fun _ => 0) = 0 := by
  simp [curveLength]

/-- Length of the `s`-slice of a variation. -/
noncomputable def variationLength (Gamma : CurveVariation n) (a b s : ℝ) : ℝ :=
  curveLength (n := n) a b (Gamma.tangentField s)

@[simp] theorem variationLength_eq_curveLength
    (Gamma : CurveVariation n) (a b s : ℝ) :
    variationLength (n := n) Gamma a b s =
      curveLength (n := n) a b (Gamma.tangentField s) :=
  rfl

/-- Unit-speed condition on a slice of a variation. -/
def UnitSpeedAt (Gamma : CurveVariation n) (s : ℝ) : Prop :=
  ∀ t, speed (n := n) (Gamma.tangentField s) t = 1

theorem unitSpeedAt_iff
    {Gamma : CurveVariation n} {s : ℝ} :
    UnitSpeedAt (n := n) Gamma s ↔ ∀ t, speed (n := n) (Gamma.tangentField s) t = 1 :=
  Iff.rfl

end Variation.Curve
