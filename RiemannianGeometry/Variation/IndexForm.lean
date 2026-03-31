import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Ring
import Curvature.SectionalRicci
import Variation.CurveVariation

namespace Variation.Curve

open scoped BigOperators

variable {n : ℕ}

/-- A field derivative along the reference curve, packaged for the index form. -/
abbrev AlongFieldDerivative := ℝ → Vector n

/-- The curvature contribution in the index form. -/
def curvaturePairing
    (RVTT : ℝ → Vector n) (W : ℝ → Vector n) (t : ℝ) : ℝ :=
  pairing n (RVTT t) (W t)

/-- The kinetic contribution in the index form. -/
def kineticPairing
    (nablaV nablaW : AlongFieldDerivative (n := n)) (t : ℝ) : ℝ :=
  pairing n (nablaV t) (nablaW t)

/-- The scalar integrand of the index form. -/
def indexFormIntegrand
    (nablaV nablaW : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n) (W : ℝ → Vector n) (t : ℝ) : ℝ :=
  kineticPairing (n := n) nablaV nablaW t - curvaturePairing (n := n) RVTT W t

/-- The abstract index form along a geodesic segment. -/
noncomputable def indexForm
    (a b : ℝ)
    (nablaV nablaW : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n) (W : ℝ → Vector n) : ℝ :=
  ∫ t in a..b, indexFormIntegrand (n := n) nablaV nablaW RVTT W t

theorem curvaturePairing_add_left
    (RVTT₁ RVTT₂ W : ℝ → Vector n) (t : ℝ) :
    curvaturePairing (n := n) (fun s => RVTT₁ s + RVTT₂ s) W t =
      curvaturePairing (n := n) RVTT₁ W t + curvaturePairing (n := n) RVTT₂ W t := by
  simp [curvaturePairing, pairing_add_left]

theorem curvaturePairing_smul_left
    (c : ℝ) (RVTT W : ℝ → Vector n) (t : ℝ) :
    curvaturePairing (n := n) (fun s => c • RVTT s) W t =
      c * curvaturePairing (n := n) RVTT W t := by
  simp [curvaturePairing, pairing_smul_left]

theorem kineticPairing_add_left
    (nablaV₁ nablaV₂ nablaW : AlongFieldDerivative (n := n)) (t : ℝ) :
    kineticPairing (n := n) (fun s => nablaV₁ s + nablaV₂ s) nablaW t =
      kineticPairing (n := n) nablaV₁ nablaW t + kineticPairing (n := n) nablaV₂ nablaW t := by
  simp [kineticPairing, pairing_add_left]

theorem kineticPairing_add_right
    (nablaV nablaW₁ nablaW₂ : AlongFieldDerivative (n := n)) (t : ℝ) :
    kineticPairing (n := n) nablaV (fun s => nablaW₁ s + nablaW₂ s) t =
      kineticPairing (n := n) nablaV nablaW₁ t + kineticPairing (n := n) nablaV nablaW₂ t := by
  simp [kineticPairing, pairing_add_right]

theorem kineticPairing_smul_left
    (c : ℝ) (nablaV nablaW : AlongFieldDerivative (n := n)) (t : ℝ) :
    kineticPairing (n := n) (fun s => c • nablaV s) nablaW t =
      c * kineticPairing (n := n) nablaV nablaW t := by
  simp [kineticPairing, pairing_smul_left]

theorem kineticPairing_smul_right
    (c : ℝ) (nablaV nablaW : AlongFieldDerivative (n := n)) (t : ℝ) :
    kineticPairing (n := n) nablaV (fun s => c • nablaW s) t =
      c * kineticPairing (n := n) nablaV nablaW t := by
  simp [kineticPairing, pairing_smul_right]

theorem indexFormIntegrand_add_left
    (nablaV₁ nablaV₂ nablaW : AlongFieldDerivative (n := n))
    (RVTT₁ RVTT₂ W : ℝ → Vector n) (t : ℝ) :
    indexFormIntegrand (n := n) (fun s => nablaV₁ s + nablaV₂ s) nablaW
        (fun s => RVTT₁ s + RVTT₂ s) W t =
      indexFormIntegrand (n := n) nablaV₁ nablaW RVTT₁ W t +
        indexFormIntegrand (n := n) nablaV₂ nablaW RVTT₂ W t := by
  simp [indexFormIntegrand, kineticPairing_add_left, curvaturePairing_add_left, sub_eq_add_neg]
  ring

theorem indexFormIntegrand_smul_left
    (c : ℝ) (nablaV nablaW : AlongFieldDerivative (n := n))
    (RVTT W : ℝ → Vector n) (t : ℝ) :
    indexFormIntegrand (n := n) (fun s => c • nablaV s) nablaW (fun s => c • RVTT s) W t =
      c * indexFormIntegrand (n := n) nablaV nablaW RVTT W t := by
  simp [indexFormIntegrand, kineticPairing_smul_left, curvaturePairing_smul_left]
  ring

theorem indexForm_add_left
    {a b : ℝ}
    {nablaV₁ nablaV₂ nablaW : AlongFieldDerivative (n := n)}
    {RVTT₁ RVTT₂ W : ℝ → Vector n}
    (h₁ :
      IntervalIntegrable
        (fun t => indexFormIntegrand (n := n) nablaV₁ nablaW RVTT₁ W t) MeasureTheory.volume a b)
    (h₂ :
      IntervalIntegrable
        (fun t => indexFormIntegrand (n := n) nablaV₂ nablaW RVTT₂ W t) MeasureTheory.volume a b) :
    indexForm (n := n) a b (fun t => nablaV₁ t + nablaV₂ t) nablaW
        (fun t => RVTT₁ t + RVTT₂ t) W =
      indexForm (n := n) a b nablaV₁ nablaW RVTT₁ W +
        indexForm (n := n) a b nablaV₂ nablaW RVTT₂ W := by
  rw [indexForm]
  calc
    ∫ t in a..b,
        indexFormIntegrand (n := n) (fun s => nablaV₁ s + nablaV₂ s) nablaW
          (fun s => RVTT₁ s + RVTT₂ s) W t
      = ∫ t in a..b,
          (indexFormIntegrand (n := n) nablaV₁ nablaW RVTT₁ W t +
            indexFormIntegrand (n := n) nablaV₂ nablaW RVTT₂ W t) := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact indexFormIntegrand_add_left (n := n) nablaV₁ nablaV₂ nablaW RVTT₁ RVTT₂ W t
    _ = (∫ t in a..b, indexFormIntegrand (n := n) nablaV₁ nablaW RVTT₁ W t) +
          ∫ t in a..b, indexFormIntegrand (n := n) nablaV₂ nablaW RVTT₂ W t := by
          exact intervalIntegral.integral_add h₁ h₂
    _ = indexForm (n := n) a b nablaV₁ nablaW RVTT₁ W +
          indexForm (n := n) a b nablaV₂ nablaW RVTT₂ W := by
          simp [indexForm]

theorem indexForm_smul_left
    {a b c : ℝ}
    {nablaV nablaW : AlongFieldDerivative (n := n)}
    {RVTT W : ℝ → Vector n}
    (h :
      IntervalIntegrable
        (fun t => indexFormIntegrand (n := n) nablaV nablaW RVTT W t) MeasureTheory.volume a b) :
    indexForm (n := n) a b (fun t => c • nablaV t) nablaW (fun t => c • RVTT t) W =
      c * indexForm (n := n) a b nablaV nablaW RVTT W := by
  rw [indexForm]
  calc
    ∫ t in a..b,
        indexFormIntegrand (n := n) (fun s => c • nablaV s) nablaW (fun s => c • RVTT s) W t
      = ∫ t in a..b, c • indexFormIntegrand (n := n) nablaV nablaW RVTT W t := by
          apply intervalIntegral.integral_congr
          intro t ht
          simpa using indexFormIntegrand_smul_left (n := n) c nablaV nablaW RVTT W t
    _ = c • ∫ t in a..b, indexFormIntegrand (n := n) nablaV nablaW RVTT W t := by
          simpa using h.integral_smul c
    _ = c * indexForm (n := n) a b nablaV nablaW RVTT W := by
          simp [indexForm]

theorem indexForm_symm
    {a b : ℝ}
    {nablaV nablaW : AlongFieldDerivative (n := n)}
    {RVTT RWTT V W : ℝ → Vector n}
    (hkin : ∀ t, kineticPairing (n := n) nablaV nablaW t = kineticPairing (n := n) nablaW nablaV t)
    (hcurv : ∀ t, curvaturePairing (n := n) RVTT W t = curvaturePairing (n := n) RWTT V t) :
    indexForm (n := n) a b nablaV nablaW RVTT W =
      indexForm (n := n) a b nablaW nablaV RWTT V := by
  rw [indexForm, indexForm]
  apply intervalIntegral.integral_congr
  intro t ht
  simp [indexFormIntegrand, hkin t, hcurv t]

/-- A field vanishes at the endpoints of a segment. -/
def VanishesAtEndpoints (V : ℝ → Vector n) (a b : ℝ) : Prop :=
  V a = 0 ∧ V b = 0

/-- Nonnegativity package for the index form on minimizing geodesics. -/
def IndexFormNonnegative
    (a b : ℝ)
    (nablaV : AlongFieldDerivative (n := n))
    (RVTT : ℝ → Vector n)
    (V : ℝ → Vector n) : Prop :=
  0 ≤ indexForm (n := n) a b nablaV nablaV RVTT V

end Variation.Curve
