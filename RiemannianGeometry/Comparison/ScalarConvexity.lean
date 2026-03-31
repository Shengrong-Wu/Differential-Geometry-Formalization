import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Scalar convexity for Cartan-Hadamard

This file proves the 1D analytical core of the Cartan-Hadamard theorem:
if a twice-differentiable function has nonneg second derivative, vanishes at 0,
and has positive initial derivative, then it stays strictly positive.

The proof uses Lagrange's mean value theorem twice:
1. Since y'' ≥ 0, y' is nondecreasing → y'(c) ≥ y'(0) > 0 for c > 0
2. By MVT on y: y(t) = y(0) + y'(c) · t = y'(c) · t > 0

## Main result

`positive_of_nonneg_second_deriv`: if y(0) = 0, y'(0) > 0, y'' ≥ 0 on (0,∞),
then y(t) > 0 for all t > 0.
-/

namespace Comparison

open Set

/-- If `y'` has nonneg derivative on `(0, ∞)` and is differentiable at 0,
then `y'` is nondecreasing: `y'(0) ≤ y'(s)` for all `s > 0`. -/
private theorem deriv_nondecreasing
    {y' y'' : ℝ → ℝ}
    (hy'_0 : HasDerivAt y' (y'' 0) 0)
    (hy'' : ∀ x : ℝ, 0 < x → HasDerivAt y' (y'' x) x)
    (hconv : ∀ x : ℝ, 0 < x → 0 ≤ y'' x)
    {s : ℝ} (hs : 0 < s) :
    y' 0 ≤ y' s := by
  -- ContinuousOn y' on [0, s]
  have hcont : ContinuousOn y' (Icc 0 s) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
    · exact hy'_0.continuousAt.continuousWithinAt
    · exact (hy'' x hx_pos).continuousAt.continuousWithinAt
  -- HasDerivAt y' y'' on (0, s)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) s, HasDerivAt y' (y'' x) x :=
    fun x hx => hy'' x hx.1
  -- By MVT: ∃ c ∈ (0,s), y''(c) = (y'(s) - y'(0)) / (s - 0)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope y' y'' hs hcont hderiv
  -- y''(c) ≥ 0 and s > 0, so y'(s) - y'(0) = y''(c) * s ≥ 0
  have hc_pos : 0 < c := hc.1
  have h_nonneg : 0 ≤ y'' c := hconv c hc_pos
  -- hslope: y''(c) = (y'(s) - y'(0)) / (s - 0)
  have hs_pos' : (0 : ℝ) < s - 0 := by linarith
  have hkey : y' s - y' 0 = y'' c * s := by
    have h := hslope
    simp only [sub_zero] at h
    rw [h]
    field_simp
  nlinarith

/-- **Scalar convexity for Cartan-Hadamard.** If `y(0) = 0`, `y'(0) > 0`, and
`y'' ≥ 0` on `(0, ∞)`, then `y(t) > 0` for all `t > 0`.

This is the 1D analytical core of the Cartan-Hadamard "no conjugate points" argument.
Under nonpositive sectional curvature, the Jacobi field norm satisfies `‖J‖'' ≥ 0`
(since the curvature term has the right sign), so `‖J(t)‖ > 0` for t > 0. -/
theorem positive_of_nonneg_second_deriv
    {y y' y'' : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy1 : 0 < y' 0)
    (hy_0 : HasDerivAt y (y' 0) 0)
    (hy : ∀ x : ℝ, 0 < x → HasDerivAt y (y' x) x)
    (hy'_0 : HasDerivAt y' (y'' 0) 0)
    (hy' : ∀ x : ℝ, 0 < x → HasDerivAt y' (y'' x) x)
    (hconv : ∀ x : ℝ, 0 < x → 0 ≤ y'' x) :
    ∀ t : ℝ, 0 < t → 0 < y t := by
  intro t ht
  -- ContinuousOn y on [0, t]
  have hcont : ContinuousOn y (Icc 0 t) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
    · exact hy_0.continuousAt.continuousWithinAt
    · exact (hy x hx_pos).continuousAt.continuousWithinAt
  -- HasDerivAt y on (0, t)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) t, HasDerivAt y (y' x) x :=
    fun x hx => hy x hx.1
  -- By MVT: ∃ c ∈ (0,t), y'(c) = (y(t) - y(0)) / (t - 0)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope y y' ht hcont hderiv
  have hc_pos : 0 < c := hc.1
  -- y'(c) ≥ y'(0) > 0 since y' is nondecreasing
  have hderiv_c : y' 0 ≤ y' c :=
    deriv_nondecreasing hy'_0 hy' hconv hc_pos
  -- y(t) = y(0) + y'(c) * t = y'(c) * t > 0
  have hkey : y t - y 0 = y' c * t := by
    have h := hslope
    simp only [sub_zero] at h
    rw [h]
    field_simp
  nlinarith

end Comparison
