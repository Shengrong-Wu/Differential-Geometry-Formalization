import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Data.Real.Sign

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
open scoped Topology

/-- Monotonicity of a derivative on an interval from a nonnegative second derivative. -/
private theorem deriv_nondecreasing_on_interval
    {y' y'' : ℝ → ℝ} {a s : ℝ}
    (ha : 0 ≤ a)
    (hy'_a : HasDerivAt y' (y'' a) a)
    (hy'' : ∀ x : ℝ, 0 < x → HasDerivAt y' (y'' x) x)
    (hconv : ∀ x : ℝ, 0 < x → 0 ≤ y'' x)
    (has : a < s) :
    y' a ≤ y' s := by
  have hcont : ContinuousOn y' (Icc a s) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
    · exact hy'_a.continuousAt.continuousWithinAt
    · exact (hy'' x (lt_of_le_of_lt ha hx_pos)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo a s, HasDerivAt y' (y'' x) x := by
    intro x hx
    exact hy'' x (lt_of_le_of_lt ha hx.1)
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope y' y'' has hcont hderiv
  have hc_pos : 0 < c := lt_of_le_of_lt ha hc.1
  have h_nonneg : 0 ≤ y'' c := hconv c hc_pos
  have hkey : y'' c * (s - a) = y' s - y' a := by
    exact (eq_div_iff (sub_ne_zero.mpr has.ne')).mp hslope
  have hs_nonneg : 0 ≤ s - a := sub_nonneg.mpr (le_of_lt has)
  nlinarith

/-- If `y'` has nonneg derivative on `(0, ∞)` and is differentiable at 0,
then `y'` is nondecreasing: `y'(0) ≤ y'(s)` for all `s > 0`. -/
private theorem deriv_nondecreasing
    {y' y'' : ℝ → ℝ}
    (hy'_0 : HasDerivAt y' (y'' 0) 0)
    (hy'' : ∀ x : ℝ, 0 < x → HasDerivAt y' (y'' x) x)
    (hconv : ∀ x : ℝ, 0 < x → 0 ≤ y'' x)
    {s : ℝ} (hs : 0 < s) :
    y' 0 ≤ y' s := by
  simpa using deriv_nondecreasing_on_interval
    (a := 0) (s := s) (by positivity) hy'_0 hy'' hconv hs

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

/-- A squared-norm convexity variant avoiding the singular `√u` packaging at `0`.

If `u(0) = 0`, `u'(0) = 0`, `u''(0) > 0`, and `u'' ≥ 0` on `(0, ∞)`, then `u(t) > 0` for
all `t > 0`. This is the natural shape for Cartan-Hadamard when `u = ‖J‖²`. -/
theorem positive_of_nonneg_second_deriv_of_zero_deriv_zero
    {u u' u'' : ℝ → ℝ}
    (hu0 : u 0 = 0)
    (hu'0 : u' 0 = 0)
    (hu_0 : HasDerivAt u (u' 0) 0)
    (hu : ∀ x : ℝ, 0 < x → HasDerivAt u (u' x) x)
    (hu'_0 : HasDerivAt u' (u'' 0) 0)
    (hu''0_pos : 0 < u'' 0)
    (hu' : ∀ x : ℝ, 0 < x → HasDerivAt u' (u'' x) x)
    (hconv : ∀ x : ℝ, 0 < x → 0 ≤ u'' x) :
    ∀ t : ℝ, 0 < t → 0 < u t := by
  have hderiv_pos : deriv u' 0 > 0 := by
    simpa [hu'_0.deriv] using hu''0_pos
  have hsign :
      ∀ᶠ x in 𝓝 (0 : ℝ), SignType.sign (u' x) = SignType.sign (x - 0) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos hderiv_pos hu'0
  have hu'_pos_nhds : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < u' x := by
    filter_upwards [hsign.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with x hx hx0
    have hxsign : SignType.sign x = 1 := sign_eq_one_iff.mpr hx0
    have hsignx : SignType.sign (u' x) = 1 := by
      simpa [sub_zero, hxsign] using hx
    exact sign_eq_one_iff.mp hsignx
  obtain ⟨b, hb, hbsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hu'_pos_nhds
  have hb0 : 0 < b := hb
  have hseed_pos : 0 < u' (b / 2) := by
    apply hbsub
    constructor
    · linarith
    · linarith
  have hu'_pos : ∀ x : ℝ, 0 < x → 0 < u' x := by
    intro x hx
    by_cases hxb : x < b
    · exact hbsub ⟨hx, hxb⟩
    · have hmono : u' (b / 2) ≤ u' x := by
        refine deriv_nondecreasing_on_interval (a := b / 2) (s := x) ?_ ?_ hu' hconv ?_
        · linarith
        · exact hu' (b / 2) (by linarith)
        · linarith
      linarith
  intro t ht
  have hcont : ContinuousOn u (Icc 0 t) := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with rfl | hx_pos
    · exact hu_0.continuousAt.continuousWithinAt
    · exact (hu x hx_pos).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) t, HasDerivAt u (u' x) x := by
    intro x hx
    exact hu x hx.1
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope u u' ht hcont hderiv
  have hc_pos : 0 < c := hc.1
  have huc_pos : 0 < u' c := hu'_pos c hc_pos
  have hkey : u' c * t = u t - u 0 := by
    have htmp : u' c * (t - 0) = u t - u 0 :=
      (eq_div_iff (sub_ne_zero.mpr ht.ne')).mp hslope
    simpa using htmp
  nlinarith

end Comparison
