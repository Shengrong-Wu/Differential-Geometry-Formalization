import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Comparison.ODEModels

/-! This owner file packages the scalar comparison argument on `modelPosDomain`; the remaining
gap is still the derivation of the Wronskian sign from the stored subsolution inequality. -/

namespace Comparison

open scoped Topology

/-- Any point in the model-positive domain is strictly positive. -/
theorem zero_lt_of_mem_modelPosDomain
    {k t : ℝ}
    (ht : t ∈ modelPosDomain k) :
    0 < t := by
  by_cases hk : 0 < k
  · have ht' : t ∈ Set.Ioo 0 (Real.pi / Real.sqrt k) := by
      simpa [modelPosDomain, hk] using ht
    exact ht'.1
  · simpa [modelPosDomain, hk] using ht

/-- The model-positive domain sits inside the positive half-line. -/
theorem modelPosDomain_subset_Ioi
    (k : ℝ) :
    modelPosDomain k ⊆ Set.Ioi (0 : ℝ) := by
  intro t ht
  exact zero_lt_of_mem_modelPosDomain ht

/-- The honest comparison domain is convex. -/
theorem modelPosDomain_convex
    (k : ℝ) :
    Convex ℝ (modelPosDomain k) := by
  by_cases hk : 0 < k
  · simpa [modelPosDomain, hk] using
      (convex_Ioo (0 : ℝ) (Real.pi / Real.sqrt k))
  · simpa [modelPosDomain, hk] using convex_Ioi (0 : ℝ)

/-- The honest comparison domain is open. -/
theorem isOpen_modelPosDomain
    (k : ℝ) :
    IsOpen (modelPosDomain k) := by
  by_cases hk : 0 < k
  · simpa [modelPosDomain, hk] using
      (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / Real.sqrt k)))
  · simpa [modelPosDomain, hk] using isOpen_Ioi

/-- The constant-curvature model function is strictly positive on its honest comparison domain. -/
theorem sn_pos_of_mem_modelPosDomain
    {k t : ℝ}
    (ht : t ∈ modelPosDomain k) :
    0 < sn k t := by
  by_cases hk : 0 < k
  · rcases (by simpa [modelPosDomain, hk] using ht : t ∈ Set.Ioo 0 (Real.pi / Real.sqrt k)) with
      ⟨ht0, htpi⟩
    have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos_of_pos hk
    have hsqrt_ne : Real.sqrt k ≠ 0 := ne_of_gt hsqrt
    have harg_pos : 0 < Real.sqrt k * t := mul_pos hsqrt ht0
    have harg_lt_pi : Real.sqrt k * t < Real.pi := by
      calc
        Real.sqrt k * t < Real.sqrt k * (Real.pi / Real.sqrt k) :=
          mul_lt_mul_of_pos_left htpi hsqrt
        _ = Real.pi := by
          field_simp [hsqrt_ne]
    rw [show sn k t = Real.sin (Real.sqrt k * t) / Real.sqrt k by simp [sn, hk]]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi harg_pos harg_lt_pi) hsqrt
  · have ht0 : 0 < t := by simpa [modelPosDomain, hk] using ht
    by_cases h0 : k = 0
    · subst h0
      simpa [sn] using ht0
    · have hkneg : k < 0 := lt_of_le_of_ne (le_of_not_gt hk) h0
      have hsqrt : 0 < Real.sqrt (-k) := Real.sqrt_pos_of_pos (neg_pos.mpr hkneg)
      have harg_pos : 0 < Real.sqrt (-k) * t := mul_pos hsqrt ht0
      rw [show sn k t = Real.sinh (Real.sqrt (-k) * t) / Real.sqrt (-k) by
        simp [sn, hk, h0]]
      exact div_pos (Real.sinh_pos_iff.mpr harg_pos) hsqrt

/-- The constant-curvature model never vanishes on the honest comparison domain. -/
theorem sn_ne_zero_of_mem_modelPosDomain
    {k t : ℝ}
    (ht : t ∈ modelPosDomain k) :
    sn k t ≠ 0 :=
  (sn_pos_of_mem_modelPosDomain ht).ne'

/-- The Wronskian sign condition that would follow from the scalar subsolution inequality in the
full Sturm proof. -/
def ScalarWronskianUpperBound
    (k : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
    deriv y t * sn k t - y t * deriv (sn k) t ≤ 0

/-- The scalar Wronskian numerator against the model solution `sn k`. -/
noncomputable def scalarWronskian
    (k : ℝ) (y : ℝ → ℝ) : ℝ → ℝ :=
  fun t => deriv y t * sn k t - y t * deriv (sn k) t

/-- Derivative formula for the scalar Wronskian numerator on `modelPosDomain`. -/
theorem hasDerivAt_scalarWronskian
    {k : ℝ} {y : ℝ → ℝ}
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    (hy2 :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
        HasDerivAt (deriv y) (deriv (deriv y) t) t)
    {t : ℝ}
    (ht : t ∈ modelPosDomain k) :
    HasDerivAt (scalarWronskian k y)
      ((deriv (deriv y) t + k * y t) * sn k t) t := by
  have hy' := hy ht
  have hy2' := hy2 ht
  have hsn := hasDerivAt_sn k t
  have hdsn := hasDerivAt_deriv_sn k t
  have hmul1 :
      HasDerivAt (fun s : ℝ => deriv y s * sn k s)
        (deriv (deriv y) t * sn k t + deriv y t * deriv (sn k) t) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hy2'.mul hsn
  have hmul2 :
      HasDerivAt (fun s : ℝ => y s * deriv (sn k) s)
        (deriv y t * deriv (sn k) t + y t * (-k * sn k t)) t := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hy'.mul hdsn
  have hsub := hmul1.sub hmul2
  convert hsub using 1 <;> ring

/-- The scalar Wronskian derivative is nonpositive whenever `y`` satisfies the subsolution
inequality on `modelPosDomain`. -/
theorem deriv_scalarWronskian_nonpos_of_subsolution
    {k : ℝ} {y : ℝ → ℝ}
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    (hy2ineq :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
        HasDerivAt (deriv y) (deriv (deriv y) t) t ∧
          deriv (deriv y) t + k * y t ≤ 0)
    {t : ℝ}
    (ht : t ∈ modelPosDomain k) :
    deriv (scalarWronskian k y) t ≤ 0 := by
  have hy2' := (hy2ineq ht).1
  rw [(hasDerivAt_scalarWronskian hy (fun hs hhs => (hy2ineq hhs).1) ht).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (hy2ineq ht).2 (le_of_lt (sn_pos_of_mem_modelPosDomain ht))

/-- The scalar Wronskian is antitone on `modelPosDomain` under the honest subsolution data. -/
theorem antitoneOn_scalarWronskian_of_subsolution
    {k : ℝ} {y : ℝ → ℝ}
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    (hy2ineq :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
        HasDerivAt (deriv y) (deriv (deriv y) t) t ∧
          deriv (deriv y) t + k * y t ≤ 0) :
    AntitoneOn (scalarWronskian k y) (modelPosDomain k) := by
  have hcont :
      ContinuousOn (scalarWronskian k y) (modelPosDomain k) := by
    intro t ht
    exact (hasDerivAt_scalarWronskian hy (fun hs hhs => (hy2ineq hhs).1) ht).continuousAt.continuousWithinAt
  have hdiff :
      DifferentiableOn ℝ (scalarWronskian k y) (modelPosDomain k) := by
    intro t ht
    exact (hasDerivAt_scalarWronskian hy (fun hs hhs => (hy2ineq hhs).1) ht).differentiableAt.differentiableWithinAt
  have hnonpos :
      ∀ t ∈ modelPosDomain k, deriv (scalarWronskian k y) t ≤ 0 := by
    intro t ht
    exact deriv_scalarWronskian_nonpos_of_subsolution hy hy2ineq ht
  have hdiffInterior :
      DifferentiableOn ℝ (scalarWronskian k y) (interior (modelPosDomain k)) := by
    simpa [isOpen_modelPosDomain k |>.interior_eq] using hdiff
  have hnonposInterior :
      ∀ t ∈ interior (modelPosDomain k), deriv (scalarWronskian k y) t ≤ 0 := by
    simpa [isOpen_modelPosDomain k |>.interior_eq] using hnonpos
  exact antitoneOn_of_deriv_nonpos (modelPosDomain_convex k) hcont hdiffInterior hnonposInterior

/-- Differentiability at the origin recovered from a nonzero stored derivative value. -/
theorem hasDerivAt_of_deriv_eq_one
    {f : ℝ → ℝ}
    (h : deriv f 0 = 1) :
    HasDerivAt f 1 0 := by
  have hdiff : DifferentiableAt ℝ f 0 := by
    by_contra hndiff
    have hzero : deriv f 0 = 0 := deriv_zero_of_not_differentiableAt hndiff
    linarith
  simpa [h] using hdiff.hasDerivAt

/-- The ratio against the identity tends to the stored initial slope at the origin. -/
theorem tendsto_div_id_at_zero_of_initial
    {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy1 : deriv y 0 = 1) :
    Filter.Tendsto (fun t : ℝ => y t / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hy' : HasDerivAt y 1 0 := hasDerivAt_of_deriv_eq_one hy1
  simpa [div_eq_mul_inv, hy0, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
    hy'.tendsto_slope_zero_right

/-- The canonical scalar model is asymptotic to the identity at the origin. -/
theorem tendsto_sn_div_id_at_zero
    (k : ℝ) :
    Filter.Tendsto (fun t : ℝ => sn k t / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hsn' : HasDerivAt (sn k) 1 0 := by
    simpa [deriv_sn_zero k] using hasDerivAt_sn k 0
  simpa [div_eq_mul_inv, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc,
    (sn_hasModelInitialConditions k).1] using
    hsn'.tendsto_slope_zero_right

/-- Any scalar function with the same first-order initial data as `sn k` has ratio `y / sn k`
tending to `1` from the right at the origin. -/
theorem tendsto_div_sn_at_zero_of_initial
    {k : ℝ} {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy1 : deriv y 0 = 1) :
    Filter.Tendsto (fun t : ℝ => y t / sn k t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hquot :=
    (tendsto_div_id_at_zero_of_initial hy0 hy1).div (tendsto_sn_div_id_at_zero k) (by norm_num : (1 : ℝ) ≠ 0)
  have hcongr :
      ((fun t : ℝ => (y t / t) / (sn k t / t)) =ᶠ[𝓝[>] (0 : ℝ)] fun t => y t / sn k t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp [ht0]
  simpa using hquot.congr' hcongr

/-- The comparison ratio against the canonical scalar model. -/
noncomputable def scalarComparisonRatio
    (k : ℝ) (y : ℝ → ℝ) : ℝ → ℝ :=
  fun t => y t / sn k t

/-- Derivative formula for the scalar comparison ratio on the honest comparison domain. -/
theorem hasDerivAt_scalarComparisonRatio
    {k : ℝ} {y : ℝ → ℝ}
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    {t : ℝ}
    (ht : t ∈ modelPosDomain k) :
    HasDerivAt (scalarComparisonRatio k y)
      ((deriv y t * sn k t - y t * deriv (sn k) t) / (sn k t) ^ 2) t := by
  have hy' := hy ht
  have hsn' := hasDerivAt_sn k t
  have hsn0 : sn k t ≠ 0 := sn_ne_zero_of_mem_modelPosDomain ht
  simpa [scalarComparisonRatio, div_eq_mul_inv, pow_two, sub_eq_add_neg, mul_comm, mul_left_comm,
    mul_assoc] using hy'.div hsn' hsn0

/-- The scalar comparison ratio is antitone on the honest comparison domain once the Wronskian sign
has been established. -/
theorem antitoneOn_scalarComparisonRatio
    {k : ℝ} {y : ℝ → ℝ}
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    (hW : ScalarWronskianUpperBound k y) :
    AntitoneOn (scalarComparisonRatio k y) (modelPosDomain k) := by
  have hcont :
      ContinuousOn (scalarComparisonRatio k y) (modelPosDomain k) := by
    intro t ht
    exact (hasDerivAt_scalarComparisonRatio hy ht).continuousAt.continuousWithinAt
  have hdiff :
      DifferentiableOn ℝ (scalarComparisonRatio k y) (modelPosDomain k) := by
    intro t ht
    exact (hasDerivAt_scalarComparisonRatio hy ht).differentiableAt.differentiableWithinAt
  have hnonpos :
      ∀ t ∈ modelPosDomain k, deriv (scalarComparisonRatio k y) t ≤ 0 := by
    intro t ht
    rw [(hasDerivAt_scalarComparisonRatio hy ht).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (hW ht) (sq_nonneg _)
  have hdiffInterior :
      DifferentiableOn ℝ (scalarComparisonRatio k y) (interior (modelPosDomain k)) := by
    simpa [isOpen_modelPosDomain k |>.interior_eq] using hdiff
  have hnonposInterior :
      ∀ t ∈ interior (modelPosDomain k), deriv (scalarComparisonRatio k y) t ≤ 0 := by
    simpa [isOpen_modelPosDomain k |>.interior_eq] using hnonpos
  exact antitoneOn_of_deriv_nonpos (modelPosDomain_convex k) hcont hdiffInterior hnonposInterior

/-- Owner theorem: the Wronskian sign is derived internally from the honest scalar ODE data and
initial conditions, so the public scalar comparison route no longer needs an external witness. -/
theorem scalarWronskianUpperBound_of_subsolution
    {k : ℝ} {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy1 : deriv y 0 = 1)
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    (hy2ineq :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
        HasDerivAt (deriv y) (deriv (deriv y) t) t ∧
          deriv (deriv y) t + k * y t ≤ 0) :
    ScalarWronskianUpperBound k y := by
  intro t ht
  by_contra hpos
  let ratio := scalarComparisonRatio k y
  have hantiW : AntitoneOn (scalarWronskian k y) (modelPosDomain k) :=
    antitoneOn_scalarWronskian_of_subsolution hy hy2ineq
  have hlimRatio :
      Filter.Tendsto ratio (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    tendsto_div_sn_at_zero_of_initial hy0 hy1
  have hratioNear : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), |ratio u - 1| < (1 / 4 : ℝ) := by
    simpa [one_div, Set.mem_setOf_eq] using hlimRatio.eventually (by
      simpa [Metric.ball, Real.dist_eq, Set.mem_setOf_eq] using
        Metric.ball_mem_nhds (1 : ℝ) (by norm_num : 0 < (1 / 4 : ℝ)))
  have hsnNear : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), sn k u / u < (2 : ℝ) := by
    exact (tendsto_sn_div_id_at_zero k).eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  rw [(nhdsGT_basis 0).eventually_iff] at hratioNear hsnNear
  obtain ⟨δratio, hδratio_pos, hδratio⟩ := hratioNear
  obtain ⟨δsn, hδsn_pos, hδsn⟩ := hsnNear
  let δ : ℝ := min δsn (min δratio (min (t / 2) ((scalarWronskian k y) t / 4)))
  let s : ℝ := δ / 4
  have ht_pos : 0 < t := zero_lt_of_mem_modelPosDomain ht
  have hWt_pos : 0 < (scalarWronskian k y) t := by
    exact lt_of_not_ge hpos
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hs_lt_δ : s < δ := by
    dsimp [s]
    nlinarith
  have h2s_lt_δ : 2 * s < δ := by
    dsimp [s]
    nlinarith
  have h2s_lt_t : 2 * s < t := by
    have hδ_le : δ ≤ t / 2 := by
      dsimp [δ]
      exact min_le_of_right_le (min_le_of_right_le (min_le_left _ _))
    dsimp [s]
    nlinarith
  have hs_lt_2s : s < 2 * s := by nlinarith
  have hs_lt_t : s < t := lt_trans hs_lt_2s h2s_lt_t
  have hs_dom : s ∈ modelPosDomain k :=
    modelPosDomain_downward_closed ht hs_pos hs_lt_t
  have h2s_pos : 0 < 2 * s := by positivity
  have h2s_dom : 2 * s ∈ modelPosDomain k :=
    modelPosDomain_downward_closed ht h2s_pos h2s_lt_t
  obtain ⟨c, hc, hcSlope⟩ :
      ∃ c ∈ Set.Ioo s (2 * s),
        ((deriv y c * sn k c - y c * deriv (sn k) c) / (sn k c) ^ 2) =
          (ratio (2 * s) - ratio s) / ((2 * s) - s) := by
    refine exists_hasDerivAt_eq_slope (a := s) (b := 2 * s)
      (f := ratio)
      (f' := fun u => ((deriv y u * sn k u - y u * deriv (sn k) u) / (sn k u) ^ 2))
      ?_ ?_ ?_
    · linarith
    · intro u hu
      have hu_dom : u ∈ modelPosDomain k := by
        refine modelPosDomain_downward_closed ht ?_ ?_
        · nlinarith [hs_pos, hu.1]
        · nlinarith [hu.2, h2s_lt_t]
      exact (hasDerivAt_scalarComparisonRatio hy hu_dom).continuousAt.continuousWithinAt
    · intro u hu
      have hu_dom : u ∈ modelPosDomain k := by
        refine modelPosDomain_downward_closed ht ?_ ?_
        · nlinarith [hs_pos, hu.1]
        · nlinarith [hu.2, h2s_lt_t]
      simpa [ratio] using hasDerivAt_scalarComparisonRatio hy hu_dom
  have hc_pos : 0 < c := lt_trans hs_pos hc.1
  have hc_lt_t : c < t := lt_trans hc.2 h2s_lt_t
  have hc_dom : c ∈ modelPosDomain k :=
    modelPosDomain_downward_closed ht hc_pos hc_lt_t
  have hWc_ge : (scalarWronskian k y) t ≤ scalarWronskian k y c :=
    hantiW hc_dom ht hc_lt_t.le
  have hc_lt_δsn : c < δsn := by
    have hc_lt_δ : c < δ := lt_trans hc.2 h2s_lt_δ
    have hδ_le_δsn : δ ≤ δsn := by
      dsimp [δ]
      exact min_le_left _ _
    exact lt_of_lt_of_le hc_lt_δ hδ_le_δsn
  have hsn_over : sn k c / c < (2 : ℝ) := hδsn ⟨hc_pos, hc_lt_δsn⟩
  have hsn_le_four_s : sn k c ≤ 4 * s := by
    have hsn_lt_two_c : sn k c < 2 * c := by
      exact (div_lt_iff₀ hc_pos).mp hsn_over
    have hc_le_two_s : c ≤ 2 * s := hc.2.le
    nlinarith
  have hsn_sq_le : (sn k c) ^ 2 ≤ 16 * s ^ 2 := by
    have hsn_nonneg : 0 ≤ sn k c := le_of_lt (sn_pos_of_mem_modelPosDomain hc_dom)
    nlinarith
  have hsn_sq_pos : 0 < (sn k c) ^ 2 := by
    exact sq_pos_of_ne_zero (sn_ne_zero_of_mem_modelPosDomain hc_dom)
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hlower_deriv :
      (scalarWronskian k y) t / (16 * s ^ 2) ≤
        ((deriv y c * sn k c - y c * deriv (sn k) c) / (sn k c) ^ 2) := by
    have h1 :
        (scalarWronskian k y) t / (16 * s ^ 2) ≤
          (scalarWronskian k y) t / (sn k c) ^ 2 := by
      exact div_le_div_of_nonneg_left (le_of_lt hWt_pos) hsn_sq_pos hsn_sq_le
    have h2 :
        (scalarWronskian k y) t / (sn k c) ^ 2 ≤
          (scalarWronskian k y) c / (sn k c) ^ 2 := by
      exact div_le_div_of_nonneg_right hWc_ge (sq_nonneg _)
    simpa [scalarWronskian] using h1.trans h2
  have hlower_slope :
      (scalarWronskian k y) t / (16 * s ^ 2) ≤ (ratio (2 * s) - ratio s) / s := by
    rw [show (2 * s) - s = s by ring] at hcSlope
    simpa [hcSlope] using hlower_deriv
  have hdiff_lower :
      (scalarWronskian k y) t / (16 * s) ≤ ratio (2 * s) - ratio s := by
    have htmp := hlower_slope
    have hs_factor : 16 * s ^ 2 = (16 * s) * s := by ring
    rw [hs_factor] at htmp
    field_simp [hs_ne] at htmp
    have htmp' : scalarWronskian k y t ≤ (16 * s) * (ratio (2 * s) - ratio s) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
    have htmp'' : scalarWronskian k y t ≤ (ratio (2 * s) - ratio s) * (16 * s) := by
      simpa [mul_comm] using htmp'
    have h16s_pos : 0 < 16 * s := by positivity
    exact (div_le_iff₀ h16s_pos).2 htmp''
  have hs_le_w : s ≤ (scalarWronskian k y) t / 16 := by
    have hδ_le : δ ≤ (scalarWronskian k y) t / 4 := by
      dsimp [δ]
      exact min_le_of_right_le (min_le_of_right_le (min_le_right _ _))
    dsimp [s]
    nlinarith
  have hone_le : (1 : ℝ) ≤ (scalarWronskian k y) t / (16 * s) := by
    have : 16 * s ≤ (scalarWronskian k y) t := by nlinarith
    exact (one_le_div (by positivity : 0 < 16 * s)).2 this
  have hdiff_ge_one : (1 : ℝ) ≤ ratio (2 * s) - ratio s := hone_le.trans hdiff_lower
  have hs_lt_δratio : s < δratio := by
    have hδ_le_δratio : δ ≤ δratio := by
      dsimp [δ]
      exact min_le_of_right_le (min_le_left _ _)
    exact lt_of_lt_of_le hs_lt_δ hδ_le_δratio
  have h2s_lt_δratio : 2 * s < δratio := by
    have hδ_le_δratio : δ ≤ δratio := by
      dsimp [δ]
      exact min_le_of_right_le (min_le_left _ _)
    exact lt_of_lt_of_le h2s_lt_δ hδ_le_δratio
  have hs_ratio : |ratio s - 1| < (1 / 4 : ℝ) := hδratio ⟨hs_pos, hs_lt_δratio⟩
  have h2s_ratio : |ratio (2 * s) - 1| < (1 / 4 : ℝ) := hδratio ⟨h2s_pos, h2s_lt_δratio⟩
  have hdiff_abs : |ratio (2 * s) - ratio s| < (1 / 2 : ℝ) := by
    refine abs_lt.mpr ?_
    constructor
    · have hAlo : -(1 / 4 : ℝ) < ratio (2 * s) - 1 := (abs_lt.mp h2s_ratio).1
      have hBhi : ratio s - 1 < (1 / 4 : ℝ) := (abs_lt.mp hs_ratio).2
      linarith
    · have hAhi : ratio (2 * s) - 1 < (1 / 4 : ℝ) := (abs_lt.mp h2s_ratio).2
      have hBlo : -(1 / 4 : ℝ) < ratio s - 1 := (abs_lt.mp hs_ratio).1
      linarith
  have hhalf_lt : (1 / 2 : ℝ) < ratio (2 * s) - ratio s := by
    exact lt_of_lt_of_le (by norm_num) hdiff_ge_one
  have hhalf_lt_abs : (1 / 2 : ℝ) < |ratio (2 * s) - ratio s| :=
    lt_of_lt_of_le hhalf_lt (le_abs_self _)
  linarith

/-- Owner theorem for the scalar comparison layer once the Wronskian sign has been derived: the
subsolution stays below the canonical constant-curvature model on `modelPosDomain`. -/
theorem scalarComparison_of_wronskianNonpos
    {k : ℝ} {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy1 : deriv y 0 = 1)
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    (hW : ScalarWronskianUpperBound k y) :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → y t ≤ sn k t := by
  let ratio := scalarComparisonRatio k y
  have hanti : AntitoneOn ratio (modelPosDomain k) :=
    antitoneOn_scalarComparisonRatio hy hW
  have hlim : Filter.Tendsto ratio (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    tendsto_div_sn_at_zero_of_initial hy0 hy1
  intro t ht
  have ht0 : 0 < t := zero_lt_of_mem_modelPosDomain ht
  by_cases hratio : ratio t ≤ 1
  · have hsnpos : 0 < sn k t := sn_pos_of_mem_modelPosDomain ht
    dsimp [ratio, scalarComparisonRatio] at hratio
    simpa using (div_le_iff₀ hsnpos).mp hratio
  · have hlt : Set.Iio t ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds ht0)
    set ε : ℝ := (ratio t - 1) / 2 with hεdef
    have hεpos : 0 < ε := by
      have : 1 < ratio t := lt_of_not_ge hratio
      linarith
    have hnear : {s : ℝ | ratio s < 1 + ε} ∈ 𝓝[>] (0 : ℝ) := by
      exact hlim.eventually (Iio_mem_nhds (by linarith [hεpos]))
    have hsmall :
        {s : ℝ | s ∈ modelPosDomain k ∧ s < t ∧ ratio s < 1 + ε} ∈ 𝓝[>] (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin, hlt, hnear] with s hs0 hst hsratio
      exact ⟨modelPosDomain_downward_closed ht hs0 hst, hst, hsratio⟩
    obtain ⟨s, hsdom, hst, hsratio⟩ :
        ∃ s : ℝ, s ∈ modelPosDomain k ∧ s < t ∧ ratio s < 1 + ε := by
      rcases (Filter.nonempty_of_mem hsmall) with ⟨s, hs⟩
      exact ⟨s, hs.1, hs.2.1, hs.2.2⟩
    have hanti_st : ratio t ≤ ratio s :=
      hanti hsdom ht hst.le
    have hlt_ratio : 1 + ε < ratio t := by
      linarith [hεdef]
    linarith

/-- Public owner theorem for scalar comparison: the Wronskian sign is now derived internally from
the honest scalar ODE/subsolution data and initial conditions. -/
theorem scalarComparison_of_subsolution
    {k : ℝ} {y : ℝ → ℝ}
    (hy0 : y 0 = 0)
    (hy1 : deriv y 0 = 1)
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    (hy2ineq :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
        HasDerivAt (deriv y) (deriv (deriv y) t) t ∧
          deriv (deriv y) t + k * y t ≤ 0) :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → y t ≤ sn k t :=
  scalarComparison_of_wronskianNonpos hy0 hy1 hy
    (scalarWronskianUpperBound_of_subsolution hy0 hy1 hy hy2ineq)

end Comparison
