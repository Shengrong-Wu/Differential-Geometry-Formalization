import ODE.Core
import ODE.UniformRemainder
import ODE.LinearizedGlobal
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Fixed-time Fréchet differentiability for autonomous ODE flows

This file proves that for a `C¹` autonomous ODE `x' = F(x)`, the fixed-time flow map
`z ↦ Φ(z, t)` is Fréchet differentiable in the initial state `z`.

The derivative is the fixed-time evaluation of the linearised equation
`J'(s) = (fderiv ℝ F (γ(s)))(J(s))`, `J(t₀) = h`. -/

namespace ODE.Autonomous

open Set Metric Real Filter Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Boundary interface (kept for backward compatibility) -/

/-- Boundary interface for fixed-time Fréchet differentiability of a local autonomous flow in the
initial state. -/
def HasFlowFDerivAtFixedTime
    (flow : E → ℝ → E) (source : Set E) (timeDomain : Set ℝ) : Prop :=
  ∀ {z : E}, z ∈ source → ∀ {t : ℝ}, t ∈ timeDomain →
    HasFDerivAt (fun z' => flow z' t) (fderiv ℝ (fun z' => flow z' t) z) z

/-- Projection theorem for the fixed-time differentiability boundary witness. -/
theorem hasFDerivAt_flow_fixedTime
    {flow : E → ℝ → E} {source : Set E} {timeDomain : Set ℝ}
    (hflow : HasFlowFDerivAtFixedTime flow source timeDomain)
    {z : E} (hz : z ∈ source) {t : ℝ} (ht : t ∈ timeDomain) :
    HasFDerivAt (fun z' => flow z' t) (fderiv ℝ (fun z' => flow z' t) z) z :=
  hflow hz ht

/-- Thin `DifferentiableAt` corollary from the fixed-time boundary witness. -/
theorem differentiableAt_flow_fixedTime
    {flow : E → ℝ → E} {source : Set E} {timeDomain : Set ℝ}
    (hflow : HasFlowFDerivAtFixedTime flow source timeDomain)
    {z : E} (hz : z ∈ source) {t : ℝ} (ht : t ∈ timeDomain) :
    DifferentiableAt ℝ (fun z' => flow z' t) z :=
  (hflow hz ht).differentiableAt

/-- Pointwise-on-source `DifferentiableOn` corollary from the fixed-time boundary witness. -/
theorem differentiableOn_flow_fixedTime
    {flow : E → ℝ → E} {source : Set E} {timeDomain : Set ℝ}
    (hflow : HasFlowFDerivAtFixedTime flow source timeDomain)
    {t : ℝ} (ht : t ∈ timeDomain) :
    DifferentiableOn ℝ (fun z' => flow z' t) source := by
  intro z hz
  exact (hflow hz ht).differentiableAt.differentiableWithinAt

/-! ## Gronwall bound for the first-order error -/

/-- **Gronwall bound on the linearisation error.** The function
`e(s) = flow(z+h, s) - flow(z, s) - J_h(s)` satisfies `‖e(t)‖ ≤ C(ε_rem) * ‖h‖`,
where `C(ε_rem) → 0` as `ε_rem → 0`.

This is the analytic core of the differentiability proof: it shows the remainder
is controlled by the Taylor defect of `F` along the reference trajectory. -/
theorem flow_linearisation_error_bound [FiniteDimensional ℝ E] [CompleteSpace E]
    {F : E → E} (hF : ContDiff ℝ 1 F)
    {flow : E → ℝ → E} {t₀ ε : ℝ} {z₀ : E} {r : ℝ} {a : ℝ}
    (hε : 0 < ε) {K : ℝ≥0}
    (hKlip : LipschitzOnWith K F (closedBall z₀ a))
    (hsolves : ∀ x ∈ closedBall z₀ r,
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt (flow x) (F (flow x t)) (Icc (t₀ - ε) (t₀ + ε)) t)
    (hcont : ∀ x ∈ closedBall z₀ r,
        ContinuousOn (flow x) (Icc (t₀ - ε) (t₀ + ε)))
    (hstay : ∀ x ∈ closedBall z₀ r,
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), flow x t ∈ closedBall z₀ a)
    (hinit : ∀ x ∈ closedBall z₀ r, flow x t₀ = x)
    {M : ℝ≥0}
    (hMbnd : ∀ x ∈ closedBall z₀ a, ‖fderiv ℝ F x‖ ≤ ↑M)
    {z : E} (hz : z ∈ closedBall z₀ r)
    {h : E} (hzh : z + h ∈ closedBall z₀ r)
    {t : ℝ} (ht : t ∈ Icc (t₀ - ε) (t₀ + ε))
    (htge : t₀ ≤ t)
    {J : LinearizedSolutionData (fun s => fderiv ℝ F (flow z s)) t₀ ε h}
    {ε_rem : ℝ} (hεrem : 0 < ε_rem)
    (htaylor : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ y : E, ‖y - flow z s‖ ≤ ‖h‖ * exp (↑K * ε) →
        ‖F y - F (flow z s) - (fderiv ℝ F (flow z s)) (y - flow z s)‖ ≤ ε_rem * ‖y - flow z s‖) :
    ‖flow (z + h) t - flow z t - J.sol t‖ ≤
      gronwallBound 0 ↑M (ε_rem * ‖h‖ * exp (↑K * ε)) (t - t₀) := by
  -- Define error e(s) = flow(z+h,s) - flow(z,s) - J.sol s
  set e : ℝ → E := fun s => flow (z + h) s - flow z s - J.sol s with he_def
  -- e(t₀) = 0
  have he_init : ‖e t₀‖ ≤ 0 := by
    simp [he_def, hinit (z + h) hzh, hinit z hz, J.initial]
  -- e is continuous
  have he_cont : ContinuousOn e (Icc t₀ (t₀ + ε)) :=
    (((hcont (z + h) hzh).sub (hcont z hz)).sub J.continuousOn).mono
      (Icc_subset_Icc (by linarith) le_rfl)
  -- Lipschitz bound: ‖flow(z+h,s) - flow(z,s)‖ ≤ ‖h‖ * exp(K*ε)
  have hflow_dist : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε),
      ‖flow (z + h) s - flow z s‖ ≤ ‖h‖ * exp (↑K * ε) := by
    intro s hs
    rw [← dist_eq_norm]
    calc dist (flow (z + h) s) (flow z s)
        ≤ dist (z + h) z * exp (↑K * ε) :=
          flow_fixedTime_dist_le hε hKlip hsolves hcont hstay hinit hzh hz hs
      _ = ‖h‖ * exp (↑K * ε) := by
          congr 1; rw [show dist (z + h) z = ‖h‖ from by simp [dist_eq_norm]]
  -- HasDerivWithinAt for e on Ici at each s ∈ Ico t₀ (t₀+ε)
  have he_deriv : ∀ s ∈ Ico t₀ (t₀ + ε),
      HasDerivWithinAt e
        (F (flow (z + h) s) - F (flow z s) - (fderiv ℝ F (flow z s)) (J.sol s))
        (Ici s) s := by
    intro s hs
    have hs_mem : s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hφ := hasDerivWithinAt_Ici_of_Icc_symmetric
      (hsolves (z + h) hzh s hs_mem) hε hs.1 hs.2
    have hψ := hasDerivWithinAt_Ici_of_Icc_symmetric
      (hsolves z hz s hs_mem) hε hs.1 hs.2
    have hJ := hasDerivWithinAt_Ici_of_Icc_symmetric
      (J.solves s ⟨by linarith [hs.1], by linarith [hs.2]⟩) hε hs.1 hs.2
    exact (hφ.sub hψ).sub hJ
  -- Norm bound on e'(s): ‖e'(s)‖ ≤ M * ‖e(s)‖ + ε_rem * ‖h‖ * exp(K*ε)
  have he_bound : ∀ s ∈ Ico t₀ (t₀ + ε),
      ‖F (flow (z + h) s) - F (flow z s) - (fderiv ℝ F (flow z s)) (J.sol s)‖ ≤
        ↑M * ‖e s‖ + ε_rem * ‖h‖ * exp (↑K * ε) := by
    intro s hs
    set φ := flow (z + h) s
    set ψ := flow z s
    -- Split: F(φ) - F(ψ) - A(J) = [F(φ) - F(ψ) - A(φ-ψ)] + A(e(s))
    have hsplit :
        F φ - F ψ - (fderiv ℝ F ψ) (J.sol s) =
          (F φ - F ψ - (fderiv ℝ F ψ) (φ - ψ)) + (fderiv ℝ F ψ) (e s) := by
      simp only [he_def, map_sub, φ, ψ]
      abel
    rw [hsplit]
    have hs_mem : s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    calc ‖(F φ - F ψ - (fderiv ℝ F ψ) (φ - ψ)) + (fderiv ℝ F ψ) (e s)‖
        ≤ ‖F φ - F ψ - (fderiv ℝ F ψ) (φ - ψ)‖ + ‖(fderiv ℝ F ψ) (e s)‖ := norm_add_le _ _
      _ ≤ ε_rem * ‖φ - ψ‖ + ‖fderiv ℝ F ψ‖ * ‖e s‖ := by
          apply add_le_add
          · exact htaylor s hs_mem φ (hflow_dist s hs_mem)
          · exact (fderiv ℝ F ψ).le_opNorm (e s)
      _ ≤ ε_rem * (‖h‖ * exp (↑K * ε)) + ↑M * ‖e s‖ := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hflow_dist s hs_mem) hεrem.le
          · exact mul_le_mul_of_nonneg_right
              (hMbnd ψ (hstay z hz s hs_mem)) (norm_nonneg _)
      _ = ↑M * ‖e s‖ + ε_rem * ‖h‖ * exp (↑K * ε) := by ring
  -- Apply Gronwall
  have htt : t ∈ Icc t₀ (t₀ + ε) := ⟨htge, ht.2⟩
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    he_cont he_deriv he_init he_bound t htt
  exact hgronwall

/-! ## Gronwall arithmetic helpers -/

/-- `exp(x) - 1 ≤ x * exp(x)` for all `x : ℝ`. -/
theorem exp_sub_one_le_mul_exp (x : ℝ) : exp x - 1 ≤ x * exp x := by
  have h1 := add_one_le_exp (-x)
  have h2 : exp (-x) * exp x = 1 := by rw [← exp_add]; simp
  nlinarith [exp_nonneg x]

/-- **Gronwall bound with zero initial condition.**
`gronwallBound(0, M, C, T) ≤ C * ε * exp(M * ε)` when `0 ≤ T ≤ ε`, `0 ≤ M`, `0 ≤ C`. -/
theorem gronwallBound_zero_le_mul_exp {M C T ε : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hTε : T ≤ ε) (hε : 0 < ε) (hM : 0 ≤ M) :
    gronwallBound 0 M C T ≤ C * ε * exp (M * ε) := by
  by_cases hM0 : M = 0
  · rw [gronwallBound, if_pos hM0]; simp only [zero_mul, zero_add]
    calc C * T ≤ C * ε := mul_le_mul_of_nonneg_left hTε hC
      _ ≤ C * ε * exp (M * ε) := by
          rw [hM0, zero_mul, exp_zero]; linarith [mul_nonneg hC hε.le]
  · rw [gronwallBound, if_neg hM0]; simp only [zero_mul, zero_add]
    have hM_pos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    calc C / M * (exp (M * T) - 1)
        ≤ C / M * (M * T * exp (M * T)) :=
          mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp (M * T))
            (div_nonneg hC hM_pos.le)
      _ ≤ C * ε * exp (M * ε) := by
          have : C / M * (M * T * exp (M * T)) = C * T * exp (M * T) := by
            field_simp
          linarith [mul_le_mul (mul_le_mul_of_nonneg_left hTε hC)
            (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hTε hM_pos.le))
            (exp_nonneg _) (by positivity : 0 ≤ C * ε)]

/-! ## Fixed-time derivative from a supplied linearized family -/

set_option maxHeartbeats 3200000 in
/-- If the fixed-time evaluation map `L` is already identified with a chosen linearized
solution family along the reference trajectory, then `L` is the Fréchet derivative of the
fixed-time flow map. This is the internal explicit-derivative form used by
`ODE/FlowContDiff.lean`. -/
theorem hasFDerivAt_flowFixedTime_of_contDiff_of_linearized
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {F : E → E} (hF : ContDiff ℝ 1 F)
    {flow : E → ℝ → E} {t₀ ε : ℝ} {z₀ : E} {r : ℝ} (hr : 0 < r) {a : ℝ}
    (hε : 0 < ε)
    {K : ℝ≥0}
    (hKlip : LipschitzOnWith K F (closedBall z₀ a))
    (hsolves : ∀ x ∈ closedBall z₀ r,
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt (flow x) (F (flow x t))
            (Icc (t₀ - ε) (t₀ + ε)) t)
    (hcont : ∀ x ∈ closedBall z₀ r,
        ContinuousOn (flow x) (Icc (t₀ - ε) (t₀ + ε)))
    (hstay : ∀ x ∈ closedBall z₀ r,
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), flow x t ∈ closedBall z₀ a)
    (hinit : ∀ x ∈ closedBall z₀ r, flow x t₀ = x)
    {M : ℝ≥0}
    (hMbnd : ∀ x ∈ closedBall z₀ a, ‖fderiv ℝ F x‖ ≤ ↑M)
    {z : E} (hz : z ∈ ball z₀ r)
    {t : ℝ} (ht : t ∈ Icc (t₀ - ε) (t₀ + ε))
    (J_family : ∀ h : E,
      LinearizedSolutionData (fun s => fderiv ℝ F (flow z s)) t₀ ε h)
    (L : E →L[ℝ] E)
    (hL : ∀ h : E, L h = (J_family h).sol t) :
    HasFDerivAt (fun z' => flow z' t) L z := by
  have hFcont_fderiv : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  have hz_closed : z ∈ closedBall z₀ r := ball_subset_closedBall hz
  have hz_dist : dist z z₀ < r := mem_ball.mp hz
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set C_lip := exp (↑K * ε) with hClip_def
  set C_gr := C_lip * ε * exp (↑M * ε) + 1 with hCgr_def
  have hCgr_pos : 0 < C_gr := by positivity
  set ε_rem := c / (2 * C_gr) with hεrem_def
  have hεrem_pos : 0 < ε_rem := div_pos hc (by positivity)
  obtain ⟨ρ_taylor, hρ_taylor_pos, htaylor_raw⟩ :=
    tube_remainder_estimate hF (hcont z hz_closed) hεrem_pos
  set gap := r - dist z z₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith [hz_dist]
  set ρ := min (min (ρ_taylor / (C_lip + 1)) (gap / 2)) 1 with hρ_def
  have hρ_pos : 0 < ρ := by
    apply lt_min
    · apply lt_min
      · exact div_pos hρ_taylor_pos (by positivity)
      · linarith
    · exact one_pos
  rw [Filter.Eventually, Metric.mem_nhds_iff]
  refine ⟨ρ, hρ_pos, ?_⟩
  intro h hh
  rw [mem_ball, dist_zero_right] at hh
  have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hh (min_le_right _ _)
  have hhr : ‖h‖ < gap / 2 := lt_of_lt_of_le hh
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hh_taylor : ‖h‖ * C_lip < ρ_taylor := by
    have hClip_pos' : (0 : ℝ) < C_lip + 1 := by positivity
    have : ‖h‖ < ρ_taylor / (C_lip + 1) :=
      lt_of_lt_of_le hh (le_trans (min_le_left _ _) (min_le_left _ _))
    have hClip_le : C_lip ≤ C_lip + 1 := le_add_of_nonneg_right one_pos.le
    calc ‖h‖ * C_lip ≤ ‖h‖ * (C_lip + 1) :=
          mul_le_mul_of_nonneg_left hClip_le (norm_nonneg _)
      _ < ρ_taylor / (C_lip + 1) * (C_lip + 1) :=
          mul_lt_mul_of_pos_right this hClip_pos'
      _ = ρ_taylor := div_mul_cancel₀ ρ_taylor hClip_pos'.ne'
  have hzh : z + h ∈ closedBall z₀ r := by
    rw [mem_closedBall]
    have h1 : dist (z + h) z₀ ≤ dist (z + h) z + dist z z₀ := dist_triangle _ z _
    have h2 : dist (z + h) z = ‖h‖ := by simp [dist_eq_norm]
    linarith
  let Jh := J_family h
  have htaylor_adapted : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε),
      ∀ y : E, ‖y - flow z s‖ ≤ ‖h‖ * exp (↑K * ε) →
        ‖F y - F (flow z s) - (fderiv ℝ F (flow z s)) (y - flow z s)‖ ≤
          ε_rem * ‖y - flow z s‖ := by
    intro s hs y hy
    exact htaylor_raw s hs y (le_trans hy hh_taylor.le)
  have hLh : L h = Jh.sol t := hL h
  show ‖flow (z + h) t - flow z t - L h‖ ≤ c * ‖h‖
  rw [show flow (z + h) t - flow z t - L h =
      flow (z + h) t - flow z t - Jh.sol t by rw [hLh]]
  by_cases htge : t₀ ≤ t
  · have herr := @flow_linearisation_error_bound E _ _ _ _ F hF flow t₀ ε z₀ r a
      hε K hKlip hsolves hcont hstay hinit M hMbnd z hz_closed h hzh t ht htge
      (J := Jh) ε_rem hεrem_pos htaylor_adapted
    calc ‖flow (z + h) t - flow z t - Jh.sol t‖
        ≤ gronwallBound 0 ↑M (ε_rem * ‖h‖ * exp (↑K * ε)) (t - t₀) := herr
      _ ≤ c * ‖h‖ := by
          set C_err := ε_rem * ‖h‖ * exp (↑K * ε) with hCerr_def
          have hgr_bound := gronwallBound_zero_le_mul_exp
            (by positivity : 0 ≤ C_err) (by linarith : 0 ≤ t - t₀)
            (by linarith [ht.2] : t - t₀ ≤ ε) hε (NNReal.coe_nonneg M)
          calc gronwallBound 0 ↑M C_err (t - t₀)
              ≤ C_err * ε * exp (↑M * ε) := hgr_bound
            _ = ε_rem * ‖h‖ * (C_lip * ε * exp (↑M * ε)) := by
                simp only [hCerr_def, hClip_def]; ring
            _ ≤ ε_rem * ‖h‖ * C_gr := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                linarith [show (0 : ℝ) < 1 from one_pos]
            _ = c / (2 * C_gr) * ‖h‖ * C_gr := by rw [hεrem_def]
            _ = c / 2 * ‖h‖ := by
                have hCgr_ne : C_gr ≠ 0 := ne_of_gt hCgr_pos
                field_simp
            _ ≤ c * ‖h‖ := by nlinarith [norm_nonneg h]
  · push_neg at htge
    set t' := 2 * t₀ - t with ht'_def
    have ht'_gt : t₀ < t' := by linarith
    have ht'_le : t' ≤ t₀ + ε := by linarith [ht.1]
    set e_rev : ℝ → E := fun s =>
      flow (z + h) (2 * t₀ - s) - flow z (2 * t₀ - s) - Jh.sol (2 * t₀ - s) with he_rev_def
    have he_rev_init : ‖e_rev t₀‖ ≤ 0 := by
      simp [he_rev_def, show 2 * t₀ - t₀ = t₀ from by ring,
            hinit (z + h) hzh, hinit z hz_closed, Jh.initial]
    have hmaps : MapsTo (fun s => 2 * t₀ - s) (Icc t₀ t') (Icc (t₀ - ε) (t₀ + ε)) := by
      intro s hs; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have he_rev_cont : ContinuousOn e_rev (Icc t₀ t') := by
      apply ContinuousOn.sub
      · apply ContinuousOn.sub
        · exact (hcont (z + h) hzh).comp (continuousOn_const.sub continuousOn_id) hmaps
        · exact (hcont z hz_closed).comp (continuousOn_const.sub continuousOn_id) hmaps
      · exact Jh.continuousOn.comp (continuousOn_const.sub continuousOn_id) hmaps
    have he_rev_deriv : ∀ s ∈ Ico t₀ t',
        HasDerivWithinAt e_rev
          (-(F (flow (z + h) (2 * t₀ - s)) - F (flow z (2 * t₀ - s)) -
            (fderiv ℝ F (flow z (2 * t₀ - s))) (Jh.sol (2 * t₀ - s))))
          (Ici s) s := by
      intro s hs
      have hs_rev : 2 * t₀ - s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hs_int_lo : t₀ - ε < 2 * t₀ - s := by linarith [hs.2]
      have hs_int_hi : 2 * t₀ - s < t₀ + ε := by linarith [hs.1]
      have hφ := (hsolves (z + h) hzh (2 * t₀ - s) hs_rev).hasDerivAt
        (Icc_mem_nhds hs_int_lo hs_int_hi)
      have hψ := (hsolves z hz_closed (2 * t₀ - s) hs_rev).hasDerivAt
        (Icc_mem_nhds hs_int_lo hs_int_hi)
      have hJ := (Jh.solves (2 * t₀ - s) hs_rev).hasDerivAt
        (Icc_mem_nhds hs_int_lo hs_int_hi)
      have hrev_map : HasDerivAt (fun s : ℝ => 2 * t₀ - s) (-1) s := by
        convert (hasDerivAt_const s (2 * t₀)).sub (hasDerivAt_id s) using 1
        ring
      have hcomp := ((hφ.sub hψ).sub hJ).scomp s hrev_map
      simp only [Function.comp_def, neg_one_smul] at hcomp
      exact hcomp.hasDerivWithinAt
    have he_rev_bound : ∀ s ∈ Ico t₀ t',
        ‖-(F (flow (z + h) (2 * t₀ - s)) - F (flow z (2 * t₀ - s)) -
          (fderiv ℝ F (flow z (2 * t₀ - s))) (Jh.sol (2 * t₀ - s)))‖ ≤
          ↑M * ‖e_rev s‖ + ε_rem * ‖h‖ * exp (↑K * ε) := by
      intro s hs
      rw [norm_neg]
      have hs_rev : 2 * t₀ - s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hflow_dist_bwd : ∀ u ∈ Icc (t₀ - ε) (t₀ + ε),
          ‖flow (z + h) u - flow z u‖ ≤ ‖h‖ * exp (↑K * ε) := by
        intro u hu
        rw [← dist_eq_norm]
        calc dist (flow (z + h) u) (flow z u)
            ≤ dist (z + h) z * exp (↑K * ε) :=
              flow_fixedTime_dist_le hε hKlip hsolves hcont hstay hinit hzh hz_closed hu
          _ = ‖h‖ * exp (↑K * ε) := by
              congr 1
              rw [show dist (z + h) z = ‖h‖ from by simp [dist_eq_norm]]
      set φ_rev := flow (z + h) (2 * t₀ - s)
      set ψ_rev := flow z (2 * t₀ - s)
      have hsplit :
          F φ_rev - F ψ_rev - (fderiv ℝ F ψ_rev) (Jh.sol (2 * t₀ - s)) =
            (F φ_rev - F ψ_rev - (fderiv ℝ F ψ_rev) (φ_rev - ψ_rev)) +
            (fderiv ℝ F ψ_rev) (e_rev s) := by
        simp only [he_rev_def, map_sub, φ_rev, ψ_rev]
        abel
      rw [hsplit]
      calc ‖(F φ_rev - F ψ_rev - (fderiv ℝ F ψ_rev) (φ_rev - ψ_rev)) +
            (fderiv ℝ F ψ_rev) (e_rev s)‖
          ≤ ‖F φ_rev - F ψ_rev - (fderiv ℝ F ψ_rev) (φ_rev - ψ_rev)‖ +
              ‖(fderiv ℝ F ψ_rev) (e_rev s)‖ := norm_add_le _ _
        _ ≤ ε_rem * ‖φ_rev - ψ_rev‖ + ‖fderiv ℝ F ψ_rev‖ * ‖e_rev s‖ := by
            apply add_le_add
            · exact htaylor_adapted (2 * t₀ - s) hs_rev φ_rev (hflow_dist_bwd (2 * t₀ - s) hs_rev)
            · exact (fderiv ℝ F ψ_rev).le_opNorm (e_rev s)
        _ ≤ ε_rem * (‖h‖ * exp (↑K * ε)) + ↑M * ‖e_rev s‖ := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left (hflow_dist_bwd (2 * t₀ - s) hs_rev) hεrem_pos.le
            · exact mul_le_mul_of_nonneg_right
                (hMbnd ψ_rev (hstay z hz_closed (2 * t₀ - s) hs_rev)) (norm_nonneg _)
        _ = ↑M * ‖e_rev s‖ + ε_rem * ‖h‖ * exp (↑K * ε) := by ring
    have hgr_rev := norm_le_gronwallBound_of_norm_deriv_right_le
      he_rev_cont he_rev_deriv he_rev_init he_rev_bound t' (right_mem_Icc.mpr ht'_gt.le)
    have h2t : 2 * t₀ - (2 * t₀ - t) = t := by ring
    simp only [he_rev_def, ht'_def, h2t] at hgr_rev
    set C_err := ε_rem * ‖h‖ * exp (↑K * ε) with hCerr_def
    have hgr_bound := gronwallBound_zero_le_mul_exp
      (by positivity : 0 ≤ C_err) (by linarith : 0 ≤ t' - t₀)
      (by linarith [ht.1] : t' - t₀ ≤ ε) hε (NNReal.coe_nonneg M)
    calc ‖flow (z + h) t - flow z t - Jh.sol t‖
        ≤ gronwallBound 0 ↑M C_err (t' - t₀) := hgr_rev
      _ ≤ C_err * ε * exp (↑M * ε) := hgr_bound
      _ = ε_rem * ‖h‖ * (C_lip * ε * exp (↑M * ε)) := by
          simp only [hCerr_def, hClip_def]
          ring
      _ ≤ ε_rem * ‖h‖ * C_gr := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [show (0 : ℝ) < 1 from one_pos]
      _ = c / (2 * C_gr) * ‖h‖ * C_gr := by rw [hεrem_def]
      _ = c / 2 * ‖h‖ := by
          have hCgr_ne : C_gr ≠ 0 := ne_of_gt hCgr_pos
          field_simp
      _ ≤ c * ‖h‖ := by nlinarith [norm_nonneg h]

/-! ## The main theorem -/

set_option maxHeartbeats 3200000 in
/-- **Fixed-time Fréchet differentiability for a C¹ autonomous local flow.**

Given a `C¹` vector field `F : E → E` and a local flow solving `x' = F(x)` on
`Icc (t₀ - ε) (t₀ + ε)`, the fixed-time map `z ↦ flow z t` is Fréchet differentiable
at every interior point of the source ball.

No public smallness hypothesis on `M * ε`. The global linearised CLM from
`ODE/Linearized.lean` removes the short-time constraint internally. -/
theorem hasFlowFDerivAtFixedTime_of_contDiff [FiniteDimensional ℝ E] [CompleteSpace E]
    {F : E → E} (hF : ContDiff ℝ 1 F)
    {flow : E → ℝ → E} {t₀ ε : ℝ} {z₀ : E} {r : ℝ} (hr : 0 < r) {a : ℝ}
    (hε : 0 < ε)
    {K : ℝ≥0}
    (hKlip : LipschitzOnWith K F (closedBall z₀ a))
    (hsolves : ∀ x ∈ closedBall z₀ r,
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt (flow x) (F (flow x t))
            (Icc (t₀ - ε) (t₀ + ε)) t)
    (hcont : ∀ x ∈ closedBall z₀ r,
        ContinuousOn (flow x) (Icc (t₀ - ε) (t₀ + ε)))
    (hstay : ∀ x ∈ closedBall z₀ r,
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), flow x t ∈ closedBall z₀ a)
    (hinit : ∀ x ∈ closedBall z₀ r, flow x t₀ = x)
    {M : ℝ≥0}
    (hMbnd : ∀ x ∈ closedBall z₀ a, ‖fderiv ℝ F x‖ ≤ ↑M) :
    HasFlowFDerivAtFixedTime flow (ball z₀ r) (Icc (t₀ - ε) (t₀ + ε)) := by
  have hFdiff : Differentiable ℝ F := (contDiff_one_iff_fderiv.mp hF).1
  have hFcont_fderiv : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  intro z hz t ht
  have hz_closed : z ∈ closedBall z₀ r := ball_subset_closedBall hz
  have hz_dist : dist z z₀ < r := mem_ball.mp hz
  suffices hda : DifferentiableAt ℝ (fun z' => flow z' t) z from hda.hasFDerivAt
  rw [show DifferentiableAt ℝ (fun z' => flow z' t) z ↔
      ∃ L' : E →L[ℝ] E, HasFDerivAt (fun z' => flow z' t) L' z from
      ⟨fun hd => ⟨_, hd.hasFDerivAt⟩, fun ⟨L', hL'⟩ => hL'.differentiableAt⟩]
  -- The linearised coefficient field
  set A : ℝ → E →L[ℝ] E := fun s => fderiv ℝ F (flow z s) with hA_def
  have hAcont : ContinuousOn A (Icc (t₀ - ε) (t₀ + ε)) :=
    hFcont_fderiv.continuousOn.comp (hcont z hz_closed) (fun s hs => hstay z hz_closed s hs)
  have hAbnd : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ‖A s‖ ≤ ↑M :=
    fun s hs => hMbnd (flow z s) (hstay z hz_closed s hs)
  -- Get global CLM and solution family at time t (no smallness hypothesis)
  obtain ⟨J_family, L, hL⟩ := exists_linearizedSolution_clm_on_Icc hε hAcont hAbnd ht
  refine ⟨L, ?_⟩
  -- Prove HasFDerivAt (fun z' => flow z' t) L z via isLittleO
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  -- Get Taylor remainder radius for ε_rem chosen to make the Gronwall bound ≤ c * ‖h‖
  set C_lip := exp (↑K * ε) with hClip_def
  set C_gr := C_lip * ε * exp (↑M * ε) + 1 with hCgr_def
  have hCgr_pos : 0 < C_gr := by positivity
  set ε_rem := c / (2 * C_gr) with hεrem_def
  have hεrem_pos : 0 < ε_rem := div_pos hc (by positivity)
  -- Tube remainder bound
  obtain ⟨ρ_taylor, hρ_taylor_pos, htaylor_raw⟩ :=
    tube_remainder_estimate hF (hcont z hz_closed) hεrem_pos
  -- Choose ρ using the gap to the boundary
  set gap := r - dist z z₀ with hgap_def
  have hgap_pos : 0 < gap := by linarith [hz_dist]
  set ρ := min (min (ρ_taylor / (C_lip + 1)) (gap / 2)) 1 with hρ_def
  have hρ_pos : 0 < ρ := by
    apply lt_min; apply lt_min
    · exact div_pos hρ_taylor_pos (by positivity)
    · linarith
    · exact one_pos
  -- Eventually in 𝓝 0
  rw [Filter.Eventually, Metric.mem_nhds_iff]
  exact ⟨ρ, hρ_pos, fun h hh => by
    rw [mem_ball, dist_zero_right] at hh
    -- ‖h‖ < ρ, so ‖h‖ < 1, ‖h‖ < r/2, ‖h‖ * C_lip < ρ_taylor
    have hh1 : ‖h‖ < 1 := lt_of_lt_of_le hh (min_le_right _ _)
    have hhr : ‖h‖ < gap / 2 := lt_of_lt_of_le hh
      (le_trans (min_le_left _ _) (min_le_right _ _))
    have hh_taylor : ‖h‖ * C_lip < ρ_taylor := by
      have hClip_pos' : (0 : ℝ) < C_lip + 1 := by positivity
      have : ‖h‖ < ρ_taylor / (C_lip + 1) :=
        lt_of_lt_of_le hh (le_trans (min_le_left _ _) (min_le_left _ _))
      have hClip_le : C_lip ≤ C_lip + 1 := le_add_of_nonneg_right one_pos.le
      calc ‖h‖ * C_lip ≤ ‖h‖ * (C_lip + 1) :=
            mul_le_mul_of_nonneg_left hClip_le (norm_nonneg _)
        _ < ρ_taylor / (C_lip + 1) * (C_lip + 1) :=
            mul_lt_mul_of_pos_right this hClip_pos'
        _ = ρ_taylor := div_mul_cancel₀ ρ_taylor hClip_pos'.ne'
    -- z + h ∈ closedBall z₀ r (since z ∈ ball z₀ r and ‖h‖ < gap/2)
    have hzh : z + h ∈ closedBall z₀ r := by
      rw [mem_closedBall]
      have h1 : dist (z + h) z₀ ≤ dist (z + h) z + dist z z₀ := dist_triangle _ z _
      have h2 : dist (z + h) z = ‖h‖ := by simp [dist_eq_norm]
      linarith
    -- Get linearised solution from the global family
    let Jh := J_family h
    -- Taylor remainder condition for flow_linearisation_error_bound
    have htaylor_adapted : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε),
        ∀ y : E, ‖y - flow z s‖ ≤ ‖h‖ * exp (↑K * ε) →
          ‖F y - F (flow z s) - (fderiv ℝ F (flow z s)) (y - flow z s)‖ ≤
            ε_rem * ‖y - flow z s‖ := by
      intro s hs y hy
      exact htaylor_raw s hs y (le_trans hy hh_taylor.le)
    -- Apply forward/backward Gronwall
    have hLh : L h = Jh.sol t := hL h
    show ‖flow (z + h) t - flow z t - L h‖ ≤ c * ‖h‖
    rw [show flow (z + h) t - flow z t - L h =
        flow (z + h) t - flow z t - Jh.sol t by rw [hLh]]
    by_cases htge : t₀ ≤ t
    · -- Forward case
      have herr := @flow_linearisation_error_bound E _ _ _ _ F hF flow t₀ ε z₀ r a
        hε K hKlip hsolves hcont hstay hinit M hMbnd z hz_closed h hzh t ht htge
        (J := Jh) ε_rem hεrem_pos htaylor_adapted
      calc ‖flow (z + h) t - flow z t - Jh.sol t‖
          ≤ gronwallBound 0 ↑M (ε_rem * ‖h‖ * exp (↑K * ε)) (t - t₀) := herr
        _ ≤ c * ‖h‖ := by
            -- gronwallBound(0, M, C, T) with δ=0:
            -- If M = 0: = C * T ≤ C * ε
            -- If M ≠ 0: = C/M * (exp(M*T) - 1) ≤ C * T * exp(M*T) ≤ C * ε * exp(M*ε)
            -- Either way: ≤ (ε_rem * ‖h‖ * C_lip) * ε * exp(M*ε) + 0
            --           = ε_rem * ‖h‖ * (C_lip * ε * exp(M*ε))
            --           ≤ ε_rem * ‖h‖ * C_gr
            --           = c/(2*C_gr) * ‖h‖ * C_gr = c*‖h‖/2 ≤ c*‖h‖
            -- gronwallBound(0, M, C, s) with C = ε_rem * ‖h‖ * C_lip, s = t - t₀
            -- Case M = 0: = C * s ≤ C * ε
            -- Case M ≠ 0: = (C/M) * (exp(M*s) - 1) ≤ C * s * exp(M*s) ≤ C * ε * exp(M*ε)
            -- Either way: ≤ ε_rem * ‖h‖ * C_lip * ε * exp(M*ε)
            --           ≤ ε_rem * ‖h‖ * C_gr = (c/(2*C_gr)) * ‖h‖ * C_gr = c/2 * ‖h‖ ≤ c * ‖h‖
            set C_err := ε_rem * ‖h‖ * exp (↑K * ε) with hCerr_def
            have hgr_bound := gronwallBound_zero_le_mul_exp
              (by positivity : 0 ≤ C_err) (by linarith : 0 ≤ t - t₀)
              (by linarith [ht.2] : t - t₀ ≤ ε) hε (NNReal.coe_nonneg M)
            calc gronwallBound 0 ↑M C_err (t - t₀)
                ≤ C_err * ε * exp (↑M * ε) := hgr_bound
              _ = ε_rem * ‖h‖ * (C_lip * ε * exp (↑M * ε)) := by
                  simp only [hCerr_def, hClip_def]; ring
              _ ≤ ε_rem * ‖h‖ * C_gr := by
                  apply mul_le_mul_of_nonneg_left _ (by positivity)
                  linarith [show (0 : ℝ) < 1 from one_pos]
              _ = c / (2 * C_gr) * ‖h‖ * C_gr := by rw [hεrem_def]
              _ = c / 2 * ‖h‖ := by
                  have hCgr_ne : C_gr ≠ 0 := ne_of_gt hCgr_pos
                  field_simp
              _ ≤ c * ‖h‖ := by nlinarith [norm_nonneg h]
    · -- Backward case: time-reverse the error to [t₀, 2t₀-t] and apply forward Gronwall.
      push_neg at htge
      set t' := 2 * t₀ - t with ht'_def
      have ht'_gt : t₀ < t' := by linarith
      have ht'_le : t' ≤ t₀ + ε := by linarith [ht.1]
      -- The forward error bound at t' ≥ t₀ gives:
      -- ‖flow(z+h, t') - flow(z, t') - Jh.sol t'‖ ≤ gronwall bound
      -- But we need the bound at t, not t'.
      -- Key: the error at t can be bounded by the REVERSED Gronwall on [t₀, t'].
      -- Define: rev_e(s) = e(2t₀-s) = flow(z+h, 2t₀-s) - flow(z, 2t₀-s) - Jh.sol(2t₀-s).
      -- Then rev_e(t₀) = e(t₀) and rev_e(t') = e(2t₀-t') = e(t).
      -- The derivative of rev_e satisfies the same M-Lipschitz + C_err inequality.
      -- By forward Gronwall on [t₀, t']: ‖rev_e(t')‖ ≤ gronwallBound 0 M C_err (t'-t₀).
      -- Then the same arithmetic as the forward case gives ≤ c * ‖h‖.

      -- Apply the forward error bound theorem at t' (which satisfies t₀ ≤ t')
      have ht'_mem : t' ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith, ht'_le⟩
      have herr' := @flow_linearisation_error_bound E _ _ _ _ F hF flow t₀ ε z₀ r a
        hε K hKlip hsolves hcont hstay hinit M hMbnd z hz_closed h hzh t' ht'_mem
        (le_of_lt ht'_gt) (J := Jh) ε_rem hεrem_pos htaylor_adapted
      -- ‖flow(z+h,t') - flow(z,t') - Jh.sol t'‖ ≤ gronwallBound 0 M C_err (t'-t₀)
      -- Now: t' - t₀ = t₀ - t ≤ ε, so the same arithmetic applies.
      -- But we need the bound at t, not at t'. We need a different approach.

      -- DIRECT approach: use the backward Gronwall on the error curve.
      -- The error e(s) = flow(z+h,s) - flow(z,s) - Jh.sol(s) satisfies:
      -- e(t₀) = 0 and ‖e'(s)‖ ≤ M*‖e(s)‖ + C_err for the same C_err.
      -- By the backward version of Gronwall (time-reverse):
      -- ‖e(t)‖ ≤ gronwallBound 0 M C_err (t₀ - t) since t < t₀.
      -- And t₀ - t ≤ ε, so the same final arithmetic gives ≤ c*‖h‖.

      -- Define the reversed error
      set e_rev : ℝ → E := fun s =>
        flow (z + h) (2 * t₀ - s) - flow z (2 * t₀ - s) - Jh.sol (2 * t₀ - s) with he_rev_def
      -- e_rev(t₀) = e(t₀) = 0, e_rev(t') = e(t)
      have he_rev_init : ‖e_rev t₀‖ ≤ 0 := by
        simp [he_rev_def, show 2 * t₀ - t₀ = t₀ from by ring,
              hinit (z + h) hzh, hinit z hz_closed, Jh.initial]
      -- e_rev is continuous on [t₀, t']
      have hmaps : MapsTo (fun s => 2 * t₀ - s) (Icc t₀ t') (Icc (t₀ - ε) (t₀ + ε)) := by
        intro s hs; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have he_rev_cont : ContinuousOn e_rev (Icc t₀ t') := by
        apply ContinuousOn.sub
        · apply ContinuousOn.sub
          · exact (hcont (z + h) hzh).comp (continuousOn_const.sub continuousOn_id) hmaps
          · exact (hcont z hz_closed).comp (continuousOn_const.sub continuousOn_id) hmaps
        · exact Jh.continuousOn.comp (continuousOn_const.sub continuousOn_id) hmaps
      -- HasDerivWithinAt for e_rev: derivative is the negated error derivative
      -- ‖e_rev'(s)‖ = ‖-e'(2t₀-s)‖ = ‖e'(2t₀-s)‖ ≤ M*‖e(2t₀-s)‖ + C_err = M*‖e_rev(s)‖ + C_err
      -- This gives the forward Gronwall inequality for e_rev on [t₀, t'].
      have he_rev_deriv : ∀ s ∈ Ico t₀ t',
          HasDerivWithinAt e_rev
            (-(F (flow (z + h) (2 * t₀ - s)) - F (flow z (2 * t₀ - s)) -
              (fderiv ℝ F (flow z (2 * t₀ - s))) (Jh.sol (2 * t₀ - s))))
            (Ici s) s := by
        intro s hs
        have hs_rev : 2 * t₀ - s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
        have hs_int_lo : t₀ - ε < 2 * t₀ - s := by linarith [hs.2]
        have hs_int_hi : 2 * t₀ - s < t₀ + ε := by linarith [hs.1]
        -- Derivatives of each component at 2t₀-s, then compose with reversal map
        have hφ := (hsolves (z + h) hzh (2 * t₀ - s) hs_rev).hasDerivAt
          (Icc_mem_nhds hs_int_lo hs_int_hi)
        have hψ := (hsolves z hz_closed (2 * t₀ - s) hs_rev).hasDerivAt
          (Icc_mem_nhds hs_int_lo hs_int_hi)
        have hJ := (Jh.solves (2 * t₀ - s) hs_rev).hasDerivAt
          (Icc_mem_nhds hs_int_lo hs_int_hi)
        have hrev_map : HasDerivAt (fun s : ℝ => 2 * t₀ - s) (-1) s := by
          convert (hasDerivAt_const s (2 * t₀)).sub (hasDerivAt_id s) using 1; ring
        have hcomp := ((hφ.sub hψ).sub hJ).scomp s hrev_map
        simp only [Function.comp_def, neg_one_smul] at hcomp
        exact hcomp.hasDerivWithinAt
      -- Norm bound on e_rev'(s)
      have he_rev_bound : ∀ s ∈ Ico t₀ t',
          ‖-(F (flow (z + h) (2 * t₀ - s)) - F (flow z (2 * t₀ - s)) -
            (fderiv ℝ F (flow z (2 * t₀ - s))) (Jh.sol (2 * t₀ - s)))‖ ≤
            ↑M * ‖e_rev s‖ + ε_rem * ‖h‖ * exp (↑K * ε) := by
        intro s hs
        rw [norm_neg]
        have hs_rev : 2 * t₀ - s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
        -- Lipschitz bound for flow distance (same as in flow_linearisation_error_bound)
        have hflow_dist_bwd : ∀ u ∈ Icc (t₀ - ε) (t₀ + ε),
            ‖flow (z + h) u - flow z u‖ ≤ ‖h‖ * exp (↑K * ε) := by
          intro u hu
          rw [← dist_eq_norm]
          calc dist (flow (z + h) u) (flow z u)
              ≤ dist (z + h) z * exp (↑K * ε) :=
                flow_fixedTime_dist_le hε hKlip hsolves hcont hstay hinit hzh hz_closed hu
            _ = ‖h‖ * exp (↑K * ε) := by
                congr 1; rw [show dist (z + h) z = ‖h‖ from by simp [dist_eq_norm]]
        -- Same splitting as forward case
        set φ_rev := flow (z + h) (2 * t₀ - s)
        set ψ_rev := flow z (2 * t₀ - s)
        have hsplit :
            F φ_rev - F ψ_rev - (fderiv ℝ F ψ_rev) (Jh.sol (2 * t₀ - s)) =
              (F φ_rev - F ψ_rev - (fderiv ℝ F ψ_rev) (φ_rev - ψ_rev)) +
              (fderiv ℝ F ψ_rev) (e_rev s) := by
          simp only [he_rev_def, map_sub, φ_rev, ψ_rev]; abel
        rw [hsplit]
        calc ‖(F φ_rev - F ψ_rev - (fderiv ℝ F ψ_rev) (φ_rev - ψ_rev)) +
              (fderiv ℝ F ψ_rev) (e_rev s)‖
            ≤ ‖F φ_rev - F ψ_rev - (fderiv ℝ F ψ_rev) (φ_rev - ψ_rev)‖ +
              ‖(fderiv ℝ F ψ_rev) (e_rev s)‖ := norm_add_le _ _
          _ ≤ ε_rem * ‖φ_rev - ψ_rev‖ + ‖fderiv ℝ F ψ_rev‖ * ‖e_rev s‖ := by
              apply add_le_add
              · exact htaylor_adapted (2 * t₀ - s) hs_rev φ_rev (hflow_dist_bwd (2 * t₀ - s) hs_rev)
              · exact (fderiv ℝ F ψ_rev).le_opNorm (e_rev s)
          _ ≤ ε_rem * (‖h‖ * exp (↑K * ε)) + ↑M * ‖e_rev s‖ := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left (hflow_dist_bwd (2 * t₀ - s) hs_rev) hεrem_pos.le
              · exact mul_le_mul_of_nonneg_right
                  (hMbnd ψ_rev (hstay z hz_closed (2 * t₀ - s) hs_rev)) (norm_nonneg _)
          _ = ↑M * ‖e_rev s‖ + ε_rem * ‖h‖ * exp (↑K * ε) := by ring
      -- Apply forward Gronwall to e_rev on [t₀, t']
      have hgr_rev := norm_le_gronwallBound_of_norm_deriv_right_le
        he_rev_cont he_rev_deriv he_rev_init he_rev_bound t' (right_mem_Icc.mpr ht'_gt.le)
      -- e_rev(t') = e(2t₀-t') = e(t)
      have h2t : 2 * t₀ - (2 * t₀ - t) = t := by ring
      simp only [he_rev_def, ht'_def, h2t] at hgr_rev
      -- ‖e(t)‖ ≤ gronwallBound 0 M (ε_rem*‖h‖*C_lip) (t'-t₀) = gronwallBound 0 M C_err (t₀-t)
      -- Same arithmetic as forward case since t'-t₀ = t₀-t ≤ ε
      set C_err := ε_rem * ‖h‖ * exp (↑K * ε) with hCerr_def
      have hgr_bound := gronwallBound_zero_le_mul_exp
        (by positivity : 0 ≤ C_err) (by linarith : 0 ≤ t' - t₀)
        (by linarith [ht.1] : t' - t₀ ≤ ε) hε (NNReal.coe_nonneg M)
      calc ‖flow (z + h) t - flow z t - Jh.sol t‖
          ≤ gronwallBound 0 ↑M C_err (t' - t₀) := hgr_rev
        _ ≤ C_err * ε * exp (↑M * ε) := hgr_bound
        _ = ε_rem * ‖h‖ * (C_lip * ε * exp (↑M * ε)) := by
            simp only [hCerr_def, hClip_def]; ring
        _ ≤ ε_rem * ‖h‖ * C_gr := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [show (0 : ℝ) < 1 from one_pos]
        _ = c / (2 * C_gr) * ‖h‖ * C_gr := by rw [hεrem_def]
        _ = c / 2 * ‖h‖ := by
            have hCgr_ne : C_gr ≠ 0 := ne_of_gt hCgr_pos
            field_simp
        _ ≤ c * ‖h‖ := by nlinarith [norm_nonneg h]
  ⟩

end ODE.Autonomous
