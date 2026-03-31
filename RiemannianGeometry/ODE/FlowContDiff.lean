import ODE.FlowFDeriv

/-! # C¹ regularity of autonomous ODE flows in initial conditions

If the vector field `F : E → E` is `C¹`, then the flow map `z ↦ flow(z, t)` is also `C¹`
as a function of the initial condition `z`, for each fixed time `t`.

The proof uses `contDiffAt_one_iff`: provides a continuous derivative function on a
neighborhood. The derivative comes from `hasFlowFDerivAtFixedTime_of_contDiff`. The
continuity of the derivative follows from the Grönwall estimate on the linearized ODE. -/

namespace ODE.Autonomous

open Set Metric Filter NNReal
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

private theorem linearizedCLM_sub_le_of_uniformCoeff
    {A B : ℝ → E →L[ℝ] E} {t₀ ε : ℝ}
    (hε : 0 < ε)
    {M : ℝ≥0}
    (hAbnd : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ‖A s‖ ≤ ↑M)
    (hBbnd : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ‖B s‖ ≤ ↑M)
    {η : ℝ} (hη : 0 ≤ η)
    (hcoeff : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ‖A s - B s‖ ≤ η)
    {t : ℝ} (ht : t ∈ Icc (t₀ - ε) (t₀ + ε))
    (JA : ∀ v : E, LinearizedSolutionData A t₀ ε v)
    (JB : ∀ v : E, LinearizedSolutionData B t₀ ε v)
    {LA LB : E →L[ℝ] E}
    (hLA : ∀ v : E, LA v = (JA v).sol t)
    (hLB : ∀ v : E, LB v = (JB v).sol t) :
    ‖LA - LB‖ ≤ η * ε * Real.exp (↑M * ε) * Real.exp (↑M * ε) := by
  have hbound_nonneg : 0 ≤ η * ε * Real.exp (↑M * ε) * Real.exp (↑M * ε) := by positivity
  rw [ContinuousLinearMap.opNorm_le_iff hbound_nonneg]
  intro v
  by_cases htge : t₀ ≤ t
  · have hB_lip : ∀ s ∈ Ico t₀ (t₀ + ε), LipschitzOnWith M (B s : E → E) univ := by
      intro s hs
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le
        (hBbnd s ⟨by linarith [hs.1], hs.2.le⟩)).lipschitzOnWith
    have hJA_cont : ContinuousOn (JA v).sol (Icc t₀ (t₀ + ε)) :=
      (JA v).continuousOn.mono (Icc_subset_Icc (by linarith) le_rfl)
    have hJB_cont : ContinuousOn (JB v).sol (Icc t₀ (t₀ + ε)) :=
      (JB v).continuousOn.mono (Icc_subset_Icc (by linarith) le_rfl)
    have hJA_deriv : ∀ s ∈ Ico t₀ (t₀ + ε),
        HasDerivWithinAt (JA v).sol (A s ((JA v).sol s)) (Ici s) s := by
      intro s hs
      exact hasDerivWithinAt_Ici_of_Icc_symmetric
        ((JA v).solves s ⟨by linarith [hs.1], hs.2.le⟩) hε hs.1 hs.2
    have hJB_deriv : ∀ s ∈ Ico t₀ (t₀ + ε),
        HasDerivWithinAt (JB v).sol (B s ((JB v).sol s)) (Ici s) s := by
      intro s hs
      exact hasDerivWithinAt_Ici_of_Icc_symmetric
        ((JB v).solves s ⟨by linarith [hs.1], hs.2.le⟩) hε hs.1 hs.2
    have hJA_err : ∀ s ∈ Ico t₀ (t₀ + ε),
        dist (A s ((JA v).sol s)) (B s ((JA v).sol s)) ≤ η * ‖v‖ * Real.exp (↑M * ε) := by
      intro s hs
      have hs_mem : s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.1], hs.2.le⟩
      calc
        dist (A s ((JA v).sol s)) (B s ((JA v).sol s))
            = ‖(A s - B s) ((JA v).sol s)‖ := by
                rw [dist_eq_norm]
                simp
        _ ≤ ‖A s - B s‖ * ‖(JA v).sol s‖ := (A s - B s).le_opNorm _
        _ ≤ η * ‖(JA v).sol s‖ := by
            exact mul_le_mul_of_nonneg_right (hcoeff s hs_mem) (norm_nonneg _)
        _ ≤ η * (‖v‖ * Real.exp (↑M * ε)) := by
            exact mul_le_mul_of_nonneg_left
              (linearizedSolution_norm_le (JA v) hε hAbnd hs_mem) hη
        _ = η * ‖v‖ * Real.exp (↑M * ε) := by ring
    have hJB_err : ∀ s ∈ Ico t₀ (t₀ + ε),
        dist (B s ((JB v).sol s)) (B s ((JB v).sol s)) ≤ 0 := by
      intro s hs
      simp
    have hinit : dist ((JA v).sol t₀) ((JB v).sol t₀) ≤ 0 := by
      rw [(JA v).initial, (JB v).initial, dist_self]
    have htt : t ∈ Icc t₀ (t₀ + ε) := ⟨htge, ht.2⟩
    have hdist := dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun s => (B s : E → E)) (s := fun _ => (univ : Set E)) (K := M)
      (f := (JA v).sol) (f' := fun s => A s ((JA v).sol s))
      (g := (JB v).sol) (g' := fun s => B s ((JB v).sol s))
      hB_lip hJA_cont hJA_deriv hJA_err (fun _ _ => mem_univ _)
      hJB_cont hJB_deriv hJB_err (fun _ _ => mem_univ _) hinit t htt
    set C_err := η * ‖v‖ * Real.exp (↑M * ε) with hCerr_def
    have hgr_bound := gronwallBound_zero_le_mul_exp
      (by positivity : 0 ≤ C_err) (by linarith : 0 ≤ t - t₀)
      (by linarith [ht.2] : t - t₀ ≤ ε) hε (NNReal.coe_nonneg M)
    calc
      ‖(LA - LB) v‖ = dist (LA v) (LB v) := by
        rw [dist_eq_norm]
        simp
      _ = dist ((JA v).sol t) ((JB v).sol t) := by rw [hLA v, hLB v]
      _ ≤ gronwallBound 0 ↑M C_err (t - t₀) := by simpa [hCerr_def] using hdist
      _ ≤ C_err * ε * Real.exp (↑M * ε) := hgr_bound
      _ = (η * ε * Real.exp (↑M * ε) * Real.exp (↑M * ε)) * ‖v‖ := by
          simp [hCerr_def]
          ring
  · push_neg at htge
    set t' := 2 * t₀ - t with ht'_def
    have ht'_gt : t₀ < t' := by linarith
    have ht'_le : t' ≤ t₀ + ε := by linarith [ht.1]
    have hJA_cont : ContinuousOn (fun s => (JA v).sol (2 * t₀ - s)) (Icc t₀ t') := by
      refine (JA v).continuousOn.comp (continuousOn_const.sub continuousOn_id) ?_
      intro s hs
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hJB_cont : ContinuousOn (fun s => (JB v).sol (2 * t₀ - s)) (Icc t₀ t') := by
      refine (JB v).continuousOn.comp (continuousOn_const.sub continuousOn_id) ?_
      intro s hs
      exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hJA_deriv : ∀ s ∈ Ico t₀ t',
        HasDerivWithinAt (fun u => (JA v).sol (2 * t₀ - u))
          (-(A (2 * t₀ - s) ((JA v).sol (2 * t₀ - s)))) (Ici s) s := by
      intro s hs
      have hs_mem : 2 * t₀ - s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hs_lo : t₀ - ε < 2 * t₀ - s := by linarith [hs.2]
      have hs_hi : 2 * t₀ - s < t₀ + ε := by linarith [hs.1]
      have hJ_at : HasDerivAt (JA v).sol (A (2 * t₀ - s) ((JA v).sol (2 * t₀ - s))) (2 * t₀ - s) :=
        ((JA v).solves (2 * t₀ - s) hs_mem).hasDerivAt (Icc_mem_nhds hs_lo hs_hi)
      have hrev : HasDerivAt (fun u : ℝ => 2 * t₀ - u) (-1) s := by
        convert (hasDerivAt_const s (2 * t₀)).sub (hasDerivAt_id s) using 1
        ring
      have hcomp := hJ_at.scomp s hrev
      simpa only [Function.comp_def, neg_one_smul] using hcomp.hasDerivWithinAt
    have hJB_deriv : ∀ s ∈ Ico t₀ t',
        HasDerivWithinAt (fun u => (JB v).sol (2 * t₀ - u))
          (-(B (2 * t₀ - s) ((JB v).sol (2 * t₀ - s)))) (Ici s) s := by
      intro s hs
      have hs_mem : 2 * t₀ - s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hs_lo : t₀ - ε < 2 * t₀ - s := by linarith [hs.2]
      have hs_hi : 2 * t₀ - s < t₀ + ε := by linarith [hs.1]
      have hJ_at : HasDerivAt (JB v).sol (B (2 * t₀ - s) ((JB v).sol (2 * t₀ - s))) (2 * t₀ - s) :=
        ((JB v).solves (2 * t₀ - s) hs_mem).hasDerivAt (Icc_mem_nhds hs_lo hs_hi)
      have hrev : HasDerivAt (fun u : ℝ => 2 * t₀ - u) (-1) s := by
        convert (hasDerivAt_const s (2 * t₀)).sub (hasDerivAt_id s) using 1
        ring
      have hcomp := hJ_at.scomp s hrev
      simpa only [Function.comp_def, neg_one_smul] using hcomp.hasDerivWithinAt
    have hJA_err : ∀ s ∈ Ico t₀ t',
        dist (-(A (2 * t₀ - s) ((JA v).sol (2 * t₀ - s))))
          (-(B (2 * t₀ - s) ((JA v).sol (2 * t₀ - s)))) ≤ η * ‖v‖ * Real.exp (↑M * ε) := by
      intro s hs
      have hs_mem : 2 * t₀ - s ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      rw [dist_eq_norm, neg_sub_neg]
      calc
        ‖(B (2 * t₀ - s)) ((JA v).sol (2 * t₀ - s)) - (A (2 * t₀ - s)) ((JA v).sol (2 * t₀ - s))‖
            = ‖(A (2 * t₀ - s) - B (2 * t₀ - s)) ((JA v).sol (2 * t₀ - s))‖ := by
              rw [show (B (2 * t₀ - s)) ((JA v).sol (2 * t₀ - s)) -
                    (A (2 * t₀ - s)) ((JA v).sol (2 * t₀ - s)) =
                    -((A (2 * t₀ - s) - B (2 * t₀ - s)) ((JA v).sol (2 * t₀ - s))) by
                    simp]
              rw [norm_neg]
        _ 
            ≤ ‖A (2 * t₀ - s) - B (2 * t₀ - s)‖ * ‖(JA v).sol (2 * t₀ - s)‖ :=
              (A (2 * t₀ - s) - B (2 * t₀ - s)).le_opNorm _
        _ ≤ η * ‖(JA v).sol (2 * t₀ - s)‖ := by
            exact mul_le_mul_of_nonneg_right (hcoeff (2 * t₀ - s) hs_mem) (norm_nonneg _)
        _ ≤ η * (‖v‖ * Real.exp (↑M * ε)) := by
            exact mul_le_mul_of_nonneg_left
              (linearizedSolution_norm_le (JA v) hε hAbnd hs_mem) hη
        _ = η * ‖v‖ * Real.exp (↑M * ε) := by ring
    have hJB_err : ∀ s ∈ Ico t₀ t',
        dist (-(B (2 * t₀ - s) ((JB v).sol (2 * t₀ - s))))
          (-(B (2 * t₀ - s) ((JB v).sol (2 * t₀ - s)))) ≤ 0 := by
      intro s hs
      simp
    have hinit : dist ((JA v).sol t₀) ((JB v).sol t₀) ≤ 0 := by
      rw [(JA v).initial, (JB v).initial, dist_self]
    have hBrev_lip : ∀ s ∈ Ico t₀ t', LipschitzOnWith M (fun y => -(B (2 * t₀ - s) y)) univ := by
      intro s hs
      rw [← one_mul M]
      exact LipschitzWith.id.neg.comp_lipschitzOnWith
        ((ContinuousLinearMap.lipschitzWith_of_opNorm_le
          (hBbnd (2 * t₀ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩)).lipschitzOnWith)
    have htt' : t' ∈ Icc t₀ t' := right_mem_Icc.mpr ht'_gt.le
    have hdist := dist_le_of_approx_trajectories_ODE_of_mem
      (v := fun s y => -(B (2 * t₀ - s) y)) (s := fun _ => (univ : Set E)) (K := M)
      (f := fun s => (JA v).sol (2 * t₀ - s))
      (f' := fun s => -(A (2 * t₀ - s) ((JA v).sol (2 * t₀ - s))))
      (g := fun s => (JB v).sol (2 * t₀ - s))
      (g' := fun s => -(B (2 * t₀ - s) ((JB v).sol (2 * t₀ - s))))
      hBrev_lip hJA_cont hJA_deriv hJA_err (fun _ _ => mem_univ _)
      hJB_cont hJB_deriv hJB_err (fun _ _ => mem_univ _)
      (by
        have h2 : 2 * t₀ - t₀ = t₀ := by ring
        change dist ((JA v).sol (2 * t₀ - t₀)) ((JB v).sol (2 * t₀ - t₀)) ≤ 0
        simpa [h2] using hinit)
      t' htt'
    set C_err := η * ‖v‖ * Real.exp (↑M * ε) with hCerr_def
    have hgr_bound := gronwallBound_zero_le_mul_exp
      (by positivity : 0 ≤ C_err) (by linarith : 0 ≤ t' - t₀)
      (by linarith [ht.1] : t' - t₀ ≤ ε) hε (NNReal.coe_nonneg M)
    have h2t : 2 * t₀ - t' = t := by
      rw [ht'_def]
      ring
    calc
      ‖(LA - LB) v‖ = dist (LA v) (LB v) := by
        rw [dist_eq_norm]
        simp
      _ = dist ((JA v).sol t) ((JB v).sol t) := by rw [hLA v, hLB v]
      _ = dist ((JA v).sol (2 * t₀ - t')) ((JB v).sol (2 * t₀ - t')) := by simpa [h2t]
      _ ≤ gronwallBound 0 ↑M C_err (t' - t₀) := by simpa [hCerr_def] using hdist
      _ ≤ C_err * ε * Real.exp (↑M * ε) := hgr_bound
      _ = (η * ε * Real.exp (↑M * ε) * Real.exp (↑M * ε)) * ‖v‖ := by
          simp [hCerr_def]
          ring

/-- The flow of a `C¹` autonomous vector field is `C¹` in the initial condition at each
fixed time. -/
theorem contDiffAt_flow_of_contDiff
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
    {t : ℝ} (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) :
    ContDiffAt ℝ 1 (fun z' => flow z' t) z := by
  classical
  let gap : ℝ := r - dist z z₀
  have hgap_pos : 0 < gap := by
    have hz_dist : dist z z₀ < r := mem_ball.mp hz
    linarith
  let ρ : ℝ := gap / 2
  have hρ_pos : 0 < ρ := by positivity
  let u : Set E := ball z ρ
  have hzu : z ∈ u := by
    simp [u, hρ_pos]
  have hu_nhds : u ∈ 𝓝 z := isOpen_ball.mem_nhds hzu
  have hu_sub_ball : u ⊆ ball z₀ r := by
    intro x hx
    rw [mem_ball] at hx ⊢
    have hxρ : dist x z < gap / 2 := by
      simpa [u, ρ] using hx
    have hz_dist : dist z z₀ < r := mem_ball.mp hz
    calc
      dist x z₀ ≤ dist x z + dist z z₀ := dist_triangle _ _ _
      _ < gap / 2 + dist z z₀ := by
        exact add_lt_add_of_lt_of_le hxρ le_rfl
      _ < r := by linarith
  have hFcont_fderiv : Continuous (fderiv ℝ F) := hF.continuous_fderiv one_ne_zero
  let hExists :
      ∀ x : E, x ∈ u →
        ∃ J : ∀ v : E, LinearizedSolutionData (fun s => fderiv ℝ F (flow x s)) t₀ ε v,
          ∃ L : E →L[ℝ] E, ∀ v : E, L v = (J v).sol t := by
    intro x hx
    have hxr : x ∈ ball z₀ r := hu_sub_ball hx
    have hxc : x ∈ closedBall z₀ r := ball_subset_closedBall hxr
    have hAcont : ContinuousOn (fun s => fderiv ℝ F (flow x s)) (Icc (t₀ - ε) (t₀ + ε)) :=
      hFcont_fderiv.continuousOn.comp (hcont x hxc) (fun s hs => hstay x hxc s hs)
    have hAbnd : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ‖fderiv ℝ F (flow x s)‖ ≤ ↑M := by
      intro s hs
      exact hMbnd (flow x s) (hstay x hxc s hs)
    exact exists_linearizedSolution_clm_on_Icc hε hAcont hAbnd ht
  let Jloc : ∀ x : E, x ∈ u → ∀ v : E,
      LinearizedSolutionData (fun s => fderiv ℝ F (flow x s)) t₀ ε v :=
    fun x hx => Classical.choose (hExists x hx)
  let Dloc : ∀ x : E, x ∈ u → E →L[ℝ] E :=
    fun x hx => Classical.choose (Classical.choose_spec (hExists x hx))
  have hDloc : ∀ x : E, ∀ hx : x ∈ u, ∀ v : E, Dloc x hx v = (Jloc x hx v).sol t := by
    intro x hx v
    exact Classical.choose_spec (Classical.choose_spec (hExists x hx)) v
  let D : E → E →L[ℝ] E := fun x =>
    if hx : x ∈ u then Dloc x hx else 0
  rw [contDiffAt_one_iff]
  refine ⟨D, u, hu_nhds, ?_, ?_⟩
  · intro x hx
    rw [Metric.continuousWithinAt_iff]
    intro c hc
    have hxc_ball : x ∈ ball z₀ r := hu_sub_ball hx
    have hxc_closed : x ∈ closedBall z₀ r := ball_subset_closedBall hxc_ball
    have hcompact : IsCompact (closedBall z₀ a) := isCompact_closedBall z₀ a
    have huc : UniformContinuousOn (fderiv ℝ F) (closedBall z₀ a) :=
      hcompact.uniformContinuousOn_of_continuous (hFcont_fderiv.continuousOn)
    rw [Metric.uniformContinuousOn_iff_le] at huc
    set C_lip : ℝ := Real.exp (↑K * ε)
    have hC_lip_pos : 0 < C_lip := by
      dsimp [C_lip]
      positivity
    have hC_lip_ge_one : 1 ≤ C_lip := by
      dsimp [C_lip]
      exact Real.one_le_exp (by positivity)
    set η₀ : ℝ := c / (2 * C_lip * ε * Real.exp (↑M * ε) * Real.exp (↑M * ε))
    have hη₀_pos : 0 < η₀ := by
      dsimp [η₀]
      positivity
    have htarget_pos :
        0 < η₀ := hη₀_pos
    obtain ⟨δ₀, hδ₀_pos, huc₀⟩ := huc η₀ htarget_pos
    refine ⟨δ₀ / C_lip, div_pos hδ₀_pos (by positivity), ?_⟩
    intro y hy hxy
    have hyr_ball : y ∈ ball z₀ r := hu_sub_ball hy
    have hyr_closed : y ∈ closedBall z₀ r := ball_subset_closedBall hyr_ball
    have hcoeff : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε),
        ‖fderiv ℝ F (flow x s) - fderiv ℝ F (flow y s)‖ ≤
          η₀ := by
      intro s hs
      have hxy' : dist x y < δ₀ / C_lip := by simpa [dist_comm] using hxy
      have hdist_flow : dist (flow x s) (flow y s) ≤ dist x y * Real.exp (↑K * ε) :=
          flow_fixedTime_dist_le hε hKlip hsolves hcont hstay hinit hxc_closed hyr_closed hs
      have hdist_le : dist (flow x s) (flow y s) ≤ δ₀ := by
        calc
          dist (flow x s) (flow y s) ≤ dist x y * C_lip := by simpa [C_lip] using hdist_flow
          _ ≤ (δ₀ / C_lip) * C_lip := by
            exact mul_le_mul_of_nonneg_right (le_of_lt hxy') hC_lip_pos.le
          _ = δ₀ := by field_simp [hC_lip_pos.ne']
      simpa [dist_eq_norm] using
        huc₀ (flow x s) (hstay x hxc_closed s hs) (flow y s) (hstay y hyr_closed s hs) hdist_le
    have hDxDy := linearizedCLM_sub_le_of_uniformCoeff
      hε
      (fun s hs => hMbnd (flow x s) (hstay x hxc_closed s hs))
      (fun s hs => hMbnd (flow y s) (hstay y hyr_closed s hs))
      (show 0 ≤ η₀ by positivity)
      hcoeff ht (Jloc x hx) (Jloc y hy) (hDloc x hx) (hDloc y hy)
    have hDxDy' : ‖Dloc x hx - Dloc y hy‖ ≤ c / (2 * C_lip) := by
      calc
        ‖Dloc x hx - Dloc y hy‖
            ≤ η₀ * ε *
                Real.exp (↑M * ε) * Real.exp (↑M * ε) := hDxDy
        _ = c / (2 * C_lip) := by
            dsimp [η₀]
            field_simp [hC_lip_pos.ne', hε.ne', Real.exp_ne_zero]
    have hDy : D y = Dloc y hy := by simp [D, hy]
    have hDx : D x = Dloc x hx := by simp [D, hx]
    have hxy_norm : dist (D x) (D y) < c := by
      rw [hDy, hDx, dist_eq_norm]
      have htwoC_pos : 0 < 2 * C_lip := by positivity
      have htwoC_gt_one : 1 < 2 * C_lip := by
        nlinarith [hC_lip_ge_one]
      have hhalf_lt : c / (2 * C_lip) < c := by
        rw [div_lt_iff₀ htwoC_pos]
        nlinarith [hc, htwoC_gt_one]
      exact lt_of_le_of_lt hDxDy' hhalf_lt
    rw [dist_comm]
    exact hxy_norm
  · intro x hx
    have hxr : x ∈ ball z₀ r := hu_sub_ball hx
    have hderiv :=
      hasFDerivAt_flowFixedTime_of_contDiff_of_linearized
        hF hr hε hKlip hsolves hcont hstay hinit hMbnd hxr ht
        (Jloc x hx) (Dloc x hx) (hDloc x hx)
    simpa [D, hx] using hderiv

end ODE.Autonomous
