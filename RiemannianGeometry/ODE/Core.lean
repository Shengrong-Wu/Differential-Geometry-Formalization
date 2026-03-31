import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.NNReal.Basic

/-! # Autonomous ODE flow adapter layer

Provides the quantitative fixed-time Lipschitz dependence estimate for autonomous local flows,
normalising the existing `HasDerivWithinAt`-on-`Icc` API to the `HasDerivWithinAt`-on-`Ici`
form required by the Gronwall theorems in Mathlib. -/

namespace ODE.Autonomous

open Set Metric Real Filter Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## Derivative conversion -/

/-- Convert `HasDerivWithinAt` on `Icc a b` at an interior point to `HasDerivWithinAt` on
`Ici t`, via upgrading to `HasDerivAt`. -/
theorem hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc
    {φ : ℝ → E} {y : E} {a b t : ℝ}
    (h : HasDerivWithinAt φ y (Icc a b) t)
    (hat : a < t) (htb : t < b) :
    HasDerivWithinAt φ y (Ici t) t :=
  (h.hasDerivAt (Icc_mem_nhds hat htb)).hasDerivWithinAt

/-- Convert `HasDerivWithinAt` on a symmetric `Icc` to `HasDerivWithinAt` on `Ici`,
for points in the forward half-open subinterval `Ico t₀ (t₀ + ε)`. -/
theorem hasDerivWithinAt_Ici_of_Icc_symmetric
    {φ : ℝ → E} {y : E} {t₀ ε t : ℝ}
    (h : HasDerivWithinAt φ y (Icc (t₀ - ε) (t₀ + ε)) t)
    (hε : 0 < ε) (hle : t₀ ≤ t) (hlt : t < t₀ + ε) :
    HasDerivWithinAt φ y (Ici t) t :=
  hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc h (by linarith) hlt

/-- Convert `HasDerivWithinAt` on `Icc a b` at an interior point to `HasDerivWithinAt` on
`Iic t`, via upgrading to `HasDerivAt`. -/
theorem hasDerivWithinAt_Iic_of_hasDerivWithinAt_Icc
    {φ : ℝ → E} {y : E} {a b t : ℝ}
    (h : HasDerivWithinAt φ y (Icc a b) t)
    (hat : a < t) (htb : t < b) :
    HasDerivWithinAt φ y (Iic t) t :=
  (h.hasDerivAt (Icc_mem_nhds hat htb)).hasDerivWithinAt

/-- Convert `HasDerivWithinAt` on a symmetric `Icc` to `HasDerivWithinAt` on `Iic`,
for points in the backward half-open subinterval `Ioc (t₀ - ε) t₀`. -/
theorem hasDerivWithinAt_Iic_of_Icc_symmetric
    {φ : ℝ → E} {y : E} {t₀ ε t : ℝ}
    (h : HasDerivWithinAt φ y (Icc (t₀ - ε) (t₀ + ε)) t)
    (hε : 0 < ε) (hlt : t₀ - ε < t) (hle : t ≤ t₀) :
    HasDerivWithinAt φ y (Iic t) t :=
  hasDerivWithinAt_Iic_of_hasDerivWithinAt_Icc h hlt (by linarith)

/-! ## Forward Gronwall for autonomous flows -/

/-- Forward distance bound for two trajectories of the same autonomous ODE on `[a, b]`. -/
theorem flow_dist_le_forward
    {F : E → E} {K : ℝ≥0} {S : Set E}
    {φ ψ : ℝ → E} {a b δ : ℝ}
    (hK : LipschitzOnWith K F S)
    (hφc : ContinuousOn φ (Icc a b))
    (hφd : ∀ t ∈ Ico a b, HasDerivWithinAt φ (F (φ t)) (Ici t) t)
    (hφS : ∀ t ∈ Ico a b, φ t ∈ S)
    (hψc : ContinuousOn ψ (Icc a b))
    (hψd : ∀ t ∈ Ico a b, HasDerivWithinAt ψ (F (ψ t)) (Ici t) t)
    (hψS : ∀ t ∈ Ico a b, ψ t ∈ S)
    (hδ : dist (φ a) (ψ a) ≤ δ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    dist (φ t) (ψ t) ≤ δ * exp (↑K * (t - a)) :=
  dist_le_of_trajectories_ODE_of_mem (v := fun _ => F) (s := fun _ => S)
    (fun t _ => hK) hφc hφd hφS hψc hψd hψS hδ t ht

/-- Approximate-trajectory Gronwall for an autonomous ODE on `[a, b]`. -/
theorem flow_approx_dist_le_forward
    {F : E → E} {K : ℝ≥0} {S : Set E}
    {φ ψ : ℝ → E} {φ' ψ' : ℝ → E} {a b δ εf εg : ℝ}
    (hK : LipschitzOnWith K F S)
    (hφc : ContinuousOn φ (Icc a b))
    (hφd : ∀ t ∈ Ico a b, HasDerivWithinAt φ (φ' t) (Ici t) t)
    (hφerr : ∀ t ∈ Ico a b, dist (φ' t) (F (φ t)) ≤ εf)
    (hφS : ∀ t ∈ Ico a b, φ t ∈ S)
    (hψc : ContinuousOn ψ (Icc a b))
    (hψd : ∀ t ∈ Ico a b, HasDerivWithinAt ψ (ψ' t) (Ici t) t)
    (hψerr : ∀ t ∈ Ico a b, dist (ψ' t) (F (ψ t)) ≤ εg)
    (hψS : ∀ t ∈ Ico a b, ψ t ∈ S)
    (hδ : dist (φ a) (ψ a) ≤ δ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    dist (φ t) (ψ t) ≤ gronwallBound δ ↑K (εf + εg) (t - a) :=
  dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ => F) (s := fun _ => S)
    (fun t _ => hK) hφc hφd hφerr hφS hψc hψd hψerr hψS hδ t ht

/-! ## Fixed-time Lipschitz estimate -/

/-- Fixed-time Lipschitz estimate for an autonomous local flow on `Icc (t₀ - ε) (t₀ + ε)`.

For two initial states `x, y` in the source ball, the flow satisfies
`dist (flow x t) (flow y t) ≤ dist x y * exp (K * ε)` for every `t` in the time domain. -/
theorem flow_fixedTime_dist_le
    {F : E → E} {K : ℝ≥0} {S : Set E}
    {flow : E → ℝ → E} {t₀ ε : ℝ} {x₀ : E} {r : ℝ}
    (hε : 0 < ε)
    (hK : LipschitzOnWith K F S)
    (hsolves : ∀ x ∈ closedBall x₀ r,
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt (flow x) (F (flow x t))
            (Icc (t₀ - ε) (t₀ + ε)) t)
    (hcont : ∀ x ∈ closedBall x₀ r,
        ContinuousOn (flow x) (Icc (t₀ - ε) (t₀ + ε)))
    (hstay : ∀ x ∈ closedBall x₀ r,
        ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), flow x t ∈ S)
    (hinit : ∀ x ∈ closedBall x₀ r, flow x t₀ = x)
    {x y : E} (hx : x ∈ closedBall x₀ r) (hy : y ∈ closedBall x₀ r)
    {t : ℝ} (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) :
    dist (flow x t) (flow y t) ≤ dist x y * exp (↑K * ε) := by
  -- Forward bound on [t₀, t₀ + ε]
  by_cases htge : t₀ ≤ t
  · -- Forward case: apply Gronwall on [t₀, t₀ + ε]
    have htt : t ∈ Icc t₀ (t₀ + ε) := ⟨htge, ht.2⟩
    -- Convert HasDerivWithinAt on full Icc to HasDerivWithinAt on Ici
    -- All points t ∈ Ico t₀ (t₀+ε) lie in Ioo(t₀-ε, t₀+ε)
    have hφd : ∀ s ∈ Ico t₀ (t₀ + ε),
        HasDerivWithinAt (flow x) (F (flow x s)) (Ici s) s := by
      intro s hs
      exact hasDerivWithinAt_Ici_of_Icc_symmetric
        (hsolves x hx s ⟨by linarith [hs.1], by linarith [hs.2]⟩) hε hs.1 hs.2
    have hψd : ∀ s ∈ Ico t₀ (t₀ + ε),
        HasDerivWithinAt (flow y) (F (flow y s)) (Ici s) s := by
      intro s hs
      exact hasDerivWithinAt_Ici_of_Icc_symmetric
        (hsolves y hy s ⟨by linarith [hs.1], by linarith [hs.2]⟩) hε hs.1 hs.2
    have hφc : ContinuousOn (flow x) (Icc t₀ (t₀ + ε)) :=
      (hcont x hx).mono (Icc_subset_Icc (by linarith) le_rfl)
    have hψc : ContinuousOn (flow y) (Icc t₀ (t₀ + ε)) :=
      (hcont y hy).mono (Icc_subset_Icc (by linarith) le_rfl)
    have hφS : ∀ s ∈ Ico t₀ (t₀ + ε), flow x s ∈ S := by
      intro s hs; exact hstay x hx s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hψS : ∀ s ∈ Ico t₀ (t₀ + ε), flow y s ∈ S := by
      intro s hs; exact hstay y hy s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hδ : dist (flow x t₀) (flow y t₀) ≤ dist x y := by
      rw [hinit x hx, hinit y hy]
    calc dist (flow x t) (flow y t)
          ≤ dist x y * exp (↑K * (t - t₀)) :=
            flow_dist_le_forward hK hφc hφd hφS hψc hψd hψS hδ htt
        _ ≤ dist x y * exp (↑K * ε) := by
            apply mul_le_mul_of_nonneg_left _ dist_nonneg
            apply exp_le_exp.mpr
            apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg K)
            linarith [ht.2]
  · -- Backward case: time reversal
    push_neg at htge
    -- We reverse time: define rev_x(s) = flow x (2*t₀ - s) on [t₀, 2*t₀ - t].
    -- Then rev_x(t₀) = flow x t₀ = x, and rev_x solves x' = -F(x).
    -- Apply forward Gronwall to -F (which has the same Lipschitz constant).
    -- Note: 2*t₀ - t ∈ (t₀, t₀+ε] since t ∈ [t₀-ε, t₀).
    have htt : t ∈ Icc (t₀ - ε) t₀ := ⟨ht.1, htge.le⟩
    -- The reversed interval endpoint
    set t' := 2 * t₀ - t with ht'_def
    have ht'_gt : t₀ < t' := by linarith
    have ht'_le : t' ≤ t₀ + ε := by linarith [ht.1]
    have htt' : t' ∈ Icc t₀ (t₀ + ε) := ⟨ht'_gt.le, ht'_le⟩
    -- -F is Lipschitz with the same constant
    have hK_neg : LipschitzOnWith K (fun x => -F x) S := by
      rw [← one_mul K]
      exact LipschitzWith.id.neg.comp_lipschitzOnWith hK
    -- Define the reversed curves
    set rev_x : ℝ → E := fun s => flow x (2 * t₀ - s) with hrev_x_def
    set rev_y : ℝ → E := fun s => flow y (2 * t₀ - s) with hrev_y_def
    -- MapsTo for the time reversal on the interval
    have hmaps : MapsTo (fun s => 2 * t₀ - s) (Icc t₀ t') (Icc (t₀ - ε) (t₀ + ε)) := by
      intro s hs; constructor <;> simp only [ht'_def] at hs <;> linarith [hs.1, hs.2]
    -- Continuity of the reversed curves on [t₀, t']
    have hrev_x_cont : ContinuousOn rev_x (Icc t₀ t') :=
      (hcont x hx).comp (continuousOn_const.sub continuousOn_id) hmaps
    have hrev_y_cont : ContinuousOn rev_y (Icc t₀ t') :=
      (hcont y hy).comp (continuousOn_const.sub continuousOn_id) hmaps
    -- The reversed curves solve x' = -F(x) on [t₀, t']
    have hrev_x_deriv : ∀ s ∈ Ico t₀ t',
        HasDerivWithinAt rev_x (-F (rev_x s)) (Ici s) s := by
      intro s hs
      -- 2*t₀ - s is in the open interior of [t₀-ε, t₀+ε]
      have hs1 : t₀ - ε < 2 * t₀ - s := by linarith [hs.2]
      have hs2 : 2 * t₀ - s < t₀ + ε := by linarith [hs.1]
      -- Upgrade flow x derivative at interior point to HasDerivAt
      have hfx := hsolves x hx (2 * t₀ - s) ⟨by linarith, by linarith⟩
      have hfx_at : HasDerivAt (flow x) (F (flow x (2 * t₀ - s))) (2 * t₀ - s) :=
        hfx.hasDerivAt (Icc_mem_nhds hs1 hs2)
      -- The time reversal map s ↦ 2*t₀ - s has derivative -1
      have hrev : HasDerivAt (fun s : ℝ => 2 * t₀ - s) (-1) s := by
        have h1 := hasDerivAt_const s (2 * t₀)
        have h2 := hasDerivAt_id s
        have h3 := h1.sub h2
        simp only [sub_zero] at h3
        convert h3 using 1
        ring
      -- Chain rule: (flow x ∘ (2*t₀ - ·)) has derivative (-1) • F(...)
      have hcomp := hfx_at.scomp s hrev
      simp only [Function.comp_def, neg_one_smul] at hcomp
      exact hcomp.hasDerivWithinAt
    have hrev_y_deriv : ∀ s ∈ Ico t₀ t',
        HasDerivWithinAt rev_y (-F (rev_y s)) (Ici s) s := by
      intro s hs
      have hs1 : t₀ - ε < 2 * t₀ - s := by linarith [hs.2]
      have hs2 : 2 * t₀ - s < t₀ + ε := by linarith [hs.1]
      have hfy := hsolves y hy (2 * t₀ - s) ⟨by linarith, by linarith⟩
      have hfy_at : HasDerivAt (flow y) (F (flow y (2 * t₀ - s))) (2 * t₀ - s) :=
        hfy.hasDerivAt (Icc_mem_nhds hs1 hs2)
      have hrev : HasDerivAt (fun s : ℝ => 2 * t₀ - s) (-1) s := by
        have h1 := hasDerivAt_const s (2 * t₀)
        have h2 := hasDerivAt_id s
        have h3 := h1.sub h2
        simp only [sub_zero] at h3
        convert h3 using 1
        ring
      have hcomp := hfy_at.scomp s hrev
      simp only [Function.comp_def, neg_one_smul] at hcomp
      exact hcomp.hasDerivWithinAt
    -- The reversed curves stay in S
    have hrev_x_S : ∀ s ∈ Ico t₀ t', rev_x s ∈ S := by
      intro s hs
      exact hstay x hx (2 * t₀ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hrev_y_S : ∀ s ∈ Ico t₀ t', rev_y s ∈ S := by
      intro s hs
      exact hstay y hy (2 * t₀ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    -- Initial conditions: rev_x(t₀) = flow x t₀ = x, similarly for y
    have hrev_init : dist (rev_x t₀) (rev_y t₀) ≤ dist x y := by
      show dist (flow x (2 * t₀ - t₀)) (flow y (2 * t₀ - t₀)) ≤ dist x y
      have : 2 * t₀ - t₀ = t₀ := by ring
      rw [this, hinit x hx, hinit y hy]
    -- Apply forward Gronwall to -F on [t₀, t']
    have hgronwall := flow_dist_le_forward hK_neg
      hrev_x_cont hrev_x_deriv hrev_x_S
      hrev_y_cont hrev_y_deriv hrev_y_S
      hrev_init (right_mem_Icc.mpr ht'_gt.le)
    -- At s = t': rev_x(t') = flow x (2*t₀ - (2*t₀-t)) = flow x t
    show dist (flow x t) (flow y t) ≤ dist x y * exp (↑K * ε)
    have h2t : 2 * t₀ - (2 * t₀ - t) = t := by ring
    simp only [hrev_x_def, hrev_y_def, ht'_def, h2t] at hgronwall
    calc dist (flow x t) (flow y t)
        ≤ dist x y * exp (↑K * (t' - t₀)) := hgronwall
      _ ≤ dist x y * exp (↑K * ε) := by
          apply mul_le_mul_of_nonneg_left _ dist_nonneg
          apply exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg K)
          linarith [ht.1]

end ODE.Autonomous
