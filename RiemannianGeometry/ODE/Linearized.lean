import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Data.NNReal.Basic
import ODE.Core

/-! # Short-time linearised solution operator

Given a continuous operator field `A : [a,b] → (E →L[ℝ] E)`, build the solution of the
linearised equation `J'(t) = A(t)(J(t))` with `J(t₀) = v`, and show the fixed-time evaluation
`v ↦ J_v(t)` is a continuous linear map. -/

namespace ODE.Autonomous

open Set Metric Real Filter NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## Existence for the linearised equation -/

/-- The linearised equation `J'(t) = A(t)(J(t))` with initial datum `v` has a unique solution
on a short interval around `t₀`, obtained from Picard–Lindelöf for the time-dependent linear
vector field `(t, x) ↦ A(t)(x)`.

We package the solution and its key properties. -/
structure LinearizedSolutionData
    (A : ℝ → E →L[ℝ] E) (t₀ : ℝ) (T : ℝ) (v : E) where
  /-- The solution curve. -/
  sol : ℝ → E
  /-- Initial condition. -/
  initial : sol t₀ = v
  /-- The curve solves the linearised equation on `Icc (t₀ - T) (t₀ + T)`. -/
  solves : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
    HasDerivWithinAt sol (A t (sol t)) (Icc (t₀ - T) (t₀ + T)) t
  /-- Continuity on the existence interval. -/
  continuousOn : ContinuousOn sol (Icc (t₀ - T) (t₀ + T))

set_option maxHeartbeats 800000 in
/-- Existence of the linearised solution on a short interval.

Given `A` continuous with `‖A(t)‖ ≤ M` on the interval, and time half-width `T` satisfying
`M * T * (‖v‖ + 1) ≤ 1`, the linearised ODE has a solution. -/
theorem exists_linearizedSolutionData
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ} {v : E}
    (hT : 0 < T)
    (hAcont : ContinuousOn A (Icc (t₀ - T) (t₀ + T)))
    {M : ℝ≥0}
    (hAbnd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖A t‖ ≤ M)
    (hsmall : (M : ℝ) * T * (‖v‖ + 1) ≤ 1) :
    Nonempty (LinearizedSolutionData A t₀ T v) := by
  set f : ℝ → E → E := fun t x => A t x with hf_def
  have ht₀_mem : t₀ ∈ Icc (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  set t₀' : Icc (t₀ - T) (t₀ + T) := ⟨t₀, ht₀_mem⟩
  set L : ℝ≥0 := M * (‖v‖₊ + 1) with hL_def
  have hpl : IsPicardLindelof f t₀' v 1 0 L M := {
    lipschitzOnWith := fun t ht => by
      exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hAbnd t ht)).lipschitzOnWith
    continuousOn := fun x _ => by
      exact ((ContinuousLinearMap.apply ℝ E x).continuous).comp_continuousOn hAcont
    norm_le := fun t ht x hx => by
      have hxnorm : ‖x‖ ≤ ‖v‖ + 1 := by
        have hxv : ‖x - v‖ ≤ 1 := by
          rw [← dist_eq_norm]; exact mem_closedBall.mp hx
        linarith [norm_le_insert' x v]
      calc ‖A t x‖ ≤ ‖A t‖ * ‖x‖ := (A t).le_opNorm x
        _ ≤ ↑M * (‖v‖ + 1) := by
          apply mul_le_mul (hAbnd t ht) hxnorm (norm_nonneg _) (NNReal.coe_nonneg M)
        _ = ↑L := by simp [hL_def, NNReal.coe_mul, NNReal.coe_add, coe_nnnorm]
    mul_max_le := by
      simp only [Subtype.coe_mk, NNReal.coe_zero, sub_zero]
      show (↑L : ℝ) * max ((t₀ + T) - t₀) (t₀ - (t₀ - T)) ≤ ↑(1 : ℝ≥0)
      simp only [add_sub_cancel_left, sub_sub_cancel, max_self, NNReal.coe_one]
      calc (↑L : ℝ) * T = ↑M * (‖v‖ + 1) * T := by
            simp [hL_def, NNReal.coe_mul, NNReal.coe_add, coe_nnnorm]
        _ = (↑M : ℝ) * T * (‖v‖ + 1) := by ring
        _ ≤ 1 := hsmall
  }
  obtain ⟨α, hα_init, hα_deriv⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨⟨α, hα_init, hα_deriv,
    fun t ht => (hα_deriv t ht).continuousWithinAt⟩⟩

/-! ## Linearity of the solution operator -/

set_option maxHeartbeats 400000 in
theorem linearizedSolution_add_eq
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ} {v₁ v₂ : E}
    (J₁ : LinearizedSolutionData A t₀ T v₁)
    (J₂ : LinearizedSolutionData A t₀ T v₂)
    (hT : 0 < T)
    {K : ℝ≥0}
    (hAlip : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith K (A t : E → E) univ)
    (Jsum : LinearizedSolutionData A t₀ T (v₁ + v₂)) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      Jsum.sol t = J₁.sol t + J₂.sol t := by
  have ht₀_mem : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  have hsum_cont : ContinuousOn (fun t => J₁.sol t + J₂.sol t) (Icc (t₀ - T) (t₀ + T)) :=
    J₁.continuousOn.add J₂.continuousOn
  have hJsum_deriv : ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt Jsum.sol (A t (Jsum.sol t)) t := by
    intro t ht
    exact (Jsum.solves t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hsum_deriv : ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt (fun s => J₁.sol s + J₂.sol s) (A t (J₁.sol t + J₂.sol t)) t := by
    intro t ht
    have h1 := (J₁.solves t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have h2 := (J₂.solves t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have h12 := h1.add h2
    rw [← map_add] at h12
    exact h12
  exact ODE_solution_unique_of_mem_Icc
    (v := fun t => ⇑(A t)) (s := fun _ => univ)
    (fun t ht => hAlip t (Ioo_subset_Icc_self ht))
    ht₀_mem Jsum.continuousOn hJsum_deriv (fun _ _ => mem_univ _)
    hsum_cont hsum_deriv (fun _ _ => mem_univ _)
    (by rw [Jsum.initial, J₁.initial, J₂.initial])

set_option maxHeartbeats 400000 in
theorem linearizedSolution_smul_eq
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ} {c : ℝ} {v : E}
    (J : LinearizedSolutionData A t₀ T v)
    (hT : 0 < T)
    {K : ℝ≥0}
    (hAlip : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith K (A t : E → E) univ)
    (Jc : LinearizedSolutionData A t₀ T (c • v)) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      Jc.sol t = c • J.sol t := by
  have ht₀_mem : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  exact ODE_solution_unique_of_mem_Icc
    (v := fun t => ⇑(A t)) (s := fun _ => univ)
    (fun t ht => hAlip t (Ioo_subset_Icc_self ht))
    ht₀_mem Jc.continuousOn
    (fun t ht => (Jc.solves t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ => mem_univ _) (J.continuousOn.const_smul c)
    (fun t ht => by
      have h := (J.solves t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      have hcJ := h.const_smul c
      rwa [show c • (A t) (J.sol t) = (A t) (c • J.sol t) from
        ((A t).map_smul c (J.sol t)).symm] at hcJ)
    (fun _ _ => mem_univ _)
    (by rw [Jc.initial, J.initial])

set_option maxHeartbeats 400000 in
theorem linearizedSolution_eq
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ} {v : E}
    (J₁ J₂ : LinearizedSolutionData A t₀ T v)
    (hT : 0 < T)
    {K : ℝ≥0}
    (hAlip : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith K (A t : E → E) univ) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T), J₁.sol t = J₂.sol t := by
  have ht₀_mem : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  exact ODE_solution_unique_of_mem_Icc
    (v := fun t => ⇑(A t)) (s := fun _ => univ)
    (fun t ht => hAlip t (Ioo_subset_Icc_self ht))
    ht₀_mem J₁.continuousOn
    (fun t ht => (J₁.solves t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ => mem_univ _)
    J₂.continuousOn
    (fun t ht => (J₂.solves t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ => mem_univ _)
    (by rw [J₁.initial, J₂.initial])

/-! ## Gronwall bound for the linearised solution -/

set_option maxHeartbeats 400000 in
theorem linearizedSolution_norm_le
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ} {v : E}
    (J : LinearizedSolutionData A t₀ T v)
    (hT : 0 < T)
    {M : ℝ≥0}
    (hAbnd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖A t‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    ‖J.sol t‖ ≤ ‖v‖ * exp (M * T) := by
  by_cases htge : t₀ ≤ t
  · have htt : t ∈ Icc t₀ (t₀ + T) := ⟨htge, ht.2⟩
    have hcont_sub : ContinuousOn J.sol (Icc t₀ (t₀ + T)) :=
      J.continuousOn.mono (Icc_subset_Icc (by linarith) le_rfl)
    have hderiv : ∀ s ∈ Ico t₀ (t₀ + T),
        HasDerivWithinAt J.sol (A s (J.sol s)) (Ici s) s := by
      intro s hs
      exact hasDerivWithinAt_Ici_of_Icc_symmetric
        (J.solves s ⟨by linarith [hs.1], hs.2.le⟩) hT hs.1 hs.2
    have hinit : ‖J.sol t₀‖ ≤ ‖v‖ := by rw [J.initial]
    have hbound : ∀ s ∈ Ico t₀ (t₀ + T),
        ‖A s (J.sol s)‖ ≤ ↑M * ‖J.sol s‖ + 0 := by
      intro s hs; rw [add_zero]
      exact le_trans ((A s).le_opNorm _)
        (mul_le_mul_of_nonneg_right (hAbnd s ⟨by linarith [hs.1], hs.2.le⟩) (norm_nonneg _))
    calc ‖J.sol t‖
        ≤ gronwallBound ‖v‖ ↑M 0 (t - t₀) :=
          norm_le_gronwallBound_of_norm_deriv_right_le hcont_sub hderiv hinit hbound t htt
      _ = ‖v‖ * exp (↑M * (t - t₀)) := gronwallBound_ε0 ‖v‖ ↑M (t - t₀)
      _ ≤ ‖v‖ * exp (↑M * T) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [htt.2]) (NNReal.coe_nonneg M))
  · push_neg at htge
    set t' := 2 * t₀ - t
    have ht'_gt : t₀ < t' := by linarith
    have ht'_le : t' ≤ t₀ + T := by linarith [ht.1]
    set rev : ℝ → E := fun s => J.sol (2 * t₀ - s)
    have hmaps : MapsTo (fun s => 2 * t₀ - s) (Icc t₀ t') (Icc (t₀ - T) (t₀ + T)) := by
      intro s hs; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hrev_cont : ContinuousOn rev (Icc t₀ t') :=
      J.continuousOn.comp (continuousOn_const.sub continuousOn_id) hmaps
    have hrev_deriv : ∀ s ∈ Ico t₀ t',
        HasDerivWithinAt rev (-A (2 * t₀ - s) (rev s)) (Ici s) s := by
      intro s hs
      have hJs := J.solves (2 * t₀ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      have hJs_at : HasDerivAt J.sol (A (2 * t₀ - s) (J.sol (2 * t₀ - s))) (2 * t₀ - s) :=
        hJs.hasDerivAt (Icc_mem_nhds (by linarith [hs.2]) (by linarith [hs.1]))
      have hrev_map : HasDerivAt (fun s : ℝ => 2 * t₀ - s) (-1) s := by
        convert (hasDerivAt_const s (2 * t₀)).sub (hasDerivAt_id s) using 1; ring
      have hcomp := hJs_at.scomp s hrev_map
      simp only [Function.comp_def, neg_one_smul] at hcomp
      exact hcomp.hasDerivWithinAt
    have hbound : ∀ s ∈ Ico t₀ t',
        ‖-A (2 * t₀ - s) (rev s)‖ ≤ ↑M * ‖rev s‖ + 0 := by
      intro s hs; rw [add_zero, norm_neg]
      exact le_trans ((A (2 * t₀ - s)).le_opNorm _)
        (mul_le_mul_of_nonneg_right
          (hAbnd (2 * t₀ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩) (norm_nonneg _))
    have hinit : ‖rev t₀‖ ≤ ‖v‖ := by
      show ‖J.sol (2 * t₀ - t₀)‖ ≤ ‖v‖; rw [show 2 * t₀ - t₀ = t₀ from by ring, J.initial]
    have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
      hrev_cont hrev_deriv hinit hbound t' (right_mem_Icc.mpr ht'_gt.le)
    have hgr' : ‖J.sol t‖ ≤ gronwallBound ‖v‖ ↑M 0 (t' - t₀) := by
      convert hgr using 2; simp [rev, t', show 2 * t₀ - (2 * t₀ - t) = t from by ring]
    calc ‖J.sol t‖
        ≤ gronwallBound ‖v‖ ↑M 0 (t' - t₀) := hgr'
      _ = ‖v‖ * exp (↑M * (t' - t₀)) := gronwallBound_ε0 ‖v‖ ↑M (t' - t₀)
      _ ≤ ‖v‖ * exp (↑M * T) := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.1]) (NNReal.coe_nonneg M))

/-! ## Continuous linear map at fixed time (short-time engine) -/

/-- The fixed-time evaluation of the linearised solution defines a continuous linear map,
given the short-time constraint `M * T ≤ 1/2`. -/
theorem exists_linearizedSolution_clm
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ}
    (hT : 0 < T)
    (hAcont : ContinuousOn A (Icc (t₀ - T) (t₀ + T)))
    {M : ℝ≥0}
    (hAbnd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖A t‖ ≤ M)
    (hsmall : (M : ℝ) * T ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    ∃ L : E →L[ℝ] E, ∀ v : E, ∀ (Jv : LinearizedSolutionData A t₀ T v),
      L v = Jv.sol t := by
  classical
  have hAlip : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith M (A s : E → E) univ := by
    intro s hs
    exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hAbnd s hs)).lipschitzOnWith
  have hexists : ∀ v : E, Nonempty (LinearizedSolutionData A t₀ T v) := by
    intro v
    let c : ℝ := ‖v‖ + 1
    have hc : 0 < c := by positivity
    let w : E := c⁻¹ • v
    have hw_norm_le : ‖w‖ ≤ 1 := by
      dsimp [w, c]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc, inv_mul_eq_div]
      exact (div_le_iff₀ hc).2 (by linarith)
    have hw_small : (M : ℝ) * T * (‖w‖ + 1) ≤ 1 := by
      have : (↑M : ℝ) * T * (‖w‖ + 1) ≤ (↑M : ℝ) * T * 2 := by
        apply mul_le_mul_of_nonneg_left (by linarith [hw_norm_le])
        exact mul_nonneg (NNReal.coe_nonneg M) hT.le
      linarith
    obtain ⟨Jw⟩ := exists_linearizedSolutionData hT hAcont hAbnd hw_small
    refine ⟨{ sol := fun s => c • Jw.sol s
              initial := by rw [Jw.initial]; dsimp [w, c]; rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
              solves := fun s hs => by simpa [w, c, map_smul] using (Jw.solves s hs).const_smul c
              continuousOn := Jw.continuousOn.const_smul c }⟩
  let J : ∀ v : E, LinearizedSolutionData A t₀ T v := fun v => Classical.choice (hexists v)
  have hunique :
      ∀ {v : E} (J₁ J₂ : LinearizedSolutionData A t₀ T v) {s : ℝ},
        s ∈ Icc (t₀ - T) (t₀ + T) → J₁.sol s = J₂.sol s := by
    intro v J₁ J₂ s hs
    have ht₀_mem : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
    exact ODE_solution_unique_of_mem_Icc
      (v := fun u => ⇑(A u)) (s := fun _ => univ)
      (fun u hu => hAlip u (Ioo_subset_Icc_self hu))
      ht₀_mem J₁.continuousOn
      (fun u hu => (J₁.solves u ⟨hu.1.le, hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2))
      (fun _ _ => mem_univ _) J₂.continuousOn
      (fun u hu => (J₂.solves u ⟨hu.1.le, hu.2.le⟩).hasDerivAt (Icc_mem_nhds hu.1 hu.2))
      (fun _ _ => mem_univ _) (by rw [J₁.initial, J₂.initial]) hs
  let Llin : E →ₗ[ℝ] E :=
    { toFun := fun v => (J v).sol t
      map_add' := by
        intro v₁ v₂
        simpa using linearizedSolution_add_eq (J v₁) (J v₂) hT hAlip (J (v₁ + v₂)) t ht
      map_smul' := by
        intro c v
        simpa using linearizedSolution_smul_eq (J v) hT hAlip (J (c • v)) t ht }
  let C : ℝ≥0 := ⟨exp (M * T), by positivity⟩
  refine ⟨Llin.mkContinuous C (fun v => by
    simpa [Llin, C, mul_comm] using linearizedSolution_norm_le (J v) hT hAbnd ht), ?_⟩
  intro v Jv; change Llin v = Jv.sol t; exact hunique (J v) Jv ht

/-! ## Restricting linearised solutions -/

/-- Restrict a `LinearizedSolutionData` to a subinterval centred at a different point `c`. -/
def LinearizedSolutionData.restrictCenter
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ} {v : E}
    (J : LinearizedSolutionData A t₀ T v)
    {c δ : ℝ}
    (hsub : Icc (c - δ) (c + δ) ⊆ Icc (t₀ - T) (t₀ + T)) :
    LinearizedSolutionData A c δ (J.sol c) where
  sol := J.sol
  initial := rfl
  solves t ht := (J.solves t (hsub ht)).mono hsub
  continuousOn := J.continuousOn.mono hsub

/-! ## Short-time existence on subintervals (scaling trick) -/

/-- Existence on any subinterval via the scaling trick. -/
theorem exists_linearizedSolutionData_on_sub
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ}
    (hAcont : ContinuousOn A (Icc (t₀ - T) (t₀ + T)))
    {M : ℝ≥0}
    (hAbnd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖A t‖ ≤ M)
    {c δ : ℝ} (hδ : 0 < δ) (hMδ : (↑M : ℝ) * δ ≤ 1 / 2)
    (hsub : Icc (c - δ) (c + δ) ⊆ Icc (t₀ - T) (t₀ + T))
    (v : E) :
    Nonempty (LinearizedSolutionData A c δ v) := by
  let s : ℝ := ‖v‖ + 1
  have hs : 0 < s := by positivity
  let w : E := s⁻¹ • v
  have hw_le : ‖w‖ ≤ 1 := by
    dsimp [w, s]; rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, inv_mul_eq_div]
    exact (div_le_iff₀ hs).2 (by linarith)
  have hw_small : (↑M : ℝ) * δ * (‖w‖ + 1) ≤ 1 := by
    have : (↑M : ℝ) * δ * (‖w‖ + 1) ≤ (↑M : ℝ) * δ * 2 := by
      apply mul_le_mul_of_nonneg_left (by linarith [hw_le])
      exact mul_nonneg (NNReal.coe_nonneg M) hδ.le
    linarith
  obtain ⟨Jw⟩ := exists_linearizedSolutionData hδ (hAcont.mono hsub)
    (fun t ht => hAbnd t (hsub ht)) hw_small
  exact ⟨{ sol := fun t => s • Jw.sol t
           initial := by rw [Jw.initial]; dsimp [w, s]; rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
           solves := fun t ht => by simpa [map_smul] using (Jw.solves t ht).const_smul s
           continuousOn := Jw.continuousOn.const_smul s }⟩

end ODE.Autonomous
