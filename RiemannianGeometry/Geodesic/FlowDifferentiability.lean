import Mathlib.Analysis.Calculus.FDeriv.Basic
import Geodesic.LocalExistence
import ODE.FlowContDiff

/-! # Differentiability of the geodesic flow in initial state

This file proves that the local coordinate geodesic flow is Fréchet differentiable in the
initial-state variable at each fixed time. It specialises the generic `C¹` autonomous ODE
differentiability theorem from `ODE/FlowFDeriv` to the geodesic spray.
-/

namespace Geodesic.Coordinate

open NNReal

variable {n : ℕ}

/-- The open interior of the spatial source for the local coordinate geodesic flow. -/
def localCoordinateGeodesicFlowOpenSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) : Set (State n) :=
  Metric.ball z₀ (localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀).r

/-- Differentiability of the chosen local geodesic flow in the initial-state variable.
Uses the open ball as source (interior of the Picard-Lindelöf existence ball). -/
def HasFlowFDerivAtInitialState
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) : Prop :=
  ODE.Autonomous.HasFlowFDerivAtFixedTime
    (fun z t => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z, t))
    (localCoordinateGeodesicFlowOpenSource (n := n) Gamma t₀ z₀)
    (localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀)

/-- The geodesic spray is `C¹`, so its flow is Fréchet differentiable in the initial state. -/
theorem hasFlowFDerivAtInitialState_of_smoothChristoffel
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    HasFlowFDerivAtInitialState (n := n) Gamma t₀ z₀ := by
  -- The geodesic spray F is C¹
  have hF : ContDiff ℝ 1 (geodesicSpray (christoffelFieldOfSmooth Gamma)) :=
    (contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)
  set data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  set F := geodesicSpray (christoffelFieldOfSmooth Gamma)
  set flow := fun z t => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z, t)
  -- The flow solves the ODE
  have hsolves : ∀ x ∈ Metric.closedBall z₀ data.r,
      ∀ t ∈ Set.Icc (t₀ - data.ε) (t₀ + data.ε),
        HasDerivWithinAt (flow x) (F (flow x t))
          (Set.Icc (t₀ - data.ε) (t₀ + data.ε)) t := by
    intro x hx t ht
    have := data.isGeodesic x hx t ht
    simpa [IsCoordinateGeodesicOn, geodesicVectorField, flow,
      localCoordinateGeodesicFlow, data] using this
  have hcont : ∀ x ∈ Metric.closedBall z₀ data.r,
      ContinuousOn (flow x) (Set.Icc (t₀ - data.ε) (t₀ + data.ε)) := by
    intro x hx; exact fun t ht => (hsolves x hx t ht).continuousWithinAt
  have hstay : ∀ x ∈ Metric.closedBall z₀ data.r,
      ∀ t ∈ Set.Icc (t₀ - data.ε) (t₀ + data.ε),
        flow x t ∈ Metric.closedBall z₀ data.a := by
    intro x hx t ht; exact data.mem_closedBall x hx t ht
  have hinit : ∀ x ∈ Metric.closedBall z₀ data.r, flow x t₀ = x := by
    intro x hx; exact data.initial x hx
  -- Lipschitz bound (autonomous spray → extract at t = t₀)
  have hKlip : LipschitzOnWith data.K F (Metric.closedBall z₀ data.a) := by
    have ht₀_mem : t₀ ∈ Set.Icc (t₀ - data.ε) (t₀ + data.ε) :=
      ⟨by linarith [data.hε], by linarith [data.hε]⟩
    simpa [geodesicVectorField, F] using data.lipschitzOnWith t₀ ht₀_mem
  -- Operator norm bound
  have hFdiff : ContDiff ℝ 1 F := (contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)
  obtain ⟨M_val, hM_bound⟩ :=
    (isCompact_closedBall z₀ (data.a : ℝ)).exists_bound_of_continuousOn
      (hFdiff.continuous_fderiv one_ne_zero).continuousOn
  set M : NNReal := Real.toNNReal (max M_val 0) with hM_def
  have hMbnd : ∀ x ∈ Metric.closedBall z₀ (data.a : ℝ), ‖fderiv ℝ F x‖ ≤ ↑M := by
    intro x hx
    simp only [hM_def, Real.coe_toNNReal _ (le_max_right M_val 0)]
    exact le_trans (hM_bound x hx) (le_max_left _ _)
  -- Apply ODE theorem (returns HasFlowFDerivAtFixedTime on ball z₀ data.r)
  show ODE.Autonomous.HasFlowFDerivAtFixedTime flow
    (Metric.ball z₀ data.r) (Set.Icc (t₀ - data.ε) (t₀ + data.ε))
  exact ODE.Autonomous.hasFlowFDerivAtFixedTime_of_contDiff hF data.hr data.hε hKlip
    hsolves hcont hstay hinit hMbnd

/-- Exported: the local geodesic flow is Fréchet differentiable at interior initial states. -/
theorem hasFDerivAt_localCoordinateGeodesicFlow_initialState
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n)
    {z : State n}
    (hz : z ∈ localCoordinateGeodesicFlowOpenSource (n := n) Gamma t₀ z₀)
    {t : ℝ}
    (ht : t ∈ localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀) :
    HasFDerivAt
      (fun z' : State n =>
        localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t))
      (fderiv ℝ
        (fun z' : State n =>
          localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t)) z)
      z :=
  ODE.Autonomous.hasFDerivAt_flow_fixedTime
    (hasFlowFDerivAtInitialState_of_smoothChristoffel (n := n) Gamma t₀ z₀) hz ht

/-- Membership in the open source from membership in the closed source,
when the point is strictly interior (dist < r). -/
theorem mem_openSource_of_mem_source_interior
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n)
    {z : State n}
    (hz : z ∈ localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀)
    (hz_int : dist z z₀ < (localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀).r) :
    z ∈ localCoordinateGeodesicFlowOpenSource (n := n) Gamma t₀ z₀ :=
  Metric.mem_ball.mpr hz_int

/-- Backward-compatible wrapper consuming an explicit `hdiff` witness (now redundant). -/
theorem hasFDerivAt_localCoordinateGeodesicFlow_initialState_of_witness
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n)
    {z : State n}
    (hz : z ∈ localCoordinateGeodesicFlowOpenSource (n := n) Gamma t₀ z₀)
    {t : ℝ}
    (ht : t ∈ localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀)
    (_hdiff : HasFlowFDerivAtInitialState (n := n) Gamma t₀ z₀) :
    HasFDerivAt
      (fun z' : State n =>
        localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t))
      (fderiv ℝ
        (fun z' : State n =>
          localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t)) z)
      z :=
  hasFDerivAt_localCoordinateGeodesicFlow_initialState (n := n) Gamma t₀ z₀ hz ht

/-- Thin `DifferentiableAt` corollary for the fixed-time local geodesic flow. -/
theorem differentiableAt_localCoordinateGeodesicFlow_initialState
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n)
    {z : State n}
    (hz : z ∈ localCoordinateGeodesicFlowOpenSource (n := n) Gamma t₀ z₀)
    {t : ℝ}
    (ht : t ∈ localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀) :
    DifferentiableAt ℝ
      (fun z' : State n =>
        localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t)) z :=
  (hasFDerivAt_localCoordinateGeodesicFlow_initialState
    (n := n) Gamma t₀ z₀ hz ht).differentiableAt

/-- The fixed-time local coordinate geodesic flow is `C¹` in the initial state. -/
theorem contDiffAt_localCoordinateGeodesicFlow_initialState
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n)
    {z : State n}
    (hz : z ∈ localCoordinateGeodesicFlowOpenSource (n := n) Gamma t₀ z₀)
    {t : ℝ}
    (ht : t ∈ localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀) :
    ContDiffAt ℝ 1
      (fun z' : State n =>
        localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t)) z := by
  have hF : ContDiff ℝ 1 (geodesicSpray (christoffelFieldOfSmooth Gamma)) :=
    (contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)
  set data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  set F := geodesicSpray (christoffelFieldOfSmooth Gamma)
  set flow := fun z t => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z, t)
  have hsolves : ∀ x ∈ Metric.closedBall z₀ data.r,
      ∀ t ∈ Set.Icc (t₀ - data.ε) (t₀ + data.ε),
        HasDerivWithinAt (flow x) (F (flow x t))
          (Set.Icc (t₀ - data.ε) (t₀ + data.ε)) t := by
    intro x hx t ht
    have := data.isGeodesic x hx t ht
    simpa [IsCoordinateGeodesicOn, geodesicVectorField, flow,
      localCoordinateGeodesicFlow, data] using this
  have hcont : ∀ x ∈ Metric.closedBall z₀ data.r,
      ContinuousOn (flow x) (Set.Icc (t₀ - data.ε) (t₀ + data.ε)) := by
    intro x hx
    exact fun t ht => (hsolves x hx t ht).continuousWithinAt
  have hstay : ∀ x ∈ Metric.closedBall z₀ data.r,
      ∀ t ∈ Set.Icc (t₀ - data.ε) (t₀ + data.ε),
        flow x t ∈ Metric.closedBall z₀ data.a := by
    intro x hx t ht
    exact data.mem_closedBall x hx t ht
  have hinit : ∀ x ∈ Metric.closedBall z₀ data.r, flow x t₀ = x := by
    intro x hx
    exact data.initial x hx
  have hKlip : LipschitzOnWith data.K F (Metric.closedBall z₀ data.a) := by
    have ht₀_mem : t₀ ∈ Set.Icc (t₀ - data.ε) (t₀ + data.ε) :=
      ⟨by linarith [data.hε], by linarith [data.hε]⟩
    simpa [geodesicVectorField, F] using data.lipschitzOnWith t₀ ht₀_mem
  have hFdiff : ContDiff ℝ 1 F := (contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)
  obtain ⟨M_val, hM_bound⟩ :=
    (isCompact_closedBall z₀ (data.a : ℝ)).exists_bound_of_continuousOn
      (hFdiff.continuous_fderiv one_ne_zero).continuousOn
  set M : NNReal := Real.toNNReal (max M_val 0) with hM_def
  have hMbnd : ∀ x ∈ Metric.closedBall z₀ (data.a : ℝ), ‖fderiv ℝ F x‖ ≤ ↑M := by
    intro x hx
    simp only [hM_def, Real.coe_toNNReal _ (le_max_right M_val 0)]
    exact le_trans (hM_bound x hx) (le_max_left _ _)
  exact ODE.Autonomous.contDiffAt_flow_of_contDiff hF data.hr data.hε hKlip
    hsolves hcont hstay hinit hMbnd hz ht

/-- Variational field: the Fréchet derivative of the flow applied to a direction. -/
theorem flow_fderiv_at_initial_of_smoothChristoffel
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n)
    {z : State n}
    (hz : z ∈ localCoordinateGeodesicFlowOpenSource (n := n) Gamma t₀ z₀)
    {t : ℝ}
    (ht : t ∈ localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀)
    (w : State n) :
    HasDerivAt
      (fun s : ℝ => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z + s • w, t))
      ((fderiv ℝ
        (fun z' => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t)) z) w)
      0 := by
  have hg := hasFDerivAt_localCoordinateGeodesicFlow_initialState
    (n := n) Gamma t₀ z₀ hz ht
  have hf : HasDerivAt (fun s : ℝ => z + s • w) w 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • w) ((1 : ℝ) • w) 0 :=
      (hasDerivAt_id 0).smul_const w
    simp only [one_smul] at h1
    have h2 := (hasDerivAt_const 0 z).add h1
    rwa [show (0 : State n) + w = w from zero_add w] at h2
  have hg' : HasFDerivAt (fun z' => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t))
      (fderiv ℝ (fun z' => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z', t)) z)
      (z + (0 : ℝ) • w) := by rwa [zero_smul, add_zero]
  have h3 := hg'.comp_hasDerivAt 0 hf
  simp only [zero_smul, add_zero] at h3
  exact h3

end Geodesic.Coordinate
