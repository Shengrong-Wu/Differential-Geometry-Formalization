import Exponential.DexpContinuity
import Exponential.JacobiDexp
import Exponential.VariationDexp
import ODE.LinearizedGlobal
import ODE.FlowFDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace Exponential.Coordinate
open scoped Topology
open Set Filter

variable {n : ℕ}

private theorem invScaledVelocity_mem_localCoordinateGeodesicFlowOpenSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p) :
    ((p,
      (Geodesic.Coordinate.localCoordinateGeodesicFlowData
        (n := n) Gamma 0 (baseState n p)).ε⁻¹ • v) : Geodesic.Coordinate.State n) ∈
      Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource
        (n := n) Gamma 0 (baseState n p) := by
  let z₀ := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  change dist
      ((p, data.ε⁻¹ • v) : Geodesic.Coordinate.State n) z₀ < data.r
  have hvnorm : ‖v‖ < data.ε * data.r := by
    have hbal : v ∈ Metric.ball (0 : Velocity n) (data.ε * data.r) := by
      simpa [coordinateExpSource, localCoordinateExponentialSource, z₀, data] using hv
    rwa [Metric.mem_ball, dist_zero_right] at hbal
  have hscaled : ‖data.ε⁻¹ • v‖ < data.r := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos data.hε, inv_mul_eq_div]
    exact (div_lt_iff₀ data.hε).mpr
      (by linarith [mul_comm (data.r : ℝ) (data.ε : ℝ)])
  calc
    dist ((p, data.ε⁻¹ • v) : Geodesic.Coordinate.State n) z₀
        = dist (data.ε⁻¹ • v) (0 : Geodesic.Coordinate.Velocity n) := by
            simp [z₀, data, baseState, dist_prod_same_left]
    _ = ‖data.ε⁻¹ • v‖ := by rw [dist_eq_norm, sub_zero]
    _ < data.r := hscaled

private theorem scaled_unit_time_mem_localCoordinateGeodesicFlowTimeDomain
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (Geodesic.Coordinate.localCoordinateGeodesicFlowData
      (n := n) Gamma 0 (baseState n p)).ε * t ∈
      Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain
        (n := n) Gamma 0 (baseState n p) := by
  let z₀ := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  show data.ε * t ∈ Set.Icc (0 - data.ε) (0 + data.ε)
  simp only [zero_sub, zero_add]
  constructor
  · nlinarith [ht.1, data.hε]
  · nlinarith [ht.2, data.hε]

private theorem statePosition_fderiv_geodesicSpray_eq_stateVelocity
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (z y : Geodesic.Coordinate.State n) :
    Geodesic.Coordinate.statePosition n
      ((fderiv ℝ
          (Geodesic.Coordinate.geodesicSpray
            (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) z) y) =
      Geodesic.Coordinate.stateVelocity n y := by
  let F :=
    Geodesic.Coordinate.geodesicSpray
      (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
  have hF :
      HasFDerivAt F (fderiv ℝ F z) z :=
    (((Geodesic.Coordinate.contDiff_geodesicSpray (n := n) Gamma).of_le
      (by simp)).contDiffAt.differentiableAt one_ne_zero).hasFDerivAt
  have hcomp :
      HasFDerivAt
        (fun z' : Geodesic.Coordinate.State n =>
          Geodesic.Coordinate.statePosition n (F z'))
        ((ContinuousLinearMap.fst ℝ (Position n) (Velocity n)).comp (fderiv ℝ F z))
        z := by
    simpa [Geodesic.Coordinate.statePosition] using
      (ContinuousLinearMap.fst ℝ (Position n) (Velocity n)).hasFDerivAt.comp z hF
  have hsnd :
      HasFDerivAt
        (fun z' : Geodesic.Coordinate.State n =>
          Geodesic.Coordinate.statePosition n (F z'))
        (ContinuousLinearMap.snd ℝ (Position n) (Velocity n))
        z := by
    simpa [F, Geodesic.Coordinate.geodesicSpray, Geodesic.Coordinate.statePosition,
      Geodesic.Coordinate.stateVelocity] using
      (ContinuousLinearMap.snd ℝ (Position n) (Velocity n)).hasFDerivAt
  have hEq :
      (ContinuousLinearMap.fst ℝ (Position n) (Velocity n)).comp (fderiv ℝ F z) =
        ContinuousLinearMap.snd ℝ (Position n) (Velocity n) :=
    HasFDerivAt.unique hcomp hsnd
  have hEval := congrArg (fun L : Geodesic.Coordinate.State n →L[ℝ] Position n => L y) hEq
  simpa [ContinuousLinearMap.comp_apply, F, Geodesic.Coordinate.statePosition,
    Geodesic.Coordinate.stateVelocity] using hEval

/-- Along a fixed radial time-slice, the position component of the spray-built geodesic family
agrees with the corresponding line through `coordinateExp`, so the derivative in the initial
velocity direction is `t • dexp_{t • v}(w)`. This is the owner-local positional identity for the
radial variation field. -/
theorem hasDerivAt_geodesicFamily_position_line
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p)
    (w : Velocity n)
    {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ =>
        Geodesic.Coordinate.statePosition n
          ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve (v + s • w) t))
      (t • ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) w))
      0 := by
  let expMap := coordinateExp (n := n) Gamma p
  have htv : t • v ∈ coordinateExpSource (n := n) Gamma p :=
    smul_mem_coordinateExpSource (n := n) Gamma p hv ht.1 ht.2
  have hfd :
      HasFDerivAt expMap (fderiv ℝ expMap (t • v)) (t • v) :=
    (contDiffAt_coordinateExp (n := n) Gamma p htv).differentiableAt_one.hasFDerivAt
  have hline :
      HasDerivAt (fun s : ℝ => t • (v + s • w)) (t • w) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • (t • w)) (t • w) 0 := by
      simpa [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (t • w))
    have haux : HasDerivAt (fun s : ℝ => t • v + s • (t • w)) (t • w) 0 := by
      simpa [Pi.add_apply] using h1.const_add (t • v)
    convert haux using 1
    funext s
    simp [smul_add, smul_smul, mul_comm]
  have hfd' :
      HasFDerivAt expMap (fderiv ℝ expMap (t • v)) (t • (v + (0 : ℝ) • w)) := by
    simpa [zero_smul, add_zero] using hfd
  have hExp :
      HasDerivAt (fun s : ℝ => expMap (t • (v + s • w)))
        ((fderiv ℝ expMap (t • v)) (t • w))
        0 := by
    simpa [Function.comp] using hfd'.comp_hasDerivAt 0 hline
  have hExp' :
      HasDerivAt (fun s : ℝ => expMap (t • (v + s • w)))
        (t • ((fderiv ℝ expMap (t • v)) w))
        0 := by
    simpa [ContinuousLinearMap.map_smul] using hExp
  have hmem_eventually :
      ∀ᶠ s in 𝓝 (0 : ℝ), v + s • w ∈ coordinateExpSource (n := n) Gamma p := by
    have hopen : IsOpen (coordinateExpSource (n := n) Gamma p) :=
      isOpen_localCoordinateExponentialSource (n := n) p Gamma
    have hcont :
        ContinuousAt (fun s : ℝ => v + s • w) 0 :=
      ((continuous_const.add (continuous_id.smul continuous_const))).continuousAt
    have hv' : v + (0 : ℝ) • w ∈ coordinateExpSource (n := n) Gamma p := by
      simpa [zero_smul, add_zero] using hv
    exact hcont.preimage_mem_nhds (hopen.mem_nhds hv')
  have heq :
      (fun s : ℝ =>
        Geodesic.Coordinate.statePosition n
          ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve (v + s • w) t))
        =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ => expMap (t • (v + s • w))) := by
    filter_upwards [hmem_eventually] with s hs
    symm
    exact coordinateExp_smul_eq_geodesicFamily_position (n := n) Gamma p hs ht
  exact hExp'.congr_of_eventuallyEq heq

/-- The state-space variation of the spray-built geodesic family obtained by differentiating the
initial state in the pure-velocity direction. This stays owner-local and is intended for the final
radial Gauss-lemma proof. -/
noncomputable def geodesicFamilyStateVariation
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    (v w : Velocity n)
    (t : ℝ) : Geodesic.Coordinate.State n := by
  let z₀ := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let ε := data.ε
  exact
    (fderiv ℝ
      (fun z' : Geodesic.Coordinate.State n =>
        Geodesic.Coordinate.localCoordinateGeodesicFlow
          (n := n) Gamma 0 z₀ (z', ε * t))
      ((p, ε⁻¹ • v) : Geodesic.Coordinate.State n))
      ((0 : Position n), ε⁻¹ • w)

/-- The position component of the phase-space variation agrees with the explicit radial
variation field `t • dexp_{t•v}(w)`. This lets later owner proofs work with the actual
variational curve produced by the geodesic flow, rather than carrying raw `fderiv` expressions
throughout the argument. -/
theorem statePosition_geodesicFamilyStateVariation_eq
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p)
    (w : Velocity n)
    {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Geodesic.Coordinate.statePosition n
      (geodesicFamilyStateVariation (n := n) Gamma p v w t) =
      t • ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) w) := by
  let z₀ := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let ε := data.ε
  let ins : Velocity n → Geodesic.Coordinate.State n := fun u => (p, ε⁻¹ • u)
  let wstate : Geodesic.Coordinate.State n := ((0 : Position n), ε⁻¹ • w)
  have hins_mem : ins v ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource (n := n) Gamma 0 z₀ := by
    simp only [Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource, Metric.mem_ball]
    have hvnorm : ‖v‖ < data.ε * data.r := by
      have hbal : v ∈ Metric.ball (0 : Velocity n) (data.ε * data.r) := by
        simpa [coordinateExpSource, localCoordinateExponentialSource, z₀, data] using hv
      rwa [Metric.mem_ball, dist_zero_right] at hbal
    have hscaled : ‖ε⁻¹ • v‖ < data.r := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos data.hε, inv_mul_eq_div]
      exact (div_lt_iff₀ (show (0 : ℝ) < data.ε from data.hε)).mpr
        (by linarith [mul_comm (data.r : ℝ) (data.ε : ℝ)])
    calc
      dist (ins v) z₀ = dist (ε⁻¹ • v) (0 : Geodesic.Coordinate.Velocity n) := by
        simp [ins, z₀, baseState, dist_prod_same_left]
      _ = ‖ε⁻¹ • v‖ := by rw [dist_eq_norm, sub_zero]
      _ < data.r := hscaled
  have htime :
      ε * t ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
    show ε * t ∈ Set.Icc (0 - data.ε) (0 + data.ε)
    simp only [zero_sub, zero_add]
    constructor
    · nlinarith [ht.1, data.hε]
    · nlinarith [ht.2, data.hε]
  have hflow :
      HasDerivAt
        (fun s : ℝ =>
          Geodesic.Coordinate.localCoordinateGeodesicFlow
            (n := n) Gamma 0 z₀ (ins (v + s • w), ε * t))
        (geodesicFamilyStateVariation (n := n) Gamma p v w t)
        0 := by
    have hins_line :
        HasDerivAt (fun s : ℝ => ins (v + s • w)) wstate 0 := by
      have hvel :
          HasDerivAt (fun s : ℝ => ε⁻¹ • (v + s • w)) (ε⁻¹ • w) 0 := by
        have haux :
            HasDerivAt (fun s : ℝ => ε⁻¹ • v + s • (ε⁻¹ • w)) (ε⁻¹ • w) 0 := by
          have hbase := ((hasDerivAt_id (0 : ℝ)).smul_const (ε⁻¹ • w)).const_add (ε⁻¹ • v)
          simpa [one_smul, Pi.add_apply] using hbase
        simpa [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using haux
      simpa [ins, Geodesic.Coordinate.statePosition, Geodesic.Coordinate.stateVelocity] using
        (hasDerivAt_const (0 : ℝ) p).prodMk hvel
    have hfd :=
      Geodesic.Coordinate.flow_fderiv_at_initial_of_smoothChristoffel
        (n := n) Gamma 0 z₀ hins_mem htime wstate
    simpa [geodesicFamilyStateVariation, ins, wstate, zero_smul, add_zero, smul_add, smul_smul,
      z₀, data, mul_comm, mul_left_comm, mul_assoc] using hfd
  have hpos_flow :
      HasDerivAt
        (fun s : ℝ =>
          Geodesic.Coordinate.statePosition n
            (Geodesic.Coordinate.localCoordinateGeodesicFlow
              (n := n) Gamma 0 z₀ (ins (v + s • w), ε * t)))
        (Geodesic.Coordinate.statePosition n
          (geodesicFamilyStateVariation (n := n) Gamma p v w t))
        0 := by
    simpa [Geodesic.Coordinate.statePosition] using
      (ContinuousLinearMap.fst ℝ (Position n) (Velocity n)).hasFDerivAt.comp_hasDerivAt 0 hflow
  have hpos_line :
      HasDerivAt
        (fun s : ℝ =>
          Geodesic.Coordinate.statePosition n
            ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve (v + s • w) t))
        (t • ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) w))
        0 :=
    hasDerivAt_geodesicFamily_position_line (n := n) Gamma p hv w ht
  have hsame :
      (fun s : ℝ =>
        Geodesic.Coordinate.statePosition n
          (Geodesic.Coordinate.localCoordinateGeodesicFlow
            (n := n) Gamma 0 z₀ (ins (v + s • w), ε * t))) =
      (fun s : ℝ =>
        Geodesic.Coordinate.statePosition n
          ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve (v + s • w) t)) := by
    funext s
    simpa [geodesicFamilyAtBaseOfLocalCoordinateFlow, rescaledLocalCoordinateGeodesic,
      Geodesic.Coordinate.timeRescaleStateCurve, ins, z₀, data, ε, baseState, smul_add,
      smul_smul, mul_comm, mul_left_comm, mul_assoc]
  have hpos_flow' :
      HasDerivAt
        (fun s : ℝ =>
          Geodesic.Coordinate.statePosition n
            ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve (v + s • w) t))
        (Geodesic.Coordinate.statePosition n
          (geodesicFamilyStateVariation (n := n) Gamma p v w t))
        0 := by
    simpa [hsame] using hpos_flow
  exact HasDerivAt.unique hpos_flow' hpos_line

/-- The position component of the spray-built state variation solves the expected `t`-evolution
equation: its derivative is the velocity component of the same state variation, scaled by the
unit-interval time factor `ε`. This keeps the remaining radial proof on the actual variational
curve produced by the geodesic flow. -/
theorem hasDerivWithinAt_statePosition_geodesicFamilyStateVariation
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p)
    (w : Velocity n)
    {t : ℝ}
    (ht : t ∈ Ico (0 : ℝ) 1) :
    HasDerivWithinAt
      (fun τ : ℝ =>
        Geodesic.Coordinate.statePosition n
          (geodesicFamilyStateVariation (n := n) Gamma p v w τ))
      ((Geodesic.Coordinate.localCoordinateGeodesicFlowData
          (n := n) Gamma 0 (baseState n p)).ε •
        Geodesic.Coordinate.stateVelocity n
          (geodesicFamilyStateVariation (n := n) Gamma p v w t))
      (Ici t) t := by
  let z₀ := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let ε := data.ε
  let z : Geodesic.Coordinate.State n := (p, ε⁻¹ • v)
  let wstate : Geodesic.Coordinate.State n := ((0 : Position n), ε⁻¹ • w)
  let F :=
    Geodesic.Coordinate.geodesicSpray
      (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
  let flow : Geodesic.Coordinate.State n → ℝ → Geodesic.Coordinate.State n :=
    fun z' s =>
      Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z', s)
  have hz_open :
      z ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource (n := n) Gamma 0 z₀ := by
    simpa [z, z₀, data] using
      invScaledVelocity_mem_localCoordinateGeodesicFlowOpenSource (n := n) Gamma p hv
  have hz_closed : z ∈ Metric.closedBall z₀ data.r := Metric.mem_closedBall.2 (le_of_lt hz_open)
  have hFcontDiff : ContDiff ℝ 1 F :=
    (Geodesic.Coordinate.contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)
  have hsolves : ∀ x ∈ Metric.closedBall z₀ data.r,
      ∀ s ∈ Set.Icc (0 - data.ε) (0 + data.ε),
        HasDerivWithinAt (flow x) (F (flow x s))
          (Set.Icc (0 - data.ε) (0 + data.ε)) s := by
    intro x hx s hs
    have := data.isGeodesic x hx s hs
    simpa [Geodesic.Coordinate.IsCoordinateGeodesicOn, Geodesic.Coordinate.geodesicVectorField,
      flow, F, Geodesic.Coordinate.localCoordinateGeodesicFlow, data] using this
  have hcont : ∀ x ∈ Metric.closedBall z₀ data.r,
      ContinuousOn (flow x) (Set.Icc (0 - data.ε) (0 + data.ε)) := by
    intro x hx
    exact fun s hs => (hsolves x hx s hs).continuousWithinAt
  have hstay : ∀ x ∈ Metric.closedBall z₀ data.r,
      ∀ s ∈ Set.Icc (0 - data.ε) (0 + data.ε),
        flow x s ∈ Metric.closedBall z₀ data.a := by
    intro x hx s hs
    exact data.mem_closedBall x hx s hs
  have hinit : ∀ x ∈ Metric.closedBall z₀ data.r, flow x 0 = x := by
    intro x hx
    exact data.initial x hx
  have hKlip : LipschitzOnWith data.K F (Metric.closedBall z₀ data.a) := by
    have h0mem : (0 : ℝ) ∈ Set.Icc (0 - data.ε) (0 + data.ε) := by
      constructor <;> linarith [data.hε]
    simpa [Geodesic.Coordinate.geodesicVectorField, F] using data.lipschitzOnWith 0 h0mem
  obtain ⟨M_val, hM_bound⟩ :=
    (isCompact_closedBall z₀ (data.a : ℝ)).exists_bound_of_continuousOn
      (hFcontDiff.continuous_fderiv one_ne_zero).continuousOn
  set M : NNReal := Real.toNNReal (max M_val 0) with hM_def
  have hMbnd : ∀ x ∈ Metric.closedBall z₀ (data.a : ℝ), ‖fderiv ℝ F x‖ ≤ ↑M := by
    intro x hx
    simp only [hM_def, Real.coe_toNNReal _ (le_max_right M_val 0)]
    exact le_trans (hM_bound x hx) (le_max_left _ _)
  let A : ℝ → Geodesic.Coordinate.State n →L[ℝ] Geodesic.Coordinate.State n :=
    fun s => fderiv ℝ F (flow z s)
  have hAcont : ContinuousOn A (Set.Icc (0 - data.ε) (0 + data.ε)) := by
    exact ((hFcontDiff.continuous_fderiv one_ne_zero).continuousOn.comp
      (hcont z hz_closed) (fun s hs => hstay z hz_closed s hs))
  have hAbnd : ∀ s ∈ Set.Icc (0 - data.ε) (0 + data.ε), ‖A s‖ ≤ M := by
    intro s hs
    exact hMbnd (flow z s) (hstay z hz_closed s hs)
  have hAlip : ∀ s ∈ Set.Icc (0 - data.ε) (0 + data.ε),
      LipschitzOnWith M (A s : Geodesic.Coordinate.State n → Geodesic.Coordinate.State n) univ := by
    intro s hs
    exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hAbnd s hs)).lipschitzOnWith
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 - data.ε) (0 + data.ε) := by
    constructor <;> linarith [data.hε]
  obtain ⟨Jbase, _, _⟩ :=
    ODE.Autonomous.exists_linearizedSolution_clm_on_Icc
      (E := Geodesic.Coordinate.State n) data.hε hAcont hAbnd h0mem
  have hstate_eq_on :
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        geodesicFamilyStateVariation (n := n) Gamma p v w τ =
          (Jbase wstate).sol (ε * τ) := by
    intro τ hτ
    have htime :
        ε * τ ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain
          (n := n) Gamma 0 z₀ := by
      simpa [z₀, data] using
        scaled_unit_time_mem_localCoordinateGeodesicFlowTimeDomain (n := n) Gamma p hτ
    obtain ⟨Jτ, Lτ, hLτ⟩ :=
      ODE.Autonomous.exists_linearizedSolution_clm_on_Icc
        (E := Geodesic.Coordinate.State n) data.hε hAcont hAbnd htime
    have hLbase : ∀ h : Geodesic.Coordinate.State n,
        Lτ h = (Jbase h).sol (ε * τ) := by
      intro h
      rw [hLτ]
      exact ODE.Autonomous.linearizedSolution_eq (Jτ h) (Jbase h) data.hε hAlip
        (ε * τ) htime
    have hfd :
        HasFDerivAt (fun z' : Geodesic.Coordinate.State n => flow z' (ε * τ)) Lτ z := by
      exact ODE.Autonomous.hasFDerivAt_flowFixedTime_of_contDiff_of_linearized
        (E := Geodesic.Coordinate.State n) hFcontDiff data.hr data.hε hKlip
        hsolves hcont hstay hinit hMbnd hz_open htime Jbase Lτ hLbase
    have hins_line :
        HasDerivAt (fun s : ℝ => z + s • wstate) wstate 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s • wstate) ((1 : ℝ) • wstate) 0 :=
        (hasDerivAt_id 0).smul_const wstate
      simp only [one_smul] at h1
      simpa using h1.const_add z
    have hflow1 :
        HasDerivAt (fun s : ℝ => flow (z + s • wstate) (ε * τ))
          (geodesicFamilyStateVariation (n := n) Gamma p v w τ) 0 := by
      simpa [flow, z, wstate, z₀, data, geodesicFamilyStateVariation, add_zero, zero_smul] using
        Geodesic.Coordinate.flow_fderiv_at_initial_of_smoothChristoffel
          (n := n) Gamma 0 z₀ hz_open htime wstate
    have hflow2 :
        HasDerivAt (fun s : ℝ => flow (z + s • wstate) (ε * τ)) (Lτ wstate) 0 := by
      have hfd' :
          HasFDerivAt (fun z' : Geodesic.Coordinate.State n => flow z' (ε * τ)) Lτ
            (z + (0 : ℝ) • wstate) := by
        simpa [zero_smul, add_zero] using hfd
      simpa [Function.comp] using hfd'.comp_hasDerivAt 0 hins_line
    calc
      geodesicFamilyStateVariation (n := n) Gamma p v w τ = Lτ wstate :=
        HasDerivAt.unique hflow1 hflow2
      _ = (Jbase wstate).sol (ε * τ) := hLbase wstate
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have htime :
      ε * t ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain
        (n := n) Gamma 0 z₀ := by
    simpa [z₀, data] using
      scaled_unit_time_mem_localCoordinateGeodesicFlowTimeDomain (n := n) Gamma p ht_mem
  have hJ_at :
      HasDerivAt
        (fun s : ℝ => (Jbase wstate).sol s)
        (A (ε * t) ((Jbase wstate).sol (ε * t)))
        (ε * t) := by
    have hlow : 0 - data.ε < ε * t := by nlinarith [data.hε, ht.1, ht.2]
    have hhigh : ε * t < 0 + data.ε := by nlinarith [data.hε, ht.2]
    exact ((Jbase wstate).solves (ε * t) htime).hasDerivAt (Icc_mem_nhds hlow hhigh)
  have hscale : HasDerivAt (fun τ : ℝ => ε * τ) ε t := by
    simpa [mul_comm] using (hasDerivAt_const_mul (x := t) ε)
  have hcomp :
      HasDerivAt
        (fun τ : ℝ => (Jbase wstate).sol (ε * τ))
        (ε • A (ε * t) ((Jbase wstate).sol (ε * t)))
        t := by
    simpa [Function.comp] using hJ_at.scomp t hscale
  have hpos_lin :
      HasDerivAt
        (fun τ : ℝ =>
          Geodesic.Coordinate.statePosition n ((Jbase wstate).sol (ε * τ)))
        (ε • Geodesic.Coordinate.stateVelocity n ((Jbase wstate).sol (ε * t)))
        t := by
    have hraw :
        HasDerivAt
          (fun τ : ℝ =>
            Geodesic.Coordinate.statePosition n ((Jbase wstate).sol (ε * τ)))
          (Geodesic.Coordinate.statePosition n
            (ε • A (ε * t) ((Jbase wstate).sol (ε * t))))
          t := by
      simpa [Geodesic.Coordinate.statePosition] using
        (ContinuousLinearMap.fst ℝ (Position n) (Velocity n)).hasFDerivAt.comp_hasDerivAt t hcomp
    have hstate :
        Geodesic.Coordinate.statePosition n
          (A (ε * t) ((Jbase wstate).sol (ε * t))) =
        Geodesic.Coordinate.stateVelocity n ((Jbase wstate).sol (ε * t)) := by
      simpa [A] using
        statePosition_fderiv_geodesicSpray_eq_stateVelocity (n := n) Gamma
          (flow z (ε * t)) ((Jbase wstate).sol (ε * t))
    rw [show ε • Geodesic.Coordinate.stateVelocity n ((Jbase wstate).sol (ε * t)) =
        Geodesic.Coordinate.statePosition n
          (ε • A (ε * t) ((Jbase wstate).sol (ε * t))) by
          simpa [Geodesic.Coordinate.statePosition] using
            congrArg (fun u : Position n => ε • u) hstate.symm]
    exact hraw
  have heq :
      (fun τ : ℝ =>
        Geodesic.Coordinate.statePosition n
          (geodesicFamilyStateVariation (n := n) Gamma p v w τ)) =ᶠ[𝓝[Set.Ici t] t]
      (fun τ : ℝ =>
        Geodesic.Coordinate.statePosition n ((Jbase wstate).sol (ε * τ))) := by
    filter_upwards [inter_mem_nhdsWithin (Ici t) (Iio_mem_nhds ht.2)] with τ hτ
    have hτ_mem : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans ht.1 hτ.1, hτ.2.le⟩
    simpa using congrArg (Geodesic.Coordinate.statePosition n) (hstate_eq_on τ hτ_mem)
  have hderiv_lin :
      HasDerivWithinAt
        (fun τ : ℝ =>
          Geodesic.Coordinate.statePosition n ((Jbase wstate).sol (ε * τ)))
        (ε • Geodesic.Coordinate.stateVelocity n ((Jbase wstate).sol (ε * t)))
        (Ici t) t :=
    hpos_lin.hasDerivWithinAt
  have htarget :
      ε • Geodesic.Coordinate.stateVelocity n ((Jbase wstate).sol (ε * t)) =
        ε • Geodesic.Coordinate.stateVelocity n
          (geodesicFamilyStateVariation (n := n) Gamma p v w t) := by
    simpa [hstate_eq_on t ht_mem]
  have hderiv_var :
      HasDerivWithinAt
        (fun τ : ℝ =>
          Geodesic.Coordinate.statePosition n
            (geodesicFamilyStateVariation (n := n) Gamma p v w τ))
        (ε • Geodesic.Coordinate.stateVelocity n ((Jbase wstate).sol (ε * t)))
        (Ici t) t := by
    refine hderiv_lin.congr_of_eventuallyEq heq ?_
    simpa using congrArg (Geodesic.Coordinate.statePosition n) (hstate_eq_on t ht_mem)
  exact htarget ▸ hderiv_var

/-- The velocity component of the spray-built geodesic family is differentiable in the initial
velocity direction. This packages the phase-space flow derivative through the time-rescaled state
curve, so later owner proofs can work with the actual variation of the geodesic velocity field
without differentiating `fderiv` in the radial time variable. -/
theorem hasDerivAt_geodesicFamily_velocity_line
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p)
    (w : Velocity n)
    {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ =>
        Geodesic.Coordinate.stateVelocity n
          ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve (v + s • w) t))
      ((Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 (baseState n p)).ε •
        Geodesic.Coordinate.stateVelocity n
          (geodesicFamilyStateVariation (n := n) Gamma p v w t))
      0 := by
  let z₀ := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let ε := data.ε
  let ins : Velocity n → Geodesic.Coordinate.State n := fun u => (p, ε⁻¹ • u)
  let wstate : Geodesic.Coordinate.State n := ((0 : Position n), ε⁻¹ • w)
  have hins_mem : ins v ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource (n := n) Gamma 0 z₀ := by
    simp only [Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource, Metric.mem_ball]
    have hvnorm : ‖v‖ < data.ε * data.r := by
      have hbal : v ∈ Metric.ball (0 : Velocity n) (data.ε * data.r) := by
        simpa [coordinateExpSource, localCoordinateExponentialSource, z₀, data] using hv
      rwa [Metric.mem_ball, dist_zero_right] at hbal
    have hscaled : ‖ε⁻¹ • v‖ < data.r := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos data.hε, inv_mul_eq_div]
      exact (div_lt_iff₀ (show (0 : ℝ) < data.ε from data.hε)).mpr
        (by linarith [mul_comm (data.r : ℝ) (data.ε : ℝ)])
    calc
      dist (ins v) z₀ = dist (ε⁻¹ • v) (0 : Geodesic.Coordinate.Velocity n) := by
        simp [ins, z₀, baseState, dist_prod_same_left]
      _ = ‖ε⁻¹ • v‖ := by rw [dist_eq_norm, sub_zero]
      _ < data.r := hscaled
  have htime :
      ε * t ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
    show ε * t ∈ Set.Icc (0 - data.ε) (0 + data.ε)
    simp only [zero_sub, zero_add]
    constructor
    · nlinarith [ht.1, data.hε]
    · nlinarith [ht.2, data.hε]
  have hins_line :
      HasDerivAt (fun s : ℝ => ins (v + s • w))
        wstate 0 := by
    have hvel :
        HasDerivAt (fun s : ℝ => ε⁻¹ • (v + s • w)) (ε⁻¹ • w) 0 := by
      have haux :
          HasDerivAt (fun s : ℝ => ε⁻¹ • v + s • (ε⁻¹ • w)) (ε⁻¹ • w) 0 := by
        have hbase := ((hasDerivAt_id (0 : ℝ)).smul_const (ε⁻¹ • w)).const_add (ε⁻¹ • v)
        simpa [one_smul, Pi.add_apply] using hbase
      simpa [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc] using haux
    simpa [ins, Geodesic.Coordinate.statePosition, Geodesic.Coordinate.stateVelocity] using
      (hasDerivAt_const (0 : ℝ) p).prodMk hvel
  have hflow :
      HasDerivAt
        (fun s : ℝ =>
          Geodesic.Coordinate.localCoordinateGeodesicFlow
            (n := n) Gamma 0 z₀ (ins (v + s • w), ε * t))
        (geodesicFamilyStateVariation (n := n) Gamma p v w t)
        0 := by
    have hfd :=
      Geodesic.Coordinate.flow_fderiv_at_initial_of_smoothChristoffel
        (n := n) Gamma 0 z₀ hins_mem htime wstate
    simpa [geodesicFamilyStateVariation, ins, wstate, zero_smul, add_zero, smul_add, smul_smul,
      z₀, data, mul_comm, mul_left_comm, mul_assoc] using hfd
  have hvel_flow :
      HasDerivAt
        (fun s : ℝ =>
          Geodesic.Coordinate.stateVelocity n
            (Geodesic.Coordinate.localCoordinateGeodesicFlow
              (n := n) Gamma 0 z₀ (ins (v + s • w), ε * t)))
        (Geodesic.Coordinate.stateVelocity n
          (geodesicFamilyStateVariation (n := n) Gamma p v w t))
        0 := by
    simpa [Geodesic.Coordinate.stateVelocity] using
      (ContinuousLinearMap.snd ℝ (Position n) (Velocity n)).hasFDerivAt.comp_hasDerivAt 0 hflow
  have hscaled :
      HasDerivAt
        (fun s : ℝ =>
          ε •
            Geodesic.Coordinate.stateVelocity n
              (Geodesic.Coordinate.localCoordinateGeodesicFlow
                (n := n) Gamma 0 z₀ (ins (v + s • w), ε * t)))
        (ε •
          Geodesic.Coordinate.stateVelocity n
            (geodesicFamilyStateVariation (n := n) Gamma p v w t))
        0 := by
    simpa [one_smul] using hvel_flow.const_smul ε
  simpa [geodesicFamilyAtBaseOfLocalCoordinateFlow, rescaledLocalCoordinateGeodesic,
    ins, z₀, data, baseState, Geodesic.Coordinate.stateVelocity] using hscaled

/-- Along the spray-built radial family, the velocity component is exactly the directional
`dexp` in the radial direction. This is the owner-local version of the radial velocity identity
used by the remaining Gauss-lemma endgame. -/
theorem geodesicFamily_velocity_eq_fderiv_radial
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Geodesic.Coordinate.stateVelocity n
        ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v t) =
      (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v := by
  let dexp := hasDirectionalDexp_of_smoothChristoffel (n := n) Gamma p
  intro t ht
  let γ := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v
  have hvsource : v ∈ coordinateExpSource (n := n) Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) Gamma p hv
  have hcurveEq :
      Set.EqOn
        (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v))
        (fun τ : ℝ => Geodesic.Coordinate.statePosition n (γ τ))
        (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    simpa [γ] using
      coordinateExp_smul_eq_geodesicFamily_position (n := n) Gamma p hvsource hτ
  have hγgeod :
      Geodesic.Coordinate.IsCoordinateGeodesicOn
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
        γ
        (Set.Icc (-1 : ℝ) 1) := by
    simpa [γ] using coordinateExp_isCoordinateGeodesicOn (n := n) Gamma p hvsource
  rcases (Geodesic.Coordinate.isCoordinateGeodesicOn_iff_secondOrder
    (n := n) (Gamma := Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
    (gamma := γ) (s := Set.Icc (-1 : ℝ) 1)).mp hγgeod with ⟨hγpos, _⟩
  have hγpos' :
      HasDerivWithinAt
        (fun τ : ℝ => Geodesic.Coordinate.statePosition n (γ τ))
        (Geodesic.Coordinate.stateVelocity n (γ t))
        (Set.Icc (0 : ℝ) 1)
        t := by
    have hraw := hγpos t (by constructor <;> linarith [ht.1, ht.2])
    simpa [γ] using
      hraw.mono (by
        intro s hs
        exact ⟨by linarith [hs.1], hs.2⟩)
  have hline :
      HasDerivWithinAt
        (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v))
        (dexp.dexpDir (t • v) v)
        (Set.Icc (0 : ℝ) 1)
        t := by
    refine Exponential.Coordinate.hasDerivWithinAt_coordinateExp_comp
      (n := n) Gamma p dexp
      (α := fun τ : ℝ => τ • v)
      (U := fun _ : ℝ => v)
      (s := Set.Icc (0 : ℝ) 1)
      (t := t)
      ?_ ?_
    · simpa [one_smul] using
        (((hasDerivAt_id t).smul_const v).hasDerivWithinAt)
    · exact smul_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p hv ht
  have hline_fderiv :
      HasDerivWithinAt
        (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v))
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v)
        (Set.Icc (0 : ℝ) 1)
        t := by
    have hfd :
        HasFDerivAt (coordinateExp (n := n) Gamma p)
          (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v))
          (t • v) :=
      coordinateExpHasFDerivAtOnSource_of_smoothChristoffel (n := n) Gamma p
        (smul_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p hv ht)
    have hdexp_eq :
        dexp.dexpDir (t • v) v =
          (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v :=
      Exponential.Coordinate.dexpDir_eq_fderiv_of_hasFDerivAt
        (n := n) Gamma p dexp
        (smul_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p hv ht) hfd
    simpa [hdexp_eq] using hline
  have hradial :
      HasDerivWithinAt
        (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v))
        (Geodesic.Coordinate.stateVelocity n (γ t))
        (Set.Icc (0 : ℝ) 1)
        t := by
    exact hγpos'.congr_of_mem hcurveEq (by simpa using ht)
  have hUnique : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) 1) t :=
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)).uniqueDiffWithinAt (by simpa using ht)
  calc
    Geodesic.Coordinate.stateVelocity n (γ t)
      = derivWithin (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v)) (Set.Icc (0 : ℝ) 1) t := by
          symm
          exact hradial.derivWithin hUnique
    _ = (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v := by
          exact hline_fderiv.derivWithin hUnique

end Exponential.Coordinate
