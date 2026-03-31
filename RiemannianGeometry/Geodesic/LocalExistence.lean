import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Data.NNReal.Basic
import Geodesic.Spray

/-! This file packages the local spray flow used downstream as the source of truth for the
spray-owned radial domain and the coordinate exponential map. -/

namespace Geodesic.Coordinate

open Set ODE

variable {n : ℕ}

/-- Picard-Lindelöf gives local existence for the coordinate geodesic spray. -/
theorem exists_isCoordinateGeodesicOn_Icc_of_isPicardLindelof
    {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {z₀ z : State n} {a r L K : NNReal}
    {Gamma : ChristoffelField n}
    (hpl : IsPicardLindelof (geodesicVectorField Gamma) t₀ z₀ a r L K)
    (hz : z ∈ Metric.closedBall z₀ r) :
    ∃ gamma : ℝ → State n, gamma t₀ = z ∧
      IsCoordinateGeodesicOn Gamma gamma (Set.Icc tmin tmax) := by
  obtain ⟨gamma, hgamma0, hgamma⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hz
  refine ⟨gamma, hgamma0, ?_⟩
  intro t ht
  simpa [IsCoordinateGeodesicOn] using hgamma t ht

theorem exists_isCoordinateGeodesicOn_Icc_of_isPicardLindelof_self
    {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {z₀ : State n} {a r L K : NNReal}
    {Gamma : ChristoffelField n}
    (hpl : IsPicardLindelof (geodesicVectorField Gamma) t₀ z₀ a r L K) :
    ∃ gamma : ℝ → State n, gamma t₀ = z₀ ∧
      IsCoordinateGeodesicOn Gamma gamma (Set.Icc tmin tmax) := by
  exact exists_isCoordinateGeodesicOn_Icc_of_isPicardLindelof hpl (by simp)

/-- Choose one coordinate geodesic produced by Picard-Lindelof for the given initial state. -/
noncomputable def someCoordinateGeodesicOn_Icc
    {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {z₀ : State n} {a r L K : NNReal}
    {Gamma : ChristoffelField n}
    (hpl : IsPicardLindelof (geodesicVectorField Gamma) t₀ z₀ a r L K) :
    ℝ → State n :=
  Classical.choose (exists_isCoordinateGeodesicOn_Icc_of_isPicardLindelof_self (z₀ := z₀) hpl)

theorem someCoordinateGeodesicOn_Icc_initial
    {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {z₀ : State n} {a r L K : NNReal}
    {Gamma : ChristoffelField n}
    (hpl : IsPicardLindelof (geodesicVectorField Gamma) t₀ z₀ a r L K) :
    someCoordinateGeodesicOn_Icc (z₀ := z₀) hpl t₀ = z₀ :=
  (Classical.choose_spec
    (exists_isCoordinateGeodesicOn_Icc_of_isPicardLindelof_self (z₀ := z₀) hpl)).1

theorem someCoordinateGeodesicOn_Icc_isCoordinateGeodesicOn
    {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {z₀ : State n} {a r L K : NNReal}
    {Gamma : ChristoffelField n}
    (hpl : IsPicardLindelof (geodesicVectorField Gamma) t₀ z₀ a r L K) :
    IsCoordinateGeodesicOn Gamma (someCoordinateGeodesicOn_Icc (z₀ := z₀) hpl)
      (Set.Icc tmin tmax) :=
  (Classical.choose_spec
    (exists_isCoordinateGeodesicOn_Icc_of_isPicardLindelof_self (z₀ := z₀) hpl)).2

/-- The distinguished initial time inside the symmetric interval `[t₀ - ε, t₀ + ε]`. -/
def localTimePoint (t₀ ε : ℝ) (hε : 0 < ε) : Set.Icc (t₀ - ε) (t₀ + ε) :=
  ⟨t₀, by linarith, by linarith⟩

@[simp] theorem localTimePoint_val (t₀ ε : ℝ) (hε : 0 < ε) :
    ((localTimePoint t₀ ε hε : Set.Icc (t₀ - ε) (t₀ + ε)) : ℝ) = t₀ :=
  rfl

private theorem contDiff_stateVelocity_component (j : Fin n) :
    ContDiff ℝ ⊤ (fun z : State n => stateVelocity n z j) := by
  simpa [stateVelocity] using
    ((((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) j :
        Velocity n →L[ℝ] ℝ)).contDiff).comp contDiff_snd)

private theorem contDiff_geodesicAcceleration
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    ContDiff ℝ ⊤
      (fun z : State n =>
        geodesicAcceleration (christoffelFieldOfSmooth Gamma)
          (statePosition n z) (stateVelocity n z)) := by
  rw [contDiff_pi]
  intro i
  unfold geodesicAcceleration
  refine ContDiff.neg ?_
  refine ContDiff.sum ?_
  intro j hj
  refine ContDiff.sum ?_
  intro k hk
  have hGamma :
      ContDiff ℝ ⊤ (fun z : State n => Gamma i j k (statePosition n z)) := by
    simpa [statePosition] using (Gamma.smooth' i j k).comp contDiff_fst
  have hvj : ContDiff ℝ ⊤ (fun z : State n => stateVelocity n z j) :=
    contDiff_stateVelocity_component (n := n) j
  have hvk : ContDiff ℝ ⊤ (fun z : State n => stateVelocity n z k) :=
    contDiff_stateVelocity_component (n := n) k
  exact (hGamma.mul hvj).mul hvk

theorem contDiff_geodesicSpray
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    ContDiff ℝ ⊤ (geodesicSpray (christoffelFieldOfSmooth Gamma)) := by
  refine contDiff_snd.prodMk ?_
  simpa [geodesicSpray, statePosition, stateVelocity] using
    contDiff_geodesicAcceleration (n := n) Gamma

theorem geodesicSpray_locallyLipschitz
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ L K : NNReal,
      IsPicardLindelof
        (geodesicVectorField (christoffelFieldOfSmooth Gamma))
        (localTimePoint t₀ ε hε) z₀ 1 0 L K := by
  let F : State n → State n := geodesicSpray (christoffelFieldOfSmooth Gamma)
  have hFcontDiff : ContDiff ℝ 1 F := (contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)
  obtain ⟨K, hK⟩ :=
    hFcontDiff.contDiffOn.exists_lipschitzOnWith (n := (1 : WithTop ℕ∞))
      one_ne_zero (convex_closedBall z₀ (1 : ℝ)) (isCompact_closedBall z₀ (1 : ℝ))
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ (1 : ℝ)).exists_bound_of_continuousOn
    hFcontDiff.continuous.continuousOn
  let Lreal : ℝ := max C 1
  let L : NNReal := ⟨Lreal, by
    dsimp [Lreal]
    exact le_trans zero_le_one (le_max_right C 1)⟩
  let ε : ℝ := min (1 : ℝ) (1 / (Lreal + 1))
  have hεpos : 0 < ε := by
    have hden : 0 < Lreal + 1 := by
      dsimp [Lreal]
      positivity
    positivity
  have hsmall : Lreal * ε ≤ 1 := by
    have hεbound : ε ≤ 1 / (Lreal + 1) := min_le_right _ _
    have hden : 0 < Lreal + 1 := by
      dsimp [Lreal]
      positivity
    have hεbound' : ε * (Lreal + 1) ≤ 1 := by
      exact (le_div_iff₀ hden).mp (by simpa [one_mul] using hεbound)
    nlinarith
  refine ⟨ε, hεpos, L, K, ?_⟩
  refine
    { lipschitzOnWith := ?_
      continuousOn := ?_
      norm_le := ?_
      mul_max_le := ?_ }
  · intro t ht
    simpa [geodesicVectorField, F] using hK
  · intro x hx
    simpa [geodesicVectorField, F] using continuous_const.continuousOn
  · intro t ht x hx
    have hx' : ‖F x‖ ≤ C := hC x hx
    exact le_trans hx' (by
      change C ≤ Lreal
      dsimp [Lreal]
      exact le_max_left _ _)
  · simpa [localTimePoint, L, Lreal, ε, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hsmall

private theorem exists_flow_continuousOn_mem_closedBall
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Set.Icc tmin tmax}
    {x₀ : E} {a r L K : NNReal}
    (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E × ℝ → E,
      (∀ x ∈ Metric.closedBall x₀ r, α (x, t₀) = x ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (fun s => α (x, s)) (f t (α (x, t))) (Set.Icc tmin tmax) t) ∧
      ContinuousOn α (Metric.closedBall x₀ r ×ˢ Set.Icc tmin tmax) ∧
      ∀ x ∈ Metric.closedBall x₀ r, ∀ t ∈ Set.Icc tmin tmax,
        α (x, t) ∈ Metric.closedBall x₀ a := by
  classical
  have hfixed (x) (hx : x ∈ Metric.closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using hfixed
  set α' : E → ℝ → E := fun x => if hx : x ∈ Metric.closedBall x₀ r then
    α x hx |>.compProj else 0
  let flow : E × ℝ → E := fun xt => α' xt.1 xt.2
  have hmain :
      ∀ x ∈ Metric.closedBall x₀ r, flow (x, t₀) = x ∧
        ∀ t ∈ Set.Icc tmin tmax,
          HasDerivWithinAt (fun s => flow (x, s)) (f t (flow (x, t)))
            (Set.Icc tmin tmax) t := by
    intro x hx
    refine ⟨?_, ?_⟩
    · simp only [flow, α', dif_pos hx]
      rw [FunSpace.compProj_val, ← hα, FunSpace.next_apply₀]
    · intro t ht
      simp only [flow, α', dif_pos hx]
      rw [FunSpace.compProj_apply]
      apply hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
        (α x hx |>.continuous_compProj.continuousOn)
        (fun _ ht' => α x hx |>.compProj_mem_closedBall hf.mul_max_le)
        x ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hα]
      rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]
  have hcont :
      ContinuousOn flow (Metric.closedBall x₀ r ×ˢ Set.Icc tmin tmax) := by
    obtain ⟨L', hL'⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
    have hlip :
        ∀ t ∈ Set.Icc tmin tmax, LipschitzOnWith L' (fun x => flow (x, t)) (Metric.closedBall x₀ r) := by
      intro t ht
      refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
      simp only [flow, α', dif_pos hx, dif_pos hy]
      rw [FunSpace.compProj_apply, FunSpace.compProj_apply,
        ← FunSpace.toContinuousMap_apply_eq_apply, ← FunSpace.toContinuousMap_apply_eq_apply]
      have : Nonempty (Set.Icc tmin tmax) := ⟨t₀⟩
      apply ContinuousMap.dist_le_iff_of_nonempty.mp
      exact hL' x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hlip
    intro x hx
    exact HasDerivWithinAt.continuousOn (hmain x hx).2
  have hmem :
      ∀ x ∈ Metric.closedBall x₀ r, ∀ t ∈ Set.Icc tmin tmax,
        flow (x, t) ∈ Metric.closedBall x₀ a := by
    intro x hx t ht
    simp only [flow, α', dif_pos hx]
    exact α x hx |>.compProj_mem_closedBall hf.mul_max_le
  exact ⟨flow, hmain, hcont, hmem⟩

/-- Uniform local flow data for the smooth coordinate geodesic spray near one initial state. -/
structure LocalCoordinateGeodesicFlowData
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) where
  ε : ℝ
  hε : 0 < ε
  a : NNReal
  r : NNReal
  hr : 0 < r
  K : NNReal
  flow : State n × ℝ → State n
  initial :
    ∀ z ∈ Metric.closedBall z₀ r,
      flow (z, t₀) = z
  isGeodesic :
    ∀ z ∈ Metric.closedBall z₀ r,
      IsCoordinateGeodesicOn (christoffelFieldOfSmooth Gamma) (fun t => flow (z, t))
        (Set.Icc (t₀ - ε) (t₀ + ε))
  lipschitzOnWith :
    ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      LipschitzOnWith K (geodesicVectorField (christoffelFieldOfSmooth Gamma) t)
        (Metric.closedBall z₀ a)
  continuousOn :
    ContinuousOn flow (Metric.closedBall z₀ r ×ˢ Set.Icc (t₀ - ε) (t₀ + ε))
  mem_closedBall :
    ∀ z ∈ Metric.closedBall z₀ r, ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
      flow (z, t) ∈ Metric.closedBall z₀ a

theorem exists_localCoordinateGeodesicFlowData
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    Nonempty (LocalCoordinateGeodesicFlowData Gamma t₀ z₀) := by
  let F : State n → State n := geodesicSpray (christoffelFieldOfSmooth Gamma)
  have hFcontDiff : ContDiffAt ℝ 1 F z₀ := by
    simpa [F] using ((contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)).contDiffAt
  rcases IsPicardLindelof.of_contDiffAt_one hFcontDiff t₀ with
    ⟨ε, hε, a, r, L, K, hr, hpl⟩
  rcases exists_flow_continuousOn_mem_closedBall hpl with
    ⟨flow, hflow, hcont, hmem⟩
  refine ⟨{ ε := ε
            hε := hε
            a := a
            r := r
            hr := hr
            K := K
            flow := flow
            initial := ?_
            isGeodesic := ?_
            lipschitzOnWith := ?_
            continuousOn := hcont
            mem_closedBall := hmem }⟩
  · intro z hz
    exact (hflow z hz).1
  · intro z hz t ht
    simpa [IsCoordinateGeodesicOn, geodesicVectorField] using (hflow z hz).2 t ht
  · exact hpl.lipschitzOnWith

/-- Choose one uniform local geodesic flow around the initial state `z₀`. -/
noncomputable def localCoordinateGeodesicFlowData
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    LocalCoordinateGeodesicFlowData Gamma t₀ z₀ := by
  classical
  exact Classical.choice (exists_localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀)

/-- The state-space source ball on which the chosen uniform local geodesic flow is defined. -/
def localCoordinateGeodesicFlowSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) : Set (State n) :=
  Metric.closedBall z₀ (localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀).r

/-- The common local time interval of the chosen uniform geodesic flow. -/
def localCoordinateGeodesicFlowTimeDomain
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) : Set ℝ :=
  let data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  Set.Icc (t₀ - data.ε) (t₀ + data.ε)

/-- The chosen uniform local geodesic flow of the smooth spray. -/
noncomputable def localCoordinateGeodesicFlow
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    State n × ℝ → State n :=
  (localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀).flow

theorem self_mem_localCoordinateGeodesicFlowSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    z₀ ∈ localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀ := by
  simp [localCoordinateGeodesicFlowSource]

theorem localCoordinateGeodesicFlow_initial
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z : State n) (z₀ : State n)
    (hz : z ∈ localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀) :
    localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z, t₀) = z := by
  classical
  let data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  simpa [localCoordinateGeodesicFlow, localCoordinateGeodesicFlowSource, data] using data.initial z hz

theorem localCoordinateGeodesicFlow_isGeodesic
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z : State n) (z₀ : State n)
    (hz : z ∈ localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀) :
    IsCoordinateGeodesicOn (christoffelFieldOfSmooth Gamma)
      (fun t => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z, t))
      (localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀) := by
  classical
  let data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  simpa [localCoordinateGeodesicFlow, localCoordinateGeodesicFlowTimeDomain, data] using
    data.isGeodesic z hz

theorem localCoordinateGeodesicFlow_continuousOn
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    ContinuousOn
      (localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀)
      (localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀ ×ˢ
        localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀) := by
  classical
  let data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  simpa [localCoordinateGeodesicFlow, localCoordinateGeodesicFlowSource,
    localCoordinateGeodesicFlowTimeDomain, data] using data.continuousOn

theorem localCoordinateGeodesicFlow_lipschitzOnWith
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    ∀ t ∈ localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀,
      LipschitzOnWith (localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀).K
        (geodesicVectorField (christoffelFieldOfSmooth Gamma) t)
        (Metric.closedBall z₀ (localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀).a) := by
  classical
  let data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  simpa [localCoordinateGeodesicFlowTimeDomain, data] using data.lipschitzOnWith

theorem localCoordinateGeodesicFlow_mem_closedBall
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z : State n) (z₀ : State n)
    (hz : z ∈ localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀)
    {t : ℝ}
    (ht : t ∈ localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀) :
    localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z, t) ∈
      Metric.closedBall z₀ (localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀).a := by
  classical
  let data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  simpa [localCoordinateGeodesicFlow, localCoordinateGeodesicFlowSource,
    localCoordinateGeodesicFlowTimeDomain, data] using data.mem_closedBall z hz t ht

/-- The common local time interval on which the chosen coordinate geodesic through `z₀` is
defined. This is now derived from the uniform spray flow near `z₀`. -/
def localCoordinateGeodesicDomain
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) : Set ℝ :=
  localCoordinateGeodesicFlowTimeDomain (n := n) Gamma t₀ z₀

/-- The local coordinate geodesic through `z₀`, extracted from the uniform spray flow. -/
noncomputable def localCoordinateGeodesic
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    ℝ → State n :=
  fun t => localCoordinateGeodesicFlow (n := n) Gamma t₀ z₀ (z₀, t)

theorem localCoordinateGeodesic_initial
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    localCoordinateGeodesic (n := n) Gamma t₀ z₀ t₀ = z₀ := by
  simpa [localCoordinateGeodesic] using
    localCoordinateGeodesicFlow_initial (n := n) Gamma t₀ z₀ z₀
      (self_mem_localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀)

theorem localCoordinateGeodesic_isGeodesic
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) :
    IsCoordinateGeodesicOn (christoffelFieldOfSmooth Gamma)
      (localCoordinateGeodesic (n := n) Gamma t₀ z₀)
      (localCoordinateGeodesicDomain (n := n) Gamma t₀ z₀) := by
  simpa [localCoordinateGeodesic, localCoordinateGeodesicDomain] using
    localCoordinateGeodesicFlow_isGeodesic (n := n) Gamma t₀ z₀ z₀
      (self_mem_localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀)

theorem localCoordinateGeodesic_mem_closedBall
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : State n) {t : ℝ}
    (ht : t ∈ localCoordinateGeodesicDomain (n := n) Gamma t₀ z₀) :
    localCoordinateGeodesic (n := n) Gamma t₀ z₀ t ∈
      Metric.closedBall z₀ (localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀).a := by
  simpa [localCoordinateGeodesic, localCoordinateGeodesicDomain] using
    localCoordinateGeodesicFlow_mem_closedBall (n := n) Gamma t₀ z₀ z₀
      (self_mem_localCoordinateGeodesicFlowSource (n := n) Gamma t₀ z₀) ht

end Geodesic.Coordinate
