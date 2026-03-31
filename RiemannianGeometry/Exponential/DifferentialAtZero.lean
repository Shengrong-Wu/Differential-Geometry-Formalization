import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Exponential.Basic

namespace Exponential.Coordinate

open Asymptotics Filter Set
open scoped Topology

variable {n : ℕ}

private def affineTrialCurve (p : Position n) (v : Velocity n) : ℝ → State n :=
  fun t => (p + t • v, v)

private theorem affineTrialCurve_continuous
    (p : Position n) (v : Velocity n) :
    Continuous (affineTrialCurve (n := n) p v) := by
  have hpos : Continuous (fun t : ℝ => p + t • v) := by
    simpa using
      (continuous_const.add (continuous_id.smul (continuous_const : Continuous fun _ : ℝ => v)))
  change Continuous (fun t : ℝ => ((fun s : ℝ => p + s • v) t, (fun _ : ℝ => v) t))
  exact hpos.prodMk (continuous_const : Continuous fun _ : ℝ => v)

private theorem affineTrialCurve_hasDerivWithinAt
    (p : Position n) (v : Velocity n) {t : ℝ} :
    HasDerivWithinAt (affineTrialCurve (n := n) p v) (v, (0 : Velocity n)) (Set.Ici t) t := by
  simpa [affineTrialCurve, one_smul] using
    ((((hasDerivAt_id t).smul_const v).const_add p).prodMk (hasDerivAt_const t v)).hasDerivWithinAt

private theorem exists_geodesicAcceleration_bound
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ⦃x : Position n⦄ ⦃v : Velocity n⦄, x ∈ Metric.closedBall p R →
        ‖Geodesic.Coordinate.geodesicAcceleration
            (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) x v‖ ≤
          C * ‖v‖ ^ 2 := by
  have hcompact : IsCompact (Metric.closedBall p R) := isCompact_closedBall p R
  have hbound :
      ∀ i j k : Fin n, ∃ B : ℝ,
        ∀ x ∈ Metric.closedBall p R, ‖Gamma i j k x‖ ≤ B := by
    intro i j k
    exact hcompact.exists_bound_of_continuousOn ((Gamma.smooth' i j k).continuous.continuousOn)
  choose B hB using hbound
  have hB_nonneg : ∀ i j k, 0 ≤ B i j k := by
    intro i j k
    exact le_trans (norm_nonneg _) (hB i j k p (Metric.mem_closedBall_self hR))
  let C : ℝ := ∑ i, ∑ j, ∑ k, B i j k
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    refine Finset.sum_nonneg ?_
    intro i hi
    refine Finset.sum_nonneg ?_
    intro j hj
    exact Finset.sum_nonneg fun k hk => hB_nonneg i j k
  refine ⟨C, hC_nonneg, ?_⟩
  intro x v hx
  have hcomponent :
      ∀ i : Fin n,
        ‖Geodesic.Coordinate.geodesicAcceleration
            (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) x v i‖ ≤
          C * ‖v‖ ^ 2 := by
    intro i
    have hinner_nonneg :
        0 ≤ ∑ j, ∑ k, B i j k := by
      refine Finset.sum_nonneg ?_
      intro j hj
      exact Finset.sum_nonneg fun k hk => hB_nonneg i j k
    have hinner_le :
        ∑ j, ∑ k, B i j k ≤ C := by
      dsimp [C]
      exact Finset.single_le_sum
        (f := fun i' : Fin n => ∑ j, ∑ k, B i' j k)
        (by
          intro i' hi'
          refine Finset.sum_nonneg ?_
          intro j hj
          exact Finset.sum_nonneg fun k hk => hB_nonneg i' j k)
        (by simp)
    calc
      ‖Geodesic.Coordinate.geodesicAcceleration
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) x v i‖
          = ‖∑ j : Fin n, ∑ k : Fin n, Gamma i j k x * v j * v k‖ := by
              simp [Geodesic.Coordinate.geodesicAcceleration, norm_neg]
      _ ≤ ∑ j : Fin n, ‖∑ k : Fin n, Gamma i j k x * v j * v k‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ∑ k : Fin n, ‖Gamma i j k x * v j * v k‖ := by
            refine Finset.sum_le_sum ?_
            intro j hj
            exact norm_sum_le _ _
      _ ≤ ∑ j : Fin n, ∑ k : Fin n, B i j k * ‖v‖ ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro j hj
            refine Finset.sum_le_sum ?_
            intro k hk
            calc
              ‖Gamma i j k x * v j * v k‖ = ‖Gamma i j k x‖ * ‖v j‖ * ‖v k‖ := by
                rw [norm_mul, norm_mul]
              _ ≤ B i j k * ‖v‖ * ‖v‖ := by
                have h1 :
                    ‖Gamma i j k x‖ * ‖v j‖ ≤ B i j k * ‖v‖ :=
                  mul_le_mul (hB i j k x hx) (norm_le_pi_norm v j) (norm_nonneg _) (hB_nonneg i j k)
                exact mul_le_mul h1 (norm_le_pi_norm v k) (norm_nonneg _) <|
                  mul_nonneg (hB_nonneg i j k) (norm_nonneg _)
              _ = B i j k * ‖v‖ ^ 2 := by ring
      _ = (∑ j : Fin n, ∑ k : Fin n, B i j k) * ‖v‖ ^ 2 := by
            rw [Finset.sum_mul]
            congr with j
            rw [Finset.sum_mul]
      _ ≤ C * ‖v‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_right hinner_le (by positivity)
  have hCvv_nonneg : 0 ≤ C * ‖v‖ ^ 2 := by positivity
  exact (pi_norm_le_iff_of_nonneg hCvv_nonneg).2 hcomponent

private def freeMotionField : State n → State n :=
  fun z => (Geodesic.Coordinate.stateVelocity n z, (0 : Velocity n))

private def sprayRemainderField
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    State n → State n :=
  fun z =>
    Geodesic.Coordinate.geodesicSpray (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) z -
      freeMotionField (n := n) z

private theorem hasStrictFDerivAt_sprayRemainderField_at_base
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    HasStrictFDerivAt (sprayRemainderField (n := n) Gamma)
      (0 : State n →L[ℝ] State n) (baseState n p) := by
  let z₀ : State n := baseState n p
  have hfreeContDiff : ContDiff ℝ 1 (freeMotionField (n := n)) := by
    simpa [freeMotionField, Geodesic.Coordinate.stateVelocity] using
      (contDiff_snd.prodMk
        (contDiff_const : ContDiff ℝ 1 (fun _ : State n => (0 : Velocity n))))
  have hremContDiff : ContDiff ℝ 1 (sprayRemainderField (n := n) Gamma) := by
    exact ((Geodesic.Coordinate.contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)).sub
      hfreeContDiff
  obtain ⟨C, hC_nonneg, hacc_bound⟩ :=
    exists_geodesicAcceleration_bound (n := n) Gamma p (R := 1) (by norm_num)
  have hbigO :
      sprayRemainderField (n := n) Gamma =O[𝓝 z₀]
        (fun z : State n => ‖z - z₀‖ ^ 2) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds z₀ (show (0 : ℝ) < 1 by norm_num)] with z hz
    rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def] at hz
    have hzpos : ‖(z - z₀).1‖ < 1 := lt_of_le_of_lt (le_max_left _ _) hz
    have hzvel : ‖(z - z₀).2‖ < 1 := lt_of_le_of_lt (le_max_right _ _) hz
    have hx :
        Geodesic.Coordinate.statePosition n z ∈ Metric.closedBall p 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa [z₀, baseState] using le_of_lt hzpos
    have hvel_le : ‖Geodesic.Coordinate.stateVelocity n z‖ ≤ ‖z - z₀‖ := by
      have : ‖(z - z₀).2‖ ≤ ‖z - z₀‖ := by
        simpa [Prod.norm_def] using (le_max_right ‖(z - z₀).1‖ ‖(z - z₀).2‖)
      simpa [z₀, baseState, Geodesic.Coordinate.stateVelocity] using this
    calc
      ‖sprayRemainderField (n := n) Gamma z‖
          = ‖Geodesic.Coordinate.geodesicAcceleration
              (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
              (Geodesic.Coordinate.statePosition n z)
              (Geodesic.Coordinate.stateVelocity n z)‖ := by
                simp [sprayRemainderField, freeMotionField, Geodesic.Coordinate.geodesicSpray,
                  Geodesic.Coordinate.statePosition, Geodesic.Coordinate.stateVelocity,
                  Prod.norm_def]
      _ ≤ C * ‖Geodesic.Coordinate.stateVelocity n z‖ ^ 2 := hacc_bound hx
      _ ≤ C * ‖z - z₀‖ ^ 2 := by
            gcongr
      _ ≤ C * ‖‖z - z₀‖ ^ 2‖ := by
            have hsq : 0 ≤ ‖z - z₀‖ ^ 2 := by positivity
            simpa [Real.norm_eq_abs, abs_of_nonneg hsq]
  have hremDeriv :
      HasFDerivAt (sprayRemainderField (n := n) Gamma)
        (0 : State n →L[ℝ] State n) z₀ :=
    hbigO.hasFDerivAt (show 1 < (2 : ℕ) by norm_num)
  exact hremContDiff.contDiffAt.hasStrictFDerivAt' hremDeriv (by simp)

private theorem sprayRemainderField_base
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    sprayRemainderField (n := n) Gamma (baseState n p) = 0 := by
  ext i <;>
    simp [sprayRemainderField, freeMotionField, baseState,
      Geodesic.Coordinate.geodesicSpray, Geodesic.Coordinate.geodesicAcceleration]

private theorem gronwallBound_zero_mul
    (K x : ℝ) :
    gronwallBound 0 K x 1 = gronwallBound 0 K 1 1 * x := by
  by_cases hK : K = 0
  · simp [gronwallBound, hK]
  · simp [gronwallBound, hK, div_eq_mul_inv]
    ring

private theorem freeMotionField_norm_le
    (z : State n) :
    ‖freeMotionField (n := n) z‖ ≤ ‖z‖ := by
  rcases z with ⟨x, v⟩
  simpa [freeMotionField, Prod.norm_def] using
    (le_max_right ‖x‖ ‖v‖)

private theorem geodesic_affine_error_bound
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ ⦃v : Velocity n⦄, v ∈ coordinateExpSource (n := n) Gamma p →
        ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist
            ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v t)
            (affineTrialCurve (n := n) p v t) ≤
          D * ‖v‖ ^ 2 := by
  let z₀ : State n := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let radius : ℝ := data.ε * data.r
  let R : ℝ := 1 + data.a + data.ε * data.a + radius
  let S : Set (State n) := Metric.closedBall z₀ R
  let spray :=
    Geodesic.Coordinate.geodesicSpray (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
  have hR_nonneg : 0 ≤ R := by
    have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
    have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
    have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
    dsimp [R, radius]
    nlinarith
  have hSprayContDiff :
      ContDiff ℝ 1 spray :=
    (Geodesic.Coordinate.contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)
  have hone_ne_zero : (1 : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨K, hK⟩ :=
    hSprayContDiff.contDiffOn.exists_lipschitzOnWith
      (n := (1 : WithTop ℕ∞)) hone_ne_zero
      (convex_closedBall z₀ R) (isCompact_closedBall z₀ R)
  obtain ⟨C, hC_nonneg, hacc_bound⟩ :=
    exists_geodesicAcceleration_bound (n := n) Gamma p hR_nonneg
  let D : ℝ := max 0 (gronwallBound 0 (K : ℝ) C 1)
  refine ⟨D, le_max_left _ _, ?_⟩
  intro v hvsource t ht
  have hvnorm : ‖v‖ < radius := by
    simpa [coordinateExpSource, localCoordinateExponentialSource, Metric.mem_ball, dist_eq_norm,
      z₀, data, radius] using hvsource
  let γ : ℝ → State n := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v
  let trial : ℝ → State n := affineTrialCurve (n := n) p v
  have hγgeod :
      Geodesic.Coordinate.IsCoordinateGeodesicOn
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) γ (Set.Icc (-1 : ℝ) 1) := by
    simpa [γ] using coordinateExp_isCoordinateGeodesicOn (n := n) Gamma p hvsource
  have hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := by
    exact (HasDerivWithinAt.continuousOn hγgeod).mono fun _ ht' => ⟨by linarith [ht'.1], ht'.2⟩
  have hγderiv :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt γ ((Geodesic.Coordinate.geodesicVectorField
            (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t (γ t)) (Set.Ici t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAt :
        HasDerivAt γ
          ((Geodesic.Coordinate.geodesicVectorField
              (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t (γ t)) t := by
      simpa [γ] using
        (hγgeod t ht').hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
    exact hAt.hasDerivWithinAt
  have hγstay : ∀ t ∈ Set.Ico (0 : ℝ) 1, γ t ∈ S := by
    intro t ht
    let z : State n := (p, data.ε⁻¹ • v)
    have hR_a : (data.a : ℝ) ≤ R := by
      have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
      have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
      have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
      dsimp [R, radius]
      nlinarith
    have hR_epsa : data.ε * (data.a : ℝ) ≤ R := by
      have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
      have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
      have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
      dsimp [R, radius]
      nlinarith
    have hz :
        z ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowSource (n := n) Gamma 0 z₀ := by
      simpa [z, z₀, data] using
        invScaledVelocity_mem_localCoordinateGeodesicFlowSource (n := n) p Gamma hvsource
    have ht' : data.ε * t ∈
        Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
      simp [Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data]
      constructor <;> nlinarith [data.hε, ht.1, ht.2]
    have hmem :=
      Geodesic.Coordinate.localCoordinateGeodesicFlow_mem_closedBall
        (n := n) Gamma 0 z z₀ hz ht'
    rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def] at hmem ⊢
    have hpos : ‖Geodesic.Coordinate.statePosition n
        (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, data.ε * t)) - p‖
          ≤ data.a := (max_le_iff.mp hmem).1
    have hvel : ‖Geodesic.Coordinate.stateVelocity n
        (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, data.ε * t))‖
          ≤ data.a := by
      simpa [z₀, baseState] using (max_le_iff.mp hmem).2
    have hγt :
        γ t =
          (Geodesic.Coordinate.statePosition n
              (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀
                (z, data.ε * t)),
            data.ε •
              Geodesic.Coordinate.stateVelocity n
                (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀
                  (z, data.ε * t))) := by
      change Geodesic.Coordinate.timeRescaleStateCurve (n := n) data.ε
          (fun s =>
            Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, s)) t =
        _
      simp [Geodesic.Coordinate.timeRescaleStateCurve, z, z₀, data]
    change dist (γ t) z₀ ≤ R
    rw [dist_eq_norm, hγt]
    simp [z₀, baseState, Prod.norm_def]
    constructor
    · simpa using le_trans hpos hR_a
    · calc
        ‖data.ε • Geodesic.Coordinate.stateVelocity n
            (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, data.ε * t))‖
            = data.ε *
                ‖Geodesic.Coordinate.stateVelocity n
                    (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀
                      (z, data.ε * t))‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos data.hε]
        _ ≤ data.ε * data.a := by
                have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
                gcongr
        _ ≤ R := hR_epsa
  have htrial_cont : ContinuousOn trial (Set.Icc (0 : ℝ) 1) :=
    (affineTrialCurve_continuous (n := n) p v).continuousOn
  have htrial_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt trial (v, (0 : Velocity n)) (Set.Ici t) t := by
    intro t ht
    simpa [trial] using affineTrialCurve_hasDerivWithinAt (n := n) p v (t := t)
  have htrial_stay : ∀ t ∈ Set.Ico (0 : ℝ) 1, trial t ∈ S := by
    intro t ht
    have hR_radius : radius ≤ R := by
      have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
      have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
      have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
      dsimp [R, radius]
      nlinarith
    change dist (trial t) z₀ ≤ R
    rw [dist_eq_norm]
    simp [trial, affineTrialCurve, z₀, baseState, Prod.norm_def]
    constructor
    · calc
        ‖t • v‖ = |t| * ‖v‖ := norm_smul t v
        _ = t * ‖v‖ := by rw [abs_of_nonneg ht.1]
        _ ≤ ‖v‖ := by nlinarith [norm_nonneg v, ht.1, ht.2]
        _ ≤ radius := le_of_lt hvnorm
        _ ≤ R := hR_radius
    · calc
        ‖v‖ ≤ radius := le_of_lt hvnorm
        _ ≤ R := hR_radius
  have htrial_err :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        dist (v, (0 : Velocity n))
            ((Geodesic.Coordinate.geodesicVectorField
                (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t (trial t)) ≤
          C * ‖v‖ ^ 2 := by
    intro t ht
    have hx :
        p + t • v ∈ Metric.closedBall p R := by
      have hR_radius : radius ≤ R := by
        have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
        have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
        have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
        dsimp [R, radius]
        nlinarith
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖p + t • v - p‖ = ‖t • v‖ := by simp
        _ = |t| * ‖v‖ := norm_smul t v
        _ = t * ‖v‖ := by rw [abs_of_nonneg ht.1]
        _ ≤ ‖v‖ := by nlinarith [norm_nonneg v, ht.1, ht.2]
        _ ≤ radius := le_of_lt hvnorm
        _ ≤ R := hR_radius
    have hacc :=
      hacc_bound hx (v := v)
    simpa [trial, affineTrialCurve, Geodesic.Coordinate.geodesicVectorField,
      Geodesic.Coordinate.geodesicSpray, Geodesic.Coordinate.statePosition,
      Geodesic.Coordinate.stateVelocity, dist_eq_norm, Prod.norm_def] using hacc
  have hsprayLip :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        LipschitzOnWith K
          ((Geodesic.Coordinate.geodesicVectorField
              (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t)
          S := by
    intro t ht
    simpa [Geodesic.Coordinate.geodesicVectorField] using hK
  have hdist :=
    dist_le_of_approx_trajectories_ODE_of_mem
      (v := Geodesic.Coordinate.geodesicVectorField
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma))
      (s := fun _ : ℝ => S) (K := K) (a := 0) (b := 1)
      (εf := 0) (εg := C * ‖v‖ ^ 2) hsprayLip
      (hf := hγcont) (hf' := hγderiv)
      (f_bound := by intro τ hτ; simp)
      (hfs := hγstay) (hg := htrial_cont) (hg' := htrial_deriv)
      (g_bound := htrial_err) (hgs := htrial_stay)
      (ha := by
        have h0 : γ 0 = trial 0 := by
          simpa [γ, trial, affineTrialCurve] using
            geodesicFamilyAtBaseOfLocalCoordinateFlow_initial_state (n := n) p Gamma hvsource
        exact dist_le_zero.2 h0)
      t ht
  have hscale :
      gronwallBound 0 (K : ℝ) (C * ‖v‖ ^ 2) 1 =
        gronwallBound 0 (K : ℝ) C 1 * ‖v‖ ^ 2 := by
    by_cases hK0 : (K : ℝ) = 0
    · simp [gronwallBound, hK0, mul_assoc, mul_left_comm, mul_comm]
    · simp [gronwallBound, hK0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  calc
    dist (γ t) (trial t) ≤ gronwallBound 0 (K : ℝ) (C * ‖v‖ ^ 2) t := by
      simpa using hdist
    _ ≤ gronwallBound 0 (K : ℝ) (C * ‖v‖ ^ 2) 1 := by
      have hmono :=
        gronwallBound_mono (δ := 0) (K := (K : ℝ)) (ε := C * ‖v‖ ^ 2)
          (by norm_num) (by positivity) (show 0 ≤ (K : ℝ) by exact K.2)
      exact hmono ht.2
    _ = gronwallBound 0 (K : ℝ) C 1 * ‖v‖ ^ 2 := hscale
    _ ≤ D * ‖v‖ ^ 2 := by
        have hsq : 0 ≤ ‖v‖ ^ 2 := by positivity
        have hD : gronwallBound 0 (K : ℝ) C 1 ≤ D := le_max_right _ _
        exact mul_le_mul_of_nonneg_right hD hsq

/-- Compatibility predicate retained for `Exponential/LocalInverse.lean`. The Priority 5 API uses
the concrete theorem `hasFDerivAt_coordinateExp_at_zero` rather than taking this as a hypothesis in
new exported theorems. -/
def DifferentialAtZero
    (exp : LocalExponentialMap n) (L : Velocity n →L[ℝ] Position n) : Prop :=
  HasFDerivAt exp.toFun L 0

/-- Compatibility predicate retained for `Exponential/LocalInverse.lean`. -/
def DifferentialAtZeroIsId (exp : LocalExponentialMap n) : Prop :=
  DifferentialAtZero exp (ContinuousLinearMap.id ℝ (Velocity n))

/-- Compatibility predicate for the strict inverse-function-theorem API used downstream. -/
def StrictDifferentialAtZero
    (exp : LocalExponentialMap n) (L : Velocity n ≃L[ℝ] Position n) : Prop :=
  HasStrictFDerivAt exp.toFun (L : Velocity n →L[ℝ] Position n) 0

/-- Compatibility predicate retained for `Exponential/LocalInverse.lean`. -/
def StrictDifferentialAtZeroIsId (exp : LocalExponentialMap n) : Prop :=
  StrictDifferentialAtZero exp (velocityPositionEquiv n)

set_option maxHeartbeats 800000 in
theorem hasStrictFDerivAt_coordinateExp_at_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    HasStrictFDerivAt (coordinateExp (n := n) Gamma p)
      (velocityPositionEquiv n : Velocity n →L[ℝ] Position n) 0 := by
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε εpos
  obtain ⟨D, hD_nonneg, hD⟩ := geodesic_affine_error_bound (n := n) Gamma p
  let z₀ : State n := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let radius : ℝ := data.ε * data.r
  have hradius_pos : 0 < radius := by
    dsimp [radius]
    exact mul_pos data.hε data.hr
  let η : ℝ := min 1 (ε / (2 * Real.exp 2))
  have hη_pos : 0 < η := by
    have hdiv_pos : 0 < ε / (2 * Real.exp 2) := by
      positivity
    exact lt_min (by norm_num) hdiv_pos
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hη_le_one : η ≤ 1 := by
    dsimp [η]
    exact min_le_left _ _
  have hstrictR :=
    hasStrictFDerivAt_sprayRemainderField_at_base (n := n) Gamma p
  obtain ⟨U, hU_nhds, hU_lip⟩ :=
    hstrictR.exists_lipschitzOnWith_of_nnnorm_lt ⟨η, hη_nonneg⟩ (by simpa using hη_pos)
  obtain ⟨ρ, hρ_pos, hρU⟩ := Metric.mem_nhds_iff.mp hU_nhds
  have hD1_pos : 0 < D + 1 := by
    linarith
  let rsmall : ℝ := min radius (min 1 (ρ / (D + 1)))
  have hrsmall_pos : 0 < rsmall := by
    have hρdiv_pos : 0 < ρ / (D + 1) := by
      exact div_pos hρ_pos hD1_pos
    dsimp [rsmall]
    exact lt_min hradius_pos (lt_min (by norm_num) hρdiv_pos)
  have hrsmall_le_radius : rsmall ≤ radius := by
    dsimp [rsmall]
    exact min_le_left _ _
  have hrsmall_le_one : rsmall ≤ 1 := by
    dsimp [rsmall]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hrsmall_le_rho : rsmall ≤ ρ / (D + 1) := by
    dsimp [rsmall]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine Metric.eventually_nhds_iff_ball.mpr ⟨rsmall, hrsmall_pos, ?_⟩
  rintro ⟨v, w⟩ hvw
  rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def] at hvw
  have hvw' : max ‖v‖ ‖w‖ < rsmall := by
    simpa using hvw
  have hv_small : ‖v‖ < rsmall := lt_of_le_of_lt (le_max_left _ _) hvw'
  have hw_small : ‖w‖ < rsmall := lt_of_le_of_lt (le_max_right _ _) hvw'
  have hv_radius : ‖v‖ < radius := lt_of_lt_of_le hv_small hrsmall_le_radius
  have hw_radius : ‖w‖ < radius := lt_of_lt_of_le hw_small hrsmall_le_radius
  have hvsource : v ∈ coordinateExpSource (n := n) Gamma p := by
    simpa [coordinateExpSource, localCoordinateExponentialSource, Metric.mem_ball, dist_eq_norm,
      z₀, data, radius] using hv_radius
  have hwsource : w ∈ coordinateExpSource (n := n) Gamma p := by
    simpa [coordinateExpSource, localCoordinateExponentialSource, Metric.mem_ball, dist_eq_norm,
      z₀, data, radius] using hw_radius
  let γv : ℝ → State n := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v
  let γw : ℝ → State n := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve w
  let δ : ℝ → State n := fun t => γv t - γw t
  let trialΔ : ℝ → State n := affineTrialCurve (n := n) (0 : Position n) (v - w)
  let e : ℝ → State n := fun t => δ t - trialΔ t
  have hγ_cont :
      ∀ {u : Velocity n}, u ∈ coordinateExpSource (n := n) Gamma p →
        ContinuousOn ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u)
          (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    let γu : ℝ → State n := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u
    have hγugeod :
        Geodesic.Coordinate.IsCoordinateGeodesicOn
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) γu (Set.Icc (-1 : ℝ) 1) := by
      simpa [γu] using coordinateExp_isCoordinateGeodesicOn (n := n) Gamma p hu
    exact (HasDerivWithinAt.continuousOn hγugeod).mono fun _ ht => ⟨by linarith [ht.1], ht.2⟩
  have hγ_deriv :
      ∀ {u : Velocity n} (hu : u ∈ coordinateExpSource (n := n) Gamma p)
        {t : ℝ}, t ∈ Set.Ico (0 : ℝ) 1 →
          HasDerivWithinAt
            ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u)
            ((Geodesic.Coordinate.geodesicVectorField
                (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t
              ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u t))
            (Set.Ici t) t := by
    intro u hu t ht
    let γu : ℝ → State n := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u
    have hγugeod :
        Geodesic.Coordinate.IsCoordinateGeodesicOn
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) γu (Set.Icc (-1 : ℝ) 1) := by
      simpa [γu] using coordinateExp_isCoordinateGeodesicOn (n := n) Gamma p hu
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [ht.1, ht.2]
    have hAt :
        HasDerivAt γu
          ((Geodesic.Coordinate.geodesicVectorField
              (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t (γu t)) t := by
      simpa [γu] using
        (hγugeod t ht').hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
    simpa [γu] using hAt.hasDerivWithinAt
  have hγ_stayU :
      ∀ {u : Velocity n}, u ∈ coordinateExpSource (n := n) Gamma p →
        ‖u‖ < rsmall →
        ∀ t ∈ Set.Ico (0 : ℝ) 1, ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u t) ∈ U := by
    intro u hu hu_small t ht
    have htrial_dist : dist (affineTrialCurve (n := n) p u t) z₀ ≤ ‖u‖ := by
      rw [dist_eq_norm]
      simp [affineTrialCurve, z₀, baseState, Prod.norm_def, norm_smul, abs_of_nonneg ht.1]
      nlinarith [norm_nonneg u, ht.1, ht.2]
    have hu_le_one : ‖u‖ ≤ 1 := le_trans hu_small.le hrsmall_le_one
    have husq_le : ‖u‖ ^ 2 ≤ ‖u‖ := by
      nlinarith [norm_nonneg u, hu_le_one]
    have hmul_le_rho : (D + 1) * rsmall ≤ ρ := by
      have htmp : rsmall * (D + 1) ≤ ρ := by
        exact (le_div_iff₀ hD1_pos).mp hrsmall_le_rho
      nlinarith [htmp]
    have hdist_lt : dist ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u t) z₀ < ρ := by
      calc
        dist ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u t) z₀
          ≤ dist ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve u t)
              (affineTrialCurve (n := n) p u t) + dist (affineTrialCurve (n := n) p u t) z₀ := by
              exact dist_triangle _ _ _
        _ ≤ D * ‖u‖ ^ 2 + ‖u‖ := by
              gcongr
              exact hD hu t ⟨ht.1, ht.2.le⟩
        _ ≤ (D + 1) * ‖u‖ := by
              nlinarith [hD_nonneg, husq_le]
        _ < (D + 1) * rsmall := by
              exact mul_lt_mul_of_pos_left hu_small hD1_pos
        _ ≤ ρ := hmul_le_rho
    exact hρU (by simpa [Metric.mem_ball] using hdist_lt)
  have hγv_cont : ContinuousOn γv (Set.Icc (0 : ℝ) 1) := hγ_cont hvsource
  have hγw_cont : ContinuousOn γw (Set.Icc (0 : ℝ) 1) := hγ_cont hwsource
  have htrial_cont : ContinuousOn trialΔ (Set.Icc (0 : ℝ) 1) :=
    (affineTrialCurve_continuous (n := n) (0 : Position n) (v - w)).continuousOn
  have hδ_cont : ContinuousOn δ (Set.Icc (0 : ℝ) 1) := hγv_cont.sub hγw_cont
  have he_cont : ContinuousOn e (Set.Icc (0 : ℝ) 1) := hδ_cont.sub htrial_cont
  have htrial_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt trialΔ (freeMotionField (n := n) (trialΔ t)) (Set.Ici t) t := by
    intro t ht
    simpa [trialΔ, affineTrialCurve, freeMotionField] using
      affineTrialCurve_hasDerivWithinAt (n := n) (0 : Position n) (v - w) (t := t)
  have he_deriv :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        HasDerivWithinAt e
          (freeMotionField (n := n) (e t) +
            (sprayRemainderField (n := n) Gamma (γv t) -
              sprayRemainderField (n := n) Gamma (γw t)))
          (Set.Ici t) t := by
    intro t ht
    have hδ' := (hγ_deriv hvsource ht).sub (hγ_deriv hwsource ht)
    have htrial' := htrial_deriv t ht
    simpa [δ, e, trialΔ, freeMotionField, sprayRemainderField,
      Geodesic.Coordinate.geodesicVectorField, Geodesic.Coordinate.geodesicSpray,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hδ'.sub htrial'
  have he_bound :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ‖freeMotionField (n := n) (e t) +
            (sprayRemainderField (n := n) Gamma (γv t) -
              sprayRemainderField (n := n) Gamma (γw t))‖
          ≤ (1 + η) * ‖e t‖ + η * ‖v - w‖ := by
    intro t ht
    have hR_lip :=
      hU_lip.dist_le_mul (γv t) (hγ_stayU hvsource hv_small t ht) (γw t) (hγ_stayU hwsource hw_small t ht)
    rw [dist_eq_norm, dist_eq_norm] at hR_lip
    have hR_lip' :
        ‖sprayRemainderField (n := n) Gamma (γv t) -
            sprayRemainderField (n := n) Gamma (γw t)‖ ≤
          η * ‖γv t - γw t‖ := by
      simpa using hR_lip
    have htrial_norm : ‖trialΔ t‖ ≤ ‖v - w‖ := by
      simp [trialΔ, affineTrialCurve, Prod.norm_def, norm_smul, abs_of_nonneg ht.1]
      nlinarith [norm_nonneg (v - w), ht.1, ht.2]
    have hdelta_le : ‖γv t - γw t‖ ≤ ‖e t‖ + ‖trialΔ t‖ := by
      calc
        ‖γv t - γw t‖ = ‖e t + trialΔ t‖ := by
          simp [e, δ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ ≤ ‖e t‖ + ‖trialΔ t‖ := norm_add_le _ _
    calc
      ‖freeMotionField (n := n) (e t) +
          (sprayRemainderField (n := n) Gamma (γv t) -
            sprayRemainderField (n := n) Gamma (γw t))‖
          ≤ ‖freeMotionField (n := n) (e t)‖ +
              ‖sprayRemainderField (n := n) Gamma (γv t) -
                sprayRemainderField (n := n) Gamma (γw t)‖ := norm_add_le _ _
      _ ≤ ‖e t‖ + η * ‖γv t - γw t‖ := by
            gcongr
            exact freeMotionField_norm_le (n := n) (e t)
      _ ≤ ‖e t‖ + η * (‖e t‖ + ‖trialΔ t‖) := by
            gcongr
      _ ≤ ‖e t‖ + η * (‖e t‖ + ‖v - w‖) := by
            gcongr
      _ = (1 + η) * ‖e t‖ + η * ‖v - w‖ := by ring
  have he0 : e 0 = 0 := by
    have hγv0 : γv 0 = (p, v) := by
      simpa [γv] using
        geodesicFamilyAtBaseOfLocalCoordinateFlow_initial_state (n := n) p Gamma hvsource
    have hγw0 : γw 0 = (p, w) := by
      simpa [γw] using
        geodesicFamilyAtBaseOfLocalCoordinateFlow_initial_state (n := n) p Gamma hwsource
    simp [e, δ, trialΔ, hγv0, hγw0, affineTrialCurve]
  have he0_bound : ‖e 0‖ ≤ (0 : ℝ) := by
    simpa [he0]
  have he1 :=
    norm_le_gronwallBound_of_norm_deriv_right_le
      (f := e)
      (f' := fun t =>
        freeMotionField (n := n) (e t) +
          (sprayRemainderField (n := n) Gamma (γv t) -
            sprayRemainderField (n := n) Gamma (γw t)))
      (δ := 0) (K := 1 + η) (ε := η * ‖v - w‖) (a := 0) (b := 1)
      he_cont he_deriv he0_bound he_bound 1 (by constructor <;> norm_num)
  have hgbound : gronwallBound 0 (1 + η) 1 1 ≤ Real.exp 2 := by
    have hK_pos : 0 < 1 + η := by
      linarith
    have hK_ne : 1 + η ≠ 0 := ne_of_gt hK_pos
    have h_inv_le_one : (1 + η)⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ (by linarith)
    have hexp_nonneg : 0 ≤ Real.exp (1 + η) - 1 := by
      have h := Real.add_one_le_exp (1 + η)
      nlinarith
    have hform : gronwallBound 0 (1 + η) 1 1 = (1 + η)⁻¹ * (Real.exp (1 + η) - 1) := by
      rw [gronwallBound, if_neg hK_ne]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      gronwallBound 0 (1 + η) 1 1 = (1 + η)⁻¹ * (Real.exp (1 + η) - 1) := hform
      _ ≤ 1 * (Real.exp (1 + η) - 1) := by
            gcongr
      _ ≤ Real.exp (1 + η) := by
            nlinarith [Real.exp_pos (1 + η)]
      _ ≤ Real.exp 2 := by
            exact Real.exp_le_exp.mpr (by linarith [hη_le_one])
  have hη_le_div : η ≤ ε / (2 * Real.exp 2) := by
    dsimp [η]
    exact min_le_right _ _
  have hcoeff :
      gronwallBound 0 (1 + η) (η * ‖v - w‖) 1 ≤ ε * ‖v - w‖ := by
    have hcoeff' : gronwallBound 0 (1 + η) 1 1 * η ≤ ε := by
      have hmult :
          Real.exp 2 * η ≤ Real.exp 2 * (ε / (2 * Real.exp 2)) := by
        exact mul_le_mul_of_nonneg_left hη_le_div (by positivity)
      have hcalc : Real.exp 2 * (ε / (2 * Real.exp 2)) = ε / 2 := by
        field_simp [(Real.exp_pos 2).ne']
      calc
        gronwallBound 0 (1 + η) 1 1 * η ≤ Real.exp 2 * η := by
              gcongr
        _ ≤ ε / 2 := by
              exact hmult.trans_eq hcalc
        _ ≤ ε := by linarith
    calc
      gronwallBound 0 (1 + η) (η * ‖v - w‖) 1
          = gronwallBound 0 (1 + η) 1 1 * (η * ‖v - w‖) := by
              simpa using gronwallBound_zero_mul (K := 1 + η) (x := η * ‖v - w‖)
      _ = (gronwallBound 0 (1 + η) 1 1 * η) * ‖v - w‖ := by ring
      _ ≤ ε * ‖v - w‖ := by
            exact mul_le_mul_of_nonneg_right hcoeff' (norm_nonneg _)
  have hpos :
      ‖coordinateExp (n := n) Gamma p v - coordinateExp (n := n) Gamma p w -
          (velocityPositionEquiv n : Velocity n →L[ℝ] Position n) (v - w)‖ ≤
        ‖e 1‖ := by
    have hfst_le : ‖(e 1).1‖ ≤ ‖e 1‖ := by
      simpa [Prod.norm_def] using (le_max_left ‖(e 1).1‖ ‖(e 1).2‖)
    simpa [e, δ, trialΔ, affineTrialCurve, coordinateExp_apply, velocityPositionEquiv]
      using hfst_le
  calc
    ‖coordinateExp (n := n) Gamma p v - coordinateExp (n := n) Gamma p w -
        (velocityPositionEquiv n : Velocity n →L[ℝ] Position n) (v - w)‖
        ≤ ‖e 1‖ := hpos
    _ ≤ gronwallBound 0 (1 + η) (η * ‖v - w‖) 1 := by simpa using he1
    _ ≤ ε * ‖v - w‖ := hcoeff

theorem hasFDerivAt_coordinateExp_at_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    HasFDerivAt (coordinateExp (n := n) Gamma p)
      (ContinuousLinearMap.id ℝ (Velocity n)) 0 := by
  let z₀ : State n := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let radius : ℝ := data.ε * data.r
  let R : ℝ := 1 + data.a + data.ε * data.a + radius
  let S : Set (State n) := Metric.closedBall z₀ R
  let spray :=
    Geodesic.Coordinate.geodesicSpray (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
  have hR_nonneg : 0 ≤ R := by
    have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
    have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
    have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
    dsimp [R, radius]
    nlinarith
  have hSprayContDiff :
      ContDiff ℝ 1 spray :=
    (Geodesic.Coordinate.contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)
  have hone_ne_zero : (1 : WithTop ℕ∞) ≠ 0 := by simp
  obtain ⟨K, hK⟩ :=
    hSprayContDiff.contDiffOn.exists_lipschitzOnWith
      (n := (1 : WithTop ℕ∞)) hone_ne_zero
      (convex_closedBall z₀ R) (isCompact_closedBall z₀ R)
  obtain ⟨C, hC_nonneg, hacc_bound⟩ :=
    exists_geodesicAcceleration_bound (n := n) Gamma p hR_nonneg
  let D : ℝ := max 0 (gronwallBound 0 (K : ℝ) C 1)
  have hbigO :
      (fun v : Velocity n => coordinateExp (n := n) Gamma p v - (p + v)) =O[𝓝 (0 : Velocity n)]
        (fun v : Velocity n => ‖v - 0‖ ^ 2) := by
    have hradius : 0 < radius := by
      dsimp [radius]
      exact mul_pos data.hε data.hr
    refine Asymptotics.IsBigO.of_bound D ?_
    filter_upwards [Metric.ball_mem_nhds (0 : Velocity n) hradius] with v hv
    have hvnorm : ‖v‖ < radius := by
      simpa [Metric.mem_ball, dist_eq_norm, radius] using hv
    have hvsource : v ∈ coordinateExpSource (n := n) Gamma p := by
      simpa [coordinateExpSource, localCoordinateExponentialSource, Metric.mem_ball, dist_eq_norm,
        z₀, data, radius] using hv
    let γ : ℝ → State n := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v
    let trial : ℝ → State n := affineTrialCurve (n := n) p v
    have hγgeod :
        Geodesic.Coordinate.IsCoordinateGeodesicOn
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) γ (Set.Icc (-1 : ℝ) 1) := by
      simpa [γ] using coordinateExp_isCoordinateGeodesicOn (n := n) Gamma p hvsource
    have hγcont : ContinuousOn γ (Set.Icc (0 : ℝ) 1) := by
      exact (HasDerivWithinAt.continuousOn hγgeod).mono fun _ ht => ⟨by linarith [ht.1], ht.2⟩
    have hγderiv :
        ∀ t ∈ Set.Ico (0 : ℝ) 1,
          HasDerivWithinAt γ ((Geodesic.Coordinate.geodesicVectorField
              (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t (γ t)) (Set.Ici t) t := by
      intro t ht
      have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> linarith [ht.1, ht.2]
      have hAt :
          HasDerivAt γ
            ((Geodesic.Coordinate.geodesicVectorField
                (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t (γ t)) t := by
        simpa [γ] using
          (hγgeod t ht').hasDerivAt (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
      exact hAt.hasDerivWithinAt
    have hγstay : ∀ t ∈ Set.Ico (0 : ℝ) 1, γ t ∈ S := by
      intro t ht
      let z : State n := (p, data.ε⁻¹ • v)
      have hR_a : (data.a : ℝ) ≤ R := by
        have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
        have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
        have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
        dsimp [R, radius]
        nlinarith
      have hR_epsa : data.ε * (data.a : ℝ) ≤ R := by
        have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
        have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
        have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
        dsimp [R, radius]
        nlinarith
      have hz :
          z ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowSource (n := n) Gamma 0 z₀ := by
        simpa [z, z₀, data] using
          invScaledVelocity_mem_localCoordinateGeodesicFlowSource (n := n) p Gamma hvsource
      have ht' : data.ε * t ∈
          Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
        simp [Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data]
        constructor <;> nlinarith [data.hε, ht.1, ht.2]
      have hmem :=
        Geodesic.Coordinate.localCoordinateGeodesicFlow_mem_closedBall
          (n := n) Gamma 0 z z₀ hz ht'
      rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def] at hmem ⊢
      have hpos : ‖Geodesic.Coordinate.statePosition n
          (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, data.ε * t)) - p‖
            ≤ data.a := (max_le_iff.mp hmem).1
      have hvel : ‖Geodesic.Coordinate.stateVelocity n
          (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, data.ε * t))‖
            ≤ data.a := by
        simpa [z₀, baseState] using (max_le_iff.mp hmem).2
      have hγt :
          γ t =
            (Geodesic.Coordinate.statePosition n
                (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀
                  (z, data.ε * t)),
              data.ε •
                Geodesic.Coordinate.stateVelocity n
                  (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀
                    (z, data.ε * t))) := by
        change Geodesic.Coordinate.timeRescaleStateCurve (n := n) data.ε
            (fun s =>
              Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, s)) t =
          _
        simp [Geodesic.Coordinate.timeRescaleStateCurve, z, z₀, data]
      change dist (γ t) z₀ ≤ R
      rw [dist_eq_norm, hγt]
      simp [z₀, baseState, Prod.norm_def]
      constructor
      · simpa using le_trans hpos hR_a
      · calc
          ‖data.ε • Geodesic.Coordinate.stateVelocity n
              (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, data.ε * t))‖
              = data.ε *
                  ‖Geodesic.Coordinate.stateVelocity n
                      (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀
                        (z, data.ε * t))‖ := by
                  rw [norm_smul, Real.norm_eq_abs, abs_of_pos data.hε]
          _ ≤ data.ε * data.a := by
                  have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
                  gcongr
          _ ≤ R := hR_epsa
    have htrial_cont : ContinuousOn trial (Set.Icc (0 : ℝ) 1) :=
      (affineTrialCurve_continuous (n := n) p v).continuousOn
    have htrial_deriv :
        ∀ t ∈ Set.Ico (0 : ℝ) 1,
          HasDerivWithinAt trial (v, (0 : Velocity n)) (Set.Ici t) t := by
      intro t ht
      simpa [trial] using affineTrialCurve_hasDerivWithinAt (n := n) p v (t := t)
    have htrial_stay : ∀ t ∈ Set.Ico (0 : ℝ) 1, trial t ∈ S := by
      intro t ht
      have hR_radius : radius ≤ R := by
        have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
        have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
        have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
        dsimp [R, radius]
        nlinarith
      change dist (trial t) z₀ ≤ R
      rw [dist_eq_norm]
      simp [trial, affineTrialCurve, z₀, baseState, Prod.norm_def]
      constructor
      · calc
          ‖t • v‖ = |t| * ‖v‖ := norm_smul t v
          _ = t * ‖v‖ := by rw [abs_of_nonneg ht.1]
          _ ≤ ‖v‖ := by nlinarith [norm_nonneg v, ht.1, ht.2]
          _ ≤ radius := le_of_lt hvnorm
          _ ≤ R := hR_radius
      · calc
          ‖v‖ ≤ radius := le_of_lt hvnorm
          _ ≤ R := hR_radius
    have htrial_err :
        ∀ t ∈ Set.Ico (0 : ℝ) 1,
          dist (v, (0 : Velocity n))
              ((Geodesic.Coordinate.geodesicVectorField
                  (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t (trial t)) ≤
            C * ‖v‖ ^ 2 := by
      intro t ht
      have hx :
          p + t • v ∈ Metric.closedBall p R := by
        have hR_radius : radius ≤ R := by
          have ha_nonneg : 0 ≤ (data.a : ℝ) := data.a.2
          have hr_nonneg : 0 ≤ (data.r : ℝ) := data.r.2
          have hε_nonneg : 0 ≤ data.ε := le_of_lt data.hε
          dsimp [R, radius]
          nlinarith
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc
          ‖p + t • v - p‖ = ‖t • v‖ := by simp
          _ = |t| * ‖v‖ := norm_smul t v
          _ = t * ‖v‖ := by rw [abs_of_nonneg ht.1]
          _ ≤ ‖v‖ := by nlinarith [norm_nonneg v, ht.1, ht.2]
          _ ≤ radius := le_of_lt hvnorm
          _ ≤ R := hR_radius
      have hacc :=
        hacc_bound hx (v := v)
      simpa [trial, affineTrialCurve, Geodesic.Coordinate.geodesicVectorField,
        Geodesic.Coordinate.geodesicSpray, Geodesic.Coordinate.statePosition,
        Geodesic.Coordinate.stateVelocity, dist_eq_norm, Prod.norm_def] using hacc
    have hsprayLip :
        ∀ t ∈ Set.Ico (0 : ℝ) 1,
          LipschitzOnWith K
            ((Geodesic.Coordinate.geodesicVectorField
                (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)) t)
            S := by
      intro t ht
      simpa [Geodesic.Coordinate.geodesicVectorField] using hK
    have hdist :=
      dist_le_of_approx_trajectories_ODE_of_mem
        (v := Geodesic.Coordinate.geodesicVectorField
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma))
        (s := fun _ : ℝ => S) (K := K) (a := 0) (b := 1)
        (εf := 0) (εg := C * ‖v‖ ^ 2) hsprayLip
        (hf := hγcont) (hf' := hγderiv)
        (f_bound := by intro t ht; simp)
        (hfs := hγstay) (hg := htrial_cont) (hg' := htrial_deriv)
        (g_bound := htrial_err) (hgs := htrial_stay)
        (ha := by
          have h0 : γ 0 = trial 0 := by
            simpa [γ, trial, affineTrialCurve] using
              geodesicFamilyAtBaseOfLocalCoordinateFlow_initial_state (n := n) p Gamma hvsource
          exact dist_le_zero.2 h0)
        (1 : ℝ) (by constructor <;> norm_num)
    have hscale :
        gronwallBound 0 (K : ℝ) (C * ‖v‖ ^ 2) 1 =
          gronwallBound 0 (K : ℝ) C 1 * ‖v‖ ^ 2 := by
      by_cases hK0 : (K : ℝ) = 0
      · simp [gronwallBound, hK0, mul_assoc, mul_left_comm, mul_comm]
      · simp [gronwallBound, hK0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hpos :
        ‖coordinateExp (n := n) Gamma p v - (p + v)‖ ≤ dist (γ 1) (trial 1) := by
      have htrial1 : trial 1 = (p + v, v) := by
        simp [trial, affineTrialCurve]
      rw [coordinateExp_apply, dist_eq_norm, htrial1, Prod.norm_def]
      change
        ‖Geodesic.Coordinate.statePosition n (γ 1) - (p + v)‖ ≤
          max ‖Geodesic.Coordinate.statePosition n (γ 1) - (p + v)‖
            ‖Geodesic.Coordinate.stateVelocity n (γ 1) - v‖
      exact le_max_left _ _
    calc
      ‖coordinateExp (n := n) Gamma p v - (p + v)‖
          ≤ dist (γ 1) (trial 1) := hpos
      _ ≤ gronwallBound 0 (K : ℝ) (C * ‖v‖ ^ 2) 1 := by simpa using hdist
      _ = gronwallBound 0 (K : ℝ) C 1 * ‖v‖ ^ 2 := hscale
      _ ≤ D * ‖v - 0‖ ^ 2 := by
          have hsq : 0 ≤ ‖v‖ ^ 2 := by positivity
          have hD : gronwallBound 0 (K : ℝ) C 1 ≤ D := le_max_right _ _
          simpa [D, sub_zero] using mul_le_mul_of_nonneg_right hD hsq
      _ ≤ D * ‖‖v - 0‖ ^ 2‖ := by
          have hsq : 0 ≤ ‖v - 0‖ ^ 2 := by positivity
          simpa [Real.norm_eq_abs, abs_of_nonneg hsq]
  have hrem :
      HasFDerivAt (fun v : Velocity n => coordinateExp (n := n) Gamma p v - (p + v))
        (0 : Velocity n →L[ℝ] Position n) 0 :=
    hbigO.hasFDerivAt (show 1 < (2 : ℕ) by norm_num)
  have hlin :
      HasFDerivAt (fun v : Velocity n => p + v)
        (ContinuousLinearMap.id ℝ (Velocity n)) 0 := by
    simpa using (ContinuousLinearMap.id ℝ (Velocity n)).hasFDerivAt.const_add p
  have hsum :
      HasFDerivAt
        (fun v : Velocity n => (coordinateExp (n := n) Gamma p v - (p + v)) + (p + v))
        (0 + ContinuousLinearMap.id ℝ (Velocity n)) 0 :=
    hrem.add hlin
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum

theorem fderiv_coordinateExp_at_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    fderiv ℝ (coordinateExp (n := n) Gamma p) 0 =
      ContinuousLinearMap.id ℝ (Velocity n) := by
  simpa using (hasFDerivAt_coordinateExp_at_zero (n := n) Gamma p).fderiv

theorem strictDifferentialAtZeroIsId_coordinateExpLocalExponentialMap
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    StrictDifferentialAtZeroIsId (coordinateExpLocalExponentialMap (n := n) Gamma p) := by
  simpa [StrictDifferentialAtZeroIsId, StrictDifferentialAtZero,
    coordinateExpLocalExponentialMap, coordinateExp] using
    hasStrictFDerivAt_coordinateExp_at_zero (n := n) Gamma p

theorem differentialAtZeroIsId_coordinateExpLocalExponentialMap
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    DifferentialAtZeroIsId (coordinateExpLocalExponentialMap (n := n) Gamma p) := by
  simpa [DifferentialAtZeroIsId, DifferentialAtZero, coordinateExpLocalExponentialMap, coordinateExp]
    using hasFDerivAt_coordinateExp_at_zero (n := n) Gamma p

end Exponential.Coordinate
