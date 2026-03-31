import Geodesic.LocalExistence
import Geodesic.LocalUniqueness
import LeviCivita.CoordinateFields
import Mathlib.Topology.Algebra.Module.Equiv

/-! The basic exponential layer packages the spray-built geodesic family whose time-one map is
the local coordinate exponential map and whose radial source drives the local theory. -/

namespace Exponential.Coordinate

open scoped Topology

variable (n : ℕ)

abbrev Position := Geodesic.Coordinate.Position n
abbrev Velocity := Geodesic.Coordinate.Velocity n
abbrev State := Geodesic.Coordinate.State n

/-- The base state `(x, 0)` used for the local exponential map at `x`. -/
def baseState (basePoint : Position n) : State n :=
  (basePoint, 0)

@[simp] theorem baseState_position (basePoint : Position n) :
    Geodesic.Coordinate.statePosition n (baseState n basePoint) = basePoint :=
  rfl

@[simp] theorem baseState_velocity (basePoint : Position n) :
    Geodesic.Coordinate.stateVelocity n (baseState n basePoint) = (0 : Velocity n) :=
  rfl

/-- A coordinate local exponential map at a fixed base point, defined on an open neighborhood of
`0` in the fixed coordinate fiber `Fin n → ℝ`. -/
structure LocalExponentialMap where
  basePoint : Position n
  source : Set (Velocity n)
  source_open : IsOpen source
  zero_mem : (0 : Velocity n) ∈ source
  toFun : Velocity n → Position n

theorem localExponentialMap_ext
    {exp exp' : LocalExponentialMap n}
    (hbase : exp.basePoint = exp'.basePoint)
    (hsource : exp.source = exp'.source)
    (hfun : ∀ v, exp.toFun v = exp'.toFun v) :
    exp = exp' := by
  cases exp with
  | mk bp src hsrc hzero f =>
      cases exp' with
      | mk bp' src' hsrc' hzero' f' =>
          simp only at hbase hsource
          subst hbase
          subst hsource
          have hfun' : f = f' := by
            funext v
            exact hfun v
          subst hfun'
          simp

theorem localExponentialMap_ext_iff
    {exp exp' : LocalExponentialMap n} :
    exp = exp' ↔
      exp.basePoint = exp'.basePoint ∧ exp.source = exp'.source ∧
        ∀ v, exp.toFun v = exp'.toFun v := by
  constructor
  · intro h
    refine ⟨by simp [h], by simp [h], ?_⟩
    intro v
    simp [h]
  · rintro ⟨hbase, hsource, hfun⟩
    exact localExponentialMap_ext (n := n) hbase hsource hfun

@[simp] theorem zero_mem_localExponentialMap_source (exp : LocalExponentialMap n) :
    (0 : Velocity n) ∈ exp.source :=
  exp.zero_mem

/-- The coordinate velocity and position spaces are the same ambient Euclidean space. -/
noncomputable def velocityPositionEquiv : Velocity n ≃L[ℝ] Position n :=
  ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)

/-- A coordinate geodesic family realizing a local exponential map on its source neighborhood. -/
structure RealizedByGeodesicFamily (exp : LocalExponentialMap n) where
  solve : Velocity n → ℝ → State n
  initial_position :
    ∀ v ∈ exp.source, Geodesic.Coordinate.statePosition n (solve v 0) = exp.basePoint
  initial_velocity :
    ∀ v ∈ exp.source, Geodesic.Coordinate.stateVelocity n (solve v 0) = v
  terminal_position :
    ∀ v ∈ exp.source, Geodesic.Coordinate.statePosition n (solve v 1) = exp.toFun v

theorem realizedByGeodesicFamily_ext
    {exp : LocalExponentialMap n}
    {F F' : RealizedByGeodesicFamily n exp}
    (hsolve : ∀ v t, F.solve v t = F'.solve v t) :
    F = F' := by
  cases F with
  | mk solve hpos hvel hterm =>
      cases F' with
      | mk solve' hpos' hvel' hterm' =>
          have hsolve' : solve = solve' := by
            funext v t
            exact hsolve v t
          subst hsolve'
          simp

theorem realizedByGeodesicFamily_ext_iff
    {exp : LocalExponentialMap n}
    {F F' : RealizedByGeodesicFamily n exp} :
    F = F' ↔ ∀ v t, F.solve v t = F'.solve v t := by
  constructor
  · intro h v t
    simp [h]
  · intro h
    exact realizedByGeodesicFamily_ext (n := n) h

def expAt (exp : LocalExponentialMap n) : Velocity n → Position n :=
  exp.toFun

@[simp] theorem expAt_apply (exp : LocalExponentialMap n) (v : Velocity n) :
    expAt n exp v = exp.toFun v :=
  rfl

@[simp] theorem geodesic_family_position_zero
    {exp : LocalExponentialMap n} (h : RealizedByGeodesicFamily n exp)
    {v : Velocity n} (hv : v ∈ exp.source) :
    Geodesic.Coordinate.statePosition n (h.solve v 0) = exp.basePoint :=
  h.initial_position v hv

@[simp] theorem geodesic_family_velocity_zero
    {exp : LocalExponentialMap n} (h : RealizedByGeodesicFamily n exp)
    {v : Velocity n} (hv : v ∈ exp.source) :
    Geodesic.Coordinate.stateVelocity n (h.solve v 0) = v :=
  h.initial_velocity v hv

@[simp] theorem geodesic_family_position_one
    {exp : LocalExponentialMap n} (h : RealizedByGeodesicFamily n exp)
    {v : Velocity n} (hv : v ∈ exp.source) :
    Geodesic.Coordinate.statePosition n (h.solve v 1) = expAt n exp v :=
  h.terminal_position v hv

theorem geodesic_family_base_zero
    {exp : LocalExponentialMap n} (h : RealizedByGeodesicFamily n exp) :
    expAt n exp 0 = Geodesic.Coordinate.statePosition n (h.solve 0 1) := by
  symm
  exact geodesic_family_position_one (n := n) h exp.zero_mem

theorem geodesic_family_initial_state
    {exp : LocalExponentialMap n} (h : RealizedByGeodesicFamily n exp)
    {v : Velocity n} (hv : v ∈ exp.source) :
    h.solve v 0 = (exp.basePoint, v) := by
  apply Prod.ext
  · exact h.initial_position v hv
  · exact h.initial_velocity v hv

theorem geodesic_family_terminal_position_eq
    {exp : LocalExponentialMap n} (h : RealizedByGeodesicFamily n exp) :
    ∀ v ∈ exp.source, Geodesic.Coordinate.statePosition n (h.solve v 1) = exp.toFun v :=
  h.terminal_position

/-- A coordinate geodesic family with prescribed initial data on a velocity neighborhood. -/
structure GeodesicFamilyAtBase where
  basePoint : Position n
  source : Set (Velocity n)
  source_open : IsOpen source
  zero_mem : (0 : Velocity n) ∈ source
  solve : Velocity n → ℝ → State n
  initial_position :
    ∀ v ∈ source, Geodesic.Coordinate.statePosition n (solve v 0) = basePoint
  initial_velocity :
    ∀ v ∈ source, Geodesic.Coordinate.stateVelocity n (solve v 0) = v

theorem geodesicFamilyAtBase_ext
    {F F' : GeodesicFamilyAtBase n}
    (hbase : F.basePoint = F'.basePoint)
    (hsource : F.source = F'.source)
    (hsolve : ∀ v t, F.solve v t = F'.solve v t) :
    F = F' := by
  cases F with
  | mk base src hsrc hzero solve hpos hvel =>
      cases F' with
      | mk base' src' hsrc' hzero' solve' hpos' hvel' =>
          simp only at hbase hsource
          subst hbase
          subst hsource
          have hsolve' : solve = solve' := by
            funext v t
            exact hsolve v t
          subst hsolve'
          simp

theorem geodesicFamilyAtBase_ext_iff
    {F F' : GeodesicFamilyAtBase n} :
    F = F' ↔
      F.basePoint = F'.basePoint ∧ F.source = F'.source ∧
        ∀ v t, F.solve v t = F'.solve v t := by
  constructor
  · intro h
    refine ⟨by simp [h], by simp [h], ?_⟩
    intro v t
    simp [h]
  · rintro ⟨hbase, hsource, hsolve⟩
    exact geodesicFamilyAtBase_ext (n := n) hbase hsource hsolve

/-- The time-one map associated to a coordinate geodesic family. -/
def GeodesicFamilyAtBase.toLocalExponentialMap
    (F : GeodesicFamilyAtBase n) :
    LocalExponentialMap n where
  basePoint := F.basePoint
  source := F.source
  source_open := F.source_open
  zero_mem := F.zero_mem
  toFun v := Geodesic.Coordinate.statePosition n (F.solve v 1)

@[simp] theorem geodesicFamilyAtBase_toLocalExponentialMap_basePoint
    (F : GeodesicFamilyAtBase n) :
    F.toLocalExponentialMap.basePoint = F.basePoint :=
  rfl

@[simp] theorem geodesicFamilyAtBase_toLocalExponentialMap_source
    (F : GeodesicFamilyAtBase n) :
    F.toLocalExponentialMap.source = F.source :=
  rfl

@[simp] theorem geodesicFamilyAtBase_toLocalExponentialMap_apply
    (F : GeodesicFamilyAtBase n) (v : Velocity n) :
    F.toLocalExponentialMap.toFun v = Geodesic.Coordinate.statePosition n (F.solve v 1) :=
  rfl

/-- Every chosen coordinate geodesic family defines a realized local exponential map by time-one
evaluation on its source neighborhood. -/
def GeodesicFamilyAtBase.realizedBy
    (F : GeodesicFamilyAtBase n) :
    RealizedByGeodesicFamily n F.toLocalExponentialMap where
  solve := F.solve
  initial_position := F.initial_position
  initial_velocity := F.initial_velocity
  terminal_position := by
    intro v hv
    rfl

/-- The distinguished initial time in the unit interval `[0,1]`. -/
def unitIntervalStart : Set.Icc (0 : ℝ) 1 :=
  ⟨0, by constructor <;> norm_num⟩

@[simp] theorem unitIntervalStart_val :
    ((unitIntervalStart : Set.Icc (0 : ℝ) 1) : ℝ) = 0 :=
  rfl

/-- The velocity neighborhood obtained from the uniform short-time spray flow near `(x, 0)` by
rescaling time to `1`. -/
def localCoordinateExponentialSource
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    Set (Velocity n) :=
  let data :=
    Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 (baseState n basePoint)
  Metric.ball (0 : Velocity n) (data.ε * data.r)

theorem isOpen_localCoordinateExponentialSource
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    IsOpen (localCoordinateExponentialSource (n := n) basePoint Gamma) := by
  classical
  simp [localCoordinateExponentialSource]

theorem zero_mem_localCoordinateExponentialSource
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    (0 : Velocity n) ∈ localCoordinateExponentialSource (n := n) basePoint Gamma := by
  classical
  let data :=
    Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 (baseState n basePoint)
  have hrad : 0 < data.ε * data.r := by
    exact mul_pos data.hε data.hr
  change (0 : Velocity n) ∈ Metric.ball (0 : Velocity n) (data.ε * data.r)
  exact (Metric.mem_ball_self hrad : (0 : Velocity n) ∈ Metric.ball (0 : Velocity n) (data.ε * data.r))

theorem invScaledVelocity_mem_localCoordinateGeodesicFlowSource
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {v : Velocity n}
    (hv : v ∈ localCoordinateExponentialSource (n := n) basePoint Gamma) :
    (basePoint,
      (Geodesic.Coordinate.localCoordinateGeodesicFlowData
        (n := n) Gamma 0 (baseState n basePoint)).ε⁻¹ • v) ∈
      Geodesic.Coordinate.localCoordinateGeodesicFlowSource
        (n := n) Gamma 0 (baseState n basePoint) := by
  classical
  let z₀ := baseState n basePoint
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  have hvnorm : ‖v‖ < data.ε * data.r := by
    simpa [localCoordinateExponentialSource, z₀, data, Metric.mem_ball, dist_eq_norm] using hv
  have hscaled : ‖data.ε⁻¹ • v‖ ≤ data.r := by
    have hvdiv : ‖v‖ / data.ε < data.r := by
      refine (div_lt_iff₀ data.hε).2 ?_
      simpa [mul_comm, mul_left_comm, mul_assoc] using hvnorm
    calc
      ‖data.ε⁻¹ • v‖ = ‖v‖ / data.ε := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos data.hε, inv_mul_eq_div]
      _ ≤ data.r := le_of_lt hvdiv
  rw [Geodesic.Coordinate.localCoordinateGeodesicFlowSource, Metric.mem_closedBall]
  change dist ((basePoint, data.ε⁻¹ • v) : State n) (basePoint, (0 : Velocity n)) ≤ data.r
  rw [dist_prod_same_left]
  simpa [dist_eq_norm] using hscaled

/-- The rescaled geodesic produced from the uniform short-time spray flow near `(x, 0)`. -/
noncomputable def rescaledLocalCoordinateGeodesic
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (v : Velocity n) :
    ℝ → State n := by
  classical
  let z₀ := baseState n basePoint
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let z : State n := (basePoint, data.ε⁻¹ • v)
  exact
    Geodesic.Coordinate.timeRescaleStateCurve (n := n) data.ε
      (fun t => Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, t))

theorem rescaledLocalCoordinateGeodesic_initial_position
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {v : Velocity n}
    (hv : v ∈ localCoordinateExponentialSource (n := n) basePoint Gamma) :
    Geodesic.Coordinate.statePosition n
      (rescaledLocalCoordinateGeodesic (n := n) basePoint Gamma v 0) = basePoint := by
  classical
  let z₀ := baseState n basePoint
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let z : State n := (basePoint, data.ε⁻¹ • v)
  have hz :
      z ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowSource (n := n) Gamma 0 z₀ := by
    simpa [z, z₀, data] using
      invScaledVelocity_mem_localCoordinateGeodesicFlowSource
        (n := n) basePoint Gamma hv
  have hinit :
      Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, 0) = z :=
    Geodesic.Coordinate.localCoordinateGeodesicFlow_initial (n := n) Gamma 0 z z₀ hz
  calc
    Geodesic.Coordinate.statePosition n
        (rescaledLocalCoordinateGeodesic (n := n) basePoint Gamma v 0)
        =
      Geodesic.Coordinate.statePosition n
        (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, 0)) := by
          simp [rescaledLocalCoordinateGeodesic, z₀, z, data]
    _ = basePoint := by
      simpa [z, baseState] using congrArg (Geodesic.Coordinate.statePosition n) hinit

theorem rescaledLocalCoordinateGeodesic_initial_velocity
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {v : Velocity n}
    (hv : v ∈ localCoordinateExponentialSource (n := n) basePoint Gamma) :
    Geodesic.Coordinate.stateVelocity n
      (rescaledLocalCoordinateGeodesic (n := n) basePoint Gamma v 0) = v := by
  classical
  let z₀ := baseState n basePoint
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let z : State n := (basePoint, data.ε⁻¹ • v)
  have hz :
      z ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowSource (n := n) Gamma 0 z₀ := by
    simpa [z, z₀, data] using
      invScaledVelocity_mem_localCoordinateGeodesicFlowSource
        (n := n) basePoint Gamma hv
  have hinit :
      Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, 0) = z :=
    Geodesic.Coordinate.localCoordinateGeodesicFlow_initial (n := n) Gamma 0 z z₀ hz
  have hvel0 :
      Geodesic.Coordinate.stateVelocity n
        (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, 0)) =
      data.ε⁻¹ • v := by
    simpa [z, baseState] using congrArg (Geodesic.Coordinate.stateVelocity n) hinit
  calc
    Geodesic.Coordinate.stateVelocity n
        (rescaledLocalCoordinateGeodesic (n := n) basePoint Gamma v 0)
        = data.ε •
            Geodesic.Coordinate.stateVelocity n
              (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, 0)) := by
          simp [rescaledLocalCoordinateGeodesic, z₀, z, data]
    _ = data.ε • (data.ε⁻¹ • v) := by rw [hvel0]
    _ = v := by simp [smul_smul, data.hε.ne']

theorem rescaledLocalCoordinateGeodesic_initial_state
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {v : Velocity n}
    (hv : v ∈ localCoordinateExponentialSource (n := n) basePoint Gamma) :
    rescaledLocalCoordinateGeodesic (n := n) basePoint Gamma v 0 = (basePoint, v) := by
  apply Prod.ext
  · exact rescaledLocalCoordinateGeodesic_initial_position (n := n) basePoint Gamma hv
  · exact rescaledLocalCoordinateGeodesic_initial_velocity (n := n) basePoint Gamma hv

theorem rescaledLocalCoordinateGeodesic_isCoordinateGeodesicOn
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {v : Velocity n}
    (hv : v ∈ localCoordinateExponentialSource (n := n) basePoint Gamma) :
    Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
      (rescaledLocalCoordinateGeodesic (n := n) basePoint Gamma v)
      (Set.Icc (-1 : ℝ) 1) := by
  classical
  let z₀ := baseState n basePoint
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let z : State n := (basePoint, data.ε⁻¹ • v)
  have hz :
      z ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowSource (n := n) Gamma 0 z₀ := by
    simpa [z, z₀, data] using
      invScaledVelocity_mem_localCoordinateGeodesicFlowSource
        (n := n) basePoint Gamma hv
  have hflow :
      Geodesic.Coordinate.IsCoordinateGeodesicOn
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
        (fun t => Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, t))
        (Set.Icc (-data.ε) data.ε) := by
    simpa [Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data, sub_eq_add_neg] using
      Geodesic.Coordinate.localCoordinateGeodesicFlow_isGeodesic (n := n) Gamma 0 z z₀ hz
  simpa [rescaledLocalCoordinateGeodesic, z₀, z, data] using
    Geodesic.Coordinate.isCoordinateGeodesicOn_timeRescale (n := n) data.hε hflow

/-- Construct a coordinate geodesic family from the uniform short-time spray flow near
`(basePoint, 0)` via the quadratic velocity/time rescaling. -/
noncomputable def geodesicFamilyAtBaseOfLocalCoordinateFlow
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    GeodesicFamilyAtBase n where
  basePoint := basePoint
  source := localCoordinateExponentialSource (n := n) basePoint Gamma
  source_open := isOpen_localCoordinateExponentialSource (n := n) basePoint Gamma
  zero_mem := zero_mem_localCoordinateExponentialSource (n := n) basePoint Gamma
  solve := rescaledLocalCoordinateGeodesic (n := n) basePoint Gamma
  initial_position := by
    intro v hv
    exact rescaledLocalCoordinateGeodesic_initial_position (n := n) basePoint Gamma hv
  initial_velocity := by
    intro v hv
    exact rescaledLocalCoordinateGeodesic_initial_velocity (n := n) basePoint Gamma hv

theorem geodesicFamilyAtBaseOfLocalCoordinateFlow_isCoordinateGeodesicOn
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {v : Velocity n}
    (hv : v ∈ (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) basePoint Gamma).source) :
    Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
      ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) basePoint Gamma).solve v)
      (Set.Icc (-1 : ℝ) 1) := by
  exact rescaledLocalCoordinateGeodesic_isCoordinateGeodesicOn (n := n) basePoint Gamma hv

theorem geodesicFamilyAtBaseOfLocalCoordinateFlow_initial_state
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {v : Velocity n}
    (hv : v ∈ (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) basePoint Gamma).source) :
    (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) basePoint Gamma).solve v 0 =
      (basePoint, v) := by
  simpa [geodesicFamilyAtBaseOfLocalCoordinateFlow] using
    rescaledLocalCoordinateGeodesic_initial_state (n := n) basePoint Gamma hv

/-- The spray-built coordinate local exponential map obtained from the uniform local flow near
`(basePoint, 0)` by velocity/time rescaling. -/
noncomputable def localExponentialMapOfLocalCoordinateFlow
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    LocalExponentialMap n :=
  (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) basePoint Gamma).toLocalExponentialMap

noncomputable def localExponentialMapOfLocalCoordinateFlow_realizedBy
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    RealizedByGeodesicFamily n
      (localExponentialMapOfLocalCoordinateFlow (n := n) basePoint Gamma) :=
  (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) basePoint Gamma).realizedBy

theorem localExponentialMapOfLocalCoordinateFlow_apply
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (v : Velocity n) :
    (localExponentialMapOfLocalCoordinateFlow (n := n) basePoint Gamma).toFun v =
      Geodesic.Coordinate.statePosition n
        ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) basePoint Gamma).solve v 1) :=
  rfl

/-- The source neighborhood on which the spray-built coordinate exponential map is justified by the
uniform local flow near `(p, 0)`. -/
abbrev coordinateExpSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) : Set (Velocity n) :=
  localCoordinateExponentialSource (n := n) p Gamma

theorem isOpen_coordinateExpSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    IsOpen (coordinateExpSource (n := n) Gamma p) :=
  isOpen_localCoordinateExponentialSource (n := n) p Gamma

theorem zero_mem_coordinateExpSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    (0 : Velocity n) ∈ coordinateExpSource (n := n) Gamma p :=
  zero_mem_localCoordinateExponentialSource (n := n) p Gamma

/-- Compatibility wrapper exposing the spray-built coordinate exponential map through the older
`LocalExponentialMap` API expected by `Exponential/LocalInverse.lean`. The foundational API for
Priority 5 is `coordinateExp`, not this structure. -/
noncomputable def coordinateExpLocalExponentialMap
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    LocalExponentialMap n :=
  localExponentialMapOfLocalCoordinateFlow (n := n) p Gamma

@[simp] theorem coordinateExpLocalExponentialMap_basePoint
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    (coordinateExpLocalExponentialMap (n := n) Gamma p).basePoint = p :=
  rfl

@[simp] theorem coordinateExpLocalExponentialMap_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    (coordinateExpLocalExponentialMap (n := n) Gamma p).source =
      coordinateExpSource (n := n) Gamma p :=
  rfl

/-- The coordinate exponential map at `p`, defined as the time-one position of the spray-built
coordinate geodesic with initial state `(p, v)`. -/
noncomputable def coordinateExp
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    Velocity n → Position n :=
  (coordinateExpLocalExponentialMap (n := n) Gamma p).toFun

@[simp] theorem coordinateExp_apply
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) (v : Velocity n) :
    coordinateExp (n := n) Gamma p v =
      Geodesic.Coordinate.statePosition n
        ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v 1) :=
  rfl

theorem coordinateExp_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    coordinateExp (n := n) Gamma p 0 = p := by
  classical
  let z₀ : State n := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let gamma : ℝ → State n := Geodesic.Coordinate.localCoordinateGeodesic (n := n) Gamma 0 z₀
  let gammaConst : ℝ → State n := fun _ => z₀
  have hacc :
      Geodesic.Coordinate.geodesicAcceleration
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) p (0 : Velocity n) = 0 := by
    ext i
    simp [Geodesic.Coordinate.geodesicAcceleration]
  have hgamma :
      Geodesic.Coordinate.IsCoordinateGeodesicOn
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) gamma (Set.Icc (-data.ε) data.ε) := by
    simpa [gamma, Geodesic.Coordinate.localCoordinateGeodesic,
      Geodesic.Coordinate.localCoordinateGeodesicDomain,
      Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data, sub_eq_add_neg] using
      Geodesic.Coordinate.localCoordinateGeodesic_isGeodesic (n := n) Gamma 0 z₀
  have hgammaConst :
      Geodesic.Coordinate.IsCoordinateGeodesicOn
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) gammaConst (Set.Icc (-data.ε) data.ε) := by
    intro t ht
    simpa [gammaConst, z₀, baseState, Geodesic.Coordinate.geodesicVectorField,
      Geodesic.Coordinate.geodesicSpray, hacc] using
      (hasDerivAt_const t z₀).hasDerivWithinAt
  have hstay :
      ∀ t ∈ Set.Ioo (-data.ε) data.ε,
        gamma t ∈ Metric.closedBall z₀ data.a := by
    intro t ht
    have ht' : t ∈ Geodesic.Coordinate.localCoordinateGeodesicDomain (n := n) Gamma 0 z₀ := by
      simpa [Geodesic.Coordinate.localCoordinateGeodesicDomain,
        Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data, sub_eq_add_neg] using
        (show t ∈ Set.Icc (-data.ε) data.ε from ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    simpa [gamma] using
      Geodesic.Coordinate.localCoordinateGeodesic_mem_closedBall (n := n) Gamma 0 z₀ ht'
  have hstayConst :
      ∀ t ∈ Set.Ioo (-data.ε) data.ε,
        gammaConst t ∈ Metric.closedBall z₀ data.a := by
    intro t ht
    let _ := ht
    simp [gammaConst]
  have hinit : gamma 0 = gammaConst 0 := by
    simpa [gamma, gammaConst] using
      Geodesic.Coordinate.localCoordinateGeodesic_initial (n := n) Gamma 0 z₀
  have heq :
      Set.EqOn gamma gammaConst (Set.Icc (-data.ε) data.ε) := by
    apply Geodesic.Coordinate.eqOn_Icc_of_isCoordinateGeodesicOn_lipschitzOn
      (Gamma := Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) (t₀ := 0)
      (K := data.K) (S := Metric.closedBall z₀ data.a)
    · constructor <;> linarith [data.hε]
    · intro t ht
      have ht' : t ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
        simpa [Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data, sub_eq_add_neg] using
          (show t ∈ Set.Icc (-data.ε) data.ε from ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
      simpa using
        Geodesic.Coordinate.localCoordinateGeodesicFlow_lipschitzOnWith (n := n) Gamma 0 z₀ t ht'
    · exact hgamma
    · exact hgammaConst
    · exact hstay
    · exact hstayConst
    · exact hinit
  have hflow :
      Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z₀, data.ε) = z₀ := by
    have hεmem : data.ε ∈ Set.Icc (-data.ε) data.ε := by
      constructor
      · linarith [data.hε]
      · exact le_rfl
    simpa [gamma, gammaConst, Geodesic.Coordinate.localCoordinateGeodesic] using heq hεmem
  calc
    coordinateExp (n := n) Gamma p 0
      = Geodesic.Coordinate.statePosition n
          (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z₀, data.ε)) := by
            simp [coordinateExp_apply, geodesicFamilyAtBaseOfLocalCoordinateFlow,
              rescaledLocalCoordinateGeodesic, z₀, data, baseState]
    _ = Geodesic.Coordinate.statePosition n z₀ := by rw [hflow]
    _ = p := by simp [z₀, baseState]

theorem coordinateExp_smul_eq_geodesicFamily_position
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    coordinateExp (n := n) Gamma p (t • v) =
      Geodesic.Coordinate.statePosition n
        ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v t) := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    calc
      coordinateExp (n := n) Gamma p ((0 : ℝ) • v) = p := by
        simpa [zero_smul] using coordinateExp_zero (n := n) Gamma p
      _ = Geodesic.Coordinate.statePosition n
            ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v 0) := by
            simpa [geodesicFamilyAtBaseOfLocalCoordinateFlow] using
              (rescaledLocalCoordinateGeodesic_initial_position (n := n) p Gamma hv).symm
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    let z₀ : State n := baseState n p
    let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
    let z : State n := (p, data.ε⁻¹ • v)
    let zt : State n := (p, data.ε⁻¹ • (t • v))
    let γ : ℝ → State n :=
      fun s => Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, s)
    let γt : ℝ → State n :=
      fun s => Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (zt, s)
    have hvt : t • v ∈ coordinateExpSource (n := n) Gamma p := by
      simp only [coordinateExpSource, localCoordinateExponentialSource, Metric.mem_ball,
        dist_zero_right] at hv ⊢
      calc
        ‖t • v‖ = |t| * ‖v‖ := by simpa [Real.norm_eq_abs] using norm_smul t v
        _ ≤ 1 * ‖v‖ := by
            have habs : |t| ≤ 1 := by simpa [abs_of_nonneg ht.1] using ht.2
            gcongr
        _ = ‖v‖ := by ring
        _ < _ := hv
    have hz :
        z ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowSource (n := n) Gamma 0 z₀ := by
      simpa [z, z₀, data] using
        invScaledVelocity_mem_localCoordinateGeodesicFlowSource (n := n) p Gamma hv
    have hzt :
        zt ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowSource (n := n) Gamma 0 z₀ := by
      simpa [zt, z₀, data] using
        invScaledVelocity_mem_localCoordinateGeodesicFlowSource (n := n) p Gamma hvt
    have hγ :
        Geodesic.Coordinate.IsCoordinateGeodesicOn
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
          γ
          (Set.Icc (-data.ε) data.ε) := by
      simpa [γ, Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data] using
        Geodesic.Coordinate.localCoordinateGeodesicFlow_isGeodesic (n := n) Gamma 0 z z₀ hz
    have hγ_small :
        Geodesic.Coordinate.IsCoordinateGeodesicOn
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
          γ
          (Set.Icc (-(t * data.ε)) (t * data.ε)) := by
      refine hγ.mono ?_
      intro s hs
      constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2, data.hε]
    have hγt :
        Geodesic.Coordinate.IsCoordinateGeodesicOn
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
          γt
          (Set.Icc (-data.ε) data.ε) := by
      simpa [γt, Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data] using
        Geodesic.Coordinate.localCoordinateGeodesicFlow_isGeodesic (n := n) Gamma 0 zt z₀ hzt
    have hrescaled :
        Geodesic.Coordinate.IsCoordinateGeodesicOn
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
          (Geodesic.Coordinate.timeRescaleStateCurve (n := n) t γ)
          (Set.Icc (-data.ε) data.ε) := by
      exact Geodesic.Coordinate.isCoordinateGeodesicOn_timeRescale_interval (n := n) ht_pos hγ_small
    have hGamma :
        ∀ s ∈ Set.Ioo (-data.ε) data.ε,
          LipschitzOnWith data.K
            (Geodesic.Coordinate.geodesicVectorField
              (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) s)
            (Metric.closedBall z₀ data.a) := by
      intro s hs
      have hs_mem : s ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
        simpa [Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data] using
          (show s ∈ Set.Icc (-data.ε) data.ε from ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
      simpa [data] using
        Geodesic.Coordinate.localCoordinateGeodesicFlow_lipschitzOnWith (n := n) Gamma 0 z₀ s hs_mem
    have hγt_stay :
        ∀ s ∈ Set.Ioo (-data.ε) data.ε,
          γt s ∈ Metric.closedBall z₀ data.a := by
      intro s hs
      have hs_mem : s ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
        simpa [Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data] using
          (show s ∈ Set.Icc (-data.ε) data.ε from ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
      simpa [γt] using
        Geodesic.Coordinate.localCoordinateGeodesicFlow_mem_closedBall (n := n) Gamma 0 zt z₀ hzt hs_mem
    have hrescaled_stay :
        ∀ s ∈ Set.Ioo (-data.ε) data.ε,
          Geodesic.Coordinate.timeRescaleStateCurve (n := n) t γ s ∈ Metric.closedBall z₀ data.a := by
      intro s hs
      have hts_mem : t * s ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
        simpa [Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain, data] using
          (show t * s ∈ Set.Icc (-data.ε) data.ε by constructor <;> nlinarith [hs.1, hs.2, ht.1, ht.2, data.hε])
      have hγball :
          γ (t * s) ∈ Metric.closedBall z₀ data.a := by
        simpa [γ] using
          Geodesic.Coordinate.localCoordinateGeodesicFlow_mem_closedBall (n := n) Gamma 0 z z₀ hz hts_mem
      rw [Metric.mem_closedBall, dist_eq_norm] at hγball ⊢
      have habs : |t| ≤ 1 := by
        simpa [abs_of_nonneg ht.1] using ht.2
      calc
        ‖Geodesic.Coordinate.timeRescaleStateCurve (n := n) t γ s - z₀‖
          = max
              ‖Geodesic.Coordinate.statePosition n (γ (t * s)) - p‖
              ‖t • Geodesic.Coordinate.stateVelocity n (γ (t * s))‖ := by
                simp [Geodesic.Coordinate.timeRescaleStateCurve, z₀, baseState, Prod.norm_def]
        _ ≤ max
              ‖Geodesic.Coordinate.statePosition n (γ (t * s)) - p‖
              ‖Geodesic.Coordinate.stateVelocity n (γ (t * s))‖ := by
                apply max_le_max le_rfl
                calc
                  ‖t • Geodesic.Coordinate.stateVelocity n (γ (t * s))‖
                    = |t| * ‖Geodesic.Coordinate.stateVelocity n (γ (t * s))‖ := by
                        simpa [Real.norm_eq_abs] using norm_smul t (Geodesic.Coordinate.stateVelocity n (γ (t * s)))
                  _ ≤ 1 * ‖Geodesic.Coordinate.stateVelocity n (γ (t * s))‖ := by
                        gcongr
                  _ = ‖Geodesic.Coordinate.stateVelocity n (γ (t * s))‖ := by ring
        _ = ‖γ (t * s) - z₀‖ := by
              simp [z₀, baseState, Prod.norm_def, Geodesic.Coordinate.statePosition,
                Geodesic.Coordinate.stateVelocity]
        _ ≤ data.a := hγball
    have h0 :
        γt 0 = Geodesic.Coordinate.timeRescaleStateCurve (n := n) t γ 0 := by
      have hinit_z :
          Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z, 0) = z :=
        Geodesic.Coordinate.localCoordinateGeodesicFlow_initial (n := n) Gamma 0 z z₀ hz
      have hinit_zt :
          Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (zt, 0) = zt :=
        Geodesic.Coordinate.localCoordinateGeodesicFlow_initial (n := n) Gamma 0 zt z₀ hzt
      have hγzero : γ (t * 0) = z := by
        simpa [γ] using hinit_z
      have hpos0 :
          Geodesic.Coordinate.statePosition n (γ 0) = p := by
        simpa [γ, z, baseState] using congrArg (Geodesic.Coordinate.statePosition n) hinit_z
      have hvel0 :
          Geodesic.Coordinate.stateVelocity n (γ 0) = data.ε⁻¹ • v := by
        simpa [γ, z, baseState] using congrArg (Geodesic.Coordinate.stateVelocity n) hinit_z
      apply Prod.ext
      · calc
          Geodesic.Coordinate.statePosition n (γt 0)
              = Geodesic.Coordinate.statePosition n zt := by
                  simpa [γt] using congrArg (Geodesic.Coordinate.statePosition n) hinit_zt
          _ = p := by simp [zt]
          _ = Geodesic.Coordinate.statePosition n
                (Geodesic.Coordinate.timeRescaleStateCurve (n := n) t γ 0) := by
                  simpa [Geodesic.Coordinate.timeRescaleStateCurve] using hpos0.symm
      · calc
          Geodesic.Coordinate.stateVelocity n (γt 0)
              = Geodesic.Coordinate.stateVelocity n zt := by
                  simpa [γt] using congrArg (Geodesic.Coordinate.stateVelocity n) hinit_zt
          _ = (t * data.ε⁻¹) • v := by
                simp [zt, smul_smul, mul_comm]
          _ = t • Geodesic.Coordinate.stateVelocity n (γ 0) := by
                rw [hvel0]
                simp [smul_smul, mul_comm]
          _ = Geodesic.Coordinate.stateVelocity n
                (Geodesic.Coordinate.timeRescaleStateCurve (n := n) t γ 0) := by
                  simp [Geodesic.Coordinate.timeRescaleStateCurve]
    have heq :
        Set.EqOn γt (Geodesic.Coordinate.timeRescaleStateCurve (n := n) t γ)
          (Set.Icc (-data.ε) data.ε) := by
      apply Geodesic.Coordinate.eqOn_Icc_of_isCoordinateGeodesicOn_lipschitzOn
        (Gamma := Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) (t₀ := 0)
        (K := data.K) (S := Metric.closedBall z₀ data.a)
      · constructor <;> linarith [data.hε]
      · exact hGamma
      · exact hγt
      · exact hrescaled
      · exact hγt_stay
      · exact hrescaled_stay
      · exact h0
    have hεmem : data.ε ∈ Set.Icc (-data.ε) data.ε := by
      constructor
      · linarith [data.hε]
      · exact le_rfl
    have hpos_eq := congrArg (Geodesic.Coordinate.statePosition n) (heq hεmem)
    calc
      coordinateExp (n := n) Gamma p (t • v)
        = Geodesic.Coordinate.statePosition n (γt data.ε) := by
            simp [coordinateExp_apply, geodesicFamilyAtBaseOfLocalCoordinateFlow,
              rescaledLocalCoordinateGeodesic, z₀, zt, data, baseState, γt]
      _ = Geodesic.Coordinate.statePosition n
            (Geodesic.Coordinate.timeRescaleStateCurve (n := n) t γ data.ε) := hpos_eq
      _ = Geodesic.Coordinate.statePosition n
            ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v t) := by
            simp [geodesicFamilyAtBaseOfLocalCoordinateFlow, rescaledLocalCoordinateGeodesic,
              z₀, z, data, baseState, γ, mul_assoc, mul_left_comm, mul_comm]

theorem coordinateExp_isCoordinateGeodesicOn
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p) :
    Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
      ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v)
      (Set.Icc (-1 : ℝ) 1) :=
  geodesicFamilyAtBaseOfLocalCoordinateFlow_isCoordinateGeodesicOn (n := n) p Gamma hv

/-- Construct a coordinate geodesic family from the actual smooth spray, assuming the chosen
local geodesics are defined up to time `1` for every initial velocity at the fixed base point.
This is a global-source specialization retained for downstream compatibility. -/
noncomputable def geodesicFamilyAtBaseOfLocalCoordinateGeodesic
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (_hunit : ∀ v : Velocity n,
      (1 : ℝ) ∈ Geodesic.Coordinate.localCoordinateGeodesicDomain Gamma 0 (basePoint, v)) :
    GeodesicFamilyAtBase n where
  basePoint := basePoint
  source := Set.univ
  source_open := isOpen_univ
  zero_mem := by simp
  solve v := Geodesic.Coordinate.localCoordinateGeodesic Gamma 0 (basePoint, v)
  initial_position := by
    intro v _hv
    simpa using congrArg (Geodesic.Coordinate.statePosition n)
      (Geodesic.Coordinate.localCoordinateGeodesic_initial (n := n) Gamma 0 (basePoint, v))
  initial_velocity := by
    intro v _hv
    simpa using congrArg (Geodesic.Coordinate.stateVelocity n)
      (Geodesic.Coordinate.localCoordinateGeodesic_initial (n := n) Gamma 0 (basePoint, v))

theorem geodesicFamilyAtBaseOfLocalCoordinateGeodesic_isCoordinateGeodesicOn
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (hunit : ∀ v : Velocity n,
      (1 : ℝ) ∈ Geodesic.Coordinate.localCoordinateGeodesicDomain Gamma 0 (basePoint, v))
    (v : Velocity n) :
    Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
      ((geodesicFamilyAtBaseOfLocalCoordinateGeodesic (n := n) basePoint Gamma hunit).solve v)
      (Geodesic.Coordinate.localCoordinateGeodesicDomain Gamma 0 (basePoint, v)) := by
  exact Geodesic.Coordinate.localCoordinateGeodesic_isGeodesic (n := n) Gamma 0 (basePoint, v)

/-- The older global-source constructor obtained by evaluating chosen local geodesics at time
`1`. It is now a specialization of the local framework with `source = Set.univ`. -/
noncomputable def localExponentialMapOfLocalCoordinateGeodesic
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (hunit : ∀ v : Velocity n,
      (1 : ℝ) ∈ Geodesic.Coordinate.localCoordinateGeodesicDomain Gamma 0 (basePoint, v)) :
    LocalExponentialMap n :=
  (geodesicFamilyAtBaseOfLocalCoordinateGeodesic (n := n) basePoint Gamma hunit).toLocalExponentialMap

noncomputable def localExponentialMapOfLocalCoordinateGeodesic_realizedBy
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (hunit : ∀ v : Velocity n,
      (1 : ℝ) ∈ Geodesic.Coordinate.localCoordinateGeodesicDomain Gamma 0 (basePoint, v)) :
    RealizedByGeodesicFamily n
      (localExponentialMapOfLocalCoordinateGeodesic (n := n) basePoint Gamma hunit) :=
  (geodesicFamilyAtBaseOfLocalCoordinateGeodesic (n := n) basePoint Gamma hunit).realizedBy

theorem localExponentialMapOfLocalCoordinateGeodesic_apply
    (basePoint : Position n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (hunit : ∀ v : Velocity n,
      (1 : ℝ) ∈ Geodesic.Coordinate.localCoordinateGeodesicDomain Gamma 0 (basePoint, v))
    (v : Velocity n) :
    (localExponentialMapOfLocalCoordinateGeodesic (n := n) basePoint Gamma hunit).toFun v =
      Geodesic.Coordinate.statePosition n
        ((geodesicFamilyAtBaseOfLocalCoordinateGeodesic (n := n) basePoint Gamma hunit).solve v 1) :=
  rfl

/-- Choose a family of coordinate geodesics on `[0,1]` for all initial velocities at a base
point. This is a global-source specialization retained for compatibility. -/
noncomputable def geodesicFamilyAtBaseOfPicardLindelof
    (basePoint : Position n)
    (Gamma : Geodesic.Coordinate.ChristoffelField n)
    {a r L K : NNReal}
    (hpl : ∀ v : Velocity n,
      IsPicardLindelof (Geodesic.Coordinate.geodesicVectorField Gamma)
        (unitIntervalStart : Set.Icc (0 : ℝ) 1) (basePoint, v) a r L K) :
    GeodesicFamilyAtBase n where
  basePoint := basePoint
  source := Set.univ
  source_open := isOpen_univ
  zero_mem := by simp
  solve v :=
    Geodesic.Coordinate.someCoordinateGeodesicOn_Icc
      (t₀ := (unitIntervalStart : Set.Icc (0 : ℝ) 1))
      (z₀ := (basePoint, v)) (Gamma := Gamma) (hpl := hpl v)
  initial_position := by
    intro v _hv
    have h0 :=
      Geodesic.Coordinate.someCoordinateGeodesicOn_Icc_initial
        (t₀ := (unitIntervalStart : Set.Icc (0 : ℝ) 1))
        (z₀ := (basePoint, v)) (Gamma := Gamma) (hpl := hpl v)
    simpa [unitIntervalStart] using congrArg (Geodesic.Coordinate.statePosition n) h0
  initial_velocity := by
    intro v _hv
    have h0 :=
      Geodesic.Coordinate.someCoordinateGeodesicOn_Icc_initial
        (t₀ := (unitIntervalStart : Set.Icc (0 : ℝ) 1))
        (z₀ := (basePoint, v)) (Gamma := Gamma) (hpl := hpl v)
    simpa [unitIntervalStart] using congrArg (Geodesic.Coordinate.stateVelocity n) h0

theorem geodesicFamilyAtBaseOfPicardLindelof_isCoordinateGeodesicOn
    (basePoint : Position n)
    (Gamma : Geodesic.Coordinate.ChristoffelField n)
    {a r L K : NNReal}
    (hpl : ∀ v : Velocity n,
      IsPicardLindelof (Geodesic.Coordinate.geodesicVectorField Gamma)
        (unitIntervalStart : Set.Icc (0 : ℝ) 1) (basePoint, v) a r L K)
    (v : Velocity n) :
    Geodesic.Coordinate.IsCoordinateGeodesicOn Gamma
      ((geodesicFamilyAtBaseOfPicardLindelof (n := n) basePoint Gamma hpl).solve v)
      (Set.Icc (0 : ℝ) 1) := by
  exact Geodesic.Coordinate.someCoordinateGeodesicOn_Icc_isCoordinateGeodesicOn
    (t₀ := (unitIntervalStart : Set.Icc (0 : ℝ) 1))
    (z₀ := (basePoint, v)) (Gamma := Gamma) (hpl := hpl v)

/-- The older global-source exponential constructor from a unit-interval Picard-Lindelöf witness. -/
noncomputable def localExponentialMapOfPicardLindelof
    (basePoint : Position n)
    (Gamma : Geodesic.Coordinate.ChristoffelField n)
    {a r L K : NNReal}
    (hpl : ∀ v : Velocity n,
      IsPicardLindelof (Geodesic.Coordinate.geodesicVectorField Gamma)
        (unitIntervalStart : Set.Icc (0 : ℝ) 1) (basePoint, v) a r L K) :
    LocalExponentialMap n :=
  (geodesicFamilyAtBaseOfPicardLindelof (n := n) basePoint Gamma hpl).toLocalExponentialMap

noncomputable def localExponentialMapOfPicardLindelof_realizedBy
    (basePoint : Position n)
    (Gamma : Geodesic.Coordinate.ChristoffelField n)
    {a r L K : NNReal}
    (hpl : ∀ v : Velocity n,
      IsPicardLindelof (Geodesic.Coordinate.geodesicVectorField Gamma)
        (unitIntervalStart : Set.Icc (0 : ℝ) 1) (basePoint, v) a r L K) :
    RealizedByGeodesicFamily n
      (localExponentialMapOfPicardLindelof (n := n) basePoint Gamma hpl) :=
  (geodesicFamilyAtBaseOfPicardLindelof (n := n) basePoint Gamma hpl).realizedBy

theorem localExponentialMapOfPicardLindelof_apply
    (basePoint : Position n)
    (Gamma : Geodesic.Coordinate.ChristoffelField n)
    {a r L K : NNReal}
    (hpl : ∀ v : Velocity n,
      IsPicardLindelof (Geodesic.Coordinate.geodesicVectorField Gamma)
        (unitIntervalStart : Set.Icc (0 : ℝ) 1) (basePoint, v) a r L K)
    (v : Velocity n) :
    (localExponentialMapOfPicardLindelof (n := n) basePoint Gamma hpl).toFun v =
      Geodesic.Coordinate.statePosition n
        ((geodesicFamilyAtBaseOfPicardLindelof (n := n) basePoint Gamma hpl).solve v 1) :=
  rfl

end Exponential.Coordinate
