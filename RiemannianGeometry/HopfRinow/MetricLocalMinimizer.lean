import HopfRinow.StronglyConvex
import HopfRinow.CoordinateMetricDistance
import Exponential.LocalAnalyticConstruction
import Minimization.NormalCoordinateKinematicsConstructor

/-! # Metric-aware local minimizer owner layer

This file packages the finished local minimization results into explicit local objects that live on
top of `CoordinateMetricPath`. The goal is to connect the metric-aware distance owner layer to the
local normal-neighborhood theorems without pretending that the ambient Euclidean
`PseudoMetricSpace` on `Position n` is already the Riemannian metric.

The main objects here are:

- `CoordinateMetricKinematicPath`: a coordinate-metric path together with explicit normal-coordinate
  kinematics;
- `LocalMetricMinimizer`: a local minimizing segment from `p` to `q` with length identified with
  `metricNormalRadius`;
- constructors from both `LocalAnalyticInput` and concrete `LocalRiemannianData`.

Everything stays local and kinematic: no global path concatenation or global metric-line claim is
made in this file. -/

namespace HopfRinow

open scoped Topology

variable {n : ℕ}

namespace CoordinateMetricPath

/-- Retarget a coordinate-metric path along an endpoint equality. -/
def castTarget
    {g : Exponential.Coordinate.MetricField n}
    {p q q' : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q)
    (h : q = q') :
    CoordinateMetricPath (n := n) g p q' where
  γ := c.γ
  T := c.T
  velocity := c.velocity
  source := c.source
  target := by simpa [h] using c.target

@[simp] theorem length_castTarget
    {g : Exponential.Coordinate.MetricField n}
    {p q q' : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q)
    (h : q = q') :
    (c.castTarget h).length = c.length :=
  rfl

/-- The radial geodesic in normal coordinates as a coordinate-metric path. -/
noncomputable def radial
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv : v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    CoordinateMetricPath (n := n) g p
      (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) where
  γ := Minimization.Coordinate.radialGeodesic (n := n) Gamma p v
  T := Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v
  velocity := by
    intro t ht
    have hvsource :
        v ∈ Exponential.Coordinate.coordinateExpSource (n := n) Gamma p :=
      Exponential.Coordinate.coordinateExpPartialHomeomorph_source_subset_coordinateExpSource
        (n := n) Gamma p hv
    have hgeod :
        Geodesic.Coordinate.IsCoordinateGeodesicOn
          (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
          ((Exponential.Coordinate.geodesicFamilyAtBaseOfLocalCoordinateFlow
            (n := n) p Gamma).solve v)
          (Set.Icc (-1 : ℝ) 1) :=
      Exponential.Coordinate.coordinateExp_isCoordinateGeodesicOn
        (n := n) Gamma p hvsource
    have hpos := (Geodesic.Coordinate.isCoordinateGeodesicOn_iff_secondOrder.mp hgeod).1
    have hstate :
        HasDerivWithinAt
          (fun τ =>
            Geodesic.Coordinate.statePosition n
              ((Exponential.Coordinate.geodesicFamilyAtBaseOfLocalCoordinateFlow
                (n := n) p Gamma).solve v τ))
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v t)
          (Set.Icc (0 : ℝ) 1) t := by
      simpa [Minimization.Coordinate.radialGeodesicMetricVelocity] using
        (hpos t (by constructor <;> linarith [ht.1, ht.2])).mono
          (by intro τ hτ; constructor <;> linarith [hτ.1, hτ.2])
    exact hstate.congr_of_mem
      (fun τ hτ => by
        simpa [Minimization.Coordinate.radialGeodesic] using
          (Exponential.Coordinate.coordinateExp_smul_eq_geodesicFamily_position
            (n := n) Gamma p hvsource hτ))
      ht
  source := Minimization.Coordinate.radialGeodesic_zero (n := n) Gamma p v
  target := Minimization.Coordinate.radialGeodesic_one (n := n) Gamma p v

end CoordinateMetricPath

/-- A coordinate-metric path together with the explicit normal-coordinate kinematics needed by the
local minimization theorems. -/
structure CoordinateMetricKinematicPath
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) where
  path : CoordinateMetricPath (n := n) g p q
  U : ℝ → Exponential.Coordinate.Velocity n
  kinematics :
    Minimization.Coordinate.HasNormalCoordinateKinematics
      (n := n) Gamma p path.γ path.T U 0 1

namespace CoordinateMetricKinematicPath

/-- Retarget a kinematic path along an endpoint equality. -/
def castTarget
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q q' : Exponential.Coordinate.Position n}
    (c : CoordinateMetricKinematicPath (n := n) Gamma g p q)
    (h : q = q') :
    CoordinateMetricKinematicPath (n := n) Gamma g p q' where
  path := c.path.castTarget h
  U := c.U
  kinematics := by simpa [CoordinateMetricPath.castTarget] using c.kinematics

/-- Prefix reparametrization of a kinematic path to `[0, t]`, rescaled back to `[0,1]`. -/
def prefixPath
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricKinematicPath (n := n) Gamma g p q)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    CoordinateMetricKinematicPath (n := n) Gamma g p (c.path.γ t) where
  path := c.path.prefixPath t ht
  U := fun s => t • c.U (t * s)
  kinematics := by
    let hrestrict :
        Minimization.Coordinate.HasNormalCoordinateKinematics
          (n := n) Gamma p c.path.γ c.path.T c.U 0 t :=
      c.kinematics.restrict (c := 0) (d := t) le_rfl ht.1 ht.2
    simpa [CoordinateMetricPath.prefixPath, hrestrict] using
      hrestrict.rescaleToUnitInterval ht.1

/-- Build a kinematic path from a raw `CoordinateMetricPath` once differentiability of
`normalCoordinates` along the path and integrability of the lifted velocity field are supplied. -/
noncomputable def ofPathDifferentiableNormalCoordinates
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q)
    (hlies : Minimization.Coordinate.LiesInOn (n := n) Gamma p c.γ (Set.Icc (0 : ℝ) 1))
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t))
    (hint : IntervalIntegrable
      (fun t =>
        fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t) (c.T t))
      MeasureTheory.volume 0 1) :
    CoordinateMetricKinematicPath (n := n) Gamma g p q where
  path := c
  U := fun t =>
    fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t) (c.T t)
  kinematics := by
    have hγcont : ContinuousOn c.γ (Set.Icc (0 : ℝ) 1) :=
      HasDerivWithinAt.continuousOn c.velocity
    have hcont_nc :
        ContinuousOn
          (Minimization.Coordinate.normalCoordinateCurve (n := n) Gamma p c.γ)
          (Set.Icc (0 : ℝ) 1) := by
      intro t ht
      have hcont_t :
          ContinuousAt (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t) :=
        Exponential.Coordinate.continuousAt_normalCoordinates (n := n) Gamma p
          (by simpa [Minimization.Coordinate.LiesInOn, Minimization.Coordinate.normalNeighborhood]
            using hlies ht)
      simpa [Minimization.Coordinate.normalCoordinateCurve, Function.comp] using
        hcont_t.continuousWithinAt.comp (hγcont t ht) (by
          intro x hx
          exact Set.mem_univ _)
    exact
      Minimization.Coordinate.hasNormalCoordinateKinematics_of_differentiableNormalCoordinates
        (n := n) (Gamma := Gamma) (p := p) (γ := c.γ) (Tγ := c.T)
        zero_le_one hlies c.velocity hdiff hcont_nc hint

/-- The endpoint of a kinematic path lies in the normal neighborhood used by its kinematics. -/
theorem target_mem_normalNeighborhood
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricKinematicPath (n := n) Gamma g p q) :
    q ∈ Minimization.Coordinate.normalNeighborhood (n := n) Gamma p := by
  have hmem := c.kinematics.liesInOn (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  simpa [c.path.target] using hmem

/-- Any kinematic path inside the normal neighborhood has length at least the metric normal
radius of its endpoint. -/
theorem metricNormalRadius_le_length
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    (c : CoordinateMetricKinematicPath (n := n) Gamma g p q) :
    Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q ≤ c.path.length := by
  let v := Exponential.Coordinate.normalCoordinates (n := n) Gamma p q
  have hq : q ∈ Minimization.Coordinate.normalNeighborhood (n := n) Gamma p :=
    c.target_mem_normalNeighborhood
  have hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source := by
    dsimp [v]
    exact Exponential.Coordinate.normalCoordinates_mem_coordinateExpPartialHomeomorph_source
      (n := n) Gamma p (by simpa using hq)
  have hqexp :
      Exponential.Coordinate.coordinateExp (n := n) Gamma p v = q := by
    dsimp [v]
    exact Exponential.Coordinate.coordinateExp_normalCoordinates
      (n := n) Gamma p (by simpa using hq)
  have hqstate :
      Geodesic.Coordinate.statePosition n
        ((Exponential.Coordinate.geodesicFamilyAtBaseOfLocalCoordinateFlow
          (n := n) p Gamma).solve v 1) = q := by
    simpa using hqexp
  have hcurve :
      Minimization.Coordinate.IsCurveFrom (n := n) p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v)
        c.path.γ 0 1 := by
    constructor
    · exact c.path.source
    · calc
        c.path.γ 1 = q := c.path.target
        _ = Exponential.Coordinate.coordinateExp (n := n) Gamma p v := hqexp.symm
  have hbound :=
    input.radius_le_metricLength (v := v) hv c.path.γ c.path.T c.U hcurve c.kinematics
  simpa [CoordinateMetricPath.length, hqstate] using hbound

/-- Raw-path wrapper for `metricNormalRadius_le_length`, assuming differentiability of
`normalCoordinates` along the path and integrability of the lifted velocity field. -/
theorem metricNormalRadius_le_length_of_pathDifferentiableNormalCoordinates
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    (c : CoordinateMetricPath (n := n) g p q)
    (hlies : Minimization.Coordinate.LiesInOn (n := n) Gamma p c.γ (Set.Icc (0 : ℝ) 1))
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t))
    (hint : IntervalIntegrable
      (fun t =>
        fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t) (c.T t))
      MeasureTheory.volume 0 1) :
    Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q ≤ c.length := by
  let ck :=
    ofPathDifferentiableNormalCoordinates (n := n) (Gamma := Gamma) (g := g)
      (p := p) (q := q) c hlies hdiff hint
  simpa [ck, ofPathDifferentiableNormalCoordinates] using metricNormalRadius_le_length input ck

/-- Basepointed prefix calibration for a raw path once the normal-coordinate lift is available
via differentiability and integrability assumptions. -/
theorem metricNormalRadius_le_prefixLength_of_pathDifferentiableNormalCoordinates
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    (c : CoordinateMetricPath (n := n) g p q)
    (hlies : Minimization.Coordinate.LiesInOn (n := n) Gamma p c.γ (Set.Icc (0 : ℝ) 1))
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t))
    (hint : IntervalIntegrable
      (fun t =>
        fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t) (c.T t))
      MeasureTheory.volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p (c.γ t) ≤
      (c.prefixPath t ht).length := by
  let ck :=
    ofPathDifferentiableNormalCoordinates (n := n) (Gamma := Gamma) (g := g)
      (p := p) (q := q) c hlies hdiff hint
  simpa [ck, ofPathDifferentiableNormalCoordinates, CoordinateMetricKinematicPath.prefixPath] using
    metricNormalRadius_le_length input (ck.prefixPath t ht)

/-- Direct prefix-length form of the basepointed local calibration wrapper for raw paths. -/
theorem metricNormalRadius_le_metricCurveLength_prefix_of_pathDifferentiableNormalCoordinates
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    (c : CoordinateMetricPath (n := n) g p q)
    (hlies : Minimization.Coordinate.LiesInOn (n := n) Gamma p c.γ (Set.Icc (0 : ℝ) 1))
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t))
    (hint : IntervalIntegrable
      (fun t =>
        fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (c.γ t) (c.T t))
      MeasureTheory.volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p (c.γ t) ≤
      Minimization.Coordinate.metricCurveLength (n := n) g c.γ 0 t c.T := by
  simpa [CoordinateMetricPath.prefixPath_length_eq] using
    metricNormalRadius_le_prefixLength_of_pathDifferentiableNormalCoordinates
      (n := n) (Gamma := Gamma) (g := g) (p := p) (q := q)
      input c hlies hdiff hint ht

/-- The radial segment inside a normal neighborhood, together with its explicit normal-coordinate
kinematics. -/
noncomputable def radial
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (_input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv : v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    CoordinateMetricKinematicPath (n := n) Gamma g p
      (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) where
  path := CoordinateMetricPath.radial (n := n) Gamma g p hv
  U := Minimization.Coordinate.radialVelocityField (n := n) v
  kinematics := by
    refine
      { liesInOn := ?_
        curveVelocity := (CoordinateMetricPath.radial (n := n) Gamma g p hv).velocity
        normalVelocity := ?_
        displacement := ?_ }
    · exact Minimization.Coordinate.radialGeodesic_liesInOn (n := n) Gamma p
        (fun t ht =>
          Exponential.Coordinate.smul_mem_coordinateExpPartialHomeomorph_source
            (n := n) Gamma p hv ht)
    · intro t ht
      have hderiv :
          HasDerivWithinAt
            (fun τ : ℝ => τ • v)
            (Minimization.Coordinate.radialVelocityField (n := n) v t)
            (Set.Icc (0 : ℝ) 1) t := by
        simpa [Minimization.Coordinate.radialVelocityField, one_smul] using
          (((hasDerivAt_id t).smul_const v).hasDerivWithinAt)
      exact hderiv.congr_of_mem
        (fun τ hτ => by
          simpa only [CoordinateMetricPath.radial, Minimization.Coordinate.radialGeodesic] using
            (Exponential.Coordinate.normalCoordinates_exp_roundtrip
            (n := n) Gamma p (τ • v)
            (Exponential.Coordinate.smul_mem_coordinateExpPartialHomeomorph_source
              (n := n) Gamma p hv hτ)))
        ht
    · simpa [CoordinateMetricPath.radial] using
        (Minimization.Coordinate.radialGeodesic_hasNormalCoordinateDisplacement
          (n := n) Gamma p hv)

@[simp] theorem radial_length_eq_metricNormalRadius
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p : Exponential.Coordinate.Position n}
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv : v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    (radial (n := n) Gamma g p input hv).path.length =
      Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
  refine le_antisymm ?_ ?_
  · simpa [radial, CoordinateMetricPath.radial, CoordinateMetricPath.length] using
      input.metricLength_le_radius (v := v) hv
  · exact metricNormalRadius_le_length (n := n) input (radial (n := n) Gamma g p input hv)

theorem radial_isLocalLengthMinimizer
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p : Exponential.Coordinate.Position n}
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv : v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    Minimization.Coordinate.IsLocalLengthMinimizer (n := n) Gamma g p
      (radial (n := n) Gamma g p input hv).path.γ
      (radial (n := n) Gamma g p input hv).path.T 0 1 := by
  simpa [radial, CoordinateMetricPath.radial] using
    Minimization.Coordinate.shortGeodesicsMinimize (n := n) Gamma g p input hv

end CoordinateMetricKinematicPath

/-- A packaged local minimizing segment from `p` to `q` for the coordinate metric `g`. -/
structure LocalMetricMinimizer
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) where
  segment : CoordinateMetricKinematicPath (n := n) Gamma g p q
  length_eq_metricNormalRadius :
    segment.path.length = Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q
  isLocalLengthMinimizer :
    Minimization.Coordinate.IsLocalLengthMinimizer (n := n) Gamma g p
      segment.path.γ segment.path.T 0 1

namespace LocalMetricMinimizer

theorem length_le_metricCurveLength
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (m : LocalMetricMinimizer (n := n) Gamma g p q)
    {η : ℝ → Exponential.Coordinate.Position n}
    {Tη Uη : ℝ → Exponential.Coordinate.Velocity n}
    (hcurve : Minimization.Coordinate.IsCurveFrom (n := n) p q η 0 1)
    (hkin :
      Minimization.Coordinate.HasNormalCoordinateKinematics
        (n := n) Gamma p η Tη Uη 0 1) :
    m.segment.path.length ≤ Minimization.Coordinate.metricCurveLength (n := n) g η 0 1 Tη :=
  m.isLocalLengthMinimizer η Tη Uη
    (by simpa [m.segment.path.source, m.segment.path.target] using hcurve)
    hkin

theorem metricNormalRadius_le_metricCurveLength
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (m : LocalMetricMinimizer (n := n) Gamma g p q)
    {η : ℝ → Exponential.Coordinate.Position n}
    {Tη Uη : ℝ → Exponential.Coordinate.Velocity n}
    (hcurve : Minimization.Coordinate.IsCurveFrom (n := n) p q η 0 1)
    (hkin :
      Minimization.Coordinate.HasNormalCoordinateKinematics
        (n := n) Gamma p η Tη Uη 0 1) :
    Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q ≤
      Minimization.Coordinate.metricCurveLength (n := n) g η 0 1 Tη := by
  calc
    Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q = m.segment.path.length := by
      symm
      exact m.length_eq_metricNormalRadius
    _ ≤ Minimization.Coordinate.metricCurveLength (n := n) g η 0 1 Tη :=
      m.length_le_metricCurveLength hcurve hkin

theorem coordinateMetricDistCandidate_le_metricNormalRadius
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (m : LocalMetricMinimizer (n := n) Gamma g p q) :
    coordinateMetricDistCandidate (n := n) g p q ≤
      Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q := by
  calc
    coordinateMetricDistCandidate (n := n) g p q ≤ m.segment.path.length :=
      coordinateMetricDistCandidate_le_length m.segment.path
    _ = Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q :=
      m.length_eq_metricNormalRadius

theorem coordinateMetricChainDist_le_metricNormalRadius
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (m : LocalMetricMinimizer (n := n) Gamma g p q) :
    coordinateMetricChainDist (n := n) g p q ≤
      Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q := by
  calc
    coordinateMetricChainDist (n := n) g p q ≤
        (CoordinateMetricChain.ofPath m.segment.path).length :=
      coordinateMetricChainDist_le_length
        (cs := CoordinateMetricChain.ofPath m.segment.path)
    _ = m.segment.path.length := CoordinateMetricChain.length_ofPath _
    _ = Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q :=
      m.length_eq_metricNormalRadius

/-- Build the local minimizing radial segment to a point in the normal neighborhood. -/
noncomputable def ofMemNormalNeighborhood
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {q : Exponential.Coordinate.Position n}
    (hq : q ∈ Minimization.Coordinate.normalNeighborhood (n := n) Gamma p) :
    LocalMetricMinimizer (n := n) Gamma g p q := by
  let v := Exponential.Coordinate.normalCoordinates (n := n) Gamma p q
  have hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source := by
    dsimp [v]
    exact Exponential.Coordinate.normalCoordinates_mem_coordinateExpPartialHomeomorph_source
      (n := n) Gamma p (by simpa using hq)
  have hqexp :
      Exponential.Coordinate.coordinateExp (n := n) Gamma p v = q := by
    dsimp [v]
    exact Exponential.Coordinate.coordinateExp_normalCoordinates
      (n := n) Gamma p (by simpa using hq)
  have hqstate :
      Geodesic.Coordinate.statePosition n
        ((Exponential.Coordinate.geodesicFamilyAtBaseOfLocalCoordinateFlow
          (n := n) p Gamma).solve v 1) = q := by
    simpa using hqexp
  let segment0 := CoordinateMetricKinematicPath.radial (n := n) Gamma g p input hv
  let segment : CoordinateMetricKinematicPath (n := n) Gamma g p q :=
    segment0.castTarget hqexp
  refine
    { segment := segment
      length_eq_metricNormalRadius := ?_
      isLocalLengthMinimizer := ?_ }
  · calc
      segment.path.length = segment0.path.length := by
        simp [segment, segment0, CoordinateMetricKinematicPath.castTarget]
      _ = Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p
            (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
          CoordinateMetricKinematicPath.radial_length_eq_metricNormalRadius
            (n := n) (Gamma := Gamma) (g := g) (p := p) input hv
      _ = Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q := by
            simp [hqstate]
  · simpa [segment, segment0, CoordinateMetricKinematicPath.castTarget,
      CoordinateMetricPath.castTarget] using
      (CoordinateMetricKinematicPath.radial_isLocalLengthMinimizer
        (n := n) (Gamma := Gamma) (g := g) (p := p) input hv)

/-- Concrete-data version of `ofMemNormalNeighborhood`. -/
noncomputable def ofMemNormalNeighborhood_auto
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Exponential.Coordinate.Position n)
    {q : Exponential.Coordinate.Position n}
    (hq : q ∈ Minimization.Coordinate.normalNeighborhood (n := n) data.Gamma p) :
    LocalMetricMinimizer (n := n) data.Gamma data.metricField p q :=
  ofMemNormalNeighborhood (n := n) (Gamma := data.Gamma) (g := data.metricField) p
    (Exponential.Coordinate.canonicalLocalAnalyticInputOfLocalRiemannianData_auto data p) hq

/-- A strongly convex ball supplies the local minimizing radial segment for each point in the ball.
-/
noncomputable def ofMemClosedBall
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p : Exponential.Coordinate.Position n}
    (ball : StronglyConvexBall (n := n) Gamma p)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {q : Exponential.Coordinate.Position n}
    (hq : q ∈ Metric.closedBall p ball.radius) :
    LocalMetricMinimizer (n := n) Gamma g p q :=
  ofMemNormalNeighborhood (n := n) (Gamma := Gamma) (g := g) p input
    (ball.mem_normalNeighborhood hq)

/-- Concrete-data version of `ofMemClosedBall`. -/
noncomputable def ofMemClosedBall_auto
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Exponential.Coordinate.Position n)
    (ball : StronglyConvexBall (n := n) data.Gamma p)
    {q : Exponential.Coordinate.Position n}
    (hq : q ∈ Metric.closedBall p ball.radius) :
    LocalMetricMinimizer (n := n) data.Gamma data.metricField p q :=
  ofMemNormalNeighborhood_auto (n := n) data p (ball.mem_normalNeighborhood hq)

end LocalMetricMinimizer

/-! ### Distance equality via calibration

The chain distance `coordinateMetricChainDist g p q` equals `metricNormalRadius g Gamma p q`
when q is in the normal neighborhood, provided the **per-segment calibration** holds:

> For all x, y and all `CoordinateMetricPath g x y`, we have
> `metricNormalRadius g Gamma p y - metricNormalRadius g Gamma p x ≤ path.length`.

This is the 1-Lipschitz property of the radial distance function `ρ_p = metricNormalRadius(p, ·)`.
It follows from the Gauss lemma: the gradient of ρ_p has unit g-norm, so
`|dρ_p(v)| = |g(∇ρ_p, v)| ≤ |v|_g`.

With the calibration in hand, the chain calibration lemma
(`coordinateMetricChainDist_ge_of_calibration_zero`) gives the lower bound
`metricNormalRadius ≤ chainDist`, and the upper bound is already proved
(`coordinateMetricChainDist_le_metricNormalRadius`). -/

/-- The per-segment calibration: metricNormalRadius is 1-Lipschitz for the g-length on each
`CoordinateMetricPath` segment. This is the interface for the Gauss-lemma gradient bound. -/
def IsMetricNormalRadiusCalibration
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n) : Prop :=
  ∀ (x y : Exponential.Coordinate.Position n)
    (c : CoordinateMetricPath (n := n) g x y),
    Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p y -
      Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p x ≤ c.length

/-- Chain distance equals metric normal radius, given the per-segment calibration. -/
theorem coordinateMetricChainDist_eq_metricNormalRadius_of_calibration
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (hcalib : IsMetricNormalRadiusCalibration (n := n) Gamma g p)
    (hq : q ∈ Minimization.Coordinate.normalNeighborhood (n := n) Gamma p)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p) :
    coordinateMetricChainDist (n := n) g p q =
      Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q := by
  refine le_antisymm ?_ ?_
  · exact (LocalMetricMinimizer.ofMemNormalNeighborhood (n := n)
      (Gamma := Gamma) (g := g) p input hq).coordinateMetricChainDist_le_metricNormalRadius
  · have hbase : Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p p = 0 :=
      Minimization.Coordinate.metricNormalRadius_base (n := n) g Gamma p
    calc
      Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q
        = Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p q -
            Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p p := by
          rw [hbase, sub_zero]
      _ ≤ coordinateMetricChainDist (n := n) g p q :=
          coordinateMetricChainDist_ge_of_calibration hcalib

end HopfRinow
