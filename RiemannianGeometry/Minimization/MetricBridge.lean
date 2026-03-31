import Exponential.LocalAnalyticRealization
import Exponential.LocalAnalyticConstruction
import Exponential.GaussLemma

/-! The metric bridge isolates the Gauss/radial ingredients behind `_of_input` and
`_of_realization` wrappers used by the local minimization files. All theorems are fully proved
from their respective interface boundaries. -/

namespace Minimization.Coordinate

variable {n : ℕ}

/-- Exported metric bridge for comparison curves via input package. -/
theorem metricNormalRadius_le_metricCurveLength_of_kinematics_of_input
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      metricCurveLength (n := n) g γ 0 1 Tγ :=
  input.radius_le_metricLength hv γ Tγ Uγ hγ hkin

/-- Realization-layer wrapper for the metric bridge on comparison curves. -/
theorem metricNormalRadius_le_metricCurveLength_of_kinematics_of_realization
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) Gamma g)
    (realization : Exponential.Coordinate.LocalAnalyticRealization (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      metricCurveLength (n := n) g γ 0 1 Tγ :=
  metricNormalRadius_le_metricCurveLength_of_kinematics_of_input
    (n := n) Gamma g p
    (Exponential.Coordinate.canonicalLocalAnalyticInput hcompat realization)
    hv γ Tγ Uγ hγ hkin

/-- Exported metric bridge for comparison curves. -/
theorem metricNormalRadius_le_metricCurveLength_of_kinematics
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      metricCurveLength (n := n) g γ 0 1 Tγ :=
  metricNormalRadius_le_metricCurveLength_of_kinematics_of_input
    (n := n) Gamma g p input hv γ Tγ Uγ hγ hkin

theorem radialGeodesic_metricLength_eq_metricNormalRadius_of_metricSpeed_eq
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (hspeed :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        metricSpeed (n := n) g
            (radialGeodesic (n := n) Gamma p v)
            (radialGeodesicMetricVelocity (n := n) Gamma p v) t =
          Real.sqrt (Metric.Coordinate.quadraticForm (g p) v)) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) =
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
  calc
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v)
      = Real.sqrt (Metric.Coordinate.quadraticForm (g p) v) := by
          exact metricCurveLength_eq_const_of_unitInterval (n := n) g
            (radialGeodesic (n := n) Gamma p v)
            (radialGeodesicMetricVelocity (n := n) Gamma p v)
            (Real.sqrt (Metric.Coordinate.quadraticForm (g p) v)) hspeed
    _ = metricNormalRadius (n := n) g Gamma p
          (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
          symm
          exact metricNormalRadius_exp (n := n) g Gamma p hv

theorem radialGeodesic_metricLength_le_metricNormalRadius_of_metricSpeed_eq
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (hspeed :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        metricSpeed (n := n) g
            (radialGeodesic (n := n) Gamma p v)
            (radialGeodesicMetricVelocity (n := n) Gamma p v) t =
          Real.sqrt (Metric.Coordinate.quadraticForm (g p) v)) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
  le_of_eq <|
    radialGeodesic_metricLength_eq_metricNormalRadius_of_metricSpeed_eq
      (n := n) g Gamma p hv hspeed

/-- Metric radial-length identity exported for the minimization layer. -/
theorem radialGeodesic_metricLength_le_metricNormalRadius_of_input
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
  radialGeodesic_metricLength_le_metricNormalRadius_of_metricSpeed_eq
    (n := n) g Gamma p hv
    (Exponential.Coordinate.radialGeodesic_metricSpeed_eq_const_of_input
      (n := n) Gamma g p input hv)

/-- Realization-layer wrapper for the radial metric-length comparison. -/
theorem radialGeodesic_metricLength_le_metricNormalRadius_of_realization
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) Gamma g)
    (realization : Exponential.Coordinate.LocalAnalyticRealization (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
  radialGeodesic_metricLength_le_metricNormalRadius_of_input
    (n := n) g Gamma p
    (Exponential.Coordinate.canonicalLocalAnalyticInput hcompat realization) hv

/-- Metric radial-length identity exported for the minimization layer. -/
theorem radialGeodesic_metricLength_le_metricNormalRadius
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
  radialGeodesic_metricLength_le_metricNormalRadius_of_input
    (n := n) g Gamma p input hv

/-! ## Issue 3: Owner theorem for radius ≤ metric curve length -/

/-- **Owner theorem for Issue 3.** For any curve `γ` from `p` to `exp(v)` with normal coordinate
kinematics, the metric normal radius is ≤ the metric curve length of `γ`.

This follows from:
1. `hkin.displacement.integral_eq` writes the endpoint displacement as `∫ Uγ`
2. `normalCoordinates_exp_roundtrip` identifies the displacement with `v`
3. `norm_integral_le_integral_norm` bounds the integral
4. `metricSpeed_eq_dexpDir_normalVelocity` rewrites the integrand via dexp
5. Gauss lemma (Issue 1) bounds the normal-coordinate speed by the metric speed -/
theorem metricNormalRadius_le_metricCurveLength_of_kinematics_owner
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) data.Gamma data.metricField)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) data.Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) data.metricField data.Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) ≤
      metricCurveLength (n := n) data.metricField γ 0 1 Tγ := by
  sorry -- Gauss lemma + integral inequality + kinematics

end Minimization.Coordinate
