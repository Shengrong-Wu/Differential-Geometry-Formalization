import Exponential.JacobiDexp
import Exponential.LocalAnalyticRealization
import Exponential.GaussLemma
import Minimization.MetricBridge

/-!
# Local Analytic Realization from Concrete Riemannian Data

This file provides the concrete constructor from `LocalRiemannianData`. Metric compatibility and
the Gauss/comparison bridge fields are now derived from owner theorems; the witnessful constructor
only still accepts an explicit differentiability witness for the directional `dexp` field.

After Issue 7, constructors are also available WITHOUT an explicit differentiability witness
(`hdiff`), since `coordinateExp` is now proved differentiable.
-/

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

/-- Construct `LocalAnalyticRealization` from the concrete local Riemannian data package
together with an explicit differentiability witness for `directionalDexp`. The Gauss and metric
comparison fields are now filled from owner theorems. -/
noncomputable def localAnalyticRealizationOfLocalRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    (hdiff : CoordinateExpHasFDerivAtOnSource (n := n) data.Gamma p) :
    LocalAnalyticRealization (n := n) data.Gamma data.metricField p where
  directionalDexp := hasDirectionalDexp_of_localRiemannianData data p hdiff
  radialPairing := radialPairing_field_of_hasRadialVariationInterchange
    (n := n) data.Gamma data.metricField p
    (hasRadialVariationInterchange_of_localRiemannianData
      (n := n) data p data.isMetricCompatible)
  radius_le_metricLength := by
    intro v hv γ Tγ Uγ hγ hkin
    exact Minimization.Coordinate.metricNormalRadius_le_metricCurveLength_of_kinematics_owner
      (n := n) data p data.isMetricCompatible hv γ Tγ Uγ hγ hkin
  metricLength_le_radius := by
    intro v hv
    refine le_of_eq ?_
    calc
      Minimization.Coordinate.metricCurveLength (n := n) data.metricField
          (Minimization.Coordinate.radialGeodesic (n := n) data.Gamma p v) 0 1
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) data.Gamma p v)
        = Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v) := by
            exact Minimization.Coordinate.metricCurveLength_eq_const_of_unitInterval
              (n := n) data.metricField
              (Minimization.Coordinate.radialGeodesic (n := n) data.Gamma p v)
              (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) data.Gamma p v)
              (Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v))
              (radialGeodesic_metricSpeed_eq_const_of_directionalDexp_radialPairing
                (n := n) data.Gamma data.metricField p
                (hasDirectionalDexp_of_localRiemannianData data p hdiff)
                (radialPairing_field_of_hasRadialVariationInterchange
                  (n := n) data.Gamma data.metricField p
                  (hasRadialVariationInterchange_of_localRiemannianData
                    (n := n) data p data.isMetricCompatible))
                hv)
      _ = Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) := by
            symm
            exact Minimization.Coordinate.metricNormalRadius_exp
              (n := n) data.metricField data.Gamma p hv

/-- Canonical `LocalAnalyticInput` constructor from the concrete data package.
Metric compatibility is genuinely derived from `data`; only the differentiability witness for
`directionalDexp` remains explicit here. -/
noncomputable def canonicalLocalAnalyticInputOfLocalRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    (hdiff : CoordinateExpHasFDerivAtOnSource (n := n) data.Gamma p) :
    LocalAnalyticInput (n := n) data.Gamma data.metricField p :=
  LocalAnalyticRealization.toInput
    (localAnalyticRealizationOfLocalRiemannianData data p hdiff)
    data.isMetricCompatible

/-- **Witness-free** `LocalAnalyticRealization` constructor. Differentiability of `coordinateExp`
is now automatic (from Issue 7), and the Gauss / metric-comparison fields are derived from the
owner theorems. -/
noncomputable def localAnalyticRealizationOfLocalRiemannianData_auto
    (data : LocalRiemannianData n)
    (p : Position n) :
    LocalAnalyticRealization (n := n) data.Gamma data.metricField p where
  directionalDexp := hasDirectionalDexp_of_smoothChristoffel (n := n) data.Gamma p
  radialPairing := radialPairing_field_of_hasRadialVariationInterchange
    (n := n) data.Gamma data.metricField p
    (hasRadialVariationInterchange_of_localRiemannianData
      (n := n) data p data.isMetricCompatible)
  radius_le_metricLength := by
    intro v hv γ Tγ Uγ hγ hkin
    exact Minimization.Coordinate.metricNormalRadius_le_metricCurveLength_of_kinematics_owner
      (n := n) data p data.isMetricCompatible hv γ Tγ Uγ hγ hkin
  metricLength_le_radius := by
    intro v hv
    refine le_of_eq ?_
    calc
      Minimization.Coordinate.metricCurveLength (n := n) data.metricField
          (Minimization.Coordinate.radialGeodesic (n := n) data.Gamma p v) 0 1
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) data.Gamma p v)
        = Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v) := by
            exact Minimization.Coordinate.metricCurveLength_eq_const_of_unitInterval
              (n := n) data.metricField
              (Minimization.Coordinate.radialGeodesic (n := n) data.Gamma p v)
              (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) data.Gamma p v)
              (Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v))
              (radialGeodesic_metricSpeed_eq_const_of_directionalDexp_radialPairing
                (n := n) data.Gamma data.metricField p
                (hasDirectionalDexp_of_smoothChristoffel (n := n) data.Gamma p)
                (radialPairing_field_of_hasRadialVariationInterchange
                  (n := n) data.Gamma data.metricField p
                  (hasRadialVariationInterchange_of_localRiemannianData
                    (n := n) data p data.isMetricCompatible))
                hv)
      _ = Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) := by
            symm
            exact Minimization.Coordinate.metricNormalRadius_exp
              (n := n) data.metricField data.Gamma p hv

/-- **Witness-free** canonical `LocalAnalyticInput` constructor. -/
noncomputable def canonicalLocalAnalyticInputOfLocalRiemannianData_auto
    (data : LocalRiemannianData n)
    (p : Position n) :
    LocalAnalyticInput (n := n) data.Gamma data.metricField p :=
  LocalAnalyticRealization.toInput
    (localAnalyticRealizationOfLocalRiemannianData_auto data p)
    data.isMetricCompatible

end Exponential.Coordinate
