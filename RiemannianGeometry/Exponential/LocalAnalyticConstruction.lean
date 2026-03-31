import Exponential.JacobiDexp
import Exponential.LocalAnalyticRealization
import Exponential.GaussLemma

/-!
# Local Analytic Realization from Concrete Riemannian Data

This file provides the concrete constructor from `LocalRiemannianData` plus explicit analytic
witnesses. Metric compatibility is derived from the data; the directional `dexp` and three
geometric ingredients must be supplied explicitly.

After Issue 7, constructors are also available WITHOUT an explicit differentiability witness
(`hdiff`), since `coordinateExp` is now proved differentiable.
-/

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

/-- Construct `LocalAnalyticRealization` from the concrete local Riemannian data package
together with explicit analytic witnesses. The `directionalDexp` field requires a differentiability
witness; the three geometric ingredients must be supplied separately. -/
noncomputable def localAnalyticRealizationOfLocalRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    (hdiff : CoordinateExpHasFDerivAtOnSource (n := n) data.Gamma p)
    (hgauss :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (w : Velocity n),
        metricPairingAt data.metricField (coordinateExp (n := n) data.Gamma p v)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) v) v)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) v) w) =
          metricPairingAt data.metricField p v w)
    (hcomp :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (γ : ℝ → Position n)
        (Tγ Uγ : ℝ → Velocity n)
        (_ : Minimization.Coordinate.IsCurveFrom (n := n) p
            (coordinateExp (n := n) data.Gamma p v) γ 0 1)
        (_ : Minimization.Coordinate.HasNormalCoordinateKinematics
            (n := n) data.Gamma p γ Tγ Uγ 0 1),
        Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) ≤
          Minimization.Coordinate.metricCurveLength (n := n) data.metricField γ 0 1 Tγ) :
    LocalAnalyticRealization (n := n) data.Gamma data.metricField p where
  directionalDexp := hasDirectionalDexp_of_localRiemannianData data p hdiff
  radialPairing := hgauss
  radius_le_metricLength := hcomp
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
                (fun {v} hv w => hgauss hv w) hv)
      _ = Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) := by
            symm
            exact Minimization.Coordinate.metricNormalRadius_exp
              (n := n) data.metricField data.Gamma p hv

/-- Canonical `LocalAnalyticInput` constructor from the concrete data package.
Metric compatibility is genuinely derived from `data`; the differentiability witness and three
geometric ingredients must be supplied explicitly. -/
noncomputable def canonicalLocalAnalyticInputOfLocalRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    (hdiff : CoordinateExpHasFDerivAtOnSource (n := n) data.Gamma p)
    (hgauss :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (w : Velocity n),
        metricPairingAt data.metricField (coordinateExp (n := n) data.Gamma p v)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) v) v)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) v) w) =
          metricPairingAt data.metricField p v w)
    (hcomp :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (γ : ℝ → Position n)
        (Tγ Uγ : ℝ → Velocity n)
        (_ : Minimization.Coordinate.IsCurveFrom (n := n) p
            (coordinateExp (n := n) data.Gamma p v) γ 0 1)
        (_ : Minimization.Coordinate.HasNormalCoordinateKinematics
            (n := n) data.Gamma p γ Tγ Uγ 0 1),
        Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) ≤
          Minimization.Coordinate.metricCurveLength (n := n) data.metricField γ 0 1 Tγ) :
    LocalAnalyticInput (n := n) data.Gamma data.metricField p :=
  LocalAnalyticRealization.toInput
    (localAnalyticRealizationOfLocalRiemannianData data p hdiff hgauss hcomp)
    data.isMetricCompatible

/-- **Witness-free** `LocalAnalyticRealization` constructor. Differentiability of `coordinateExp`
is now automatic (from Issue 7); only the three geometric ingredients need to be supplied. -/
noncomputable def localAnalyticRealizationOfLocalRiemannianData_auto
    (data : LocalRiemannianData n)
    (p : Position n)
    (hgauss :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (w : Velocity n),
        metricPairingAt data.metricField (coordinateExp (n := n) data.Gamma p v)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) v) v)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) v) w) =
          metricPairingAt data.metricField p v w)
    (hcomp :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (γ : ℝ → Position n)
        (Tγ Uγ : ℝ → Velocity n)
        (_ : Minimization.Coordinate.IsCurveFrom (n := n) p
            (coordinateExp (n := n) data.Gamma p v) γ 0 1)
        (_ : Minimization.Coordinate.HasNormalCoordinateKinematics
            (n := n) data.Gamma p γ Tγ Uγ 0 1),
        Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) ≤
          Minimization.Coordinate.metricCurveLength (n := n) data.metricField γ 0 1 Tγ) :
    LocalAnalyticRealization (n := n) data.Gamma data.metricField p where
  directionalDexp := hasDirectionalDexp_of_smoothChristoffel (n := n) data.Gamma p
  radialPairing := hgauss
  radius_le_metricLength := hcomp
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
                (fun {v} hv w => hgauss hv w) hv)
      _ = Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) := by
            symm
            exact Minimization.Coordinate.metricNormalRadius_exp
              (n := n) data.metricField data.Gamma p hv

/-- **Witness-free** canonical `LocalAnalyticInput` constructor. -/
noncomputable def canonicalLocalAnalyticInputOfLocalRiemannianData_auto
    (data : LocalRiemannianData n)
    (p : Position n)
    (hgauss :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (w : Velocity n),
        metricPairingAt data.metricField (coordinateExp (n := n) data.Gamma p v)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) v) v)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) v) w) =
          metricPairingAt data.metricField p v w)
    (hcomp :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (γ : ℝ → Position n)
        (Tγ Uγ : ℝ → Velocity n)
        (_ : Minimization.Coordinate.IsCurveFrom (n := n) p
            (coordinateExp (n := n) data.Gamma p v) γ 0 1)
        (_ : Minimization.Coordinate.HasNormalCoordinateKinematics
            (n := n) data.Gamma p γ Tγ Uγ 0 1),
        Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) ≤
          Minimization.Coordinate.metricCurveLength (n := n) data.metricField γ 0 1 Tγ) :
    LocalAnalyticInput (n := n) data.Gamma data.metricField p :=
  LocalAnalyticRealization.toInput
    (localAnalyticRealizationOfLocalRiemannianData_auto data p hgauss hcomp)
    data.isMetricCompatible

end Exponential.Coordinate
