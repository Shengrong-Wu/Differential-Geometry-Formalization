import Exponential.LocalAnalyticInput

/-! The realization layer stays minimal: it packages directional `dexp` and the remaining
geometric bridge statements before metric compatibility is attached downstream. The three
geometric fields are now derivable from owner theorems proved upstream. -/

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

/-- The realization layer for the active local analytic branch, separated from metric
compatibility. This is the owner structure for the directional/Gauss/metric-bridge data before the
metric-compatibility witness is attached to produce `LocalAnalyticInput`. -/
structure LocalAnalyticRealization
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n) where
  directionalDexp : HasDirectionalDexp (n := n) Gamma p
  radialPairing :
    ∀ {v : Velocity n}
      (_hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
      (w : Velocity n),
      metricPairingAt g (coordinateExp (n := n) Gamma p v)
          ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
          ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) =
        metricPairingAt g p v w
  radius_le_metricLength :
    ∀ {v : Velocity n}
      (_hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
      (γ : ℝ → Position n)
      (Tγ Uγ : ℝ → Velocity n)
      (_hγ :
        Minimization.Coordinate.IsCurveFrom (n := n) p
          (coordinateExp (n := n) Gamma p v) γ 0 1)
      (_hkin :
        Minimization.Coordinate.HasNormalCoordinateKinematics
          (n := n) Gamma p γ Tγ Uγ 0 1),
      Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p
          (coordinateExp (n := n) Gamma p v) ≤
        Minimization.Coordinate.metricCurveLength (n := n) g γ 0 1 Tγ
  metricLength_le_radius :
    ∀ {v : Velocity n}
      (_hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source),
      Minimization.Coordinate.metricCurveLength (n := n) g
          (Minimization.Coordinate.radialGeodesic (n := n) Gamma p v) 0 1
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
        Minimization.Coordinate.metricNormalRadius (n := n) g Gamma p
          (coordinateExp (n := n) Gamma p v)

/-- Attach the metric-compatibility witness to a realization package to obtain the active local
analytic input consumed by the local minimization branch. -/
def LocalAnalyticRealization.toInput
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : MetricField n}
    {p : Position n}
    (realization : LocalAnalyticRealization (n := n) Gamma g p)
    (hcompat : IsMetricCompatible (n := n) Gamma g) :
    LocalAnalyticInput (n := n) Gamma g p where
  metricCompatible := hcompat
  directionalDexp := realization.directionalDexp
  radialPairing := realization.radialPairing
  radius_le_metricLength := realization.radius_le_metricLength
  metricLength_le_radius := realization.metricLength_le_radius

/-- Canonical conversion from the realization layer plus metric compatibility into the active
local analytic input package. -/
def canonicalLocalAnalyticInput
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : MetricField n}
    {p : Position n}
    (hcompat : IsMetricCompatible (n := n) Gamma g)
    (realization : LocalAnalyticRealization (n := n) Gamma g p) :
    LocalAnalyticInput (n := n) Gamma g p :=
  realization.toInput hcompat

@[simp] theorem canonicalLocalAnalyticInput_metricCompatible
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : MetricField n}
    {p : Position n}
    (hcompat : IsMetricCompatible (n := n) Gamma g)
    (realization : LocalAnalyticRealization (n := n) Gamma g p) :
    (canonicalLocalAnalyticInput hcompat realization).metricCompatible = hcompat :=
  rfl

@[simp] theorem canonicalLocalAnalyticInput_directionalDexp
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {g : MetricField n}
    {p : Position n}
    (hcompat : IsMetricCompatible (n := n) Gamma g)
    (realization : LocalAnalyticRealization (n := n) Gamma g p) :
    (canonicalLocalAnalyticInput hcompat realization).directionalDexp =
      realization.directionalDexp :=
  rfl

end Exponential.Coordinate
