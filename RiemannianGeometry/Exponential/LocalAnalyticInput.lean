import Metric.CoordinateMetric
import Minimization.NormalCoordinateKinematics

/-! The local analytic input package records exactly the remaining bridge data consumed by the
metric minimization layer. The structure fields are the honest interface boundary for unresolved
local analytic content. -/

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

/-- The metric pairing determined by a coordinate metric field at a base point. -/
def metricPairingAt (g : MetricField n) (p : Position n) (v w : Velocity n) : ℝ :=
  Metric.Coordinate.bilinForm (g p) v w

@[simp] theorem metricPairingAt_self
    (g : MetricField n) (p : Position n) (v : Velocity n) :
    metricPairingAt (n := n) g p v v =
      Metric.Coordinate.quadraticForm (g p) v :=
  rfl

/-- A coordinate metric-compatibility predicate for the Gauss-lemma proof. -/
def IsMetricCompatible
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n) : Prop :=
  ∃ gSmooth : LeviCivita.CoordinateField.SmoothTensor2Field n,
    (∀ x i j, g x i j = gSmooth i j x) ∧
      LeviCivita.MetricCompatible
        (LeviCivita.CoordinateField.coordinateMetricPairing gSmooth)
        (LeviCivita.CoordinateField.coordinateConnectionContext n)
        (LeviCivita.CoordinateField.covariantDerivative Gamma)

/-- Explicit package for the local analytic content used by the active minimization branch.
Metric compatibility and directional `dexp` are packaged here together with the remaining
Gauss/radius/radial bridge statements that have not yet been internalized upstream. -/
structure LocalAnalyticInput
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n) where
  metricCompatible : IsMetricCompatible (n := n) Gamma g
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

end Exponential.Coordinate
