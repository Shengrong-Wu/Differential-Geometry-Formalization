import Minimization.LocalMinimizers
import Mathlib.Tactic.Linarith

/-! This wrapper file exports the short-geodesic minimizing consequences. All theorems are
fully proved from their respective `LocalAnalyticInput` / `LocalAnalyticRealization` boundaries. -/

namespace Minimization.Coordinate

variable {n : ℕ}

/-- Uniqueness of minimizing radial geodesics inside a normal neighborhood. -/
def UniqueMinimizingRadialGeodesic
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ : ℝ → Exponential.Coordinate.Velocity n)
    (a b : ℝ) : Prop :=
  ∀ η : ℝ → Exponential.Coordinate.Position n,
    ∀ Tη : ℝ → Exponential.Coordinate.Velocity n,
    IsLocalLengthMinimizer (n := n) Gamma g p γ Tγ a b →
    IsLocalLengthMinimizer (n := n) Gamma g p η Tη a b →
    η a = γ a →
    η b = γ b →
    ∀ t ∈ Set.Icc a b, η t = γ t

/-- Euclidean minimizing property of the radial normal-coordinate segment. -/
theorem shortGeodesicsMinimize_euclidean
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) Gamma g)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    IsLocalEuclideanLengthMinimizer (n := n) Gamma p
      (radialGeodesic (n := n) Gamma p v) (radialVelocityField (n := n) v) 0 1 := by
  intro η Tη Uη hends hkin
  have hcurve :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) η 0 1 := by
    rcases hends with ⟨ha, hb⟩
    constructor
    · calc
        η 0 = radialGeodesic (n := n) Gamma p v 0 := ha
        _ = p := radialGeodesic_zero (n := n) Gamma p v
    · calc
        η 1 = radialGeodesic (n := n) Gamma p v 1 := hb
        _ = Exponential.Coordinate.coordinateExp (n := n) Gamma p v :=
          radialGeodesic_one (n := n) Gamma p v
  have hcomp :=
    radialComparison_euclidean (n := n) Gamma g hcompat p hv η Tη Uη hcurve hkin
  have hrad :=
    radialGeodesic_length_le_radius (n := n) Gamma p (v := v) hv
  linarith

/-- Genuine metric minimizing property of the short radial geodesic with explicit bridge. -/
theorem shortGeodesicsMinimize_of_metric_bridge
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hmetricComp :
      ∀ η : ℝ → Exponential.Coordinate.Position n,
        ∀ Tη Uη : ℝ → Exponential.Coordinate.Velocity n,
        IsCurveFrom (n := n) p
          (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) η 0 1 →
        HasNormalCoordinateKinematics (n := n) Gamma p η Tη Uη 0 1 →
        metricNormalRadius (n := n) g Gamma p
          (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
            metricCurveLength (n := n) g η 0 1 Tη)
    (hradial :
      metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v)) :
    IsLocalLengthMinimizer (n := n) Gamma g p
      (radialGeodesic (n := n) Gamma p v)
      (radialGeodesicMetricVelocity (n := n) Gamma p v) 0 1 := by
  intro η Tη Uη hends hkin
  have hcurve :
      IsCurveFrom (n := n) p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) η 0 1 := by
    rcases hends with ⟨ha, hb⟩
    constructor
    · calc
        η 0 = radialGeodesic (n := n) Gamma p v 0 := ha
        _ = p := radialGeodesic_zero (n := n) Gamma p v
    · calc
        η 1 = radialGeodesic (n := n) Gamma p v 1 := hb
        _ = Exponential.Coordinate.coordinateExp (n := n) Gamma p v :=
          radialGeodesic_one (n := n) Gamma p v
  have hcomp :=
    radialComparison_metric_of_metric_bridge (n := n) Gamma g p hmetricComp η Tη Uη hcurve hkin
  linarith

/-- Genuine metric minimizing property of the short radial geodesic via input. -/
theorem shortGeodesicsMinimize_of_input
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    IsLocalLengthMinimizer (n := n) Gamma g p
      (radialGeodesic (n := n) Gamma p v)
      (radialGeodesicMetricVelocity (n := n) Gamma p v) 0 1 := by
  intro η Tη Uη hends hkin
  have hcurve :
      IsCurveFrom (n := n) p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) η 0 1 := by
    rcases hends with ⟨ha, hb⟩
    constructor
    · calc
        η 0 = radialGeodesic (n := n) Gamma p v 0 := ha
        _ = p := radialGeodesic_zero (n := n) Gamma p v
    · calc
        η 1 = radialGeodesic (n := n) Gamma p v 1 := hb
        _ = Exponential.Coordinate.coordinateExp (n := n) Gamma p v :=
          radialGeodesic_one (n := n) Gamma p v
  have hcomp :=
    radialComparison_metric (n := n) Gamma g p input hv η Tη Uη hcurve hkin
  have hrad :=
    radialGeodesic_metricLength_le_metricNormalRadius
      (n := n) g Gamma p input hv
  linarith

/-- Realization-layer wrapper. -/
theorem shortGeodesicsMinimize_of_realization
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) Gamma g)
    (realization : Exponential.Coordinate.LocalAnalyticRealization (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    IsLocalLengthMinimizer (n := n) Gamma g p
      (radialGeodesic (n := n) Gamma p v)
      (radialGeodesicMetricVelocity (n := n) Gamma p v) 0 1 :=
  shortGeodesicsMinimize_of_input (n := n) Gamma g p
    (Exponential.Coordinate.canonicalLocalAnalyticInput hcompat realization) hv

/-- Genuine metric minimizing property of the short radial geodesic. -/
theorem shortGeodesicsMinimize
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    IsLocalLengthMinimizer (n := n) Gamma g p
      (radialGeodesic (n := n) Gamma p v)
      (radialGeodesicMetricVelocity (n := n) Gamma p v) 0 1 :=
  shortGeodesicsMinimize_of_input (n := n) Gamma g p input hv

/-- Inside a normal neighborhood, the local distance is the normal radius. -/
def NormalDistanceFormula
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (basePoint : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) : Prop :=
  x ∈ normalNeighborhood (n := n) Gamma basePoint ∧
    normalRadius (n := n) Gamma basePoint x =
      ‖WithLp.toLp 2 (Exponential.Coordinate.normalCoordinates (n := n) Gamma basePoint x)‖

theorem normalDistance_eq_radius
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n)
    (hx : x ∈ normalNeighborhood (n := n) Gamma p) :
    NormalDistanceFormula (n := n) Gamma p x := by
  exact ⟨hx, rfl⟩

end Minimization.Coordinate
