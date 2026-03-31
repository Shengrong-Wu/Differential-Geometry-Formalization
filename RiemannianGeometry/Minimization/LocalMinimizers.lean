import Minimization.MetricBridge

/-! Local minimizer statements stay downstream of `MetricBridge`. All theorems are proved from
their respective `LocalAnalyticInput` / `LocalAnalyticRealization` interface boundaries. -/

namespace Minimization.Coordinate

variable {n : ℕ}

/-- Euclidean minimizing property in normal coordinates. -/
def IsLocalEuclideanLengthMinimizer
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ : ℝ → Exponential.Coordinate.Velocity n)
    (a b : ℝ) : Prop :=
  ∀ η : ℝ → Exponential.Coordinate.Position n,
    ∀ Tη Uη : ℝ → Exponential.Coordinate.Velocity n,
    IsCurveFrom (n := n) (γ a) (γ b) η a b →
    HasNormalCoordinateKinematics (n := n) Gamma p η Tη Uη a b →
    Variation.Curve.curveLength (n := n) a b Tγ ≤
      Variation.Curve.curveLength (n := n) a b Uη

/-- Genuine local minimizing property measured by the coordinate metric length. -/
def IsLocalLengthMinimizer
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ : ℝ → Exponential.Coordinate.Velocity n)
    (a b : ℝ) : Prop :=
  ∀ η : ℝ → Exponential.Coordinate.Position n,
    ∀ Tη Uη : ℝ → Exponential.Coordinate.Velocity n,
    IsCurveFrom (n := n) (γ a) (γ b) η a b →
    HasNormalCoordinateKinematics (n := n) Gamma p η Tη Uη a b →
    metricCurveLength (n := n) g γ a b Tγ ≤
      metricCurveLength (n := n) g η a b Tη

/-- Euclidean comparison theorem at the minimization layer. -/
theorem radialComparison_euclidean
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) Gamma g)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    normalRadius (n := n) Gamma p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      Variation.Curve.curveLength (n := n) 0 1 Uγ := by
  let _ := g
  let _ := hcompat
  exact normalRadius_le_curveLength_of_kinematics (n := n) Gamma p hv γ Tγ Uγ hγ hkin

/-- Metric comparison theorem with explicit bridge hypothesis. -/
theorem radialComparison_metric_of_metric_bridge
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
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      metricCurveLength (n := n) g γ 0 1 Tγ :=
  hmetricComp γ Tγ Uγ hγ hkin

/-- Public metric comparison theorem via input package. -/
theorem radialComparison_metric_of_input
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
      metricCurveLength (n := n) g γ 0 1 Tγ := by
  exact metricNormalRadius_le_metricCurveLength_of_kinematics
    (n := n) Gamma g p input hv γ Tγ Uγ hγ hkin

/-- Realization-layer wrapper for the public metric comparison theorem. -/
theorem radialComparison_metric_of_realization
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
  radialComparison_metric_of_input (n := n) Gamma g p
    (Exponential.Coordinate.canonicalLocalAnalyticInput hcompat realization)
    hv γ Tγ Uγ hγ hkin

/-- Public metric comparison theorem. -/
theorem radialComparison_metric
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
  radialComparison_metric_of_input (n := n) Gamma g p input hv γ Tγ Uγ hγ hkin

end Minimization.Coordinate
