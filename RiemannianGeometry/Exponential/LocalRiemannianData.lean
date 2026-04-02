import Exponential.Differentiability
import Exponential.LocalAnalyticInput
import LeviCivita.CoordinateFields
import Metric.CoordinateMetricBounds

/-! Concrete local Riemannian data: metric tensor, inverse, symmetry, positive definiteness.
This file is purely about metric data and metric compatibility. It does not carry or derive
any differentiability facts for the exponential map. -/

namespace Exponential.Coordinate

variable {n : ℕ}

/-- Local smooth Riemannian data in the fixed coordinate model: a smooth metric tensor, a smooth
inverse tensor, symmetry for both, and the inverse-pair relation. -/
structure LocalRiemannianData (n : ℕ) where
  gSmooth : LeviCivita.CoordinateField.SmoothTensor2Field n
  gInvSmooth : LeviCivita.CoordinateField.SmoothTensor2Field n
  symm : LeviCivita.CoordinateField.IsSymmetricField gSmooth
  symmInv : LeviCivita.CoordinateField.IsSymmetricField gInvSmooth
  invPair : LeviCivita.CoordinateField.IsInversePairField gSmooth gInvSmooth
  posDef : ∀ x, Metric.Coordinate.IsPositiveDefinite (LeviCivita.CoordinateField.tensorAt gSmooth x)

namespace LocalRiemannianData

/-- The concrete coordinate metric field carried by local smooth Riemannian data. -/
def metricField (data : LocalRiemannianData n) : MetricField n :=
  fun x => LeviCivita.CoordinateField.tensorAt data.gSmooth x

/-- The Levi-Civita Christoffel field induced by the local smooth metric data. -/
noncomputable def Gamma (data : LocalRiemannianData n) :
    LeviCivita.CoordinateField.SmoothChristoffelField n :=
  LeviCivita.CoordinateField.leviCivitaChristoffelField data.gInvSmooth data.gSmooth

/-- Pointwise positive definiteness of the concrete coordinate metric field. -/
theorem metricField_posDef (data : LocalRiemannianData n) (x : Position n) :
    Metric.Coordinate.IsPositiveDefinite (data.metricField x) :=
  data.posDef x

/-- A global lower comparison of the metric with the ambient coordinate sup norm. This is a
strong global nonescape hypothesis: unlike compact-base norm comparison, it is uniform in the base
point `x`. -/
def HasGlobalMetricLowerBound (data : LocalRiemannianData n) : Prop :=
  ∃ m : ℝ, 0 < m ∧
    ∀ x : Position n, ∀ v : Velocity n,
      m * Metric.Coordinate.supNormSq v ≤
        Metric.Coordinate.quadraticForm (data.metricField x) v

/-- Unpack the global lower metric bound. -/
theorem hasGlobalMetricLowerBound_iff
    (data : LocalRiemannianData n) :
    data.HasGlobalMetricLowerBound ↔
      ∃ m : ℝ, 0 < m ∧
        ∀ x : Position n, ∀ v : Velocity n,
          m * Metric.Coordinate.supNormSq v ≤
            Metric.Coordinate.quadraticForm (data.metricField x) v := by
  rfl

/-- On any compact position set, the metric carried by `LocalRiemannianData` is uniformly
equivalent to the ambient coordinate sup norm. -/
theorem exists_uniform_metric_normComparisonOn_isCompact
    (data : LocalRiemannianData n)
    {K : Set (Position n)} (hK : IsCompact K) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ x ∈ K, ∀ v : Velocity n,
        m * Metric.Coordinate.supNormSq v ≤
          Metric.Coordinate.quadraticForm (data.metricField x) v ∧
        Metric.Coordinate.quadraticForm (data.metricField x) v ≤
          M * Metric.Coordinate.supNormSq v := by
  simpa [LocalRiemannianData.metricField] using
    Metric.Coordinate.exists_uniform_metric_normComparisonOn_isCompact
      (n := n) hK
      (g := fun x => LeviCivita.CoordinateField.tensorAt data.gSmooth x)
      (gInv := fun x => LeviCivita.CoordinateField.tensorAt data.gInvSmooth x)
      (LeviCivita.CoordinateField.SmoothTensor2Field.continuousOn_tensorAt data.gSmooth)
      (LeviCivita.CoordinateField.SmoothTensor2Field.continuousOn_tensorAt data.gInvSmooth)
      (fun x hx => data.posDef x)
      (fun x hx => data.invPair x)

/-- The induced Levi-Civita Christoffel field is metric compatible with the underlying coordinate
metric field. -/
theorem isMetricCompatible (data : LocalRiemannianData n) :
    IsMetricCompatible (n := n) data.Gamma data.metricField := by
  refine ⟨data.gSmooth, ?_, ?_⟩
  · intro x i j
    rfl
  · simpa [Gamma, metricField, LeviCivita.CoordinateField.coordinateMetricPairing] using
      (LeviCivita.CoordinateField.leviCivitaCovariantDerivative_metricCompatible
        data.gSmooth data.gInvSmooth data.symm data.symmInv data.invPair)

end LocalRiemannianData

end Exponential.Coordinate
