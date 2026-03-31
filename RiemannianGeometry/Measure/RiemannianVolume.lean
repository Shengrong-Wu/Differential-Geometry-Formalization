import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Exponential.GaussLemma
import Metric.CoordinateMetric

namespace Measure.Riemannian

open scoped ENNReal

variable {n : ℕ}

/-- A coordinate metric field over a chart domain. -/
abbrev MetricField (n : ℕ) :=
  Exponential.Coordinate.Position n → Metric.Coordinate.Tensor2 n

/-- Convert a coordinate tensor to its `Matrix` representation. -/
def tensorToMatrix (g : Metric.Coordinate.Tensor2 n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => g i j

@[simp] theorem tensorToMatrix_apply
    (g : Metric.Coordinate.Tensor2 n) (i j : Fin n) :
    tensorToMatrix g i j = g i j :=
  rfl

theorem tensorToMatrix_injective :
    Function.Injective (tensorToMatrix (n := n)) := by
  intro g g' h
  funext i j
  exact congrArg (fun M => M i j) h

/-- The coordinate density attached to a single coordinate metric tensor. -/
noncomputable def densityOfTensor (g : Metric.Coordinate.Tensor2 n) : ℝ :=
  Real.sqrt (Matrix.det (tensorToMatrix g))

theorem densityOfTensor_nonneg
    (g : Metric.Coordinate.Tensor2 n) :
    0 ≤ densityOfTensor g :=
  Real.sqrt_nonneg _

theorem densityOfTensor_congr
    {g g' : Metric.Coordinate.Tensor2 n}
    (hgg' : ∀ i j, g i j = g' i j) :
    densityOfTensor g = densityOfTensor g' := by
  apply congrArg Real.sqrt
  apply congrArg Matrix.det
  funext i j
  exact hgg' i j

/-- The chart density obtained pointwise from a coordinate metric field. -/
noncomputable def densityFromMetricField (g : MetricField n) :
    Exponential.Coordinate.Position n → ℝ :=
  fun x => densityOfTensor (g x)

theorem densityFromMetricField_congr
    {g g' : MetricField n}
    (hgg' : ∀ x i j, g x i j = g' x i j) :
    densityFromMetricField g = densityFromMetricField g' := by
  funext x
  exact densityOfTensor_congr (hgg' x)

/-- Coordinate density for the package-owned Riemannian volume measure. -/
def IsDensity (ρ : Exponential.Coordinate.Position n → ℝ) : Prop :=
  ∀ x, 0 ≤ ρ x

theorem isDensity_iff
    {ρ : Exponential.Coordinate.Position n → ℝ} :
    IsDensity ρ ↔ ∀ x, 0 ≤ ρ x :=
  Iff.rfl

/-- A chart-level package for the Riemannian volume measure. -/
structure RiemannianVolumeData where
  densityFn : Exponential.Coordinate.Position n → ℝ
  nonneg_density : IsDensity densityFn

/-- The nonnegative `ENNReal` density corresponding to the packaged chart density. -/
noncomputable def RiemannianVolumeData.densityENNReal
    (vol : RiemannianVolumeData (n := n)) :
    Exponential.Coordinate.Position n → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (vol.densityFn x)

@[simp] theorem RiemannianVolumeData.densityENNReal_apply
    (vol : RiemannianVolumeData (n := n))
    (x : Exponential.Coordinate.Position n) :
    vol.densityENNReal x = ENNReal.ofReal (vol.densityFn x) :=
  rfl

/-- The actual measure on the coordinate chart induced by the packaged density. -/
noncomputable def RiemannianVolumeData.toMeasure
    (vol : RiemannianVolumeData (n := n)) :
    MeasureTheory.Measure (Exponential.Coordinate.Position n) :=
  (MeasureTheory.volume : MeasureTheory.Measure (Exponential.Coordinate.Position n)).withDensity
    vol.densityENNReal

@[simp] theorem RiemannianVolumeData.toMeasure_apply
    (vol : RiemannianVolumeData (n := n))
    {s : Set (Exponential.Coordinate.Position n)} (hs : MeasurableSet s) :
    vol.toMeasure s =
      ∫⁻ x in s, vol.densityENNReal x
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Exponential.Coordinate.Position n)) := by
  simpa [RiemannianVolumeData.toMeasure] using
    (MeasureTheory.withDensity_apply
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (Exponential.Coordinate.Position n)))
      vol.densityENNReal hs)

theorem riemannianVolumeData_ext
    {vol vol' : RiemannianVolumeData (n := n)}
    (hdensity : ∀ x, vol.densityFn x = vol'.densityFn x) :
    vol = vol' := by
  cases vol with
  | mk density hnonneg =>
      cases vol' with
      | mk density' hnonneg' =>
          have hdensity' : density = density' := by
            funext x
            exact hdensity x
          subst hdensity'
          simp

theorem riemannianVolumeData_ext_iff
    {vol vol' : RiemannianVolumeData (n := n)} :
    vol = vol' ↔ ∀ x, vol.densityFn x = vol'.densityFn x := by
  constructor
  · intro h x
    simpa [h]
  · intro h
    exact riemannianVolumeData_ext h

theorem nonneg_density
    (vol : RiemannianVolumeData (n := n)) :
    ∀ x, 0 ≤ vol.densityFn x :=
  vol.nonneg_density

theorem isDensity_densityFromMetricField
    (g : MetricField n) :
    IsDensity (densityFromMetricField g) := by
  intro x
  exact densityOfTensor_nonneg (g x)

/-- Construct chart-level volume data directly from a coordinate metric field. -/
noncomputable def volumeDataOfMetricField (g : MetricField n) :
    RiemannianVolumeData (n := n) where
  densityFn := densityFromMetricField g
  nonneg_density := isDensity_densityFromMetricField g

/-- The actual measure induced by a coordinate metric field. -/
noncomputable def volumeMeasureOfMetricField (g : MetricField n) :
    MeasureTheory.Measure (Exponential.Coordinate.Position n) :=
  (volumeDataOfMetricField g).toMeasure

@[simp] theorem volumeMeasureOfMetricField_apply
    (g : MetricField n)
    {s : Set (Exponential.Coordinate.Position n)} (hs : MeasurableSet s) :
    volumeMeasureOfMetricField (n := n) g s =
      ∫⁻ x in s, ENNReal.ofReal (densityOfTensor (g x))
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Exponential.Coordinate.Position n)) := by
  rw [volumeMeasureOfMetricField, RiemannianVolumeData.toMeasure_apply _ hs]
  simp [RiemannianVolumeData.densityENNReal, volumeDataOfMetricField, densityFromMetricField]

@[simp] theorem volumeDataOfMetricField_densityFn
    (g : MetricField n) (x : Exponential.Coordinate.Position n) :
    (volumeDataOfMetricField g).densityFn x = densityOfTensor (g x) :=
  rfl

theorem volumeDataOfMetricField_congr
    {g g' : MetricField n}
    (hgg' : ∀ x i j, g x i j = g' x i j) :
    volumeDataOfMetricField g = volumeDataOfMetricField g' := by
  apply riemannianVolumeData_ext
  intro x
  exact congrArg (fun ρ => ρ x) (densityFromMetricField_congr hgg')

theorem riemannianVolumeData_eq_volumeDataOfMetricField_iff
    {vol : RiemannianVolumeData (n := n)} {g : MetricField n} :
    vol = volumeDataOfMetricField g ↔
      ∀ x, vol.densityFn x = densityOfTensor (g x) := by
  constructor
  · intro h x
    simpa [h] using volumeDataOfMetricField_densityFn (g := g) x
  · intro h
    apply riemannianVolumeData_ext
    exact h

/-- Equality of density functions under chart change. This is the theorem-level target that later
will be proved using Jacobian change of variables. -/
def CompatibleUnderChartChange
    (vol vol' : RiemannianVolumeData (n := n)) : Prop :=
  ∀ x, vol.densityFn x = vol'.densityFn x

theorem compatibleUnderChartChange_iff_eq
    {vol vol' : RiemannianVolumeData (n := n)} :
    CompatibleUnderChartChange vol vol' ↔ vol = vol' := by
  exact riemannianVolumeData_ext_iff.symm

theorem eq_iff_compatibleUnderChartChange
    {vol vol' : RiemannianVolumeData (n := n)} :
    vol = vol' ↔ CompatibleUnderChartChange vol vol' := by
  rw [compatibleUnderChartChange_iff_eq]

theorem compatibleUnderChartChange_of_density
    {ρ : Exponential.Coordinate.Position n → ℝ}
    (hρ : IsDensity ρ) :
    CompatibleUnderChartChange
      (n := n)
      { densityFn := ρ, nonneg_density := hρ }
      { densityFn := ρ, nonneg_density := hρ } := by
  intro x
  rfl

theorem compatibleUnderChartChange_refl
    (vol : RiemannianVolumeData (n := n)) :
    CompatibleUnderChartChange vol vol := by
  intro x
  rfl

theorem compatibleUnderChartChange_symm
    {vol vol' : RiemannianVolumeData (n := n)}
    (hvol : CompatibleUnderChartChange vol vol') :
    CompatibleUnderChartChange vol' vol := by
  intro x
  symm
  exact hvol x

theorem compatibleUnderChartChange_trans
    {vol₁ vol₂ vol₃ : RiemannianVolumeData (n := n)}
    (h₁₂ : CompatibleUnderChartChange vol₁ vol₂)
    (h₂₃ : CompatibleUnderChartChange vol₂ vol₃) :
    CompatibleUnderChartChange vol₁ vol₃ := by
  intro x
  rw [h₁₂ x, h₂₃ x]

theorem isDensity_of_compatibleUnderChartChange_left
    {vol vol' : RiemannianVolumeData (n := n)}
    (_hvol : CompatibleUnderChartChange vol vol') :
    IsDensity vol.densityFn :=
  vol.nonneg_density

theorem isDensity_of_compatibleUnderChartChange_right
    {vol vol' : RiemannianVolumeData (n := n)}
    (_hvol : CompatibleUnderChartChange vol vol') :
    IsDensity vol'.densityFn :=
  vol'.nonneg_density

theorem compatibleUnderChartChange_of_metricField_eq
    {g g' : MetricField n}
    (hgg' : ∀ x i j, g x i j = g' x i j) :
    CompatibleUnderChartChange (volumeDataOfMetricField g) (volumeDataOfMetricField g') := by
  rw [compatibleUnderChartChange_iff_eq]
  exact volumeDataOfMetricField_congr hgg'

theorem compatibleUnderChartChange_volumeDataOfMetricField_iff
    {vol : RiemannianVolumeData (n := n)} {g : MetricField n} :
    CompatibleUnderChartChange vol (volumeDataOfMetricField g) ↔
      ∀ x, vol.densityFn x = densityOfTensor (g x) := by
  rw [compatibleUnderChartChange_iff_eq, riemannianVolumeData_eq_volumeDataOfMetricField_iff]

end Measure.Riemannian
