import Comparison.Rauch
import Measure.PolarCoordinates
import Curvature.SectionalRicci

/-! The local volume-construction layer consumes the repaired Rauch input together with the polar
density package. Bridge structures carry the genuinely missing comparison steps explicitly. -/

namespace Comparison

universe u v

/-- Local volume-density comparison data in a normal neighborhood. -/
structure VolumeDensityComparisonData {n : ℕ} where
  exp : Exponential.Coordinate.LocalExponentialMap n
  vol : Measure.Riemannian.RiemannianVolumeData (n := n)
  modelDensity : Exponential.Coordinate.Velocity n → ℝ

/-- The geometric density entering local comparison is the repaired polar Jacobian. -/
noncomputable def VolumeDensityComparisonData.density
    {n : ℕ} (data : VolumeDensityComparisonData (n := n)) :
    Exponential.Coordinate.Velocity n → ℝ :=
  Measure.Riemannian.canonicalPolarDensity data.exp data.vol

/-- Local comparison inequality for the exponential Jacobian / density. -/
def HasLocalVolumeDensityComparison
    {n : ℕ} (data : VolumeDensityComparisonData (n := n)) : Prop :=
  ∀ v, data.density v ≤ data.modelDensity v

/-- The differential inequality package that later feeds Bishop comparison. -/
def HasLogJacobianDifferentialInequality
    {n : ℕ} (data : VolumeDensityComparisonData (n := n)) : Prop :=
  HasLocalVolumeDensityComparison data

theorem localVolumeDensityComparison_of_pointwise
    {n : ℕ} {data : VolumeDensityComparisonData (n := n)}
    (h : ∀ v, data.density v ≤ data.modelDensity v) :
    HasLocalVolumeDensityComparison data :=
  h

theorem localVolumeDensityComparison_of_inducedDensity
    {n : ℕ} {data : VolumeDensityComparisonData (n := n)}
    (hpolar : Measure.Riemannian.HasPolarDecomposition data.exp data.vol)
    (h :
      ∀ v, Measure.Riemannian.pullbackDensity data.exp data.vol v ≤ data.modelDensity v) :
    HasLocalVolumeDensityComparison data := by
  intro v
  simpa [VolumeDensityComparisonData.density] using
    (show Measure.Riemannian.canonicalPolarDensity data.exp data.vol v ≤ data.modelDensity v by
      rw [← Measure.Riemannian.HasPolarDecomposition.pullbackDensity_apply hpolar v]
      exact h v)

theorem logJacobianDifferentialInequality_of_localComparison
    {n : ℕ} {data : VolumeDensityComparisonData (n := n)}
    (h : HasLocalVolumeDensityComparison data) :
    HasLogJacobianDifferentialInequality data :=
  h

/-- Construction-layer bridge for local volume comparison. Carries the Rauch → density step
as an explicit bridge field. -/
structure LocalVolumeComparisonConstruction {n : ℕ} where
  data : VolumeDensityComparisonData (n := n)
  polar : Measure.Riemannian.HasPolarDecomposition data.exp data.vol
  rauchInput : RauchInputData
  comparisonFromRauch :
    RauchNormComparison rauchInput.modelData.k rauchInput.data →
      HasLocalVolumeDensityComparison data

theorem localVolumeDensityComparison_of_construction
    {n : ℕ} (construction : LocalVolumeComparisonConstruction (n := n)) :
    HasLocalVolumeDensityComparison construction.data :=
  construction.comparisonFromRauch
    (rauch_normComparison_of_scalarComparison construction.rauchInput)

theorem logJacobianDifferentialInequality_of_construction
    {n : ℕ} (construction : LocalVolumeComparisonConstruction (n := n)) :
    HasLogJacobianDifferentialInequality construction.data :=
  logJacobianDifferentialInequality_of_localComparison
    (localVolumeDensityComparison_of_construction construction)

/-- Global volume-growth data for Bishop-Gromov comparison. -/
structure VolumeGrowthData where
  volume : ℝ → ℝ
  modelVolume : ℝ → ℝ

/-- The Bishop-Gromov ratio associated to a pair of volume profiles. -/
noncomputable def bishopGromovRatio (data : VolumeGrowthData) : ℝ → ℝ :=
  fun r => data.volume r / data.modelVolume r

/-- Global Bishop-Gromov monotonicity package: the volume ratio `V(r)/V_model(r)` is
monotone nonincreasing on positive radii. The value at `r = 0` is not packaged here because the
literal quotient `V(0) / V_model(0)` is a `0 / 0` boundary point in the current representation. -/
def HasBishopGromovMonotonicity (data : VolumeGrowthData) : Prop :=
  AntitoneOn (bishopGromovRatio data) (Set.Ioi 0)

/-- The local density comparison data induces a global volume-growth package. -/
def VolumeGrowthData.ofLocal
    {n : ℕ} (_data : VolumeDensityComparisonData (n := n))
    (volume modelVolume : ℝ → ℝ) : VolumeGrowthData where
  volume := volume
  modelVolume := modelVolume

@[simp] theorem bishopGromovRatio_ofLocal
    {n : ℕ} {localData : VolumeDensityComparisonData (n := n)}
    {volume modelVolume : ℝ → ℝ} :
    bishopGromovRatio (VolumeGrowthData.ofLocal localData volume modelVolume) =
      fun r => volume r / modelVolume r :=
  rfl

theorem bishopGromov_of_antitone_ratio
    {data : VolumeGrowthData}
    (hmono : AntitoneOn (bishopGromovRatio data) (Set.Ioi 0)) :
    HasBishopGromovMonotonicity data :=
  hmono

/-- Construction-layer bridge for the Bishop-Gromov monotonicity argument. Carries the
local → global step as an explicit bridge field. -/
structure BishopGromovConstruction {n : ℕ} where
  localData : VolumeDensityComparisonData (n := n)
  growthData : VolumeGrowthData
  monotonicityFromLocal :
    HasLogJacobianDifferentialInequality localData →
      HasBishopGromovMonotonicity growthData

theorem bishopGromov_of_construction
    {n : ℕ} (construction : BishopGromovConstruction (n := n))
    (hlocal : HasLogJacobianDifferentialInequality construction.localData) :
    HasBishopGromovMonotonicity construction.growthData :=
  construction.monotonicityFromLocal hlocal

end Comparison
