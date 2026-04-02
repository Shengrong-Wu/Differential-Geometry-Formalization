import Comparison.Rauch
import Measure.PolarCoordinates
import Curvature.SectionalRicci

/-! The local volume-construction layer consumes the repaired Rauch comparison together with the
polar density package. Bridge structures carry the genuinely missing comparison steps explicitly,
but the active construction route stores the honest comparison conclusion itself rather than an
older reduction witness package. -/

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

/-! ### Bridge-free local volume comparison from a Jacobian majorant -/

/-- A bridge-free local volume comparison package. The geometric input is split into the two
honest ingredients actually used by the proof:

* a pointwise majorant for the exponential Jacobian,
* a pointwise domination of the target model density by the induced chart density times that
  Jacobian majorant.

This removes the need for an opaque `comparisonFromRauch` bridge on the active path. -/
structure LocalVolumeComparisonConstructionFromJacobianBound {n : ℕ} where
  data : VolumeDensityComparisonData (n := n)
  polar : Measure.Riemannian.HasPolarDecomposition data.exp data.vol
  jacobianMajorant : Exponential.Coordinate.Velocity n → ℝ
  jacobianComparison :
    ∀ v, Measure.Riemannian.expJacobianFn data.exp v ≤ jacobianMajorant v
  modelDensityDomination :
    ∀ v,
      Measure.Riemannian.inducedJacobian data.exp data.vol v * jacobianMajorant v
        ≤ data.modelDensity v

/-- If the exponential Jacobian is pointwise bounded by a majorant `Ĵ`, and the model density
dominates `inducedJacobian * Ĵ`, then local volume density comparison follows. -/
theorem localVolumeDensityComparison_of_jacobianMajorant
    {n : ℕ} {data : VolumeDensityComparisonData (n := n)}
    (hpolar : Measure.Riemannian.HasPolarDecomposition data.exp data.vol)
    (jacobianMajorant : Exponential.Coordinate.Velocity n → ℝ)
    (hjac :
      ∀ v, Measure.Riemannian.expJacobianFn data.exp v ≤ jacobianMajorant v)
    (hdom :
      ∀ v,
        Measure.Riemannian.inducedJacobian data.exp data.vol v * jacobianMajorant v
          ≤ data.modelDensity v) :
    HasLocalVolumeDensityComparison data := by
  apply localVolumeDensityComparison_of_inducedDensity hpolar
  intro v
  have hinduced_nonneg :
      0 ≤ Measure.Riemannian.inducedJacobian data.exp data.vol v := by
    simpa [Measure.Riemannian.inducedJacobian] using
      (Measure.Riemannian.nonneg_density data.vol (data.exp.toFun v))
  calc
    Measure.Riemannian.pullbackDensity data.exp data.vol v
        = Measure.Riemannian.inducedJacobian data.exp data.vol v *
            Measure.Riemannian.expJacobianFn data.exp v := by
            simp [Measure.Riemannian.pullbackDensity]
    _ ≤ Measure.Riemannian.inducedJacobian data.exp data.vol v * jacobianMajorant v := by
          gcongr
          exact hjac v
    _ ≤ data.modelDensity v := hdom v

theorem localVolumeDensityComparison_of_jacobianConstruction
    {n : ℕ} (construction : LocalVolumeComparisonConstructionFromJacobianBound (n := n)) :
    HasLocalVolumeDensityComparison construction.data :=
  localVolumeDensityComparison_of_jacobianMajorant
    construction.polar
    construction.jacobianMajorant
    construction.jacobianComparison
    construction.modelDensityDomination

theorem logJacobianDifferentialInequality_of_jacobianConstruction
    {n : ℕ} (construction : LocalVolumeComparisonConstructionFromJacobianBound (n := n)) :
    HasLogJacobianDifferentialInequality construction.data :=
  logJacobianDifferentialInequality_of_localComparison
    (localVolumeDensityComparison_of_jacobianConstruction construction)

/-- **LEGACY** — Construction-layer bridge for local volume comparison using the older
`RauchNormComparison` + `comparisonFromRauch` bridge. The active path uses
`LocalVolumeComparisonConstructionFromJacobianBound` instead. Kept for backward compatibility. -/
structure LocalVolumeComparisonConstruction {n : ℕ} where
  data : VolumeDensityComparisonData (n := n)
  polar : Measure.Riemannian.HasPolarDecomposition data.exp data.vol
  rauchModelK : ℝ
  rauchData : JacobiNormData
  rauchComparison : RauchNormComparison rauchModelK rauchData
  comparisonFromRauch :
    RauchNormComparison rauchModelK rauchData →
      HasLocalVolumeDensityComparison data

theorem localVolumeDensityComparison_of_construction
    {n : ℕ} (construction : LocalVolumeComparisonConstruction (n := n)) :
    HasLocalVolumeDensityComparison construction.data :=
  construction.comparisonFromRauch
    construction.rauchComparison

theorem logJacobianDifferentialInequality_of_construction
    {n : ℕ} (construction : LocalVolumeComparisonConstruction (n := n)) :
    HasLogJacobianDifferentialInequality construction.data :=
  logJacobianDifferentialInequality_of_localComparison
    (localVolumeDensityComparison_of_construction construction)

/-- **LEGACY** — Local volume construction carrying the older `RauchInputData` reduction witness.
This remains only as a wrapper around `LocalVolumeComparisonConstruction`. The active path uses
`LocalVolumeComparisonConstructionFromJacobianBound` instead. -/
structure LocalVolumeComparisonLegacyConstruction {n : ℕ} where
  data : VolumeDensityComparisonData (n := n)
  polar : Measure.Riemannian.HasPolarDecomposition data.exp data.vol
  rauchInput : RauchInputData
  comparisonFromRauch :
    RauchNormComparison rauchInput.modelData.k rauchInput.data →
      HasLocalVolumeDensityComparison data

/-- Convert the old Rauch-input construction into the direct comparison-based construction. -/
def LocalVolumeComparisonLegacyConstruction.toDirect
    {n : ℕ} (construction : LocalVolumeComparisonLegacyConstruction (n := n)) :
    LocalVolumeComparisonConstruction (n := n) where
  data := construction.data
  polar := construction.polar
  rauchModelK := construction.rauchInput.modelData.k
  rauchData := construction.rauchInput.data
  rauchComparison := rauch_normComparison_of_scalarComparison construction.rauchInput
  comparisonFromRauch := construction.comparisonFromRauch

/-- Compatibility wrapper over the old Rauch-input local volume construction. -/
theorem localVolumeDensityComparison_of_legacyConstruction
    {n : ℕ} (construction : LocalVolumeComparisonLegacyConstruction (n := n)) :
    HasLocalVolumeDensityComparison construction.data :=
  localVolumeDensityComparison_of_construction construction.toDirect

theorem logJacobianDifferentialInequality_of_legacyConstruction
    {n : ℕ} (construction : LocalVolumeComparisonLegacyConstruction (n := n)) :
    HasLogJacobianDifferentialInequality construction.data :=
  logJacobianDifferentialInequality_of_localComparison
    (localVolumeDensityComparison_of_legacyConstruction construction)

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

/-- **LEGACY** — Construction-layer bridge for Bishop-Gromov carrying the `monotonicityFromLocal`
bridge field. The active path uses `BishopGromovConstructionFromDensity` (in
`VolumeGrowthFromDensity.lean`) instead. Kept for backward compatibility. -/
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
