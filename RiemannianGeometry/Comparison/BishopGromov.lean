import Comparison.VolumeGrowthFromDensity

/-! Public Bishop-Gromov wrapper. -/

namespace Comparison

universe u v

/-- Data package for a Bishop-Gromov theorem on the active bridge-free path. -/
structure BishopGromovInput {n : ℕ} where
  construction : BishopGromovConstructionFromDensity (n := n)

theorem bishopGromov_of_localVolumeComparison
    {n : ℕ} (input : BishopGromovInput (n := n))
    (hlocal : HasLogJacobianDifferentialInequality input.construction.localData) :
    HasBishopGromovMonotonicity input.construction.growthData :=
  bishopGromov_of_densityConstruction input.construction hlocal

/-- **LEGACY** — Bishop-Gromov input using the older `BishopGromovConstruction` bridge. The active
path uses `BishopGromovInput` (wrapping `BishopGromovConstructionFromDensity`) instead. -/
structure BishopGromovLegacyInput {n : ℕ} where
  construction : BishopGromovConstruction (n := n)

/-- **LEGACY** — Compatibility wrapper over the legacy bridge-based Bishop-Gromov construction. -/
theorem bishopGromov_of_localVolumeComparison_legacy
    {n : ℕ} (input : BishopGromovLegacyInput (n := n))
    (hlocal : HasLogJacobianDifferentialInequality input.construction.localData) :
    HasBishopGromovMonotonicity input.construction.growthData :=
  bishopGromov_of_construction input.construction hlocal

end Comparison
