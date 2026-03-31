import Comparison.VolumeConstruction
import Comparison.VolumeComparisonLocal

/-! Public Bishop-Gromov wrapper. -/

namespace Comparison

universe u v

/-- Data package for a Bishop-Gromov theorem. -/
structure BishopGromovInput {n : ℕ} where
  construction : BishopGromovConstruction (n := n)

theorem bishopGromov_of_localVolumeComparison
    {n : ℕ} (input : BishopGromovInput (n := n))
    (hlocal : HasLogJacobianDifferentialInequality input.construction.localData) :
    HasBishopGromovMonotonicity input.construction.growthData :=
  bishopGromov_of_construction input.construction hlocal

end Comparison
