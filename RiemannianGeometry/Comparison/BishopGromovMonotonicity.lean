import Comparison.VolumeGrowthFromDensity

/-! # Bishop-Gromov monotonicity from per-ray differential inequality

This file proves that the local per-ray differential inequality on the volume density ratio
implies monotonicity of `volume(r) / modelVolume(r)` on `[0, ∞)`.

The proof is a one-dimensional integral argument: if the log-Jacobian defect has nonpositive
derivative along each radial ray, then the ratio is monotone. -/

namespace Comparison

variable {n : ℕ}

/-- Thin wrapper around the owner theorem in `VolumeGrowthFromDensity`. -/
theorem bishopGromov_monotonicity_of_local_inequality
    (data : VolumeGrowthFromDensityData (n := n))
    (hlocal : HasLogJacobianDifferentialInequality data.localData) :
    HasBishopGromovMonotonicity data.growthData :=
  bishopGromov_monotonicity_of_density_growth data hlocal

end Comparison
