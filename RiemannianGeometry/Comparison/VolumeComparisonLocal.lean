import Comparison.VolumeConstruction

/-! Thin local-volume wrapper around `Comparison/VolumeConstruction.lean`. -/

namespace Comparison

universe u v

/-- Geometric data package for a local volume comparison theorem. -/
structure LocalVolumeComparisonInput {n : ℕ} where
  construction : LocalVolumeComparisonConstructionFromJacobianBound (n := n)

theorem localVolumeDensityComparison_of_input
    {n : ℕ} (input : LocalVolumeComparisonInput (n := n)) :
    HasLocalVolumeDensityComparison input.construction.data :=
  localVolumeDensityComparison_of_jacobianConstruction input.construction

theorem logJacobianDifferentialInequality_of_input
    {n : ℕ} (input : LocalVolumeComparisonInput (n := n)) :
    HasLogJacobianDifferentialInequality input.construction.data :=
  logJacobianDifferentialInequality_of_jacobianConstruction input.construction

end Comparison
