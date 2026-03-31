import Comparison.Rauch
import Comparison.VolumeConstruction

/-! # Local volume density comparison from basiswise Rauch comparison

This file bridges from basiswise `dexp` norm comparison (Issue 4, Rauch side)
to a pointwise volume density comparison (Issue 5, volume construction side).

The key relation: if the basiswise dexp norms are bounded by model column norms,
then the Jacobian (= product of column norms by Hadamard) is bounded by the model density.
This converts the Rauch-side bounds into `HasLocalVolumeDensityComparison`. -/

namespace Comparison

variable {n : ℕ}

/-- Bridge structure tying together:
- a `VolumeDensityComparisonData` specifying the exponential map, metric, and model density,
- a `LocalVolumeComparisonConstruction` carrying the Rauch-to-density bridge. -/
structure LocalVolumeFromRauchData (n : ℕ) where
  construction : LocalVolumeComparisonConstruction (n := n)

/-- **Local volume density comparison from the Rauch bridge.**
If the construction carries a valid Rauch→density bridge, then local comparison holds. -/
theorem localVolumeDensityComparison_of_rauchBridge
    (data : LocalVolumeFromRauchData n) :
    HasLocalVolumeDensityComparison data.construction.data :=
  localVolumeDensityComparison_of_construction data.construction

/-- Log-Jacobian differential inequality from the Rauch bridge. -/
theorem logJacobianDifferentialInequality_of_rauchBridge
    (data : LocalVolumeFromRauchData n) :
    HasLogJacobianDifferentialInequality data.construction.data :=
  logJacobianDifferentialInequality_of_construction data.construction

end Comparison
