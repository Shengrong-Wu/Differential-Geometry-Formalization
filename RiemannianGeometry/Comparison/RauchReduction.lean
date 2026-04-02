import Comparison.ScalarJacobiComparison

/-! The Rauch reduction layer exposes the scalar comparison dependency directly through the reduced
norm data rather than hiding it behind extra owner layers. -/

namespace Comparison

/-- Norm data for a Jacobi field after reduction to a parallel orthonormal frame. -/
structure JacobiNormData where
  jacobiNorm : ℝ → ℝ
  modelNorm : ℝ → ℝ

/-- **LEGACY** — Subsolution norm data for the old Rauch reduction route. The active comparison
path uses `HasScalarJacobiComparison` / `RauchNormSupersolutionData` instead. Kept only for
backward compatibility with consumers that still speak the subsolution API. -/
structure RauchNormODEData
    (data : JacobiNormData) (modelData : ModelJacobiData) : Prop where
  initialValue : data.jacobiNorm 0 = 0
  initialSlope : deriv data.jacobiNorm 0 = 1
  hasFirstDeriv :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain modelData.k →
      HasDerivAt data.jacobiNorm (deriv data.jacobiNorm t) t
  normSubsolution :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain modelData.k →
      HasDerivAt (deriv data.jacobiNorm) (deriv (deriv data.jacobiNorm) t) t ∧
        deriv (deriv data.jacobiNorm) t + modelData.k * data.jacobiNorm t ≤ 0

/-- Supersolution-flavored norm data for the repaired Rauch reduction route. This matches the sign
naturally produced by the squared-norm/square-root argument and should be preferred over the older
subsolution-oriented compatibility package when the geometry supplies that stronger route. -/
structure RauchNormSupersolutionData
    (data : JacobiNormData) (modelData : ModelJacobiData) : Prop where
  initialValue : data.jacobiNorm 0 = 0
  initialSlope : deriv data.jacobiNorm 0 = 1
  hasFirstDeriv :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain modelData.k →
      HasDerivAt data.jacobiNorm (deriv data.jacobiNorm t) t
  normSupersolution :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain modelData.k →
      HasDerivAt (deriv data.jacobiNorm) (deriv (deriv data.jacobiNorm) t) t ∧
        0 ≤ deriv (deriv data.jacobiNorm) t + modelData.k * data.jacobiNorm t

/-- A packaged reduction of a Jacobi field to a scalar comparison problem. -/
structure HasRauchReduction (k : ℝ) (data : JacobiNormData) : Prop where
  pointwise_bound : SatisfiesModelNormBound k data.jacobiNorm data.modelNorm

/-- **LEGACY** — Geometric input data for the old Rauch reduction route. The active comparison path
uses `ScalarJacobiComparisonData` + `HasScalarJacobiComparison` directly. This structure is kept
only for backward compatibility; new code should not depend on it. -/
structure RauchInputData where
  data : JacobiNormData
  modelData : ModelJacobiData
  normODE : RauchNormODEData data modelData
  matchesScalarModel : data.modelNorm = sn modelData.k

/-- Supersolution-side Rauch input. This is the honest compatibility package for the repaired
vector-to-scalar reduction route; the older `RauchInputData` remains only for legacy consumers
that still speak the subsolution API. -/
structure RauchSupersolutionInputData where
  data : JacobiNormData
  modelData : ModelJacobiData
  normODE : RauchNormSupersolutionData data modelData
  matchesScalarModel : data.modelNorm = sn modelData.k

/-- The scalar comparison package canonically attached to Rauch input data. -/
noncomputable def RauchInputData.scalarComparisonData
    (input : RauchInputData) : ScalarJacobiComparisonData where
  jacobiNorm := input.data.jacobiNorm
  modelData := canonicalModelJacobiData input.modelData.k

/-- The supersolution-side scalar comparison package canonically attached to repaired Rauch input
data. -/
noncomputable def RauchSupersolutionInputData.scalarComparisonData
    (input : RauchSupersolutionInputData) : ScalarJacobiComparisonData where
  jacobiNorm := input.data.jacobiNorm
  modelData := canonicalModelJacobiData input.modelData.k

/-- The norm-comparison conclusion of Rauch. -/
def RauchNormComparison (k : ℝ) (data : JacobiNormData) : Prop :=
  SatisfiesModelNormBound k data.jacobiNorm data.modelNorm

/-- Supersolution-side norm comparison conclusion of Rauch. This is the honest target of the
positivity-set `‖J‖` route: the model lies below the Jacobi norm. -/
def RauchNormLowerComparison (k : ℝ) (data : JacobiNormData) : Prop :=
  SatisfiesModelNormLowerBound k data.jacobiNorm data.modelNorm

/-- The packaged Rauch reduction can be recovered directly from the pointwise norm comparison.
This lets downstream comparison files work with the honest comparison conclusion itself, while the
older `RauchInputData` route remains only as a compatibility wrapper. -/
theorem hasRauchReduction_of_normComparison
    {k : ℝ} {data : JacobiNormData}
    (hcomp : RauchNormComparison k data) :
    HasRauchReduction k data := by
  exact ⟨hcomp⟩

/-- Package-owned Rauch theorem: once the Jacobi field is reduced to the scalar model problem, the
pointwise norm comparison follows. -/
theorem rauch_normComparison
    {k : ℝ}
    {data : JacobiNormData}
    (hred : HasRauchReduction k data) :
    RauchNormComparison k data :=
  hred.pointwise_bound

/-- Once the scalar comparison layer has produced the honest pointwise bound, the Rauch reduction
package is immediate. This theorem is the comparison-side exit point after the stored reduction
witness has been deleted from `RauchInputData`. -/
theorem hasRauchReduction_of_scalarComparison
    (input : RauchInputData) :
    HasRauchReduction input.modelData.k input.data := by
  have hmodel :
      input.scalarComparisonData.modelNorm = sn input.scalarComparisonData.modelData.k := by
    simp [RauchInputData.scalarComparisonData, ScalarJacobiComparisonData.modelNorm,
      canonicalModelJacobiData_model, canonicalModelJacobiData_k]
  have hscalar : HasScalarJacobiComparison input.scalarComparisonData :=
    hasScalarJacobiComparison_of_subsolution
      hmodel
      input.normODE.initialValue
      input.normODE.initialSlope
      input.normODE.hasFirstDeriv
      input.normODE.normSubsolution
  refine ⟨?_⟩
  intro t ht
  have hpoint := hscalar ht
  simpa [RauchInputData.scalarComparisonData, ScalarJacobiComparisonData.modelNorm,
    canonicalModelJacobiData_model, input.matchesScalarModel] using hpoint

theorem rauch_normComparison_of_scalarComparison
    (input : RauchInputData) :
    RauchNormComparison input.modelData.k input.data :=
  rauch_normComparison (hasRauchReduction_of_scalarComparison input)

/-- Supersolution-side Rauch lower comparison. This is the honest route matching the repaired
scalar supersolution theorem; it is intentionally separate from `RauchNormComparison`, which has
the opposite orientation and drives the active Jacobian-majorant path. -/
theorem rauch_lowerComparison_of_scalarSupersolution
    (input : RauchSupersolutionInputData) :
    RauchNormLowerComparison input.modelData.k input.data := by
  have hmodel :
      input.scalarComparisonData.modelNorm = sn input.scalarComparisonData.modelData.k := by
    simp [RauchSupersolutionInputData.scalarComparisonData, ScalarJacobiComparisonData.modelNorm,
      canonicalModelJacobiData_model, canonicalModelJacobiData_k]
  have hscalar : HasScalarJacobiLowerComparison input.scalarComparisonData :=
    hasScalarJacobiLowerComparison_of_supersolution
      hmodel
      input.normODE.initialValue
      input.normODE.initialSlope
      input.normODE.hasFirstDeriv
      input.normODE.normSupersolution
  intro t ht
  have hpoint := hscalar ht
  simpa [RauchSupersolutionInputData.scalarComparisonData, ScalarJacobiComparisonData.modelNorm,
    canonicalModelJacobiData_model, input.matchesScalarModel] using hpoint

end Comparison
