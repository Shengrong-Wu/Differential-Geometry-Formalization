import Comparison.ScalarJacobiComparison

/-! The Rauch reduction layer exposes the scalar comparison dependency directly through the reduced
norm data rather than hiding it behind extra owner layers. -/

namespace Comparison

/-- Norm data for a Jacobi field after reduction to a parallel orthonormal frame. -/
structure JacobiNormData where
  jacobiNorm : ℝ → ℝ
  modelNorm : ℝ → ℝ

/-- Honest norm-level data expected by the scalar Sturm comparison layer. The final Rauch proof
should consume this package instead of bare `Prop` placeholders. -/
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

/-- A packaged reduction of a Jacobi field to a scalar comparison problem. -/
structure HasRauchReduction (k : ℝ) (data : JacobiNormData) : Prop where
  pointwise_bound : SatisfiesModelNormBound k data.jacobiNorm data.modelNorm

/-- Geometric input data for the Rauch reduction layer. The actual vector-to-scalar reduction owner
theorem is still blocked, so this structure continues to carry the reduction witness explicitly
while the public `dexp` export layer stays separate. -/
structure RauchInputData where
  data : JacobiNormData
  modelData : ModelJacobiData
  normODE : RauchNormODEData data modelData
  matchesScalarModel : data.modelNorm = sn modelData.k

/-- The scalar comparison package canonically attached to Rauch input data. -/
noncomputable def RauchInputData.scalarComparisonData
    (input : RauchInputData) : ScalarJacobiComparisonData where
  jacobiNorm := input.data.jacobiNorm
  modelData := canonicalModelJacobiData input.modelData.k

/-- The norm-comparison conclusion of Rauch. -/
def RauchNormComparison (k : ℝ) (data : JacobiNormData) : Prop :=
  SatisfiesModelNormBound k data.jacobiNorm data.modelNorm

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

end Comparison
