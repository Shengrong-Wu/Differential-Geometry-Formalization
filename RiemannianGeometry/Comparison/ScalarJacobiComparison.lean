import Comparison.SturmComparison

/-! This wrapper file converts the scalar Sturm owner theorem into the package-level
`HasScalarJacobiComparison` interface without adding new comparison structures. -/

namespace Comparison

/-- Honest scalar model data for the one-dimensional Jacobi comparison equation. -/
structure ModelJacobiData where
  k : ℝ
  model : ℝ → ℝ
  solvesODE : SolvesModelJacobiODE k model
  initial : HasModelInitialConditions model

/-- The canonical constant-curvature scalar model carried by `sn k`. -/
noncomputable def canonicalModelJacobiData (k : ℝ) : ModelJacobiData where
  k := k
  model := sn k
  solvesODE := sn_solvesModelJacobiODE k
  initial := sn_hasModelInitialConditions k

@[simp] theorem canonicalModelJacobiData_k
    (k : ℝ) :
    (canonicalModelJacobiData k).k = k :=
  rfl

@[simp] theorem canonicalModelJacobiData_model
    (k : ℝ) :
    (canonicalModelJacobiData k).model = sn k :=
  rfl

/-- Scalar comparison data: a geometric Jacobi norm together with an honest scalar model. This
file currently packages the scalar side and the domain-aware comparison target on
`modelPosDomain`; the Wronskian/Sturm owner theorem still lives outside this wrapper layer. -/
structure ScalarJacobiComparisonData where
  jacobiNorm : ℝ → ℝ
  modelData : ModelJacobiData

/-- The scalar-model norm used for comparison. -/
def ScalarJacobiComparisonData.modelNorm
    (data : ScalarJacobiComparisonData) : ℝ → ℝ :=
  data.modelData.model

/-- The honest comparison domain attached to the scalar model. -/
noncomputable def ScalarJacobiComparisonData.comparisonDomain
    (data : ScalarJacobiComparisonData) : Set ℝ :=
  modelPosDomain data.modelData.k

/-- The scalar comparison conclusion attached to honest scalar model data on the model-positive
domain. -/
def HasScalarJacobiComparison
    (data : ScalarJacobiComparisonData) : Prop :=
  SatisfiesModelNormBound data.modelData.k data.jacobiNorm data.modelNorm

theorem hasScalarJacobiComparison_of_pointwise
    {data : ScalarJacobiComparisonData}
    (h :
      ∀ ⦃t : ℝ⦄, t ∈ data.comparisonDomain → data.jacobiNorm t ≤ data.modelNorm t) :
    HasScalarJacobiComparison data :=
  h

/-- Package-level scalar comparison bridge from the canonical Sturm owner theorem. The Wronskian
sign is now derived upstream in `Comparison/SturmComparison.lean`, so this public bridge only
consumes honest scalar ODE/subsolution data on `modelPosDomain`. -/
theorem hasScalarJacobiComparison_of_subsolution
    {data : ScalarJacobiComparisonData}
    (hmodel : data.modelNorm = sn data.modelData.k)
    (hy0 : data.jacobiNorm 0 = 0)
    (hy1 : deriv data.jacobiNorm 0 = 1)
    (hy :
      ∀ ⦃t : ℝ⦄, t ∈ data.comparisonDomain →
        HasDerivAt data.jacobiNorm (deriv data.jacobiNorm t) t)
    (hy2ineq :
      ∀ ⦃t : ℝ⦄, t ∈ data.comparisonDomain →
        HasDerivAt (deriv data.jacobiNorm) (deriv (deriv data.jacobiNorm) t) t ∧
          deriv (deriv data.jacobiNorm) t + data.modelData.k * data.jacobiNorm t ≤ 0) :
    HasScalarJacobiComparison data := by
  intro t ht
  rw [hmodel]
  exact scalarComparison_of_subsolution hy0 hy1 hy hy2ineq ht

end Comparison
