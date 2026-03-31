import Jacobi.ExistenceUniqueness
import Variation.SecondVariation

namespace Jacobi

universe u v

/-- A Jacobi field vanishes at two parameter values. -/
def VanishesAt
    {V : Type u} [Zero V] (J : ParallelTransport.FieldAlong V) (a b : ℝ) : Prop :=
  J a = 0 ∧ J b = 0

theorem vanishesAt_iff
    {V : Type u} [Zero V] {J : ParallelTransport.FieldAlong V} {a b : ℝ} :
    VanishesAt J a b ↔ J a = 0 ∧ J b = 0 :=
  Iff.rfl

theorem vanishesAt_comm
    {V : Type u} [Zero V] {J : ParallelTransport.FieldAlong V} {a b : ℝ} :
    VanishesAt J a b ↔ VanishesAt J b a := by
  constructor <;> intro h <;> exact ⟨h.2, h.1⟩

/-- Conjugate points along a geodesic, packaged through a nontrivial Jacobi field vanishing at both
endpoints. -/
def AreConjugate
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong V)
    (nablaTT : AlongSecondDerivative V)
    (a b : ℝ) : Prop :=
  ∃ J : ParallelTransport.FieldAlong V,
    J ≠ 0 ∧ VanishesAt J a b ∧ IsJacobiField R T nablaTT J

/-- Endpoint-value formulation of conjugate points. -/
def HasConjugateEndpointValueProblem
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong V)
    (nablaTT : AlongSecondDerivative V)
    (a b : ℝ) : Prop :=
  ∃ J : ParallelTransport.FieldAlong V, VanishesAt J a b ∧ IsJacobiField R T nablaTT J

/-- Conjugate-point data at time `0`, expressed through a concrete Jacobi solver. -/
def HasConjugatePointAtZero
    {V : Type u} [Zero V]
    (J : JacobiOperator V) (b : ℝ) : Prop :=
  ∃ data : InitialData V, data.value = 0 ∧ J data ≠ 0 ∧ J data b = 0

theorem hasConjugatePointAtZero_iff
    {V : Type u} [Zero V] {J : JacobiOperator V} {b : ℝ} :
    HasConjugatePointAtZero J b ↔
      ∃ data : InitialData V, data.value = 0 ∧ J data ≠ 0 ∧ J data b = 0 :=
  Iff.rfl

/-- Endpoint-value conjugate-point data at time `0`, expressed through a concrete Jacobi solver. -/
def HasConjugateEndpointValueProblemAtZero
    {V : Type u} [Zero V]
    (J : JacobiOperator V) (b : ℝ) : Prop :=
  ∃ data : InitialData V, data.value = 0 ∧ J data b = 0

theorem hasConjugateEndpointValueProblemAtZero_iff
    {V : Type u} [Zero V] {J : JacobiOperator V} {b : ℝ} :
    HasConjugateEndpointValueProblemAtZero J b ↔
      ∃ data : InitialData V, data.value = 0 ∧ J data b = 0 :=
  Iff.rfl

theorem hasConjugateEndpointValueProblem_of_areConjugate
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {a b : ℝ}
    (h : AreConjugate R T nablaTT a b) :
    HasConjugateEndpointValueProblem R T nablaTT a b := by
  rcases h with ⟨J, _, hvan, hJ⟩
  exact ⟨J, hvan, hJ⟩

theorem areConjugate_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {a b : ℝ} :
    AreConjugate R T nablaTT a b ↔
      ∃ J : ParallelTransport.FieldAlong V,
        J ≠ 0 ∧ VanishesAt J a b ∧ IsJacobiField R T nablaTT J :=
  Iff.rfl

theorem hasConjugateEndpointValueProblem_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {a b : ℝ} :
    HasConjugateEndpointValueProblem R T nablaTT a b ↔
      ∃ J : ParallelTransport.FieldAlong V, VanishesAt J a b ∧ IsJacobiField R T nablaTT J :=
  Iff.rfl

theorem areConjugate_zero_iff_hasConjugatePointAtZero
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J : JacobiOperator V}
    (hJ : IsJacobiOperator R T nablaTT J)
    {b : ℝ} :
    AreConjugate R T nablaTT 0 b ↔ HasConjugatePointAtZero J b := by
  constructor
  · rintro ⟨W, hWne, hvan, hWjac⟩
    let data : InitialData V := ⟨0, nablaTT W 0⟩
    have hEq : W = J data :=
      eq_of_isJacobiOperator hJ ⟨hvan.1, rfl, hWjac⟩
    refine ⟨data, rfl, ?_, ?_⟩
    · simpa [hEq] using hWne
    · simpa [hEq] using hvan.2
  · rintro ⟨data, hdata0, hJne, hJb⟩
    have hspec := isJacobiOperator_spec hJ data
    refine ⟨J data, hJne, ?_, hspec.2.2⟩
    refine ⟨?_, hJb⟩
    simpa [hdata0] using hspec.1

theorem hasConjugateEndpointValueProblem_zero_iff_hasConjugateEndpointValueProblemAtZero
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J : JacobiOperator V}
    (hJ : IsJacobiOperator R T nablaTT J)
    {b : ℝ} :
    HasConjugateEndpointValueProblem R T nablaTT 0 b ↔
      HasConjugateEndpointValueProblemAtZero J b := by
  constructor
  · rintro ⟨W, hvan, hWjac⟩
    let data : InitialData V := ⟨0, nablaTT W 0⟩
    have hEq : W = J data :=
      eq_of_isJacobiOperator hJ ⟨hvan.1, rfl, hWjac⟩
    refine ⟨data, rfl, ?_⟩
    simpa [hEq] using hvan.2
  · rintro ⟨data, hdata0, hJb⟩
    have hspec := isJacobiOperator_spec hJ data
    refine ⟨J data, ?_, hspec.2.2⟩
    refine ⟨?_, hJb⟩
    simpa [hdata0] using hspec.1

end Jacobi
