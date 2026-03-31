import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Determinant

/-! # Hadamard's determinant bound -/

open Finset Module.Free InnerProductSpace Module

variable {n : ℕ}

/-- **Hadamard's inequality** for the Gram-Schmidt basis determinant. -/
theorem abs_gramSchmidt_det_le_prod_norm
    {f : Fin n → EuclideanSpace ℝ (Fin n)}
    (h : finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n)) :
    |((gramSchmidtOrthonormalBasis h f).toBasis.det f)| ≤ ∏ i : Fin n, ‖f i‖ := by
  classical
  rw [gramSchmidtOrthonormalBasis_det h f, Finset.abs_prod]
  apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
  intro i _
  calc |@inner ℝ _ _ (gramSchmidtOrthonormalBasis h f i) (f i)|
      ≤ ‖gramSchmidtOrthonormalBasis h f i‖ * ‖f i‖ := abs_real_inner_le_norm _ _
    _ = ‖f i‖ := by rw [(gramSchmidtOrthonormalBasis h f).orthonormal.1 i, one_mul]

/-- For any basis `b`, `LinearMap.det A = b.det (A ∘ b)`. -/
private theorem linearMap_det_eq_basis_det_comp
    (b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    LinearMap.det A = b.det (fun i => A (b i)) := by
  have h := b.det_comp A (fun i => b i)
  rw [Basis.det_self, mul_one] at h; exact h.symm

/-- **Hadamard's inequality for `LinearMap.det`** on `EuclideanSpace ℝ (Fin n)`. -/
theorem abs_linearMap_det_le_prod_norm
    (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    |LinearMap.det A| ≤ ∏ i : Fin n, ‖A (EuclideanSpace.basisFun (Fin n) ℝ i)‖ := by
  classical
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin n)) = Fintype.card (Fin n) := by simp
  set e := EuclideanSpace.basisFun (Fin n) ℝ
  set f : Fin n → EuclideanSpace ℝ (Fin n) := fun i => A (e i)
  set b := gramSchmidtOrthonormalBasis hdim f
  -- Step 1: LinearMap.det A = e.toBasis.det f
  rw [linearMap_det_eq_basis_det_comp e.toBasis A]
  -- Step 2: e.toBasis.det = (e.toBasis.det b) • b.toBasis.det (alternating form uniqueness)
  have hsmul : e.toBasis.det = (e.toBasis.det (fun i => b.toBasis i)) • b.toBasis.det :=
    (e.toBasis.det).eq_smul_basis_det b.toBasis
  -- So e.toBasis.det f = (e.toBasis.det b) * (b.toBasis.det f)
  have hfactor : e.toBasis.det (fun i => A (e.toBasis i)) =
      (e.toBasis.det (fun i => b.toBasis i)) * (b.toBasis.det f) := by
    have key : (e.toBasis.det) f = ((e.toBasis.det (fun i => b.toBasis i)) • b.toBasis.det) f :=
      congr_fun (AlternatingMap.coe_injective.eq_iff.mpr hsmul) f
    simp [AlternatingMap.smul_apply] at key
    exact key
  rw [hfactor, abs_mul]
  -- Step 3: |e.toBasis.det b| = 1 (orthonormal change-of-basis)
  have hone : |e.toBasis.det (fun i => b.toBasis i)| = 1 := by
    rcases OrthonormalBasis.det_to_matrix_orthonormalBasis_real e b with h1 | h1 <;> simp [h1]
  rw [hone, one_mul]
  -- Step 4: |b.toBasis.det f| ≤ ∏ ‖f i‖ (Gram-Schmidt Hadamard)
  exact abs_gramSchmidt_det_le_prod_norm hdim
