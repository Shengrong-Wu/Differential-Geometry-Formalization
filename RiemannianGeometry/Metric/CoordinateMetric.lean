import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace Metric.Coordinate

variable {n : ℕ}

/-- A coordinate metric tensor in `Fin n` coordinates. -/
abbrev Tensor2 (n : ℕ) := Fin n → Fin n → ℝ

/-- A coordinate inverse metric tensor in `Fin n` coordinates. -/
abbrev InverseTensor2 (n : ℕ) := Fin n → Fin n → ℝ

/-- The quadratic form associated to a coordinate metric tensor. -/
def quadraticForm (g : Tensor2 n) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v i * g i j * v j

/-- Symmetry of a coordinate metric tensor. -/
def IsSymmetric (g : Tensor2 n) : Prop :=
  ∀ i j, g i j = g j i

/-- Positive definiteness of a coordinate metric tensor. -/
def IsPositiveDefinite (g : Tensor2 n) : Prop :=
  IsSymmetric g ∧ ∀ v : Fin n → ℝ, v ≠ 0 → 0 < quadraticForm g v

/-- `gInv` is an inverse for `g` in coordinates. -/
def IsInversePair (g : Tensor2 n) (gInv : InverseTensor2 n) : Prop :=
  ∀ i j, ∑ k : Fin n, gInv i k * g k j = if i = j then 1 else 0

/-- The `i`th standard basis vector in `Fin n` coordinates. -/
def basisVector (i : Fin n) : Fin n → ℝ :=
  Pi.single i 1

theorem isSymmetric_swap {g : Tensor2 n} (hg : IsSymmetric g) (i j : Fin n) :
    g i j = g j i :=
  hg i j

theorem inversePair_apply {g : Tensor2 n} {gInv : InverseTensor2 n}
    (h : IsInversePair g gInv) (i j : Fin n) :
    ∑ k : Fin n, gInv i k * g k j = if i = j then 1 else 0 :=
  h i j

@[simp] theorem basisVector_apply_same (i : Fin n) :
    basisVector (n := n) i i = 1 := by
  simp [basisVector]

@[simp] theorem basisVector_apply_ne {i j : Fin n} (hij : j ≠ i) :
    basisVector (n := n) i j = 0 := by
  simp [basisVector, hij]

theorem basisVector_ne_zero (i : Fin n) :
    basisVector (n := n) i ≠ 0 := by
  intro h
  have := congrArg (fun v : Fin n → ℝ => v i) h
  simpa [basisVector] using this

theorem inversePair_diag {g : Tensor2 n} {gInv : InverseTensor2 n}
    (h : IsInversePair g gInv) (i : Fin n) :
    ∑ k : Fin n, gInv i k * g k i = 1 := by
  simpa using inversePair_apply (n := n) h i i

theorem inversePair_offDiag {g : Tensor2 n} {gInv : InverseTensor2 n}
    (h : IsInversePair g gInv) {i j : Fin n} (hij : i ≠ j) :
    ∑ k : Fin n, gInv i k * g k j = 0 := by
  simp [inversePair_apply (n := n) h i j, hij]

/-- The bilinear form associated to a coordinate metric tensor. -/
def bilinForm (g : Tensor2 n) (v w : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v i * g i j * w j

theorem quadraticForm_eq_bilinForm (g : Tensor2 n) (v : Fin n → ℝ) :
    quadraticForm g v = bilinForm g v v := rfl

theorem bilinForm_comm {g : Tensor2 n} (hg : IsSymmetric g) (v w : Fin n → ℝ) :
    bilinForm g v w = bilinForm g w v := by
  simp only [bilinForm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hg j i]; ring

theorem bilinForm_basis {g : Tensor2 n} (i j : Fin n) :
    bilinForm g (basisVector i) (basisVector j) = g i j := by
  simp only [bilinForm, basisVector, Pi.single_apply]
  -- Pi.single_apply gives: if a = i then 1 else 0
  -- Outer sum: only the a = i term is nonzero
  refine (Fintype.sum_eq_single i fun a ha => ?_).trans ?_
  · simp [if_neg ha]   -- ha : a ≠ i, so `if a = i then 1 else 0 = 0`
  · -- a = i case: inner sum over b, only b = j survives
    simp only [eq_self_iff_true, if_true, one_mul]
    refine (Fintype.sum_eq_single j fun b hb => ?_).trans (by simp)
    simp [if_neg hb]   -- hb : b ≠ j

theorem IsPositiveDefinite.isSymmetric {g : Tensor2 n} (hg : IsPositiveDefinite g) :
    IsSymmetric g :=
  hg.1

theorem quadraticForm_nonneg {g : Tensor2 n} (hg : IsPositiveDefinite g)
    (v : Fin n → ℝ) : 0 ≤ quadraticForm g v := by
  by_cases hv : v = 0
  · simp [hv, quadraticForm]
  · exact le_of_lt (hg.2 v hv)

/-- Diagonal entries of a positive-definite metric are strictly positive. -/
theorem IsPositiveDefinite.pos_diag {g : Tensor2 n} (hg : IsPositiveDefinite g)
    (i : Fin n) : 0 < g i i := by
  have h := hg.2 (basisVector i) (basisVector_ne_zero i)
  have heq : quadraticForm g (basisVector i) = g i i := by
    rw [quadraticForm_eq_bilinForm, bilinForm_basis]
  linarith

/-- A positive-definite metric is nondegenerate: if the associated bilinear form vanishes
on all test vectors, the input is zero. -/
theorem IsPositiveDefinite.nondegenerate {g : Tensor2 n} (hg : IsPositiveDefinite g)
    (v : Fin n → ℝ) (h : ∀ w : Fin n → ℝ, bilinForm g v w = 0) : v = 0 := by
  by_contra hv
  have hpos : 0 < quadraticForm g v := hg.2 v hv
  rw [quadraticForm_eq_bilinForm] at hpos
  linarith [h v]

end Metric.Coordinate
