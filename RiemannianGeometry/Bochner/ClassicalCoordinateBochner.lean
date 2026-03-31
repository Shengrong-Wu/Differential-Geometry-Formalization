import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Bochner.CoordinateBochner

open BigOperators Finset

namespace Bochner.Coordinate

variable {n : ℕ}

abbrev Gradient (n : ℕ) := Covector n
abbrev Hessian (n : ℕ) := Fin n → Fin n → ℝ
abbrev ThirdCovariant (n : ℕ) := Fin n → Fin n → Fin n → ℝ

def scalarLaplacian (H : Hessian n) : ℝ :=
  ∑ i : Fin n, H i i

def roughLaplacianGradient (T : ThirdCovariant n) : Gradient n :=
  fun j => ∑ i : Fin n, T i i j

def gradientScalarLaplacian (T : ThirdCovariant n) : Gradient n :=
  fun j => ∑ i : Fin n, T j i i

def ricciTensor (R : End2 n) : Fin n → Fin n → ℝ :=
  fun j l => ∑ i : Fin n, R i l i j

def ricciAction (R : End2 n) (grad : Gradient n) : Gradient n :=
  fun j => ∑ l : Fin n, ricciTensor R j l * grad l

private lemma fsm (f : Fin n → ℝ) (c : ℝ) :
    (∑ i : Fin n, f i) * c = ∑ i : Fin n, f i * c := by
  rw [mul_comm]
  rw [← smul_eq_mul c, Finset.smul_sum]
  simp [smul_eq_mul, mul_comm c]

theorem ricciAction_eq_double_sum (R : End2 n) (grad : Gradient n) (j : Fin n) :
    ricciAction R grad j = ∑ i : Fin n, ∑ l : Fin n, R i l i j * grad l := by
  unfold ricciAction ricciTensor
  simp_rw [fsm _ _]
  rw [sum_comm]

theorem trace_commutator
    (grad : Gradient n) (third : ThirdCovariant n) (R : End2 n)
    (hcomm :
      ∀ i j k : Fin n,
        third i j k - third j i k = ∑ l : Fin n, R k l i j * grad l)
    (hthirdSymm : ∀ i j k : Fin n, third i j k = third i k j) :
    ∀ j : Fin n,
      roughLaplacianGradient third j =
        gradientScalarLaplacian third j + ricciAction R grad j := by
  intro j
  have hswap :
      ∑ i : Fin n, third i i j = ∑ i : Fin n, third i j i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hthirdSymm i i j]
  calc
    roughLaplacianGradient third j
        = ∑ i : Fin n, third i j i := by
            simpa [roughLaplacianGradient] using hswap
    _ = ∑ i : Fin n, (third j i i + ∑ l : Fin n, R i l i j * grad l) := by
          apply Finset.sum_congr rfl
          intro i hi
          linarith [hcomm i j i]
    _ = ∑ i : Fin n, third j i i + ∑ i : Fin n, ∑ l : Fin n, R i l i j * grad l := by
          rw [Finset.sum_add_distrib]
    _ = gradientScalarLaplacian third j + ∑ i : Fin n, ∑ l : Fin n, R i l i j * grad l := by
          rfl
    _ = gradientScalarLaplacian third j + ricciAction R grad j := by
          rw [← ricciAction_eq_double_sum (n := n) R grad j]

theorem trace_commutator_from_covector_identity
    (D : CoordConnectionData n) (A : End1 n) (grad : Gradient n)
    (third : ThirdCovariant n)
    (hbridge :
      ∀ i j k : Fin n,
        covectorCommutator n D A grad i j k = third i j k - third j i k)
    (hthirdSymm : ∀ i j k : Fin n, third i j k = third i k j) :
    ∀ j : Fin n,
      roughLaplacianGradient third j =
        gradientScalarLaplacian third j
          + ricciAction (curvature (coordAlgebra n D) ⟨A⟩) grad j := by
  have hcomm :
      ∀ i j k : Fin n,
        third i j k - third j i k =
          ∑ l : Fin n, curvature (coordAlgebra n D) ⟨A⟩ k l i j * grad l := by
    intro i j k
    rw [← hbridge i j k]
    exact classical_covector_commutator (n := n) D A grad i j k
  exact trace_commutator (n := n) grad third (curvature (coordAlgebra n D) ⟨A⟩) hcomm hthirdSymm

end Bochner.Coordinate
