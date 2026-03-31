import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Weitzenbock.CoordinateWeitzenbock
import Bochner.ClassicalCoordinateBochner

open BigOperators Finset

namespace Weitzenbock.Coordinate

open Bochner.Coordinate

variable {n : ℕ}

abbrev SecondCovariant (n : ℕ) := Fin n → Fin n → Fin n → ℝ
abbrev SecondDerivativeFamily (n : ℕ) := Covector n → SecondCovariant n

def dDeltaFromSecond (second : SecondDerivativeFamily n) : Covector n → Covector n :=
  fun α j => -∑ i : Fin n, second α j i i

def roughFromSecond (second : SecondDerivativeFamily n) : Covector n → Covector n :=
  fun α j => -∑ i : Fin n, second α i i j

def deltaDFromSecond (second : SecondDerivativeFamily n) : Covector n → Covector n :=
  fun α j => ∑ i : Fin n, (-second α i i j + second α i j i)

def curvatureOperator (D : CoordConnectionData n) (A : End1 n) :
    Covector n → Covector n :=
  fun α => ricciAction (Bochner.curvature (coordAlgebra n D) ⟨A⟩) α

theorem trace_covector_commutator
    (D : CoordConnectionData n) (A : End1 n)
    (second : SecondDerivativeFamily n)
    (hbridge :
      ∀ (α : Covector n) (i j k : Fin n),
        covectorCommutator n D A α i j k = second α i j k - second α j i k) :
    ∀ (α : Covector n) (j : Fin n),
      ∑ i : Fin n, second α i j i =
        ∑ i : Fin n, second α j i i + curvatureOperator D A α j := by
  intro α j
  have hcomm :
      ∀ i j k : Fin n,
        second α i j k - second α j i k =
          ∑ l : Fin n, Bochner.curvature (coordAlgebra n D) ⟨A⟩ k l i j * α l := by
    intro i j k
    rw [← hbridge α i j k]
    exact classical_covector_commutator (n := n) D A α i j k
  calc
    ∑ i : Fin n, second α i j i
        = ∑ i : Fin n, (second α j i i + ∑ l : Fin n, Bochner.curvature (coordAlgebra n D) ⟨A⟩ i l i j * α l) := by
            apply Finset.sum_congr rfl
            intro i hi
            linarith [hcomm i j i]
    _ = ∑ i : Fin n, second α j i i
          + ∑ i : Fin n, ∑ l : Fin n, Bochner.curvature (coordAlgebra n D) ⟨A⟩ i l i j * α l := by
          rw [Finset.sum_add_distrib]
    _ = ∑ i : Fin n, second α j i i + curvatureOperator D A α j := by
          unfold curvatureOperator
          rw [← ricciAction_eq_double_sum (n := n) (R := Bochner.curvature (coordAlgebra n D) ⟨A⟩) (grad := α)
            (j := j)]

theorem deltaD_from_second_eq_rough_plus_ricci_minus_dDelta
    (D : CoordConnectionData n) (A : End1 n)
    (second : SecondDerivativeFamily n)
    (hbridge :
      ∀ (α : Covector n) (i j k : Fin n),
        covectorCommutator n D A α i j k = second α i j k - second α j i k) :
    ∀ α,
      deltaDFromSecond second α =
        roughFromSecond second α + curvatureOperator D A α - dDeltaFromSecond second α := by
  intro α
  funext j
  have htrace := trace_covector_commutator (n := n) D A second hbridge α j
  calc
    deltaDFromSecond second α j
        = -(∑ i : Fin n, second α i i j) + ∑ i : Fin n, second α i j i := by
            simp [deltaDFromSecond, Finset.sum_add_distrib]
    _ = -(∑ i : Fin n, second α i i j) + (∑ i : Fin n, second α j i i + curvatureOperator D A α j) := by
          rw [htrace]
    _ = (roughFromSecond second α + curvatureOperator D A α - dDeltaFromSecond second α) j := by
          simp [roughFromSecond, dDeltaFromSecond]
          ring

def hodgeDataOfSecond
    (D : CoordConnectionData n) (A : End1 n)
    (second : SecondDerivativeFamily n)
    (hbridge :
      ∀ (α : Covector n) (i j k : Fin n),
        covectorCommutator n D A α i j k = second α i j k - second α j i k) :
    HodgeData n where
  dDelta := dDeltaFromSecond second
  deltaD := deltaDFromSecond second
  rough := roughFromSecond second
  curvatureTerm := curvatureOperator D A
  deltaD_eq_rough_plus_curvature_minus_dDelta :=
    deltaD_from_second_eq_rough_plus_ricci_minus_dDelta (n := n) D A second hbridge

theorem classical_weitzenbock_one_form
    (D : CoordConnectionData n) (A : End1 n)
    (second : SecondDerivativeFamily n)
    (hbridge :
      ∀ (α : Covector n) (i j k : Fin n),
        covectorCommutator n D A α i j k = second α i j k - second α j i k) :
    ∀ α j,
      hodgeLaplacian (coordHodgeAlgebra n (hodgeDataOfSecond (n := n) D A second hbridge)) α j =
        roughFromSecond second α j + curvatureOperator D A α j := by
  intro α j
  simpa [hodgeDataOfSecond] using
    classical_weitzenbock (n := n) (hodgeDataOfSecond (n := n) D A second hbridge) α j

end Weitzenbock.Coordinate
