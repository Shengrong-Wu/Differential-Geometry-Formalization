import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Weitzenbock.ClassicalCoordinateWeitzenbock

open BigOperators Finset

namespace Weitzenbock.Coordinate

open Bochner.Coordinate

variable {n : ℕ}

def innerProduct (u v : Covector n) : ℝ :=
  ∑ i : Fin n, u i * v i

theorem concrete_weitzenbock_one_form
    (D : CoordConnectionData n) (A : End1 n)
    (second : SecondDerivativeFamily n)
    (hbridge :
      ∀ (α : Covector n) (i j k : Fin n),
        covectorCommutator n D A α i j k = second α i j k - second α j i k) :
    ∀ α j,
      hodgeLaplacian (coordHodgeAlgebra n (hodgeDataOfSecond (n := n) D A second hbridge)) α j =
        roughFromSecond second α j
          + ∑ l : Fin n, ricciTensor (Bochner.curvature (coordAlgebra n D) ⟨A⟩) j l * α l := by
  intro α j
  simpa [curvatureOperator, ricciAction] using
    classical_weitzenbock_one_form (n := n) D A second hbridge α j

theorem concrete_weitzenbock_pairing
    (D : CoordConnectionData n) (A : End1 n)
    (second : SecondDerivativeFamily n)
    (hbridge :
      ∀ (α : Covector n) (i j k : Fin n),
        covectorCommutator n D A α i j k = second α i j k - second α j i k) :
    ∀ α,
      innerProduct α
          (hodgeLaplacian (coordHodgeAlgebra n (hodgeDataOfSecond (n := n) D A second hbridge)) α) =
        innerProduct α (roughFromSecond second α) + innerProduct α (curvatureOperator D A α) := by
  intro α
  calc
    innerProduct α
        (hodgeLaplacian (coordHodgeAlgebra n (hodgeDataOfSecond (n := n) D A second hbridge)) α)
        = ∑ j : Fin n, α j * (roughFromSecond second α j + curvatureOperator D A α j) := by
            unfold innerProduct
            apply Finset.sum_congr rfl
            intro j hj
            rw [classical_weitzenbock_one_form (n := n) D A second hbridge α j]
    _ = ∑ j : Fin n, (α j * roughFromSecond second α j + α j * curvatureOperator D A α j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = innerProduct α (roughFromSecond second α) + innerProduct α (curvatureOperator D A α) := by
          unfold innerProduct
          rw [Finset.sum_add_distrib]

end Weitzenbock.Coordinate
