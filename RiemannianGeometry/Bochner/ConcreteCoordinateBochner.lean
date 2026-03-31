import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Bochner.ClassicalCoordinateBochner

open BigOperators Finset

namespace Bochner.Coordinate

variable {n : ℕ}

def innerProduct (u v : Gradient n) : ℝ :=
  ∑ i : Fin n, u i * v i

def hessianNormSq (H : Hessian n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, H i j * H i j

def ricciQuadratic (R : End2 n) (grad : Gradient n) : ℝ :=
  innerProduct grad (ricciAction R grad)

def laplacianGradientNormSq (grad : Gradient n) (H : Hessian n) (third : ThirdCovariant n) : ℝ :=
  (2 : ℝ) * hessianNormSq H + (2 : ℝ) * innerProduct grad (roughLaplacianGradient third)

theorem concrete_coordinate_bochner
    (D : CoordConnectionData n) (A : End1 n) (grad : Gradient n)
    (H : Hessian n) (third : ThirdCovariant n)
    (hbridge :
      ∀ i j k : Fin n,
        covectorCommutator n D A grad i j k = third i j k - third j i k)
    (hthirdSymm : ∀ i j k : Fin n, third i j k = third i k j) :
    (1 / 2 : ℝ) * laplacianGradientNormSq grad H third =
      hessianNormSq H
        + innerProduct grad (gradientScalarLaplacian third)
        + ricciQuadratic (curvature (coordAlgebra n D) ⟨A⟩) grad := by
  have htrace :=
    trace_commutator_from_covector_identity (n := n) D A grad third hbridge hthirdSymm
  have hinner :
      innerProduct grad (roughLaplacianGradient third) =
        innerProduct grad (gradientScalarLaplacian third)
          + innerProduct grad (ricciAction (curvature (coordAlgebra n D) ⟨A⟩) grad) := by
    unfold innerProduct
    calc
      ∑ j : Fin n, grad j * roughLaplacianGradient third j
          = ∑ j : Fin n,
              (grad j * gradientScalarLaplacian third j
                + grad j * ricciAction (curvature (coordAlgebra n D) ⟨A⟩) grad j) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [htrace j]
              ring
      _ = ∑ j : Fin n, grad j * gradientScalarLaplacian third j
            + ∑ j : Fin n, grad j * ricciAction (curvature (coordAlgebra n D) ⟨A⟩) grad j := by
              rw [Finset.sum_add_distrib]
  calc
    (1 / 2 : ℝ) * laplacianGradientNormSq grad H third
        = (1 / 2 : ℝ) *
            ((2 : ℝ) * hessianNormSq H
              + (2 : ℝ) * innerProduct grad (roughLaplacianGradient third)) := by
            rfl
    _ = hessianNormSq H + innerProduct grad (roughLaplacianGradient third) := by
          ring
    _ = hessianNormSq H
          + innerProduct grad (gradientScalarLaplacian third)
          + innerProduct grad (ricciAction (curvature (coordAlgebra n D) ⟨A⟩) grad) := by
          rw [hinner]
          ring
    _ = hessianNormSq H
          + innerProduct grad (gradientScalarLaplacian third)
          + ricciQuadratic (curvature (coordAlgebra n D) ⟨A⟩) grad := by
          rfl

end Bochner.Coordinate
