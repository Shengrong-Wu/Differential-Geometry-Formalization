import Comparison.RauchNormCore
import Comparison.Rauch
import Curvature.SectionalRicci

/-! # Rauch curvature-to-matrix bridge

This file packages the owner-local geometric step behind the Rayleigh inequality used by the
Rauch norm core.

The key point is to avoid local coordinates on an open set. The relevant data is:

* a fixed coordinate fiber `Fin n → ℝ`,
* a family `lift t : (Fin n → ℝ) → V` identifying that fixed fiber with the normal space along
  a chosen geodesic,
* the pulled-back curvature quadratic form
  `ξ ↦ g (R (lift t ξ) T(t) T(t)) (lift t ξ)`.

Once the matrix coefficient `A(t)` of the coordinate Jacobi system is known to represent this
quadratic form, and once the geodesic is unit speed with `lift t ξ ⟂ T(t)`, the sectional
curvature upper bound immediately yields the Rayleigh inequality
`⟪A(t)ξ, ξ⟫ ≤ k ‖ξ‖²`.

So this file does not solve the entire Rauch reduction. It isolates the precise geometric bridge
that remains after the active comparison spine has been made bridge-free. -/

namespace Comparison

universe u v

open Curvature

variable {n : ℕ}

/-- A normalized sectional-curvature upper bound along unit-speed, orthogonal pairs.

This is the sign/scale-correct form needed for the Rayleigh reduction:
if `Y` has unit length and `X ⟂ Y`, then
`⟪R(X,Y)Y, X⟫ ≤ k ⟪X,X⟫`. -/
def NormalizedSectionalUpperBound
    {V : Type u}
    [AddGroup V] [SMul ℝ V]
    (g : Curvature.Pairing V ℝ) {C : LeviCivita.ConnectionContext V ℝ}
    (R : Curvature.CurvatureTensor C) (k : ℝ) : Prop :=
  ∀ X Y,
    g Y Y = 1 →
    g X Y = 0 →
    Curvature.SectionalCurvature g R X Y ≤ k * g X X

/-- Data identifying the coefficient matrix `A(t)` of the coordinate Jacobi system with the
curvature operator pulled back to a fixed normal model fiber. -/
structure CurvatureMatrixBridgeData
    {V : Type u}
    [AddGroup V] [SMul ℝ V]
    {C : LeviCivita.ConnectionContext V ℝ}
    (g : Curvature.Pairing V ℝ)
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong V)
    (sys : Jacobi.CoordinateJacobiSystem n) where
  /-- The along-geodesic identification from the fixed coordinate fiber to the ambient fiber. -/
  lift : ℝ → ParallelTransport.CoordinateVector n → V
  /-- The chosen tangent field is unit speed. -/
  tangent_unit : ∀ t, g (T t) (T t) = 1
  /-- The lifted vectors stay in the normal space. -/
  lift_normal : ∀ t ξ, g (lift t ξ) (T t) = 0
  /-- The pulled-back curvature quadratic form is represented by the matrix `A(t)`. -/
  matrix_eq_curvature :
    ∀ t ξ,
      matrixQuadForm (sys.A t) ξ =
        g (R (lift t ξ) (T t) (T t)) (lift t ξ)
  /-- The lifted identification preserves squared norms. -/
  norm_sq_eq :
    ∀ t ξ,
      g (lift t ξ) (lift t ξ) = vecNormSq ξ

/-- Once the coordinate Jacobi matrix is identified with the curvature operator pulled back along
the geodesic, the normalized sectional-curvature upper bound gives the Rayleigh inequality needed
by the Rauch norm core. -/
theorem hasRayleighUpperBound_of_curvatureBridge
    {V : Type u}
    [AddGroup V] [SMul ℝ V]
    {C : LeviCivita.ConnectionContext V ℝ}
    {g : Curvature.Pairing V ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {k : ℝ}
    (hsec : NormalizedSectionalUpperBound g R k)
    (bridge : CurvatureMatrixBridgeData (n := n) g R T sys) :
    HasRayleighUpperBound sys.A k := by
  intro t ξ
  calc
    matrixQuadForm (sys.A t) ξ
        = g (R (bridge.lift t ξ) (T t) (T t)) (bridge.lift t ξ) := by
            simpa using bridge.matrix_eq_curvature t ξ
    _ ≤ k * g (bridge.lift t ξ) (bridge.lift t ξ) := by
          exact hsec (bridge.lift t ξ) (T t) (bridge.tangent_unit t) (bridge.lift_normal t ξ)
    _ = k * vecNormSq ξ := by
          rw [bridge.norm_sq_eq t ξ]

end Comparison
