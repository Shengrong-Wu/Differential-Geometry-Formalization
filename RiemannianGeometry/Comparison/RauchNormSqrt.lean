import Comparison.RauchNormCore
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! # Rauch norm square-root route

This file records the owner-local algebra behind the square-root reduction
`u = ‖J‖²`, `f = √u`.

The important point is sign-sensitive:

* the existing `RauchNormCore` file works with a **Rayleigh upper bound**
  `⟪A(t)ξ, ξ⟫ ≤ k ‖ξ‖²`;
* combined with the Cauchy-Schwarz estimate on `u'`, this naturally yields the
  inequality needed for a **supersolution** route for `f = √u`.

So this file does not try to force a false `RauchNormODEData` construction.
Instead it packages the exact algebraic inequality that the current norm-squared
infrastructure really produces. -/

namespace Comparison

open scoped BigOperators

variable {n : ℕ}

/-- Cauchy-Schwarz for the explicit coordinate pairing `vecInner`. -/
theorem vecInner_sq_le_vecNormSq_mul_vecNormSq
    (v w : Fin n → ℝ) :
    vecInner v w ^ 2 ≤ vecNormSq v * vecNormSq w := by
  simpa [vecInner, vecNormSq, sq] using
    (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => v i) (fun i => w i))

/-- The derivative candidate `u' = 2⟨J,J'⟩` for `u = ‖J‖²` satisfies the
expected quadratic Cauchy-Schwarz bound. -/
theorem jacobi_normSq_velocity_sq_le
    (J J' : Fin n → ℝ) :
    (2 * vecInner J J') ^ 2 ≤ 4 * vecNormSq J * vecNormSq J' := by
  have hcs := vecInner_sq_le_vecNormSq_mul_vecNormSq J J'
  nlinarith

/-- Abstract algebraic criterion behind the square-root route.

If `u > 0` and `u'² ≤ 4ua`, then the square-root correction term
`u'² / (2u)` is bounded by `2a`. This is the exact inequality needed to pass
from a lower bound on `u''` to the sign-correct second-order inequality for
`f = √u`. -/
theorem sqrt_route_algebraic_criterion
    {u du a k : ℝ}
    (hu : 0 < u)
    (hcs : du ^ 2 ≤ 4 * u * a) :
    du ^ 2 / (2 * u) - 2 * k * u ≤ 2 * (a - k * u) := by
  have hden : 0 < 2 * u := by positivity
  have hdiv : du ^ 2 / (2 * u) ≤ 2 * a := by
    refine (div_le_iff₀ hden).2 ?_
    nlinarith
  nlinarith

/-- Under the current Rayleigh **upper** bound, the squared-norm route yields the
sign-correct inequality for a future square-root **supersolution** statement. -/
theorem jacobi_normSq_sqrt_supersolution_criterion_of_upperRayleigh_on
    (sys : Jacobi.CoordinateJacobiSystem n)
    {s : Set ℝ} {k : ℝ}
    (hbound : HasRayleighUpperBoundOn sys.A s k)
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    (ht : t ∈ s)
    (hpos : 0 < vecNormSq (J t)) :
    (2 * vecInner (J t) (J' t)) ^ 2 / (2 * vecNormSq (J t)) - 2 * k * vecNormSq (J t)
      ≤ 2 * (vecNormSq (J' t) - matrixQuadForm (sys.A t) (J t)) := by
  have hcs :
      (2 * vecInner (J t) (J' t)) ^ 2 ≤
        4 * vecNormSq (J t) * vecNormSq (J' t) :=
    jacobi_normSq_velocity_sq_le (J t) (J' t)
  have hquad :
      matrixQuadForm (sys.A t) (J t) ≤ k * vecNormSq (J t) :=
    hbound ht (J t)
  have hroute :
      (2 * vecInner (J t) (J' t)) ^ 2 / (2 * vecNormSq (J t)) - 2 * k * vecNormSq (J t)
        ≤ 2 * (vecNormSq (J' t) - k * vecNormSq (J t)) := by
    exact sqrt_route_algebraic_criterion hpos hcs
  nlinarith

/-- Under the current Rayleigh **upper** bound, the squared-norm route yields the
sign-correct inequality for a future square-root **supersolution** statement. -/
theorem jacobi_normSq_sqrt_supersolution_criterion_of_upperRayleigh
    (sys : Jacobi.CoordinateJacobiSystem n)
    {k : ℝ}
    (hbound : HasRayleighUpperBound sys.A k)
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    (hpos : 0 < vecNormSq (J t)) :
    (2 * vecInner (J t) (J' t)) ^ 2 / (2 * vecNormSq (J t)) - 2 * k * vecNormSq (J t)
      ≤ 2 * (vecNormSq (J' t) - matrixQuadForm (sys.A t) (J t)) := by
  exact jacobi_normSq_sqrt_supersolution_criterion_of_upperRayleigh_on
    (sys := sys) (s := Set.univ) (k := k) (hbound.on Set.univ) (by simp) hpos

end Comparison
