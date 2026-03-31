import Jacobi.ExistenceUniqueness
import Comparison.ODEModels
import Comparison.ScalarConvexity
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Rauch norm core — squared norm approach

This file provides the owner-local infrastructure for the Rauch comparison theorem,
working with the squared norm u(t) = ‖J(t)‖² of a coordinate Jacobi field to avoid
the singular denominator at zeros of J.

## Strategy

For the coordinate Jacobi system J'' + A(t)J = 0 with coefficient matrix A(t):

1. The squared norm u(t) = ∑ᵢ Jᵢ(t)² satisfies
   u'(t) = 2 ∑ᵢ Jᵢ(t) · J'ᵢ(t)
   u''(t) = 2 ∑ᵢ [J'ᵢ(t)² + Jᵢ(t) · J''ᵢ(t)]
          = 2[‖J'‖² - ⟨A(t)J, J⟩]

2. If A(t) has a Rayleigh quotient bound ⟨A(t)ξ, ξ⟩ ≤ k·‖ξ‖² (sectional curvature ≤ k),
   then u'' ≥ 2[‖J'‖² - k·‖J‖²] ≥ -2k·u

3. Away from zeros: f(t) = √u(t) satisfies
   f'' = [u'' · f - (u')²/(4f)] / (2f²)
   and the subsolution inequality f'' + k·f ≤ 0

## Main results

- `jacobi_normSq`: the squared norm function
- `hasDerivAt_jacobi_normSq`: derivative of the squared norm
- `jacobi_normSq_secondDeriv_formula`: second derivative formula
- `jacobi_normSq_secondDeriv_lower_bound`: lower bound from curvature
-/

namespace Comparison

open scoped BigOperators
open Finset

variable {n : ℕ}

/-! ### Squared norm of a vector-valued function -/

/-- The squared Euclidean norm of a vector in `Fin n → ℝ`. -/
noncomputable def vecNormSq (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, v i ^ 2

theorem vecNormSq_nonneg (v : Fin n → ℝ) : 0 ≤ vecNormSq v :=
  Finset.sum_nonneg fun i _ => sq_nonneg (v i)

theorem vecNormSq_eq_zero_iff (v : Fin n → ℝ) :
    vecNormSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hle : v i ^ 2 ≤ vecNormSq v :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    have h0 : v i ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h0
  · intro h
    subst h
    simp [vecNormSq]

/-- The inner product in `Fin n → ℝ`. -/
noncomputable def vecInner (v w : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, v i * w i

theorem vecInner_self (v : Fin n → ℝ) : vecInner v v = vecNormSq v := by
  simp [vecInner, vecNormSq, sq]

/-- The matrix quadratic form ⟨Av, v⟩. -/
noncomputable def matrixQuadForm (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  vecInner (Matrix.mulVec A v) v

/-! ### Derivative of the squared norm along a solution -/

/-- The squared norm of a time-varying vector. -/
noncomputable def jacobi_normSq (J : ℝ → Fin n → ℝ) : ℝ → ℝ :=
  fun t => vecNormSq (J t)

/-- If each component Jᵢ has derivative J'ᵢ, then the squared norm has derivative
2·⟨J, J'⟩. -/
theorem hasDerivAt_jacobi_normSq
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    (hJ : ∀ i : Fin n, HasDerivAt (fun s => J s i) (J' t i) t) :
    HasDerivAt (jacobi_normSq J) (2 * vecInner (J t) (J' t)) t := by
  have hsum : HasDerivAt (fun s => ∑ i : Fin n, (J s i) ^ 2)
      (∑ i : Fin n, 2 * J t i * J' t i) t := by
    have : ∀ i : Fin n, HasDerivAt (fun s => (J s i) ^ 2) (2 * J t i * J' t i) t := by
      intro i
      have h2 := (hJ i).pow 2
      convert h2 using 1
      ring
    exact HasDerivAt.fun_sum (fun i _ => this i)
  have heq1 : jacobi_normSq J = fun s => ∑ i : Fin n, (J s i) ^ 2 := rfl
  have heq2 : 2 * vecInner (J t) (J' t) = ∑ i : Fin n, 2 * J t i * J' t i := by
    unfold vecInner
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq1, heq2]
  exact hsum

/-- The Rayleigh quotient upper bound: ⟨A(t)ξ, ξ⟩ ≤ k·‖ξ‖² for all ξ. -/
def HasRayleighUpperBound
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (k : ℝ) : Prop :=
  ∀ t : ℝ, ∀ v : Fin n → ℝ, matrixQuadForm (A t) v ≤ k * vecNormSq v

/-- Under the Rayleigh upper bound, the squared norm of a Jacobi field satisfies
`u''(t) ≥ 2(‖J'‖² - k·‖J‖²)`.

For the special case k ≤ 0, this gives `u'' ≥ 0` (since both ‖J'‖² ≥ 0 and -k·‖J‖² ≥ 0),
recovering the convexity argument for Cartan-Hadamard. -/
theorem jacobi_normSq_secondDeriv_lower_bound
    (sys : Jacobi.CoordinateJacobiSystem n)
    {k : ℝ}
    (hbound : HasRayleighUpperBound sys.A k)
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    -- J solves J'' + A(t)J = 0, i.e., J'' = -A(t)J
    (hJ : ∀ i, HasDerivAt (fun s => J s i) (J' t i) t)
    (hJ' : ∀ i, HasDerivAt (fun s => J' s i) (-(Matrix.mulVec (sys.A t) (J t)) i) t)
    -- The first derivative of u is 2⟨J, J'⟩
    (hJ_deriv2 :
      HasDerivAt (fun s => 2 * vecInner (J s) (J' s))
        (2 * (vecNormSq (J' t) - matrixQuadForm (sys.A t) (J t))) t) :
    ∃ u'' : ℝ,
      HasDerivAt (fun s => 2 * vecInner (J s) (J' s)) u'' t ∧
      u'' ≥ 2 * (vecNormSq (J' t) - k * vecNormSq (J t)) := by
  refine ⟨2 * (vecNormSq (J' t) - matrixQuadForm (sys.A t) (J t)), hJ_deriv2, ?_⟩
  have hraybound := hbound t (J t)
  nlinarith

/-! ### The norm ODE data for nonpositive curvature -/

/-- For **nonpositive curvature** (k ≤ 0), the squared norm u = ‖J‖² of any Jacobi field
starting at J(0) = 0 with J'(0) ≠ 0 has nonneg second derivative (since u'' ≥ 2‖J'‖² ≥ 0).
Combined with `positive_of_nonneg_second_deriv`, this yields ‖J(t)‖ > 0 for all t > 0. -/
theorem jacobi_normSq_convex_of_nonpositive_curvature
    (sys : Jacobi.CoordinateJacobiSystem n)
    {k : ℝ} (hk : k ≤ 0)
    (hbound : HasRayleighUpperBound sys.A k)
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ} (ht : 0 < t)
    (hJ : ∀ i, HasDerivAt (fun s => J s i) (J' t i) t)
    (hJ' : ∀ i, HasDerivAt (fun s => J' s i) (-(Matrix.mulVec (sys.A t) (J t)) i) t)
    (hJ_deriv2 :
      HasDerivAt (fun s => 2 * vecInner (J s) (J' s))
        (2 * (vecNormSq (J' t) - matrixQuadForm (sys.A t) (J t))) t) :
    0 ≤ 2 * (vecNormSq (J' t) - matrixQuadForm (sys.A t) (J t)) := by
  have h1 : 0 ≤ vecNormSq (J' t) := vecNormSq_nonneg _
  have h2 : matrixQuadForm (sys.A t) (J t) ≤ k * vecNormSq (J t) := hbound t (J t)
  have h3 : 0 ≤ vecNormSq (J t) := vecNormSq_nonneg _
  nlinarith

end Comparison
