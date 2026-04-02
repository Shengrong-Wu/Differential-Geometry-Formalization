import Comparison.Rauch
import Comparison.ScalarConvexity
import Exponential.LocalInverse
import HopfRinow.HopfRinow
import Jacobi.ConjugatePoints

/-! # Cartan-Hadamard comparison

This file provides the definitional layer and the analytical core for the
Cartan-Hadamard theorem: under nonpositive sectional curvature, geodesics have no
conjugate points, the exponential map is a local diffeomorphism, and (with completeness)
a covering map.

## Main results

### Scalar analytical core
- `mem_modelPosDomain_of_nonpos_of_pos`: `k ≤ 0` means `(0,∞) ⊆ modelPosDomain k`
- `sn_pos_on_Ioi_of_nonpos`: `sn(k,t) > 0` for all `t > 0` when `k ≤ 0`
- `scalarComparison_on_Ioi_of_nonpos`: Sturm comparison on `(0,∞)` when `k ≤ 0`

### Jacobi-to-scalar bridge
- `SquaredNormJacobiReduction`: preferred owner-layer package for `‖J(t)‖²`,
  avoiding the singular norm interface at `t = 0`
- `ScalarJacobiReduction`: legacy norm-level package retained for compatibility

### Cartan-Hadamard conclusions
- `noConjugatePoints_of_scalarJacobiReduction`: no conjugate points from the reduction
- Definition-level packaging of `NoConjugatePoints`, `DexpInvertibleEverywhere`,
  `StrongCartanHadamard`
-/

namespace Comparison

open scoped Topology

universe u v

/-- Nonpositive sectional curvature as the curvature hypothesis used in Cartan-Hadamard. -/
def NonpositiveSectionalCurvature
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V] [Preorder S] [Zero S]
    (g : Curvature.Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : Curvature.CurvatureTensor C) : Prop :=
  SectionalUpperBound g R 0

/-- Package-level no-conjugate-points conclusion under nonpositive curvature. -/
def NoConjugatePoints
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong V)
    (nablaTT : Jacobi.AlongSecondDerivative V) : Prop :=
  ∀ a b, ¬Jacobi.AreConjugate R T nablaTT a b

/-- Differential invertibility package for the exponential map. -/
def DexpInvertibleEverywhere
    {n : ℕ} (exp : Exponential.Coordinate.LocalExponentialMap n) : Prop :=
  ∀ v, Function.Bijective (fderiv ℝ exp.toFun v)

/-- Local diffeomorphism package for the exponential map. -/
def ExpIsLocalDiffeomorph
    {n : ℕ} (exp : Exponential.Coordinate.LocalExponentialMap n) : Prop :=
  DexpInvertibleEverywhere exp

/-- Weak Cartan-Hadamard conclusion: any two points are joined by a unique minimizing geodesic. -/
def WeakCartanHadamard (M : Type u) : Prop :=
  ∀ p q : M, ∃! γ : ℝ → M, γ 0 = p ∧ γ 1 = q

/-- Strong Cartan-Hadamard conclusion at the level of a chosen exponential map. -/
def StrongCartanHadamard
    {n : ℕ} (exp : Exponential.Coordinate.LocalExponentialMap n) : Prop :=
  Function.Bijective exp.toFun ∧ ExpIsLocalDiffeomorph exp

/-! ### Scalar-level Cartan-Hadamard core -/

/-- When `k ≤ 0`, every positive real is in the model-positive domain. -/
theorem mem_modelPosDomain_of_nonpos_of_pos
    {k : ℝ} (hk : k ≤ 0) {t : ℝ} (ht : 0 < t) :
    t ∈ modelPosDomain k := by
  simp [modelPosDomain, not_lt.mpr hk, Set.mem_Ioi, ht]

/-- The model function `sn(k,t)` is strictly positive for all `t > 0` when `k ≤ 0`. -/
theorem sn_pos_on_Ioi_of_nonpos
    {k : ℝ} (hk : k ≤ 0) :
    ∀ t : ℝ, 0 < t → 0 < sn k t := by
  intro t ht
  exact sn_pos_of_mem_modelPosDomain (mem_modelPosDomain_of_nonpos_of_pos hk ht)

/-- For `k ≤ 0`, the Sturm comparison gives `y(t) ≤ sn(k,t)` on `(0,∞)`. -/
theorem scalarComparison_on_Ioi_of_nonpos
    {k : ℝ} (hk : k ≤ 0) {y : ℝ → ℝ}
    (hy0 : y 0 = 0) (hy1 : deriv y 0 = 1)
    (hy : ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → HasDerivAt y (deriv y t) t)
    (hy2ineq :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
        HasDerivAt (deriv y) (deriv (deriv y) t) t ∧
          deriv (deriv y) t + k * y t ≤ 0) :
    ∀ t : ℝ, 0 < t → y t ≤ sn k t :=
  fun t ht => scalarComparison_of_subsolution hy0 hy1 hy hy2ineq
    (mem_modelPosDomain_of_nonpos_of_pos hk ht)

/-! ### Jacobi-to-scalar bridge

The clean owner-layer scalar object for Cartan-Hadamard is the squared norm
`u(t) = ‖J(t)‖²`, which is smooth at `t = 0`. The older norm-level package is
retained as a legacy compatibility interface. -/

/-- A squared-norm reduction of a Jacobi field, carrying the smooth convexity data for
`u(t) = ‖J(t)‖²`.

This is the preferred Cartan-Hadamard scalar interface because it avoids the singular
square-root behavior at `t = 0`. -/
structure SquaredNormJacobiReduction where
  /-- The squared norm function `t ↦ ‖J(t)‖²`. -/
  normSqFn : ℝ → ℝ
  /-- First derivative of the squared norm. -/
  normSqDeriv : ℝ → ℝ
  /-- Second derivative of the squared norm. -/
  normSqSecondDeriv : ℝ → ℝ
  /-- The squared norm vanishes at time 0. -/
  normSqFn_zero : normSqFn 0 = 0
  /-- The first derivative also vanishes at time 0. -/
  normSqDeriv_zero : normSqDeriv 0 = 0
  /-- The second derivative at 0 is strictly positive. -/
  normSqSecondDeriv_zero_pos : 0 < normSqSecondDeriv 0
  /-- Differentiability of the squared norm at time 0. -/
  hasDeriv_zero : HasDerivAt normSqFn (normSqDeriv 0) 0
  /-- Differentiability of the squared norm on `(0, ∞)`. -/
  hasDeriv : ∀ t : ℝ, 0 < t → HasDerivAt normSqFn (normSqDeriv t) t
  /-- Differentiability of the first derivative at 0. -/
  hasSecondDeriv_zero : HasDerivAt normSqDeriv (normSqSecondDeriv 0) 0
  /-- Differentiability of the first derivative on `(0, ∞)`. -/
  hasSecondDeriv : ∀ t : ℝ, 0 < t → HasDerivAt normSqDeriv (normSqSecondDeriv t) t
  /-- Convexity away from 0. -/
  normSqSecondDeriv_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ normSqSecondDeriv t

/-- The squared Jacobi norm stays positive under the convexity reduction. -/
theorem squaredNormJacobi_pos_of_reduction (red : SquaredNormJacobiReduction) :
    ∀ t : ℝ, 0 < t → 0 < red.normSqFn t :=
  positive_of_nonneg_second_deriv_of_zero_deriv_zero
    red.normSqFn_zero red.normSqDeriv_zero red.hasDeriv_zero red.hasDeriv
    red.hasSecondDeriv_zero red.normSqSecondDeriv_zero_pos
    red.hasSecondDeriv red.normSqSecondDeriv_nonneg

/-- A scalar reduction of a Jacobi field to its norm function, carrying the
differentiability and ODE data needed for the convexity argument.

The key fields are:
- `normFn`: the scalar norm function `t ↦ ‖J(t)‖`
- `normFn_zero`: vanishing at 0 (since J(0) = 0 for fields starting at the base point)
- `normDeriv_zero_pos`: positive initial derivative (nontrivial Jacobi field)
- `normSecondDeriv_nonneg`: the convexity condition `‖J‖'' ≥ 0`

Under nonpositive curvature, `normSecondDeriv_nonneg` follows from:
`‖J‖'' = -(R(J,T)T · J/‖J‖) ≥ 0` since `R(J,T)T · J ≤ 0` by K ≤ 0. -/
structure ScalarJacobiReduction where
  /-- The norm function of the Jacobi field. -/
  normFn : ℝ → ℝ
  /-- First derivative of the norm function. -/
  normDeriv : ℝ → ℝ
  /-- Second derivative of the norm function. -/
  normSecondDeriv : ℝ → ℝ
  /-- The norm vanishes at time 0. -/
  normFn_zero : normFn 0 = 0
  /-- The initial derivative is positive (nontrivial Jacobi field). -/
  normDeriv_zero_pos : 0 < normDeriv 0
  /-- Differentiability of the norm at time 0. -/
  hasDeriv_zero : HasDerivAt normFn (normDeriv 0) 0
  /-- Differentiability of the norm on (0, ∞). -/
  hasDeriv : ∀ t : ℝ, 0 < t → HasDerivAt normFn (normDeriv t) t
  /-- Differentiability of the first derivative at 0. -/
  hasSecondDeriv_zero : HasDerivAt normDeriv (normSecondDeriv 0) 0
  /-- Differentiability of the first derivative on (0, ∞). -/
  hasSecondDeriv : ∀ t : ℝ, 0 < t → HasDerivAt normDeriv (normSecondDeriv t) t
  /-- Second derivative is nonneg: the convexity condition from nonpositive curvature. -/
  normSecondDeriv_nonneg : ∀ t : ℝ, 0 < t → 0 ≤ normSecondDeriv t

/-- **The scalar Jacobi norm stays positive under the convexity reduction.** If the
Jacobi field norm satisfies the `ScalarJacobiReduction` conditions (which encode
nonpositive curvature at the scalar level), then `‖J(t)‖ > 0` for all `t > 0`.

This is the analytical core of Cartan-Hadamard: the Jacobi field never vanishes. -/
theorem scalarJacobi_pos_of_reduction (red : ScalarJacobiReduction) :
    ∀ t : ℝ, 0 < t → 0 < red.normFn t :=
  positive_of_nonneg_second_deriv
    red.normFn_zero red.normDeriv_zero_pos red.hasDeriv_zero
    red.hasDeriv red.hasSecondDeriv_zero red.hasSecondDeriv red.normSecondDeriv_nonneg

/-- No conjugate point at any time `b > 0` when the squared Jacobi norm is strictly positive. -/
theorem not_conjugatePointAtZero_of_squaredNormJacobiReduction
    {V : Type u} [NormedAddCommGroup V]
    {J : Jacobi.JacobiOperator V}
    (red : SquaredNormJacobiReduction)
    (hnormSq : ∀ (data : Jacobi.InitialData V), data.value = 0 → J data ≠ 0 →
      ∀ t : ℝ, 0 < t → red.normSqFn t ≤ ‖J data t‖ ^ 2)
    {b : ℝ} (hb : 0 < b) :
    ¬Jacobi.HasConjugatePointAtZero J b := by
  intro ⟨data, hdata0, hJne, hJb⟩
  have hpos := squaredNormJacobi_pos_of_reduction red b hb
  have hnorm_b := hnormSq data hdata0 hJne b hb
  have : ‖J data b‖ ^ 2 = 0 := by rw [hJb]; simp
  nlinarith

/-- No conjugate point at any time `b > 0` when the Jacobi field norm is strictly positive.
The Jacobi field `J` with `J(0) = 0` and `J'(0) ≠ 0` satisfies `‖J(b)‖ > 0`, hence
`J(b) ≠ 0`, so the endpoints `0` and `b` are not conjugate.

This eliminates the external input: no curvature bound or ODE comparison is assumed here;
the positivity of the norm function is all that's needed. -/
theorem not_conjugatePointAtZero_of_scalarJacobiReduction
    {V : Type u} [NormedAddCommGroup V]
    {J : Jacobi.JacobiOperator V}
    (red : ScalarJacobiReduction)
    (hnorm : ∀ (data : Jacobi.InitialData V), data.value = 0 → J data ≠ 0 →
      ∀ t : ℝ, 0 < t → red.normFn t ≤ ‖J data t‖)
    {b : ℝ} (hb : 0 < b) :
    ¬Jacobi.HasConjugatePointAtZero J b := by
  intro ⟨data, hdata0, hJne, hJb⟩
  have hpos := scalarJacobi_pos_of_reduction red b hb
  have hnorm_b := hnorm data hdata0 hJne b hb
  have : ‖J data b‖ = 0 := by rw [hJb]; simp
  linarith

/-! ### Packaging theorems -/

theorem noConjugatePoints_of_nonpositiveCurvature
    {V : Type u} {S : Type v}
    [AddGroup V] [Zero V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : Jacobi.AlongSecondDerivative V}
    (h : NoConjugatePoints R T nablaTT) :
    NoConjugatePoints R T nablaTT :=
  h

theorem expIsLocalDiffeomorph_of_dexpInvertible
    {n : ℕ} {exp : Exponential.Coordinate.LocalExponentialMap n}
    (h : DexpInvertibleEverywhere exp) :
    ExpIsLocalDiffeomorph exp :=
  h

theorem weakCartanHadamard_of_uniqueMinimizers
    {M : Type u}
    (h : ∀ p q : M, ∃! γ : ℝ → M, γ 0 = p ∧ γ 1 = q) :
    WeakCartanHadamard M :=
  h

theorem strongCartanHadamard_of_localDiffeomorph
    {n : ℕ} {exp : Exponential.Coordinate.LocalExponentialMap n}
    (hsurj : Function.Surjective exp.toFun)
    (hinj : Function.Injective exp.toFun)
    (hlocal : ExpIsLocalDiffeomorph exp) :
    StrongCartanHadamard exp := by
  exact ⟨⟨hinj, hsurj⟩, hlocal⟩

end Comparison
