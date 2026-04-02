import Comparison.RauchReduction
import Comparison.RauchNormSqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Rauch positivity-set reduction

This owner-local file packages the honest lower-bound Rauch route:

* start from a coordinate Jacobi system `J'' + A(t)J = 0`,
* assume the Rayleigh upper bound on `A(t)`,
* define the scalar norm as `√(‖J(t)‖²)`,
* work only on the positivity set where this square root is smooth,
* produce the supersolution-side scalar package used by the repaired
  comparison layer.

The remaining geometric work is to construct the positivity and initial-slope
assumptions from an actual vector Jacobi field along a geodesic. This file
keeps that remaining gap explicit instead of storing a raw scalar `normODE`
claim as external input. -/

namespace Comparison

variable {n : ℕ}

open scoped Topology

/-- The scalar norm attached to a coordinate Jacobi field. -/
noncomputable def coordinateJacobiNorm
    (J : ℝ → Fin n → ℝ) : ℝ → ℝ :=
  fun t => Real.sqrt (jacobi_normSq J t)

/-- The `u'` term for `u = ‖J‖²`. -/
noncomputable def coordinateJacobiNormVelocity
    (J J' : ℝ → Fin n → ℝ) : ℝ → ℝ :=
  fun t => 2 * vecInner (J t) (J' t)

/-- The first derivative formula for `√(‖J‖²)` on the positivity set. -/
noncomputable def coordinateJacobiNormDeriv
    (J J' : ℝ → Fin n → ℝ) : ℝ → ℝ :=
  fun t => coordinateJacobiNormVelocity J J' t / (2 * coordinateJacobiNorm J t)

/-- The `u''` term for `u = ‖J‖²` under the Jacobi equation. -/
noncomputable def coordinateJacobiNormAccel
    (sys : Jacobi.CoordinateJacobiSystem n)
    (J J' : ℝ → Fin n → ℝ) : ℝ → ℝ :=
  fun t => 2 * (vecNormSq (J' t) - matrixQuadForm (sys.A t) (J t))

/-- The quotient-rule second derivative formula for `√(‖J‖²)` on the positivity set. -/
noncomputable def coordinateJacobiNormDerivDeriv
    (sys : Jacobi.CoordinateJacobiSystem n)
    (J J' : ℝ → Fin n → ℝ) : ℝ → ℝ :=
  fun t =>
    ((coordinateJacobiNormAccel sys J J' t) * (2 * coordinateJacobiNorm J t) -
        coordinateJacobiNormVelocity J J' t *
          (coordinateJacobiNormVelocity J J' t / coordinateJacobiNorm J t)) /
      (2 * coordinateJacobiNorm J t) ^ 2

theorem coordinateJacobiNorm_eq_sqrt
    (J : ℝ → Fin n → ℝ) :
    coordinateJacobiNorm J = fun t => Real.sqrt (jacobi_normSq J t) :=
  rfl

theorem coordinateJacobiNorm_zero_of_zero_initial
    {J : ℝ → Fin n → ℝ}
    (hJ0 : J 0 = 0) :
    coordinateJacobiNorm J 0 = 0 := by
  rw [coordinateJacobiNorm, jacobi_normSq, hJ0, vecNormSq]
  simp

theorem hasDerivAt_coordinateJacobiNorm_of_positive
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    (hJ : ∀ i : Fin n, HasDerivAt (fun s => J s i) (J' t i) t)
    (hpos : 0 < jacobi_normSq J t) :
    HasDerivAt (coordinateJacobiNorm J) (coordinateJacobiNormDeriv J J' t) t := by
  have hsq :
      HasDerivAt (jacobi_normSq J) (coordinateJacobiNormVelocity J J' t) t :=
    by
      simpa [coordinateJacobiNormVelocity] using hasDerivAt_jacobi_normSq (J := J) (J' := J') hJ
  have hsq_ne : jacobi_normSq J t ≠ 0 := ne_of_gt hpos
  simpa [coordinateJacobiNorm, coordinateJacobiNormDeriv, coordinateJacobiNormVelocity] using
    hsq.sqrt hsq_ne

theorem deriv_coordinateJacobiNorm_of_positive
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    (hJ : ∀ i : Fin n, HasDerivAt (fun s => J s i) (J' t i) t)
    (hpos : 0 < jacobi_normSq J t) :
    deriv (coordinateJacobiNorm J) t = coordinateJacobiNormDeriv J J' t :=
  (hasDerivAt_coordinateJacobiNorm_of_positive (J := J) (J' := J') hJ hpos).deriv

theorem hasDerivAt_coordinateJacobiNormDeriv_of_positive
    (sys : Jacobi.CoordinateJacobiSystem n)
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    (hJ : ∀ i : Fin n, HasDerivAt (fun s => J s i) (J' t i) t)
    (hJ' : ∀ i : Fin n,
      HasDerivAt (fun s => J' s i) (-(Matrix.mulVec (sys.A t) (J t)) i) t)
    (hpos : 0 < jacobi_normSq J t) :
    HasDerivAt (coordinateJacobiNormDeriv J J') (coordinateJacobiNormDerivDeriv sys J J' t) t := by
  have hnum :
      HasDerivAt (coordinateJacobiNormVelocity J J')
        (coordinateJacobiNormAccel sys J J' t) t := by
    simpa [coordinateJacobiNormVelocity, coordinateJacobiNormAccel] using
      hasDerivAt_jacobi_velocityPairing (sys := sys) (J := J) (J' := J') hJ hJ'
  have hroot :
      HasDerivAt (coordinateJacobiNorm J) (coordinateJacobiNormDeriv J J' t) t :=
    hasDerivAt_coordinateJacobiNorm_of_positive (J := J) (J' := J') hJ hpos
  have hden :
      HasDerivAt (fun s => 2 * coordinateJacobiNorm J s)
        (coordinateJacobiNormVelocity J J' t / coordinateJacobiNorm J t) t := by
    convert (hroot.const_mul (2 : ℝ)) using 1 <;>
      simp [coordinateJacobiNormDeriv, coordinateJacobiNormVelocity, two_mul, mul_assoc,
        mul_left_comm, mul_comm, div_eq_mul_inv] <;> ring
  have hden_ne : 2 * coordinateJacobiNorm J t ≠ 0 := by
    have hroot_pos : 0 < coordinateJacobiNorm J t := by
      rw [coordinateJacobiNorm]
      exact Real.sqrt_pos.2 hpos
    positivity
  simpa [coordinateJacobiNormDeriv, coordinateJacobiNormDerivDeriv,
    coordinateJacobiNormVelocity, coordinateJacobiNormAccel] using
    hnum.div hden hden_ne

theorem coordinateJacobiNorm_secondDeriv_supersolution_of_upperRayleigh_on
    (sys : Jacobi.CoordinateJacobiSystem n)
    {s : Set ℝ} {k : ℝ}
    (hbound : HasRayleighUpperBoundOn sys.A s k)
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    (ht : t ∈ s)
    (hpos : 0 < jacobi_normSq J t) :
    0 ≤ coordinateJacobiNormDerivDeriv sys J J' t + k * coordinateJacobiNorm J t := by
  have hineq :
      (coordinateJacobiNormVelocity J J' t) ^ 2 / (2 * jacobi_normSq J t) -
          2 * k * jacobi_normSq J t
        ≤ coordinateJacobiNormAccel sys J J' t := by
    simpa [coordinateJacobiNormVelocity, coordinateJacobiNormAccel] using
      jacobi_normSq_sqrt_supersolution_criterion_of_upperRayleigh_on
        (sys := sys) (s := s) (k := k) hbound ht (J := J) (J' := J') hpos
  have hu_nonneg : 0 ≤ jacobi_normSq J t := le_of_lt hpos
  have hr_pos : 0 < coordinateJacobiNorm J t := by
    rw [coordinateJacobiNorm]
    exact Real.sqrt_pos.2 hpos
  have hsq : coordinateJacobiNorm J t ^ 2 = jacobi_normSq J t := by
    simpa [coordinateJacobiNorm] using Real.sq_sqrt hu_nonneg
  have hr_ne : coordinateJacobiNorm J t ≠ 0 := hr_pos.ne'
  have hu_pos2 : 0 < 2 * jacobi_normSq J t := by positivity
  have hmult :
      coordinateJacobiNormVelocity J J' t ^ 2 - 4 * k * (jacobi_normSq J t) ^ 2 ≤
        2 * jacobi_normSq J t * coordinateJacobiNormAccel sys J J' t := by
    have hineq' :
        coordinateJacobiNormVelocity J J' t ^ 2 / (2 * jacobi_normSq J t) ≤
          coordinateJacobiNormAccel sys J J' t + 2 * k * jacobi_normSq J t := by
      linarith
    have hmul := (div_le_iff₀ hu_pos2).1 hineq'
    nlinarith [hmul]
  have hnum :
      0 ≤
        2 * jacobi_normSq J t * coordinateJacobiNormAccel sys J J' t -
          coordinateJacobiNormVelocity J J' t ^ 2 +
          4 * k * (jacobi_normSq J t) ^ 2 := by
    nlinarith [hmult]
  have hquot :
      0 ≤
        (2 * jacobi_normSq J t * coordinateJacobiNormAccel sys J J' t -
            coordinateJacobiNormVelocity J J' t ^ 2 +
            4 * k * (jacobi_normSq J t) ^ 2) /
          ((2 * coordinateJacobiNorm J t) ^ 2 * coordinateJacobiNorm J t) := by
    refine div_nonneg hnum ?_
    positivity
  have heq :
      coordinateJacobiNormDerivDeriv sys J J' t + k * coordinateJacobiNorm J t =
        (2 * jacobi_normSq J t * coordinateJacobiNormAccel sys J J' t -
            coordinateJacobiNormVelocity J J' t ^ 2 +
            4 * k * (jacobi_normSq J t) ^ 2) /
          ((2 * coordinateJacobiNorm J t) ^ 2 * coordinateJacobiNorm J t) := by
    have hsq4 : coordinateJacobiNorm J t ^ 4 = (jacobi_normSq J t) ^ 2 := by
      nlinarith [hsq]
    unfold coordinateJacobiNormDerivDeriv
    field_simp [hr_ne]
    rw [hsq, hsq4]
    ring
  rw [heq]
  exact hquot

theorem coordinateJacobiNorm_secondDeriv_supersolution_of_upperRayleigh
    (sys : Jacobi.CoordinateJacobiSystem n)
    {k : ℝ}
    (hbound : HasRayleighUpperBound sys.A k)
    {J J' : ℝ → Fin n → ℝ}
    {t : ℝ}
    (hpos : 0 < jacobi_normSq J t) :
    0 ≤ coordinateJacobiNormDerivDeriv sys J J' t + k * coordinateJacobiNorm J t := by
  exact coordinateJacobiNorm_secondDeriv_supersolution_of_upperRayleigh_on
    (sys := sys) (s := Set.univ) (k := k) (hbound.on Set.univ) (by simp) hpos

/-- A coordinate Jacobi system together with positivity-set smoothness data for the scalar norm.
The only remaining geometric gap after this structure is the initial-slope/positivity package for
an actual vector Jacobi field along a curvature-bounded geodesic. -/
structure CoordinateJacobiPositivityData
    (n : ℕ) (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ) where
  J : ℝ → Fin n → ℝ
  J' : ℝ → Fin n → ℝ
  initialValue : J 0 = 0
  initialSlope : deriv (coordinateJacobiNorm J) 0 = 1
  componentDeriv :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
      ∀ i : Fin n, HasDerivAt (fun s => J s i) (J' t i) t
  componentSecondDeriv :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
      ∀ i : Fin n, HasDerivAt (fun s => J' s i) (-(Matrix.mulVec (sys.A t) (J t)) i) t
  positive :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → 0 < jacobi_normSq J t

/-- The positivity-set route constructs the repaired supersolution input package directly from the
coordinate Jacobi system. -/
noncomputable def rauchSupersolutionInputData_of_coordinateJacobi_onModel
    (sys : Jacobi.CoordinateJacobiSystem n)
    {k : ℝ}
    (hbound : HasRayleighUpperBoundOn sys.A (modelPosDomain k) k)
    (hposData : CoordinateJacobiPositivityData n sys k) :
    RauchSupersolutionInputData where
  data := {
    jacobiNorm := coordinateJacobiNorm hposData.J
    modelNorm := sn k
  }
  modelData := canonicalModelJacobiData k
  normODE := by
    refine {
      initialValue := ?_
      initialSlope := hposData.initialSlope
      hasFirstDeriv := ?_
      normSupersolution := ?_
    }
    · simpa using coordinateJacobiNorm_zero_of_zero_initial (J := hposData.J) hposData.initialValue
    · intro t ht
      have h :=
        hasDerivAt_coordinateJacobiNorm_of_positive
          (J := hposData.J) (J' := hposData.J')
          (hposData.componentDeriv ht) (hposData.positive ht)
      simpa [h.deriv] using h
    · intro t ht
      refine ⟨?_, ?_⟩
      · have hformula' :
            HasDerivAt (coordinateJacobiNormDeriv hposData.J hposData.J')
              (coordinateJacobiNormDerivDeriv sys hposData.J hposData.J' t) t :=
          hasDerivAt_coordinateJacobiNormDeriv_of_positive
            (sys := sys) (J := hposData.J) (J' := hposData.J')
            (hposData.componentDeriv ht) (hposData.componentSecondDeriv ht) (hposData.positive ht)
        have hEq :
            deriv (coordinateJacobiNorm hposData.J) =ᶠ[𝓝 t]
              coordinateJacobiNormDeriv hposData.J hposData.J' := by
          filter_upwards [isOpen_modelPosDomain k |>.mem_nhds ht] with s hs
          exact deriv_coordinateJacobiNorm_of_positive
            (J := hposData.J) (J' := hposData.J')
            (hposData.componentDeriv hs) (hposData.positive hs)
        have hformula :
            HasDerivAt (fun s => deriv (coordinateJacobiNorm hposData.J) s)
              (coordinateJacobiNormDerivDeriv sys hposData.J hposData.J' t) t := by
          simpa using hformula'.congr_of_eventuallyEq hEq
        simpa [hformula.deriv] using hformula
      · have hformula :
            0 ≤ coordinateJacobiNormDerivDeriv sys hposData.J hposData.J' t +
              k * coordinateJacobiNorm hposData.J t :=
          coordinateJacobiNorm_secondDeriv_supersolution_of_upperRayleigh_on
            (sys := sys) (s := modelPosDomain k) (k := k) hbound ht
            (J := hposData.J) (J' := hposData.J') (hposData.positive ht)
        have hformula' :
            HasDerivAt (coordinateJacobiNormDeriv hposData.J hposData.J')
              (coordinateJacobiNormDerivDeriv sys hposData.J hposData.J' t) t :=
          hasDerivAt_coordinateJacobiNormDeriv_of_positive
            (sys := sys) (J := hposData.J) (J' := hposData.J')
            (hposData.componentDeriv ht) (hposData.componentSecondDeriv ht)
            (hposData.positive ht)
        have hEq :
            deriv (coordinateJacobiNorm hposData.J) =ᶠ[𝓝 t]
              coordinateJacobiNormDeriv hposData.J hposData.J' := by
          filter_upwards [isOpen_modelPosDomain k |>.mem_nhds ht] with s hs
          exact deriv_coordinateJacobiNorm_of_positive
            (J := hposData.J) (J' := hposData.J')
            (hposData.componentDeriv hs) (hposData.positive hs)
        have hformulaDeriv :
            HasDerivAt (fun s => deriv (coordinateJacobiNorm hposData.J) s)
              (coordinateJacobiNormDerivDeriv sys hposData.J hposData.J' t) t := by
          simpa using hformula'.congr_of_eventuallyEq hEq
        simpa [hformulaDeriv.deriv] using hformula
  matchesScalarModel := rfl

/-- The positivity-set route constructs the repaired supersolution input package directly from the
coordinate Jacobi system. -/
noncomputable def rauchSupersolutionInputData_of_coordinateJacobi
    (sys : Jacobi.CoordinateJacobiSystem n)
    {k : ℝ}
    (hbound : HasRayleighUpperBound sys.A k)
    (hposData : CoordinateJacobiPositivityData n sys k) :
    RauchSupersolutionInputData :=
  rauchSupersolutionInputData_of_coordinateJacobi_onModel
    (sys := sys) (k := k) (hbound.on (modelPosDomain k)) hposData

/-- The positivity-set reduction theorem: a coordinate Jacobi field with the Rayleigh upper bound
and the honest positivity-set smoothness package satisfies the lower Rauch comparison. -/
theorem rauch_lowerComparison_of_coordinateJacobi_onModel
    (sys : Jacobi.CoordinateJacobiSystem n)
    {k : ℝ}
    (hbound : HasRayleighUpperBoundOn sys.A (modelPosDomain k) k)
    (hposData : CoordinateJacobiPositivityData n sys k) :
    RauchNormLowerComparison k
      (rauchSupersolutionInputData_of_coordinateJacobi_onModel
        (sys := sys) hbound hposData).data := by
  exact
    rauch_lowerComparison_of_scalarSupersolution
      (rauchSupersolutionInputData_of_coordinateJacobi_onModel
        (sys := sys) hbound hposData)

/-- The positivity-set reduction theorem: a coordinate Jacobi field with the Rayleigh upper bound
and the honest positivity-set smoothness package satisfies the lower Rauch comparison. -/
theorem rauch_lowerComparison_of_coordinateJacobi
    (sys : Jacobi.CoordinateJacobiSystem n)
    {k : ℝ}
    (hbound : HasRayleighUpperBound sys.A k)
    (hposData : CoordinateJacobiPositivityData n sys k) :
    RauchNormLowerComparison k
      (rauchSupersolutionInputData_of_coordinateJacobi (sys := sys) hbound hposData).data := by
  exact rauch_lowerComparison_of_coordinateJacobi_onModel
    (sys := sys) (k := k) (hbound.on (modelPosDomain k)) hposData

end Comparison
