import Measure.RiemannianVolume
import Exponential.LocalInverse
import Measure.NormComparison
import Measure.HadamardBound

/-! The exponential-Jacobian layer keeps the determinant quantity explicit so that the downstream
polar density is carried by a genuine Jacobian function. -/

namespace Measure.Riemannian

variable {n : ℕ}

/-- The derivative of the local exponential map, viewed as an endomorphism of the fixed coordinate
fiber. The `Position`/`Velocity` aliases unfold to the same Euclidean space. -/
noncomputable def coordinateExpDerivativeEndomorphism
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (v : Exponential.Coordinate.Velocity n) :
    Exponential.Coordinate.Velocity n →L[ℝ] Exponential.Coordinate.Velocity n :=
  fderiv ℝ exp.toFun v

/-- The determinant-based Jacobian of the local exponential map in coordinates. -/
noncomputable def expJacobianFn
    (exp : Exponential.Coordinate.LocalExponentialMap n) :
    Exponential.Coordinate.Velocity n → ℝ :=
  fun v => |LinearMap.det (coordinateExpDerivativeEndomorphism exp v).toLinearMap|

/-- The canonical radial Jacobian induced by chart density and the exponential map. -/
noncomputable def inducedJacobian
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n)) :
    Exponential.Coordinate.Velocity n → ℝ :=
  fun v => vol.densityFn (exp.toFun v)

/-- The Jacobian predicate is now definitionally tied to the determinant-based Jacobian function. -/
def ExpJacobian
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (J : Exponential.Coordinate.Velocity n → ℝ) : Prop :=
  J = expJacobianFn exp

/-- Compatibility predicate expressing that the pulled-back chart density agrees with the actual
exponential Jacobian. -/
def ExpJacobianMatchesDensity
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n)) : Prop :=
  inducedJacobian exp vol = expJacobianFn exp

theorem expJacobian_iff
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {J : Exponential.Coordinate.Velocity n → ℝ} :
    ExpJacobian exp J ↔ J = expJacobianFn exp :=
  Iff.rfl

theorem expJacobian_eq
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {J : Exponential.Coordinate.Velocity n → ℝ}
    (hJ : J = expJacobianFn exp) :
    ExpJacobian exp J :=
  hJ

@[simp] theorem expJacobianFn_apply
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (v : Exponential.Coordinate.Velocity n) :
    expJacobianFn exp v = |LinearMap.det (coordinateExpDerivativeEndomorphism exp v).toLinearMap| :=
  rfl

theorem expJacobianFn_nonneg
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (v : Exponential.Coordinate.Velocity n) :
    0 ≤ expJacobianFn exp v :=
  abs_nonneg _

theorem ExpJacobian.nonneg
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {J : Exponential.Coordinate.Velocity n → ℝ}
    (hJ : ExpJacobian exp J) (v : Exponential.Coordinate.Velocity n) :
    0 ≤ J v := by
  rw [hJ]
  exact expJacobianFn_nonneg exp v

@[simp] theorem inducedJacobian_apply
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n))
    (v : Exponential.Coordinate.Velocity n) :
    inducedJacobian exp vol v = vol.densityFn (exp.toFun v) :=
  rfl

theorem expJacobianMatchesDensity_iff
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol : RiemannianVolumeData (n := n)} :
    ExpJacobianMatchesDensity exp vol ↔ inducedJacobian exp vol = expJacobianFn exp :=
  Iff.rfl

theorem ExpJacobianMatchesDensity.inducedJacobian_eq
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol : RiemannianVolumeData (n := n)}
    (hJ : ExpJacobianMatchesDensity exp vol) :
    inducedJacobian exp vol = expJacobianFn exp :=
  hJ

@[simp] theorem expJacobianFn_zero_of_differentialAtZeroIsId
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    (hdiff : Exponential.Coordinate.DifferentialAtZeroIsId exp) :
    expJacobianFn exp 0 = 1 := by
  rw [Exponential.Coordinate.DifferentialAtZeroIsId,
    Exponential.Coordinate.DifferentialAtZero] at hdiff
  rw [expJacobianFn, coordinateExpDerivativeEndomorphism, hdiff.fderiv]
  simp [LinearMap.det_id]

@[simp] theorem expJacobianFn_coordinateExpLocalExponentialMap_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    expJacobianFn
      (Exponential.Coordinate.coordinateExpLocalExponentialMap (n := n) Gamma p) 0 = 1 := by
  exact expJacobianFn_zero_of_differentialAtZeroIsId
    (exp := Exponential.Coordinate.coordinateExpLocalExponentialMap (n := n) Gamma p)
    (Exponential.Coordinate.differentialAtZeroIsId_coordinateExpLocalExponentialMap
      (n := n) Gamma p)

theorem inducedJacobian_eq_of_compatible
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol vol' : RiemannianVolumeData (n := n)}
    (hvol : CompatibleUnderChartChange vol vol') :
    inducedJacobian exp vol = inducedJacobian exp vol' := by
  funext v
  exact hvol (exp.toFun v)

theorem expJacobianMatchesDensity_of_compatible
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol vol' : RiemannianVolumeData (n := n)}
    (hvol : CompatibleUnderChartChange vol vol')
    (hJ : ExpJacobianMatchesDensity exp vol) :
    ExpJacobianMatchesDensity exp vol' := by
  rw [ExpJacobianMatchesDensity] at *
  calc
    inducedJacobian exp vol' = inducedJacobian exp vol := by
      symm
      exact inducedJacobian_eq_of_compatible (exp := exp) hvol
    _ = expJacobianFn exp := hJ

/-! ## Issue 4: Linear-algebra Jacobian bound -/

/-- The Euclidean (L²) column norm of `dexp`. This is the correct norm for the Hadamard
determinant bound, since `‖·‖` on `Fin n → ℝ` is the sup norm, not the Euclidean norm.
The Hadamard bound `|det A| ≤ ∏ᵢ ‖A eᵢ‖₂` uses the Euclidean norm. -/
noncomputable def euclideanColumnNorm
    (A : Exponential.Coordinate.Velocity n →L[ℝ] Exponential.Coordinate.Velocity n)
    (i : Fin n) : ℝ :=
  ‖(PiLp.continuousLinearEquiv (p := 2) ℝ (fun _ : Fin n => ℝ)).symm
    (A (Pi.basisFun ℝ (Fin n) i))‖

/-- **Hadamard determinant bound (Euclidean norm).** For a continuous linear map
`A : E →L[ℝ] E` on `Fin n → ℝ`, the absolute value of its determinant is bounded
by the product of its Euclidean column norms:
`|det A| ≤ ∏ᵢ ‖A eᵢ‖₂`. -/
theorem expJacobianFn_le_prod_euclidean_column_norms
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (v : Exponential.Coordinate.Velocity n)
    (_hv : v ∈ exp.source) :
    expJacobianFn exp v ≤
      ∏ i : Fin n, euclideanColumnNorm (coordinateExpDerivativeEndomorphism exp v) i := by
  -- Bridge: transport the linear map to EuclideanSpace, apply Hadamard, transport back
  set A := coordinateExpDerivativeEndomorphism exp v
  -- The WithLp equivalence is a linear isomorphism
  set L := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  -- Transport A to EuclideanSpace
  set A' : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    L.toLinearMap.comp (A.toLinearMap.comp L.symm.toLinearMap)
  -- det A' = det A (conjugation by isomorphism)
  have hdet : LinearMap.det A' = LinearMap.det A.toLinearMap := by
    exact LinearMap.det_conj A.toLinearMap L
  -- Apply Hadamard on EuclideanSpace
  have hH := abs_linearMap_det_le_prod_norm A'
  rw [hdet] at hH
  exact hH

/-- The ambient (sup) column norm is bounded by the Euclidean column norm scaled by √n.
This bridges the Rauch comparison layer (which uses the ambient norm) to the
Hadamard bound (which uses the Euclidean norm). -/
theorem norm_le_euclideanColumnNorm
    (A : Exponential.Coordinate.Velocity n →L[ℝ] Exponential.Coordinate.Velocity n)
    (i : Fin n) :
    ‖A (Pi.basisFun ℝ (Fin n) i)‖ ≤ euclideanColumnNorm A i :=
  pi_norm_le_piLp_norm _

/-- Jacobian bound from basiswise dexp Euclidean-norm comparison: if ‖dexp(v) eᵢ‖₂ ≤ fᵢ for all i,
then `expJacobianFn exp v ≤ ∏ᵢ fᵢ`. -/
theorem expJacobianFn_le_of_basiswise_euclidean_bound
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (v : Exponential.Coordinate.Velocity n)
    (hv : v ∈ exp.source)
    (f : Fin n → ℝ)
    (hf_nonneg : ∀ i, 0 ≤ f i)
    (hbound : ∀ i : Fin n,
        euclideanColumnNorm (coordinateExpDerivativeEndomorphism exp v) i ≤ f i) :
    expJacobianFn exp v ≤ ∏ i : Fin n, f i := by
  calc expJacobianFn exp v
      ≤ ∏ i : Fin n, euclideanColumnNorm (coordinateExpDerivativeEndomorphism exp v) i :=
        expJacobianFn_le_prod_euclidean_column_norms exp v hv
    _ ≤ ∏ i : Fin n, f i := by
        apply Finset.prod_le_prod
        · intro i _; exact le_trans (norm_nonneg _) (norm_le_euclideanColumnNorm _ _)
        · intro i _; exact hbound i

end Measure.Riemannian
