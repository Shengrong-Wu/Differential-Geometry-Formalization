import Measure.ExpJacobian

/-! The pullback-density layer keeps the density-side quantity explicit so that polar coordinates
stay theorem-level rather than hidden inside definitional wrappers. -/

namespace Measure.Riemannian

variable {n : ℕ}

/-- The pulled-back chart density under the local exponential map, with the determinant Jacobian
factor included. This is the density-level object that the repaired polar theorem should match. -/
noncomputable def pullbackDensity
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n)) :
    Exponential.Coordinate.Velocity n → ℝ :=
  fun v => inducedJacobian exp vol v * expJacobianFn exp v

@[simp] theorem pullbackDensity_apply
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n))
    (v : Exponential.Coordinate.Velocity n) :
    pullbackDensity exp vol v =
      inducedJacobian exp vol v * expJacobianFn exp v :=
  rfl

theorem pullbackDensity_nonneg
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n))
    (v : Exponential.Coordinate.Velocity n) :
    0 ≤ pullbackDensity exp vol v := by
  exact mul_nonneg (vol.nonneg_density (exp.toFun v)) (expJacobianFn_nonneg exp v)

/-- The nonnegative `ENNReal` density corresponding to the repaired pullback density. -/
noncomputable def pullbackDensityENNReal
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n)) :
    Exponential.Coordinate.Velocity n → ENNReal :=
  fun v => ENNReal.ofReal (pullbackDensity exp vol v)

@[simp] theorem pullbackDensityENNReal_apply
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n))
    (v : Exponential.Coordinate.Velocity n) :
    pullbackDensityENNReal exp vol v = ENNReal.ofReal (pullbackDensity exp vol v) :=
  rfl

/-- The repaired measure-level pullback package on the coordinate fiber. -/
noncomputable def pullbackMeasure
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n)) :
    MeasureTheory.Measure (Exponential.Coordinate.Velocity n) :=
  (MeasureTheory.volume : MeasureTheory.Measure (Exponential.Coordinate.Velocity n)).withDensity
    (pullbackDensityENNReal exp vol)

end Measure.Riemannian
