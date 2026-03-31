import Measure.PullbackDensity
import Exponential.NormalCoordinates

/-! Polar-coordinate bookkeeping stays centered on `canonicalPolarDensity` and
`HasPolarDecomposition`, which the comparison construction layer consumes directly. -/

namespace Measure.Riemannian

variable {n : ℕ}

/-- The canonical polar Jacobian is the determinant-based exponential Jacobian. The polar
decomposition theorem identifies the repaired pullback density with the density built from this
Jacobian factor. -/
noncomputable def canonicalPolarJacobian
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (_vol : RiemannianVolumeData (n := n)) :
    Exponential.Coordinate.Velocity n → ℝ :=
  expJacobianFn exp

/-- The repaired canonical polar density includes both the chart density pulled back along the
exponential map and the determinant Jacobian factor. -/
noncomputable def canonicalPolarDensity
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n)) :
    Exponential.Coordinate.Velocity n → ℝ :=
  fun v => inducedJacobian exp vol v * canonicalPolarJacobian exp vol v

/-- Polar-coordinate decomposition in a normal neighborhood: the repaired pullback density agrees
with the canonical polar density. -/
def HasPolarDecomposition
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n)) : Prop :=
  pullbackDensity exp vol = canonicalPolarDensity exp vol

theorem hasPolarDecomposition_of_eq
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol : RiemannianVolumeData (n := n)}
    (hpolar : pullbackDensity exp vol = canonicalPolarDensity exp vol) :
    HasPolarDecomposition exp vol :=
  hpolar

theorem HasPolarDecomposition.expJacobian
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol : RiemannianVolumeData (n := n)}
    (_hpolar : HasPolarDecomposition exp vol) :
    ExpJacobian exp (canonicalPolarJacobian exp vol) :=
  rfl

theorem HasPolarDecomposition.matchesDensity
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol : RiemannianVolumeData (n := n)}
    (hpolar : HasPolarDecomposition exp vol) :
    pullbackDensity exp vol = canonicalPolarDensity exp vol :=
  hpolar

theorem hasPolarDecomposition_iff
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol : RiemannianVolumeData (n := n)} :
    HasPolarDecomposition exp vol ↔
      pullbackDensity exp vol = canonicalPolarDensity exp vol :=
  Iff.rfl

@[simp] theorem canonicalPolarJacobian_apply
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n))
    (v : Exponential.Coordinate.Velocity n) :
    canonicalPolarJacobian exp vol v = expJacobianFn exp v :=
  rfl

@[simp] theorem canonicalPolarDensity_apply
    (exp : Exponential.Coordinate.LocalExponentialMap n)
    (vol : RiemannianVolumeData (n := n))
    (v : Exponential.Coordinate.Velocity n) :
    canonicalPolarDensity exp vol v =
      inducedJacobian exp vol v * expJacobianFn exp v :=
  rfl

theorem canonicalPolarJacobian_eq_of_compatible
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol vol' : RiemannianVolumeData (n := n)}
    (_hvol : CompatibleUnderChartChange vol vol') :
    canonicalPolarJacobian exp vol = canonicalPolarJacobian exp vol' :=
  rfl

theorem HasPolarDecomposition.inducedJacobian_eq
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol : RiemannianVolumeData (n := n)}
    (hpolar : HasPolarDecomposition exp vol) :
    pullbackDensity exp vol = canonicalPolarDensity exp vol :=
  hpolar

 theorem HasPolarDecomposition.pullbackDensity_apply
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {vol : RiemannianVolumeData (n := n)}
    (hpolar : HasPolarDecomposition exp vol)
    (v : Exponential.Coordinate.Velocity n) :
    pullbackDensity exp vol v = canonicalPolarDensity exp vol v := by
  exact congrArg (fun J => J v) hpolar

/-- The repaired owner theorem for polar coordinates is now phrased for the actual coordinate
exponential map and the package-owned volume data. -/
theorem hasPolarDecomposition_coordinateExpLocalExponentialMap
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Exponential.Coordinate.Position n) :
    HasPolarDecomposition
      (Exponential.Coordinate.coordinateExpLocalExponentialMap (n := n) Gamma p)
      (volumeDataOfMetricField (n := n) g) := by
  rfl

end Measure.Riemannian
