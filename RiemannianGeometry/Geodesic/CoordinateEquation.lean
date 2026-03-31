import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Geodesic.Basic
import LeviCivita.CoordinateFields
import LeviCivita.LocalExistence

/-! This file keeps the coordinate acceleration formulas small and reusable for the spray and
radial-source development. -/

open scoped BigOperators

namespace Geodesic.Coordinate

variable {n : ℕ}

/-- A coordinate Christoffel field depending on the base point. -/
abbrev ChristoffelField (n : ℕ) := Position n → LeviCivita.Coordinate.ChristoffelSymbol n

/-- Regard a smooth Christoffel coefficient field as an ordinary pointwise coordinate Christoffel
field. -/
def christoffelFieldOfSmooth
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) : ChristoffelField n :=
  fun x k i j => Gamma k i j x

/-- Toy model: regard a fixed Christoffel symbol as a constant coordinate field. -/
def constantChristoffelField
    (Gamma : LeviCivita.Coordinate.ChristoffelSymbol n) : ChristoffelField n :=
  fun _ => Gamma

/-- Toy constant-coefficient Levi-Civita field from the pointwise coordinate existence file. -/
noncomputable def localChristoffelField
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : LeviCivita.Coordinate.MetricDerivative n) :
    ChristoffelField n :=
  constantChristoffelField (LeviCivita.Coordinate.localLeviCivitaConnection gInv dg)

/-- The genuine smooth Levi-Civita Christoffel field coming from the field-level coordinate model. -/
noncomputable def leviCivitaChristoffelField
    (gInv g : LeviCivita.CoordinateField.SmoothTensor2Field n) :
    ChristoffelField n :=
  christoffelFieldOfSmooth (LeviCivita.CoordinateField.leviCivitaChristoffelField gInv g)

/-- The geodesic acceleration determined by the Christoffel field. -/
def geodesicAcceleration
    (Gamma : ChristoffelField n) (x : Position n) (v : Velocity n) : Velocity n :=
  fun i => -∑ j : Fin n, ∑ k : Fin n, Gamma x i j k * v j * v k

@[simp] theorem constantChristoffelField_apply
    (Gamma : LeviCivita.Coordinate.ChristoffelSymbol n) (x : Position n) :
    constantChristoffelField Gamma x = Gamma :=
  rfl

@[simp] theorem christoffelFieldOfSmooth_apply
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (x : Position n) (k i j : Fin n) :
    christoffelFieldOfSmooth Gamma x k i j = Gamma k i j x :=
  rfl

@[simp] theorem localChristoffelField_apply
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : LeviCivita.Coordinate.MetricDerivative n)
    (x : Position n) :
    localChristoffelField gInv dg x =
      LeviCivita.Coordinate.localLeviCivitaConnection gInv dg :=
  rfl

@[simp] theorem leviCivitaChristoffelField_apply
    (gInv g : LeviCivita.CoordinateField.SmoothTensor2Field n)
    (x : Position n) (k i j : Fin n) :
    leviCivitaChristoffelField gInv g x k i j =
      LeviCivita.CoordinateField.leviCivitaChristoffelField gInv g k i j x :=
  rfl

@[simp] theorem geodesicAcceleration_constant
    (Gamma : LeviCivita.Coordinate.ChristoffelSymbol n) (x : Position n) (v : Velocity n) :
    geodesicAcceleration (constantChristoffelField Gamma) x v =
      fun i => -∑ j : Fin n, ∑ k : Fin n, Gamma i j k * v j * v k :=
  rfl

@[simp] theorem geodesicAcceleration_localLeviCivitaConnection
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : LeviCivita.Coordinate.MetricDerivative n)
    (x : Position n) (v : Velocity n) :
    geodesicAcceleration (localChristoffelField gInv dg) x v =
      fun i => -∑ j : Fin n, ∑ k : Fin n,
        LeviCivita.Coordinate.localLeviCivitaConnection gInv dg i j k * v j * v k := by
  rfl

theorem geodesicAcceleration_eq_of_christoffel_eq
    {Gamma Gamma' : ChristoffelField n}
    (hGamma : ∀ x i j k, Gamma x i j k = Gamma' x i j k) :
    geodesicAcceleration Gamma = geodesicAcceleration Gamma' := by
  funext x v i
  simp [geodesicAcceleration, hGamma]

theorem localChristoffelField_eq_of_connection_eq
    {gInv : Metric.Coordinate.InverseTensor2 n}
    {dg : LeviCivita.Coordinate.MetricDerivative n}
    {Gamma : LeviCivita.Coordinate.ChristoffelSymbol n}
    (hGamma : Gamma = LeviCivita.Coordinate.localLeviCivitaConnection gInv dg) :
    constantChristoffelField Gamma = localChristoffelField gInv dg := by
  subst hGamma
  rfl

theorem geodesicAcceleration_eq_local_of_connection_eq
    {gInv : Metric.Coordinate.InverseTensor2 n}
    {dg : LeviCivita.Coordinate.MetricDerivative n}
    {Gamma : LeviCivita.Coordinate.ChristoffelSymbol n}
    (hGamma : Gamma = LeviCivita.Coordinate.localLeviCivitaConnection gInv dg) :
    geodesicAcceleration (constantChristoffelField Gamma) =
      geodesicAcceleration (localChristoffelField gInv dg) := by
  subst hGamma
  rfl

@[simp] theorem geodesicAcceleration_christoffelFieldOfSmooth
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (x : Position n) (v : Velocity n) :
    geodesicAcceleration (christoffelFieldOfSmooth Gamma) x v =
      fun i => -∑ j : Fin n, ∑ k : Fin n, Gamma i j k x * v j * v k :=
  rfl

@[simp] theorem geodesicAcceleration_leviCivitaChristoffelField
    (gInv g : LeviCivita.CoordinateField.SmoothTensor2Field n)
    (x : Position n) (v : Velocity n) :
    geodesicAcceleration (leviCivitaChristoffelField gInv g) x v =
      fun i => -∑ j : Fin n, ∑ k : Fin n,
        LeviCivita.CoordinateField.leviCivitaChristoffelField gInv g i j k x * v j * v k := by
  rfl

end Geodesic.Coordinate
