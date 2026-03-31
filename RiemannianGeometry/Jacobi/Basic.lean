import Curvature.Basic
import ParallelTransport.Basic

namespace Jacobi

universe u v

/-- A second covariant derivative operator along a fixed geodesic. -/
abbrev AlongSecondDerivative (V : Type u) := ParallelTransport.FieldAlong V → ℝ → V

/-- A Jacobi field along a geodesic solves the Jacobi equation. -/
def IsJacobiField
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong V)
    (nablaTT : AlongSecondDerivative V)
    (J : ParallelTransport.FieldAlong V) : Prop :=
  ∀ t, nablaTT J t + R (J t) (T t) (T t) = 0

/-- Endpoint data for the Jacobi initial value problem. -/
structure InitialData (V : Type u) where
  value : V
  deriv : V

theorem initialData_ext
    {V : Type u} {d d' : InitialData V}
    (hvalue : d.value = d'.value) (hderiv : d.deriv = d'.deriv) :
    d = d' := by
  cases d
  cases d'
  simp at hvalue hderiv
  simp [hvalue, hderiv]

theorem initialData_ext_iff
    {V : Type u} {d d' : InitialData V} :
    d = d' ↔ d.value = d'.value ∧ d.deriv = d'.deriv := by
  constructor
  · intro h
    simpa [h]
  · intro h
    exact initialData_ext h.1 h.2

/-- Initial data with zero initial value and prescribed initial derivative. -/
def zeroValueInitialData
    {V : Type u} [Zero V] (v : V) : InitialData V where
  value := 0
  deriv := v

@[simp] theorem zeroValueInitialData_value
    {V : Type u} [Zero V] (v : V) :
    (zeroValueInitialData v).value = 0 :=
  rfl

@[simp] theorem zeroValueInitialData_deriv
    {V : Type u} [Zero V] (v : V) :
    (zeroValueInitialData v).deriv = v :=
  rfl

theorem isJacobiField_zero_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J : ParallelTransport.FieldAlong V} :
    IsJacobiField R T nablaTT J ↔
      ∀ t, nablaTT J t + R (J t) (T t) (T t) = 0 :=
  Iff.rfl

theorem isJacobiField_congr
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R R' : Curvature.CurvatureTensor C}
    {T T' : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J J' : ParallelTransport.FieldAlong V}
    (hR : ∀ X Y Z, R X Y Z = R' X Y Z)
    (hT : T = T')
    (hJ : J = J') :
    IsJacobiField R T nablaTT J ↔ IsJacobiField R' T' nablaTT J' := by
  subst hT
  subst hJ
  constructor <;> intro h t
  · simpa [hR] using h t
  · simpa [hR] using h t

theorem isJacobiField_congr_pointwise
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J J' : ParallelTransport.FieldAlong V}
    (hJ : ∀ t, J t = J' t)
    (hnabla : ∀ t, nablaTT J t = nablaTT J' t) :
    IsJacobiField R T nablaTT J ↔ IsJacobiField R T nablaTT J' := by
  constructor <;> intro h t
  · have := h t
    simpa [hJ t, hnabla t] using this
  · have := h t
    simpa [hJ t, hnabla t] using this

end Jacobi
