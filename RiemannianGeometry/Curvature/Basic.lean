import LeviCivita.Basic

namespace Curvature

universe u v

/-- The curvature operator attached to an abstract covariant derivative. -/
def curvatureOperator
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (nabla : LeviCivita.CovariantDerivative V S C) :
    V → V → V → V :=
  fun X Y Z => nabla X (nabla Y Z) - nabla Y (nabla X Z) - nabla (C.bracket X Y) Z

/-- Bundled curvature data over an abstract connection context. -/
structure CurvatureTensor
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    (C : LeviCivita.ConnectionContext V S) where
  toFun : V → V → V → V

instance
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S} :
    CoeFun (CurvatureTensor C) (fun _ => V → V → V → V) where
  coe := CurvatureTensor.toFun

/-- The curvature tensor induced by a connection. -/
def ofConnection
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (nabla : LeviCivita.CovariantDerivative V S C) :
    CurvatureTensor C where
  toFun := curvatureOperator nabla

@[simp] theorem ofConnection_apply
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (nabla : LeviCivita.CovariantDerivative V S C) (X Y Z : V) :
    ofConnection nabla X Y Z = curvatureOperator nabla X Y Z :=
  rfl

theorem curvatureTensor_ext
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R R' : CurvatureTensor C}
    (h : ∀ X Y Z, R X Y Z = R' X Y Z) :
    R = R' := by
  cases R with
  | mk f =>
      cases R' with
      | mk g =>
          have hfun : f = g := by
            funext X Y Z
            simpa using h X Y Z
          simp [hfun]

theorem curvatureTensor_ext_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R R' : CurvatureTensor C} :
    R = R' ↔ ∀ X Y Z, R X Y Z = R' X Y Z := by
  constructor
  · intro h X Y Z
    simpa [h]
  · intro h
    exact curvatureTensor_ext h

theorem ofConnection_eq_of_eq
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {nabla nabla' : LeviCivita.CovariantDerivative V S C}
    (h : nabla = nabla') :
    ofConnection nabla = ofConnection nabla' := by
  subst h
  rfl

theorem ofConnection_eq_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {nabla : LeviCivita.CovariantDerivative V S C} {R : CurvatureTensor C} :
    ofConnection nabla = R ↔ ∀ X Y Z, curvatureOperator nabla X Y Z = R X Y Z := by
  constructor
  · intro h X Y Z
    rw [← ofConnection_apply nabla X Y Z, h]
  · intro h
    apply curvatureTensor_ext
    intro X Y Z
    rw [ofConnection_apply]
    exact h X Y Z

theorem eq_ofConnection_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {nabla : LeviCivita.CovariantDerivative V S C} {R : CurvatureTensor C} :
    R = ofConnection nabla ↔ ∀ X Y Z, R X Y Z = curvatureOperator nabla X Y Z := by
  rw [curvatureTensor_ext_iff]
  constructor
  · intro h X Y Z
    simpa [h] using (ofConnection_apply nabla X Y Z).symm
  · intro h X Y Z
    simpa [ofConnection_apply] using h X Y Z

end Curvature
