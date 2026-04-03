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

/-- Bundled curvature data over an abstract connection context, carrying first-argument
linearity as structural data. -/
structure CurvatureTensor
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    (C : LeviCivita.ConnectionContext V S) where
  toFun : V → V → V → V
  add_left : ∀ (X Y Z W : V), toFun (X + Y) Z W = toFun X Z W + toFun Y Z W
  smul_left : ∀ (a : S) (X Y Z : V), toFun (a • X) Y Z = a • toFun X Y Z

instance
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S} :
    CoeFun (CurvatureTensor C) (fun _ => V → V → V → V) where
  coe := CurvatureTensor.toFun

/-- The curvature tensor induced by a connection, given proofs that the curvature operator
is linear in the first argument. These follow from connection linearity + bracket/derivation
properties of the ambient context. -/
def ofConnection
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (nabla : LeviCivita.CovariantDerivative V S C)
    (hadd : ∀ X Y Z W : V,
      curvatureOperator nabla (X + Y) Z W =
        curvatureOperator nabla X Z W + curvatureOperator nabla Y Z W)
    (hsmul : ∀ (a : S) (X Y Z : V),
      curvatureOperator nabla (a • X) Y Z =
        a • curvatureOperator nabla X Y Z) :
    CurvatureTensor C where
  toFun := curvatureOperator nabla
  add_left := hadd
  smul_left := hsmul

@[simp] theorem ofConnection_apply
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (nabla : LeviCivita.CovariantDerivative V S C)
    (hadd : ∀ X Y Z W : V,
      curvatureOperator nabla (X + Y) Z W =
        curvatureOperator nabla X Z W + curvatureOperator nabla Y Z W)
    (hsmul : ∀ (a : S) (X Y Z : V),
      curvatureOperator nabla (a • X) Y Z =
        a • curvatureOperator nabla X Y Z)
    (X Y Z : V) :
    ofConnection nabla hadd hsmul X Y Z = curvatureOperator nabla X Y Z :=
  rfl

theorem curvatureTensor_ext
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R R' : CurvatureTensor C}
    (h : ∀ X Y Z, R X Y Z = R' X Y Z) :
    R = R' := by
  cases R with
  | mk f _ _ =>
      cases R' with
      | mk g _ _ =>
          have hfun : f = g := by
            funext X Y Z
            simpa using h X Y Z
          subst hfun
          rfl

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
    (hadd : ∀ X Y Z W : V,
      curvatureOperator nabla (X + Y) Z W =
        curvatureOperator nabla X Z W + curvatureOperator nabla Y Z W)
    (hsmul : ∀ (a : S) (X Y Z : V),
      curvatureOperator nabla (a • X) Y Z =
        a • curvatureOperator nabla X Y Z)
    (hadd' : ∀ X Y Z W : V,
      curvatureOperator nabla' (X + Y) Z W =
        curvatureOperator nabla' X Z W + curvatureOperator nabla' Y Z W)
    (hsmul' : ∀ (a : S) (X Y Z : V),
      curvatureOperator nabla' (a • X) Y Z =
        a • curvatureOperator nabla' X Y Z)
    (h : nabla = nabla') :
    ofConnection nabla hadd hsmul = ofConnection nabla' hadd' hsmul' := by
  subst h
  rfl

theorem ofConnection_eq_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {nabla : LeviCivita.CovariantDerivative V S C}
    {hadd : ∀ X Y Z W : V,
      curvatureOperator nabla (X + Y) Z W =
        curvatureOperator nabla X Z W + curvatureOperator nabla Y Z W}
    {hsmul : ∀ (a : S) (X Y Z : V),
      curvatureOperator nabla (a • X) Y Z =
        a • curvatureOperator nabla X Y Z}
    {R : CurvatureTensor C} :
    ofConnection nabla hadd hsmul = R ↔ ∀ X Y Z, curvatureOperator nabla X Y Z = R X Y Z := by
  constructor
  · intro h X Y Z
    rw [← ofConnection_apply nabla hadd hsmul X Y Z, h]
  · intro h
    apply curvatureTensor_ext
    intro X Y Z
    rw [ofConnection_apply]
    exact h X Y Z

theorem eq_ofConnection_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {nabla : LeviCivita.CovariantDerivative V S C}
    {hadd : ∀ X Y Z W : V,
      curvatureOperator nabla (X + Y) Z W =
        curvatureOperator nabla X Z W + curvatureOperator nabla Y Z W}
    {hsmul : ∀ (a : S) (X Y Z : V),
      curvatureOperator nabla (a • X) Y Z =
        a • curvatureOperator nabla X Y Z}
    {R : CurvatureTensor C} :
    R = ofConnection nabla hadd hsmul ↔ ∀ X Y Z, R X Y Z = curvatureOperator nabla X Y Z := by
  rw [curvatureTensor_ext_iff]
  constructor
  · intro h X Y Z
    simpa [h] using (ofConnection_apply nabla hadd hsmul X Y Z).symm
  · intro h X Y Z
    simpa [ofConnection_apply] using h X Y Z

end Curvature
