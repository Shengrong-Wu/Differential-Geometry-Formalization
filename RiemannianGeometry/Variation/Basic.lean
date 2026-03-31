import Mathlib.Algebra.Group.Basic

namespace Variation

universe u v

/--
Minimal algebra for the structural curvature-variation identity
`Ḟ = d_∇ Ā`.
-/
structure LocalConnectionVariationAlgebra where
  Ω1 : Type u
  Ω2 : Type v
  [instAddCommGroupΩ1 : AddCommGroup Ω1]
  [instAddCommGroupΩ2 : AddCommGroup Ω2]
  d1 : Ω1 → Ω2
  wedge11 : Ω1 → Ω1 → Ω2
  deriv1 : Ω1 → Ω1
  deriv2 : Ω2 → Ω2
  deriv2_add : ∀ β₁ β₂, deriv2 (β₁ + β₂) = deriv2 β₁ + deriv2 β₂
  deriv2_d1 : ∀ α, deriv2 (d1 α) = d1 (deriv1 α)
  deriv2_wedge11 :
    ∀ α β, deriv2 (wedge11 α β) = wedge11 (deriv1 α) β + wedge11 α (deriv1 β)

attribute [instance] LocalConnectionVariationAlgebra.instAddCommGroupΩ1
attribute [instance] LocalConnectionVariationAlgebra.instAddCommGroupΩ2

structure ConnectionForm (A : LocalConnectionVariationAlgebra) where
  val : A.Ω1

def curvature (A : LocalConnectionVariationAlgebra) (conn : ConnectionForm A) : A.Ω2 :=
  A.d1 conn.val + A.wedge11 conn.val conn.val

def connectionVariation (A : LocalConnectionVariationAlgebra) (conn : ConnectionForm A) : A.Ω1 :=
  A.deriv1 conn.val

def covariantVariation (A : LocalConnectionVariationAlgebra)
    (conn : ConnectionForm A) (B : A.Ω1) : A.Ω2 :=
  A.d1 B + A.wedge11 B conn.val + A.wedge11 conn.val B

end Variation
