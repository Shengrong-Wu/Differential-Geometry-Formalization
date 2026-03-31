import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Abel

namespace SecondBianchi

universe u v w

/--
A minimal local algebra of differential forms in degrees 1, 2, and 3.

It is designed for the local connection-form presentation
`Ω = dA + A ∧ A` and the corresponding covariant exterior derivative
`d_∇ Ω = dΩ + A ∧ Ω - Ω ∧ A`.
-/
structure LocalConnectionAlgebra where
  Ω1 : Type u
  Ω2 : Type v
  Ω3 : Type w
  [instAddCommGroupΩ1 : AddCommGroup Ω1]
  [instAddCommGroupΩ2 : AddCommGroup Ω2]
  [instAddCommGroupΩ3 : AddCommGroup Ω3]
  d1 : Ω1 → Ω2
  d2 : Ω2 → Ω3
  wedge11 : Ω1 → Ω1 → Ω2
  wedge12 : Ω1 → Ω2 → Ω3
  wedge21 : Ω2 → Ω1 → Ω3
  d2_add : ∀ β₁ β₂, d2 (β₁ + β₂) = d2 β₁ + d2 β₂
  wedge12_add_right :
    ∀ α β₁ β₂, wedge12 α (β₁ + β₂) = wedge12 α β₁ + wedge12 α β₂
  wedge21_add_left :
    ∀ β₁ β₂ α, wedge21 (β₁ + β₂) α = wedge21 β₁ α + wedge21 β₂ α
  d2_d1_eq_zero : ∀ α, d2 (d1 α) = 0
  d2_wedge11 :
    ∀ α β, d2 (wedge11 α β) = wedge21 (d1 α) β - wedge12 α (d1 β)
  wedge_assoc :
    ∀ α β γ, wedge12 α (wedge11 β γ) = wedge21 (wedge11 α β) γ

attribute [instance] LocalConnectionAlgebra.instAddCommGroupΩ1
attribute [instance] LocalConnectionAlgebra.instAddCommGroupΩ2
attribute [instance] LocalConnectionAlgebra.instAddCommGroupΩ3

structure ConnectionForm (A : LocalConnectionAlgebra) where
  val : A.Ω1

def curvature (A : LocalConnectionAlgebra) (conn : ConnectionForm A) : A.Ω2 :=
  A.d1 conn.val + A.wedge11 conn.val conn.val

def covariantExterior (A : LocalConnectionAlgebra) (conn : ConnectionForm A) (omega : A.Ω2) :
    A.Ω3 :=
  A.d2 omega + A.wedge12 conn.val omega - A.wedge21 omega conn.val

end SecondBianchi
