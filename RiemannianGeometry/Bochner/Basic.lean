import Mathlib.Algebra.Group.Basic

namespace Bochner

universe u v w x y

/--
A minimal local algebra for the bundle-valued Bochner package.

`ΩEnd1`, `ΩEnd2` model `End(E)`-valued 1- and 2-forms, while `ΩE0`, `ΩE1`,
`ΩE2` model `E`-valued 0-, 1-, and 2-forms.  The axioms are exactly the ones
needed to prove the structural identity `d_∇² = F ∧ (·)` on sections.
-/
structure BundleConnectionAlgebra where
  ΩEnd1 : Type u
  ΩEnd2 : Type v
  ΩE0 : Type w
  ΩE1 : Type x
  ΩE2 : Type y
  [instAddCommGroupΩEnd1 : AddCommGroup ΩEnd1]
  [instAddCommGroupΩEnd2 : AddCommGroup ΩEnd2]
  [instAddCommGroupΩE0 : AddCommGroup ΩE0]
  [instAddCommGroupΩE1 : AddCommGroup ΩE1]
  [instAddCommGroupΩE2 : AddCommGroup ΩE2]
  dEnd : ΩEnd1 → ΩEnd2
  dE0 : ΩE0 → ΩE1
  dE1 : ΩE1 → ΩE2
  wedgeEnd : ΩEnd1 → ΩEnd1 → ΩEnd2
  act0 : ΩEnd1 → ΩE0 → ΩE1
  act1 : ΩEnd1 → ΩE1 → ΩE2
  act2 : ΩEnd2 → ΩE0 → ΩE2
  dE1_add : ∀ ω₁ ω₂, dE1 (ω₁ + ω₂) = dE1 ω₁ + dE1 ω₂
  act1_add_right : ∀ A ω₁ ω₂, act1 A (ω₁ + ω₂) = act1 A ω₁ + act1 A ω₂
  act2_add_left : ∀ F₁ F₂ s, act2 (F₁ + F₂) s = act2 F₁ s + act2 F₂ s
  dE1_dE0_eq_zero : ∀ s, dE1 (dE0 s) = 0
  dE1_act0 : ∀ A s, dE1 (act0 A s) = act2 (dEnd A) s - act1 A (dE0 s)
  act_assoc : ∀ A B s, act1 A (act0 B s) = act2 (wedgeEnd A B) s

attribute [instance] BundleConnectionAlgebra.instAddCommGroupΩEnd1
attribute [instance] BundleConnectionAlgebra.instAddCommGroupΩEnd2
attribute [instance] BundleConnectionAlgebra.instAddCommGroupΩE0
attribute [instance] BundleConnectionAlgebra.instAddCommGroupΩE1
attribute [instance] BundleConnectionAlgebra.instAddCommGroupΩE2

structure ConnectionForm (A : BundleConnectionAlgebra) where
  val : A.ΩEnd1

def curvature (A : BundleConnectionAlgebra) (conn : ConnectionForm A) : A.ΩEnd2 :=
  A.dEnd conn.val + A.wedgeEnd conn.val conn.val

def covariantDeriv0 (A : BundleConnectionAlgebra) (conn : ConnectionForm A) (s : A.ΩE0) :
    A.ΩE1 :=
  A.dE0 s + A.act0 conn.val s

def covariantDeriv1 (A : BundleConnectionAlgebra) (conn : ConnectionForm A) (ω : A.ΩE1) :
    A.ΩE2 :=
  A.dE1 ω + A.act1 conn.val ω

def curvatureAction (A : BundleConnectionAlgebra) (conn : ConnectionForm A) (s : A.ΩE0) :
    A.ΩE2 :=
  A.act2 (curvature A conn) s

end Bochner
