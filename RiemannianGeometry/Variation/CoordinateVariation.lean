import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Variation.ComponentBridge

open BigOperators Finset

namespace Variation.Coordinate

variable (n : ℕ)

abbrev Form1 := Fin n → Fin n → Fin n → ℝ
abbrev Form2 := Fin n → Fin n → Fin n → Fin n → ℝ

instance : AddCommGroup (Form1 n) := inferInstance
instance : AddCommGroup (Form2 n) := inferInstance

def wedge11 (A B : Form1 n) : Form2 n :=
  fun i j μ ν => ∑ k : Fin n, (A i k μ * B k j ν - A i k ν * B k j μ)

structure CoordVariationData (n : ℕ) where
  d1 : Form1 n → Form2 n
  deriv1 : Form1 n → Form1 n
  deriv2 : Form2 n → Form2 n
  deriv2_add : ∀ R₁ R₂ : Form2 n, deriv2 (R₁ + R₂) = deriv2 R₁ + deriv2 R₂
  deriv2_d1 : ∀ A : Form1 n, deriv2 (d1 A) = d1 (deriv1 A)
  deriv2_wedge11 :
    ∀ A B : Form1 n, deriv2 (wedge11 n A B) = wedge11 n (deriv1 A) B + wedge11 n A (deriv1 B)

def coordAlgebra (D : CoordVariationData n) : LocalConnectionVariationAlgebra where
  Ω1 := Form1 n
  Ω2 := Form2 n
  d1 := D.d1
  wedge11 := wedge11 n
  deriv1 := D.deriv1
  deriv2 := D.deriv2
  deriv2_add := D.deriv2_add
  deriv2_d1 := D.deriv2_d1
  deriv2_wedge11 := D.deriv2_wedge11

def coordProjection (D : CoordVariationData n) :
    ComponentProjection (coordAlgebra n D) (Fin n × Fin n × Fin n × Fin n) ℝ where
  proj := fun ω ⟨i, j, μ, ν⟩ => ω i j μ ν

theorem proj_curvature_variation_eq_explicit
    (D : CoordVariationData n) (A : Form1 n) (i j μ ν : Fin n) :
    let conn : ConnectionForm (coordAlgebra n D) := ⟨A⟩
    let dotA := connectionVariation (coordAlgebra n D) conn
    (coordProjection n D).proj
        (covariantVariation (coordAlgebra n D) conn dotA) (i, j, μ, ν) =
      D.d1 dotA i j μ ν
        + (∑ k : Fin n, (dotA i k μ * A k j ν - dotA i k ν * A k j μ))
        + ∑ k : Fin n, (A i k μ * dotA k j ν - A i k ν * dotA k j μ) := by
  simp [coordProjection, covariantVariation, connectionVariation, coordAlgebra, wedge11]

theorem classical_curvature_variation
    (D : CoordVariationData n) (A : Form1 n) :
    let conn : ConnectionForm (coordAlgebra n D) := ⟨A⟩
    let dotA := connectionVariation (coordAlgebra n D) conn
    ∀ i j μ ν : Fin n,
      D.deriv2 (curvature (coordAlgebra n D) conn) i j μ ν =
        D.d1 dotA i j μ ν
          + (∑ k : Fin n, (dotA i k μ * A k j ν - dotA i k ν * A k j μ))
          + ∑ k : Fin n, (A i k μ * dotA k j ν - A i k ν * dotA k j μ) := by
  intro conn dotA i j μ ν
  have h :=
    curvature_variation_in_components (coordAlgebra n D) conn (coordProjection n D) (i, j, μ, ν)
  rw [proj_curvature_variation_eq_explicit] at h
  simpa [coordProjection, coordAlgebra] using h

end Variation.Coordinate
