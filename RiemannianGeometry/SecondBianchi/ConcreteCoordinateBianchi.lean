import Mathlib.Tactic.Ring
import SecondBianchi.ClassicalCoordinateBianchi

open BigOperators Finset

namespace SecondBianchi.Coordinate

variable {n : ℕ}

/-- `PartialTerm1 n` represents `∂_dir A^i_{j,k}` in coordinates. -/
abbrev PartialTerm1 (n : ℕ) := Form1 n → Fin n → Fin n → Fin n → Fin n → ℝ

/-- Concrete coordinate formula for the exterior derivative of a matrix-valued 1-form. -/
def concreteD1 (pderiv : PartialTerm1 n) : Form1 n → Form2 n :=
  fun A i j k l => pderiv A k i j l - pderiv A l i j k

/-- Concrete coordinate formula for the exterior derivative of a matrix-valued 2-form. -/
def concreteD2 (pderiv : PartialTerm n) : Form2 n → Form3 n :=
  fun R i j e k l =>
    pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k

/--
`ConcreteCoordDiffData` packages the coordinate differential data together with
explicit partial-derivative formulas for `d1` and `d2`.

The smooth-structure facts still needed by the abstract second Bianchi proof are
recorded as the two axioms `d2_d1` and `d2_wdg`.
-/
structure ConcreteCoordDiffData (n : ℕ) where
  pderiv1 : PartialTerm1 n
  pderiv2 : PartialTerm n
  d2_add :
    ∀ R₁ R₂ : Form2 n,
      concreteD2 pderiv2 (R₁ + R₂) = concreteD2 pderiv2 R₁ + concreteD2 pderiv2 R₂
  d2_d1 :
    ∀ A : Form1 n, concreteD2 pderiv2 (concreteD1 pderiv1 A) = 0
  d2_wdg :
    ∀ A B : Form1 n,
      concreteD2 pderiv2 (wedge11 n A B) =
        wedge21 n (concreteD1 pderiv1 A) B - wedge12 n A (concreteD1 pderiv1 B)

/-- The abstract differential data induced by the concrete coordinate formulas. -/
def ConcreteCoordDiffData.toCoordDiffData (D : ConcreteCoordDiffData n) : CoordDiffData n where
  d1 := concreteD1 D.pderiv1
  d2 := concreteD2 D.pderiv2
  d2_add := D.d2_add
  d2_d1 := D.d2_d1
  d2_wdg := D.d2_wdg

private theorem concreteD1_antisym
    (D : ConcreteCoordDiffData n) (A : Form1 n) (i j k l : Fin n) :
    concreteD1 D.pderiv1 A i j k l = -concreteD1 D.pderiv1 A i j l k := by
  simp [concreteD1]

private theorem wedge11_self_antisym
    (A : Form1 n) (i j k l : Fin n) :
    wedge11 n A A i j k l = -wedge11 n A A i j l k := by
  unfold wedge11
  rw [show -(∑ m : Fin n, (A i m l * A m j k - A i m k * A m j l)) =
      ∑ m : Fin n, -(A i m l * A m j k - A i m k * A m j l) by
        simp]
  refine Finset.sum_congr rfl ?_
  intro m hm
  ring

/--
With the concrete formula `R = dA + A ∧ A`, curvature is automatically
antisymmetric in its last two indices.
-/
theorem curvature_antisym
    (D : ConcreteCoordDiffData n) (A : Form1 n) :
    ∀ i j k l : Fin n,
      curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩ i j k l =
        -curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩ i j l k := by
  intro i j k l
  change concreteD1 D.pderiv1 A i j k l + wedge11 n A A i j k l =
    -(concreteD1 D.pderiv1 A i j l k + wedge11 n A A i j l k)
  rw [neg_add, concreteD1_antisym, wedge11_self_antisym]

/--
Concrete bridge theorem: once `d2` is defined as the cyclic sum of partial
derivatives, the only remaining hypothesis for the cyclic covariant-derivative
form is torsion-freeness of the connection coefficients.
-/
theorem cyclicCovariant_eq_component_formula_concrete
    (D : ConcreteCoordDiffData n) (A : Form1 n)
    (htf : ∀ i j k : Fin n, A i j k = A i k j)
    (i j e k l : Fin n) :
    cyclicCovariantDerivative D.pderiv2 A
        (curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩) i j e k l =
      concreteD2 D.pderiv2 (curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩) i j e k l
        + ∑ m : Fin n,
            (A i m e * curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩ m j k l
              + A i m k * curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩ m j l e
              + A i m l * curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩ m j e k)
        - ∑ m : Fin n,
            (curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩ i m e k * A m j l
              + curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩ i m k l * A m j e
              + curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩ i m l e * A m j k) := by
  simpa [ConcreteCoordDiffData.toCoordDiffData, concreteD2] using
    cyclicCovariant_eq_component_formula (D := D.toCoordDiffData) (pderiv := D.pderiv2)
      (A := A) (R := curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩)
      (hd2 := by intro i j e k l; rfl) htf (curvature_antisym D A) i j e k l

/--
Concrete classical second Bianchi identity in cyclic covariant-derivative form.

The hypotheses `hd2` and `hRantisym` are now discharged internally from the
explicit coordinate formulas for `d2` and `R`.
-/
theorem classical_second_bianchi_cyclic_concrete
    (D : ConcreteCoordDiffData n) (A : Form1 n)
    (htf : ∀ i j k : Fin n, A i j k = A i k j) :
    ∀ i j e k l : Fin n,
      cyclicCovariantDerivative D.pderiv2 A
        (curvature (coordAlgebra n D.toCoordDiffData) ⟨A⟩) i j e k l = 0 := by
  intro i j e k l
  exact classical_second_bianchi_cyclic (D := D.toCoordDiffData) (pderiv := D.pderiv2) (A := A)
    (hd2 := by intro i j e k l; rfl) htf (curvature_antisym D A) i j e k l

end SecondBianchi.Coordinate
