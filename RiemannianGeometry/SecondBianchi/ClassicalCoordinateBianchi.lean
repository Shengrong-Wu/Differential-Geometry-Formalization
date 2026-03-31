import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import SecondBianchi.CoordinateBianchi

open BigOperators Finset

namespace SecondBianchi.Coordinate

variable {n : ℕ}

/--
`PartialTerm n` represents the directional derivative contribution
`∂_dir R^i_{j,kl}` in coordinates.
-/
abbrev PartialTerm (n : ℕ) := Form2 n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ

def covariantDerivative
    (pderiv : PartialTerm n) (A : Form1 n) (R : Form2 n)
    (dir i j k l : Fin n) : ℝ :=
  pderiv R dir i j k l +
    ∑ m : Fin n,
      (A i m dir * R m j k l
        - R i m k l * A m j dir
        - A m k dir * R i j m l
        - A m l dir * R i j k m)

def cyclicCovariantDerivative
    (pderiv : PartialTerm n) (A : Form1 n) (R : Form2 n)
    (i j e k l : Fin n) : ℝ :=
  covariantDerivative pderiv A R e i j k l +
    covariantDerivative pderiv A R k i j l e +
    covariantDerivative pderiv A R l i j e k

private lemma sum_sub_four
    (f g h t : Fin n → ℝ) :
    (∑ m : Fin n, (f m - g m - h m - t m)) =
      (∑ m : Fin n, f m) - (∑ m : Fin n, g m) - (∑ m : Fin n, h m) - (∑ m : Fin n, t m) := by
  simp [sub_eq_add_neg, Finset.sum_add_distrib, add_assoc]

private lemma extra_terms_cancel
    (A : Form1 n) (R : Form2 n)
    (htf : ∀ i j k : Fin n, A i j k = A i k j)
    (hRantisym : ∀ i j k l : Fin n, R i j k l = -R i j l k)
    (i j e k l : Fin n) :
    (∑ m : Fin n,
      (-A m k e * R i j m l
        - A m l e * R i j k m
        - A m l k * R i j m e
        - A m e k * R i j l m
        - A m e l * R i j m k
        - A m k l * R i j e m)) = 0 := by
  calc
    _ = ∑ m : Fin n,
      (-A m k e * (R i j m l + R i j l m)
        - A m l e * (R i j k m + R i j m k)
        - A m l k * (R i j m e + R i j e m)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [htf m e k, htf m e l, htf m k l]
          ring
    _ = ∑ _m : Fin n, (0 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [hRantisym i j m l, hRantisym i j k m, hRantisym i j m e]
          ring
    _ = 0 := by simp

theorem cyclicCovariant_eq_component_formula
    (D : CoordDiffData n) (pderiv : PartialTerm n)
    (A : Form1 n) (R : Form2 n)
    (hd2 :
      ∀ i j e k l : Fin n,
        D.d2 R i j e k l =
          pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k)
    (htf : ∀ i j k : Fin n, A i j k = A i k j)
    (hRantisym : ∀ i j k l : Fin n, R i j k l = -R i j l k)
    (i j e k l : Fin n) :
    cyclicCovariantDerivative pderiv A R i j e k l =
      D.d2 R i j e k l
        + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
        - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k) := by
  let X : ℝ :=
    ∑ m : Fin n,
      (-A m k e * R i j m l
        - A m l e * R i j k m
        - A m l k * R i j m e
        - A m e k * R i j l m
        - A m e l * R i j m k
        - A m k l * R i j e m)
  have hsplit :
      cyclicCovariantDerivative pderiv A R i j e k l =
        D.d2 R i j e k l
          + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
          - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
          + X := by
    rw [cyclicCovariantDerivative, covariantDerivative, covariantDerivative, covariantDerivative, hd2]
    rw [sum_sub_four
        (f := fun m => A i m e * R m j k l)
        (g := fun m => R i m k l * A m j e)
        (h := fun m => A m k e * R i j m l)
        (t := fun m => A m l e * R i j k m)]
    rw [sum_sub_four
        (f := fun m => A i m k * R m j l e)
        (g := fun m => R i m l e * A m j k)
        (h := fun m => A m l k * R i j m e)
        (t := fun m => A m e k * R i j l m)]
    rw [sum_sub_four
        (f := fun m => A i m l * R m j e k)
        (g := fun m => R i m e k * A m j l)
        (h := fun m => A m e l * R i j m k)
        (t := fun m => A m k l * R i j e m)]
    set Pe : ℝ := ∑ m : Fin n, A i m e * R m j k l with hPe
    set Pk : ℝ := ∑ m : Fin n, A i m k * R m j l e with hPk
    set Pl : ℝ := ∑ m : Fin n, A i m l * R m j e k with hPl
    set Nek : ℝ := ∑ m : Fin n, R i m e k * A m j l with hNek
    set Nke : ℝ := ∑ m : Fin n, R i m k l * A m j e with hNke
    set Nle : ℝ := ∑ m : Fin n, R i m l e * A m j k with hNle
    set X₁ : ℝ := ∑ m : Fin n, A m k e * R i j m l with hX₁
    set X₂ : ℝ := ∑ m : Fin n, A m l e * R i j k m with hX₂
    set X₃ : ℝ := ∑ m : Fin n, A m l k * R i j m e with hX₃
    set X₄ : ℝ := ∑ m : Fin n, A m e k * R i j l m with hX₄
    set X₅ : ℝ := ∑ m : Fin n, A m e l * R i j m k with hX₅
    set X₆ : ℝ := ∑ m : Fin n, A m k l * R i j e m with hX₆
    have hgroup :
        (pderiv R e i j k l + (Pe - Nke - X₁ - X₂)) +
            ((pderiv R k i j l e + (Pk - Nle - X₃ - X₄)) +
              (pderiv R l i j e k + (Pl - Nek - X₅ - X₆))) =
          (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k) +
            ((Pe + Pk + Pl) - (Nek + Nke + Nle) + (-X₁ - X₂ - X₃ - X₄ - X₅ - X₆)) := by
      abel_nf
    have hpos :
        Pe + Pk + Pl =
          ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k) := by
      rw [hPe, hPk, hPl]
      simp [Finset.sum_add_distrib, add_assoc]
    have hneg :
        Nek + Nke + Nle =
          ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k) := by
      rw [hNek, hNke, hNle]
      simp [Finset.sum_add_distrib, add_assoc]
    have hextra :
        -X₁ - X₂ - X₃ - X₄ - X₅ - X₆ = X := by
      rw [hX₁, hX₂, hX₃, hX₄, hX₅, hX₆]
      dsimp [X]
      simp [sub_eq_add_neg, Finset.sum_add_distrib, add_assoc]
    have h1 :
        pderiv R e i j k l + (Pe - Nke - X₁ - X₂) +
            (pderiv R k i j l e + (Pk - Nle - X₃ - X₄)) +
          (pderiv R l i j e k + (Pl - Nek - X₅ - X₆)) =
          (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k) +
            ((Pe + Pk + Pl) - (Nek + Nke + Nle) + (-X₁ - X₂ - X₃ - X₄ - X₅ - X₆)) := by
      simpa [add_assoc] using hgroup
    have h23 :
        (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k) +
            ((Pe + Pk + Pl) - (Nek + Nke + Nle) + (-X₁ - X₂ - X₃ - X₄ - X₅ - X₆)) =
          (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k)
            + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
            - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
            + X := by
      rw [hpos, hneg, hextra]
      abel_nf
    have h24 :
        (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k)
            + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
            - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
            + X =
          D.d2 R i j e k l
            + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
            - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
            + X := by
      linarith [hd2 i j e k l]
    exact
      (h1.trans (by simpa [add_assoc] using h23)).trans
        (by simpa [add_assoc] using h24)
  have hX : X = 0 := by
    dsimp [X]
    exact extra_terms_cancel A R htf hRantisym i j e k l
  rw [hX] at hsplit
  simpa [sub_eq_add_neg, add_assoc] using hsplit

/--
Specialized bridge theorem: once you prove that the cyclic covariant derivative
matches the already-formalized component expression for `(d_∇ R)^i_{j,ekl}`,
the classical indexed second Bianchi identity follows immediately.
-/
theorem classical_second_bianchi_cyclic_of_bridge
    (D : CoordDiffData n) (pderiv : PartialTerm n)
    (A : Form1 n)
    (hbridge :
      ∀ i j e k l : Fin n,
        cyclicCovariantDerivative pderiv A (curvature (coordAlgebra n D) ⟨A⟩) i j e k l =
          D.d2 (curvature (coordAlgebra n D) ⟨A⟩) i j e k l
            + ∑ m : Fin n,
                (A i m e * curvature (coordAlgebra n D) ⟨A⟩ m j k l
                  + A i m k * curvature (coordAlgebra n D) ⟨A⟩ m j l e
                  + A i m l * curvature (coordAlgebra n D) ⟨A⟩ m j e k)
            - ∑ m : Fin n,
                (curvature (coordAlgebra n D) ⟨A⟩ i m e k * A m j l
                  + curvature (coordAlgebra n D) ⟨A⟩ i m k l * A m j e
                  + curvature (coordAlgebra n D) ⟨A⟩ i m l e * A m j k)) :
    ∀ i j e k l : Fin n,
      cyclicCovariantDerivative pderiv A (curvature (coordAlgebra n D) ⟨A⟩) i j e k l = 0 := by
  intro i j e k l
  rw [hbridge i j e k l]
  exact classical_second_bianchi (n := n) D A i j e k l

theorem classical_second_bianchi_cyclic
    (D : CoordDiffData n) (pderiv : PartialTerm n)
    (A : Form1 n)
    (hd2 :
      ∀ i j e k l : Fin n,
        D.d2 (curvature (coordAlgebra n D) ⟨A⟩) i j e k l =
          pderiv (curvature (coordAlgebra n D) ⟨A⟩) e i j k l +
            pderiv (curvature (coordAlgebra n D) ⟨A⟩) k i j l e +
            pderiv (curvature (coordAlgebra n D) ⟨A⟩) l i j e k)
    (htf : ∀ i j k : Fin n, A i j k = A i k j)
    (hRantisym :
      ∀ i j k l : Fin n,
        curvature (coordAlgebra n D) ⟨A⟩ i j k l =
          -curvature (coordAlgebra n D) ⟨A⟩ i j l k) :
    ∀ i j e k l : Fin n,
      cyclicCovariantDerivative pderiv A (curvature (coordAlgebra n D) ⟨A⟩) i j e k l = 0 := by
  apply classical_second_bianchi_cyclic_of_bridge (D := D) (pderiv := pderiv) (A := A)
  intro i j e k l
  exact cyclicCovariant_eq_component_formula D pderiv A (curvature (coordAlgebra n D) ⟨A⟩)
    hd2 htf hRantisym i j e k l

end SecondBianchi.Coordinate
