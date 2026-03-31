import Curvature.Symmetries
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

namespace Curvature

universe u v

open scoped BigOperators

/-- A scalar-valued pairing for curvature contractions. -/
abbrev Pairing (V : Type u) (S : Type v) := V → V → S

/-- Sectional curvature packaged as an abstract scalar-valued function of a 2-plane basis. -/
def SectionalCurvature
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    (g : Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) : V → V → S :=
  fun X Y => g (R X Y Y) X

@[simp] theorem sectionalCurvature_apply
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    (g : Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) (X Y : V) :
    SectionalCurvature g R X Y = g (R X Y Y) X :=
  rfl

theorem sectionalCurvature_congr
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {g g' : Pairing V S} {C : LeviCivita.ConnectionContext V S}
    {R R' : CurvatureTensor C}
    (hg : ∀ U W, g U W = g' U W)
    (hR : ∀ X Y Z, R X Y Z = R' X Y Z) :
    SectionalCurvature g R = SectionalCurvature g' R' := by
  funext X Y
  simp [SectionalCurvature, hg, hR]

/-- Ricci curvature packaged as a contraction against a chosen finite frame. -/
def RicciCurvature
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [AddCommMonoid S] [Fintype ι]
    (g : Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) (frame : ι → V) : V → V → S :=
  fun X Y => ∑ i, g (R (frame i) X Y) (frame i)

@[simp] theorem ricciCurvature_apply
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [AddCommMonoid S] [Fintype ι]
    (g : Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) (frame : ι → V) (X Y : V) :
    RicciCurvature g R frame X Y = ∑ i, g (R (frame i) X Y) (frame i) :=
  rfl

theorem ricciCurvature_congr
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [AddCommMonoid S] [Fintype ι]
    {g g' : Pairing V S} {C : LeviCivita.ConnectionContext V S}
    {R R' : CurvatureTensor C} {frame frame' : ι → V}
    (hg : ∀ U W, g U W = g' U W)
    (hR : ∀ X Y Z, R X Y Z = R' X Y Z)
    (hframe : ∀ i, frame i = frame' i) :
    RicciCurvature g R frame = RicciCurvature g' R' frame' := by
  funext X Y
  simp [RicciCurvature, hg]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hR, hframe i]

theorem ricciCurvature_eq_of_frame_eq
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [AddCommMonoid S] [Fintype ι]
    (g : Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) {frame frame' : ι → V}
    (hframe : ∀ i, frame i = frame' i) :
    RicciCurvature g R frame = RicciCurvature g R frame' := by
  exact ricciCurvature_congr (g := g) (g' := g) (R := R) (R' := R)
    (frame := frame) (frame' := frame') (fun _ _ => rfl) (fun _ _ _ => rfl) hframe

/-- Abstract Ricci lower bound interface used in comparison theorems. -/
def RicciLowerBound
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [Preorder S] [AddCommMonoid S] [Fintype ι]
    (g : Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) (frame : ι → V) (k : S) : Prop :=
  ∀ X, k ≤ RicciCurvature g R frame X X

theorem ricciLowerBound_iff
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [Preorder S] [AddCommMonoid S] [Fintype ι]
    {g : Pairing V S} {C : LeviCivita.ConnectionContext V S}
    {R : CurvatureTensor C} {frame : ι → V} {k : S} :
    RicciLowerBound g R frame k ↔ ∀ X, k ≤ RicciCurvature g R frame X X :=
  Iff.rfl

abbrev RicciLowerBoundReal
    {V : Type u} {ι : Type*}
    [AddGroup V] [SMul ℝ V] [Fintype ι]
    (g : Pairing V ℝ) {C : LeviCivita.ConnectionContext V ℝ}
    (R : CurvatureTensor C) (frame : ι → V) (k : ℝ) : Prop :=
  RicciLowerBound g R frame k

theorem ricciLowerBoundReal_iff
    {V : Type u} {ι : Type*}
    [AddGroup V] [SMul ℝ V] [Fintype ι]
    {g : Pairing V ℝ} {C : LeviCivita.ConnectionContext V ℝ}
    {R : CurvatureTensor C} {frame : ι → V} {k : ℝ} :
    RicciLowerBoundReal g R frame k ↔ ∀ X, k ≤ RicciCurvature g R frame X X :=
  Iff.rfl

theorem ricciLowerBound_of_pointwise
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [Preorder S] [AddCommMonoid S] [Fintype ι]
    (g : Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) (frame : ι → V) (k : S)
    (h : ∀ X, k ≤ RicciCurvature g R frame X X) :
    RicciLowerBound g R frame k :=
  h

theorem ricciLowerBound_mono
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [Preorder S] [AddCommMonoid S] [Fintype ι]
    {g : Pairing V S} {C : LeviCivita.ConnectionContext V S}
    {R : CurvatureTensor C} {frame : ι → V} {k k' : S}
    (hk : k' ≤ k)
    (hRic : RicciLowerBound g R frame k) :
    RicciLowerBound g R frame k' := by
  intro X
  exact le_trans hk (hRic X)

theorem ricciLowerBound_congr
    {V : Type u} {S : Type v} {ι : Type*}
    [AddGroup V] [SMul S V] [Preorder S] [AddCommMonoid S] [Fintype ι]
    {g g' : Pairing V S} {C : LeviCivita.ConnectionContext V S}
    {R R' : CurvatureTensor C} {frame frame' : ι → V} {k : S}
    (hg : ∀ U W, g U W = g' U W)
    (hR : ∀ X Y Z, R X Y Z = R' X Y Z)
    (hframe : ∀ i, frame i = frame' i) :
    RicciLowerBound g R frame k ↔ RicciLowerBound g' R' frame' k := by
  have hRic :
      RicciCurvature g R frame = RicciCurvature g' R' frame' :=
    ricciCurvature_congr (g := g) (g' := g') (R := R) (R' := R')
      (frame := frame) (frame' := frame') hg hR hframe
  have hRic' :
      RicciCurvature g' R' frame' = RicciCurvature g R frame :=
    ricciCurvature_congr (g := g') (g' := g) (R := R') (R' := R)
      (frame := frame') (frame' := frame)
      (fun U W => (hg U W).symm) (fun X Y Z => (hR X Y Z).symm) (fun i => (hframe i).symm)
  rw [ricciLowerBound_iff, ricciLowerBound_iff]
  constructor <;> intro h X
  · have hRicX : RicciCurvature g R frame X X = RicciCurvature g' R' frame' X X := by
        simpa using congrArg (fun f : V → V → S => f X X) hRic
    rw [← hRicX]
    exact h X
  · have hRicX : RicciCurvature g' R' frame' X X = RicciCurvature g R frame X X := by
        simpa using congrArg (fun f : V → V → S => f X X) hRic'
    rw [← hRicX]
    exact h X

theorem ricciLowerBoundReal_of_pointwise
    {V : Type u} {ι : Type*}
    [AddGroup V] [SMul ℝ V] [Fintype ι]
    (g : Pairing V ℝ) {C : LeviCivita.ConnectionContext V ℝ}
    (R : CurvatureTensor C) (frame : ι → V) (k : ℝ)
    (h : ∀ X, k ≤ RicciCurvature g R frame X X) :
    RicciLowerBoundReal g R frame k :=
  h

end Curvature
