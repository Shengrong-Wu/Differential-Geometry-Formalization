import Curvature.Basic
import Mathlib.Tactic.Linarith

namespace Curvature

universe u v

/-- Skew symmetry in the first two curvature slots. -/
def FirstPairSkew
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) : Prop :=
  ∀ X Y Z, R X Y Z = -R Y X Z

theorem firstPairSkew_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : CurvatureTensor C} :
    FirstPairSkew R ↔ ∀ X Y Z, R X Y Z = -R Y X Z :=
  Iff.rfl

theorem firstPairSkew_swap
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : CurvatureTensor C}
    (hR : FirstPairSkew R) :
    ∀ X Y Z, R Y X Z = -R X Y Z := by
  intro X Y Z
  simpa using hR Y X Z

/-- Under skew symmetry, the doubled repeated-entry term vanishes. -/
theorem add_self_eq_zero_of_firstPairSkew
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : CurvatureTensor C}
    (hR : FirstPairSkew R) :
    ∀ X Z, R X X Z + R X X Z = 0 := by
  intro X Z
  have h := hR X X Z
  simpa using eq_neg_iff_add_eq_zero.mp h

/-- The abstract first Bianchi-type cyclic sum predicate. -/
def FirstBianchi
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (R : CurvatureTensor C) : Prop :=
  ∀ X Y Z, R X Y Z + R Y Z X + R Z X Y = 0

theorem firstBianchi_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : CurvatureTensor C} :
    FirstBianchi R ↔ ∀ X Y Z, R X Y Z + R Y Z X + R Z X Y = 0 :=
  Iff.rfl

theorem firstBianchi_rotate
    {V : Type u} {S : Type v}
    [AddCommGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : CurvatureTensor C}
    (hR : FirstBianchi R) :
    ∀ X Y Z, R Y Z X + R Z X Y + R X Y Z = 0 := by
  intro X Y Z
  calc
    R Y Z X + R Z X Y + R X Y Z = R X Y Z + R Y Z X + R Z X Y := by
      rw [add_assoc]
      rw [add_comm (R Z X Y) (R X Y Z)]
      rw [← add_assoc]
      rw [add_comm (R Y Z X) (R X Y Z)]
    _ = 0 := hR X Y Z

theorem firstBianchi_solve_third
    {V : Type u} {S : Type v}
    [AddCommGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : CurvatureTensor C}
    (hR : FirstBianchi R) :
    ∀ X Y Z, R Z X Y = -(R X Y Z + R Y Z X) := by
  intro X Y Z
  apply eq_neg_of_add_eq_zero_left
  calc
    R Z X Y + (R X Y Z + R Y Z X) = R X Y Z + R Y Z X + R Z X Y := by
      rw [← add_assoc]
      rw [add_comm (R Z X Y) (R X Y Z)]
      rw [add_assoc]
      rw [add_comm (R Z X Y) (R Y Z X)]
      rw [← add_assoc]
    _ = 0 := hR X Y Z

end Curvature
