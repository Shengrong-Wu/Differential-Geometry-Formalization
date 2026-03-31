import Mathlib.Analysis.InnerProductSpace.Dual
import Metric.Basic

open scoped Bundle
open Bundle

namespace Metric

noncomputable section

open InnerProductSpace

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- The cotangent space is modeled as the strong dual of the tangent space. -/
abbrev CotangentSpace (x : M) := StrongDual ℝ (TangentSpace I (M := M) x)

/-- The musical `flat` map induced by the Riemannian inner product. -/
def flat (x : M) :
    TangentSpace I (M := M) x →L[ℝ] StrongDual ℝ (TangentSpace I (M := M) x) :=
  (InnerProductSpace.toDualMap ℝ (TangentSpace I (M := M) x)).toContinuousLinearMap

@[simp] theorem flat_apply (x : M) (v w : TangentSpace I (M := M) x) :
    flat (I := I) (M := M) x v w = tangentInner x v w := by
  rfl

/-- The musical `sharp` map induced by the Riemannian inner product. This requires completeness of
the tangent space so that Fréchet-Riesz is available. -/
def sharp (x : M) [CompleteSpace (TangentSpace I (M := M) x)] :
    StrongDual ℝ (TangentSpace I (M := M) x) → TangentSpace I (M := M) x :=
  (InnerProductSpace.toDual ℝ (TangentSpace I (M := M) x)).symm

@[simp] theorem sharp_apply
    (x : M) [CompleteSpace (TangentSpace I (M := M) x)]
    (ℓ : CotangentSpace (I := I) (M := M) x) (v : TangentSpace I (M := M) x) :
    tangentInner x (sharp (I := I) (M := M) x ℓ) v = ℓ v := by
  show inner ℝ (sharp (I := I) (M := M) x ℓ) v = ℓ v
  simpa [sharp] using
    (InnerProductSpace.toDual_symm_apply
      (𝕜 := ℝ) (E := TangentSpace I (M := M) x) (x := v) (y := ℓ))

@[simp] theorem sharp_flat
    (x : M) [CompleteSpace (TangentSpace I (M := M) x)] (v : TangentSpace I (M := M) x) :
    sharp (I := I) (M := M) x (flat (I := I) (M := M) x v) = v := by
  change (InnerProductSpace.toDual ℝ (TangentSpace I (M := M) x)).symm
      ((InnerProductSpace.toDual ℝ (TangentSpace I (M := M) x)) v) = v
  exact (InnerProductSpace.toDual ℝ (TangentSpace I (M := M) x)).symm_apply_apply v

@[simp] theorem flat_sharp
    (x : M) [CompleteSpace (TangentSpace I (M := M) x)]
    (ℓ : CotangentSpace (I := I) (M := M) x) :
    flat (I := I) (M := M) x (sharp (I := I) (M := M) x ℓ) = ℓ := by
  change (InnerProductSpace.toDual ℝ (TangentSpace I (M := M) x))
      ((InnerProductSpace.toDual ℝ (TangentSpace I (M := M) x)).symm ℓ) = ℓ
  exact (InnerProductSpace.toDual ℝ (TangentSpace I (M := M) x)).apply_symm_apply ℓ

theorem flat_injective (x : M) :
    Function.Injective (flat (I := I) (M := M) x) := by
  exact (InnerProductSpace.toDualMap ℝ (TangentSpace I (M := M) x)).injective

theorem flat_eq_iff (x : M) (v w : TangentSpace I (M := M) x) :
    flat (I := I) (M := M) x v = flat (I := I) (M := M) x w ↔ v = w := by
  exact (flat_injective (I := I) (M := M) x).eq_iff

theorem eq_of_flat_eq
    (x : M) {v w : TangentSpace I (M := M) x}
    (h : flat (I := I) (M := M) x v = flat (I := I) (M := M) x w) : v = w :=
  flat_injective (I := I) (M := M) x h

theorem ext_of_flat
    (x : M) {v w : TangentSpace I (M := M) x}
    (h : ∀ u : TangentSpace I (M := M) x, tangentInner x v u = tangentInner x w u) : v = w := by
  apply eq_of_flat_eq (I := I) (M := M) x
  ext u
  exact h u

end

end Metric
