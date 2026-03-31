import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

open scoped Bundle
open Bundle

namespace Metric

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- The Riemannian inner product on the tangent space at `x`. -/
def tangentInner (x : M) (v w : TangentSpace I x) : ℝ :=
  inner ℝ v w

@[simp] theorem tangentInner_eq_inner (x : M) (v w : TangentSpace I x) :
    tangentInner x v w = inner ℝ v w :=
  rfl

@[simp] theorem tangentInner_self (x : M) (v : TangentSpace I x) :
    tangentInner x v v = ‖v‖ ^ 2 := by
  simpa [tangentInner] using real_inner_self_eq_norm_sq v

theorem tangentInner_symm (x : M) (v w : TangentSpace I x) :
    tangentInner x v w = tangentInner x w v := by
  simpa [tangentInner] using (real_inner_comm v w).symm

/-- Orthogonality in a tangent space. -/
def OrthogonalAt (x : M) (v w : TangentSpace I x) : Prop :=
  tangentInner x v w = 0

theorem orthogonalAt_comm {x : M} {v w : TangentSpace I x} :
    OrthogonalAt x v w ↔ OrthogonalAt x w v := by
  simpa [OrthogonalAt] using show inner ℝ v w = 0 ↔ inner ℝ w v = 0 by
    rw [real_inner_comm]

theorem tangentInner_nonneg (x : M) (v : TangentSpace I x) :
    0 ≤ tangentInner x v v := by
  simp only [tangentInner]
  exact real_inner_self_nonneg

theorem tangentInner_zero_iff (x : M) (v : TangentSpace I x) :
    tangentInner x v v = 0 ↔ v = 0 := by
  simpa [tangentInner] using @inner_self_eq_zero ℝ _ _ _ v

theorem tangentInner_pos_of_ne_zero (x : M) {v : TangentSpace I x} (hv : v ≠ 0) :
    0 < tangentInner x v v := by
  rcases (tangentInner_nonneg x v).lt_or_eq with h | h
  · exact h
  · exact absurd ((tangentInner_zero_iff x v).mp h.symm) hv

theorem tangentInner_cauchy_schwarz (x : M) (v w : TangentSpace I x) :
    |tangentInner x v w| ≤ ‖v‖ * ‖w‖ := by
  simpa [tangentInner] using abs_real_inner_le_norm v w

end

end Metric
