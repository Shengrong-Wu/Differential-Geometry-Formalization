import Mathlib.Geometry.Manifold.Riemannian.Basic
import Metric.Basic

open scoped Bundle

namespace Metric

noncomputable section

open Bundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- Package-level alias for a smooth tangent-bundle metric. -/
abbrev SmoothMetric :=
  Bundle.ContMDiffRiemannianMetric I (⊤ : WithTop ℕ∞) E (fun x : M => TangentSpace I x)

/-- More general finite-regularity version of `SmoothMetric`. -/
abbrev ContMDiffMetric (n : WithTop ℕ∞) :=
  Bundle.ContMDiffRiemannianMetric I n E (fun x : M => TangentSpace I x)

theorem smoothMetric_inner_symm
    (g : SmoothMetric (I := I) (M := M) (E := E))
    (x : M) (v w : TangentSpace I x) :
    g.inner x v w = g.inner x w v := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change inner ℝ v w = inner ℝ w v
  exact (real_inner_comm v w).symm

theorem smoothMetric_inner_pos
    (g : SmoothMetric (I := I) (M := M) (E := E))
    (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    0 < g.inner x v v := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change 0 < inner ℝ v v
  exact real_inner_self_pos.2 hv

theorem contMDiffMetric_to_isContMDiffRiemannianBundle
    (g : ContMDiffMetric (I := I) (M := M) (E := E) n) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle I n E (fun x : M => TangentSpace I x) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  exact ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩

theorem smoothMetric_to_isContMDiffRiemannianBundle
    (g : SmoothMetric (I := I) (M := M) (E := E)) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    IsContMDiffRiemannianBundle I (⊤ : WithTop ℕ∞) E (fun x : M => TangentSpace I x) :=
  contMDiffMetric_to_isContMDiffRiemannianBundle (I := I) (M := M) (E := E) (n := ⊤) g

theorem smoothMetric_inner_nonneg
    (g : SmoothMetric (I := I) (M := M) (E := E))
    (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change 0 ≤ inner ℝ v v
  exact real_inner_self_nonneg

theorem smoothMetric_inner_zero_iff
    (g : SmoothMetric (I := I) (M := M) (E := E))
    (x : M) (v : TangentSpace I x) :
    g.inner x v v = 0 ↔ v = 0 := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  change inner ℝ v v = 0 ↔ v = 0
  simp

end

end Metric
