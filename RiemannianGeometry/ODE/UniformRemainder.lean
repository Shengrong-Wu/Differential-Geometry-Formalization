import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Uniform first-order remainder estimate

The main analytic bottleneck: for a `C¹` map on an open set, the first-order Taylor remainder
is uniformly controlled on compact subsets. -/

namespace ODE.Autonomous

open Set Metric Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Uniform remainder theorem -/

set_option maxHeartbeats 800000 in
/-- **Uniform first-order remainder estimate.** If `f` is `C¹` on an open set `U` and `K ⊆ U` is
compact, then for every `ε > 0` there exists `ρ > 0` such that for all `x ∈ K` and `y` with
`‖y - x‖ ≤ ρ`, the first-order Taylor remainder is bounded:
```
‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖
```

**Proof strategy**: thicken `K` inside `U`, use uniform continuity of `fderiv ℝ f` on the
compact thickening, then apply the mean-value remainder estimate on convex balls. -/
theorem uniform_firstOrder_remainder [FiniteDimensional ℝ E]
    {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ x ∈ K, ∀ y : E, ‖y - x‖ ≤ ρ →
      ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖ := by
  -- Step 1: Thicken K inside U
  obtain ⟨δ₀, hδ₀, hthick⟩ := hK.exists_cthickening_subset_open hU hKU
  -- Step 2: f is differentiable on U and fderiv ℝ f is continuous on U
  have hfD : DifferentiableOn ℝ f U := hf.differentiableOn one_ne_zero
  have hfDcont : ContinuousOn (fderiv ℝ f) U :=
    hf.continuousOn_fderiv_of_isOpen hU le_rfl
  -- Step 3: cthickening δ₀ K is compact
  have hcompact : IsCompact (cthickening δ₀ K) := hK.cthickening
  -- Step 4: fderiv ℝ f is uniformly continuous on the compact cthickening
  have hfDuc : UniformContinuousOn (fderiv ℝ f) (cthickening δ₀ K) :=
    hcompact.uniformContinuousOn_of_continuous (hfDcont.mono hthick)
  -- Step 5: Get ρ₁ from uniform continuity of fderiv
  rw [Metric.uniformContinuousOn_iff_le] at hfDuc
  obtain ⟨ρ₁, hρ₁, huc⟩ := hfDuc ε hε
  -- Step 6: Set ρ = min ρ₁ δ₀
  refine ⟨min ρ₁ δ₀, lt_min hρ₁ hδ₀, fun x hxK y hy => ?_⟩
  -- Step 7: Key geometric facts
  have hyρ₁ : ‖y - x‖ ≤ ρ₁ := hy.trans (min_le_left _ _)
  have hyδ₀ : ‖y - x‖ ≤ δ₀ := hy.trans (min_le_right _ _)
  have hxK' : x ∈ K := hxK
  -- closedBall x δ₀ ⊆ cthickening δ₀ K
  have hball_thick : closedBall x δ₀ ⊆ cthickening δ₀ K :=
    closedBall_subset_cthickening hxK' δ₀
  -- closedBall x δ₀ ⊆ U
  have hball_U : closedBall x δ₀ ⊆ U := hball_thick.trans hthick
  -- x and y are in closedBall x δ₀
  have hxball : x ∈ closedBall x δ₀ := mem_closedBall_self hδ₀.le
  have hyball : y ∈ closedBall x δ₀ := by
    rw [mem_closedBall, dist_eq_norm]; exact hyδ₀
  -- x ∈ cthickening
  have hx_thick : x ∈ cthickening δ₀ K := hball_thick hxball
  -- Step 8: Apply MVT to the remainder
  -- We use the MVT with HasFDerivWithinAt for each z in the ball
  -- The remainder h(z) = f(z) - f(x) - (fderiv ℝ f x)(z - x) has h(x) = 0
  -- and HasFDerivWithinAt h (fderiv ℝ f z - fderiv ℝ f x) (closedBall x δ₀) z
  -- with ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε for z in closedBall x (min ρ₁ δ₀)
  -- By MVT: ‖h(y) - h(x)‖ ≤ ε * ‖y - x‖
  -- Build HasFDerivWithinAt for the remainder
  have hfx_val : f x - f x - (fderiv ℝ f x) (x - x) = 0 := by simp
  -- For each z in the ball, f has fderiv within the ball
  have hDball : ∀ z ∈ closedBall x δ₀, HasFDerivWithinAt f (fderiv ℝ f z) (closedBall x δ₀) z := by
    intro z hz
    have hzU := hball_U hz
    have hfz : DifferentiableAt ℝ f z := (hfD z hzU).differentiableAt (hU.mem_nhds hzU)
    exact hfz.hasFDerivAt.hasFDerivWithinAt
  -- The affine map z ↦ f(x) + (fderiv ℝ f x)(z - x) has fderiv = fderiv ℝ f x
  -- So the remainder h has HasFDerivWithinAt with derivative (fderiv ℝ f z - fderiv ℝ f x)
  have hrem_deriv : ∀ z ∈ closedBall x δ₀,
      HasFDerivWithinAt (fun z => f z - f x - (fderiv ℝ f x) (z - x))
        (fderiv ℝ f z - fderiv ℝ f x) (closedBall x δ₀) z := by
    intro z hz
    have h1 := hDball z hz
    -- fderiv of the constant f(x)
    have h2 : HasFDerivWithinAt (fun _ : E => f x) (0 : E →L[ℝ] F) (closedBall x δ₀) z :=
      hasFDerivWithinAt_const (f x) z _
    -- fderiv of (fderiv ℝ f x)(z - x) = (fderiv ℝ f x) as a CLM
    have h3 : HasFDerivWithinAt (fun z => (fderiv ℝ f x) (z - x))
        (fderiv ℝ f x) (closedBall x δ₀) z := by
      have heq : (fun z => (fderiv ℝ f x) (z - x)) =
          fun z => (fderiv ℝ f x) z - (fderiv ℝ f x) x := by
        ext z; simp [map_sub]
      rw [heq]
      have := (fderiv ℝ f x).hasFDerivWithinAt (s := closedBall x δ₀).sub
        (hasFDerivWithinAt_const ((fderiv ℝ f x) x) z (closedBall x δ₀))
      rwa [sub_zero] at this
    -- Combine: f - const - linear
    convert (h1.sub h2).sub h3 using 1
    ext v; simp
  -- Bound: for z in closedBall x δ₀, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε
  -- We need z also in closedBall x ρ₁ for the uniform continuity bound
  -- But ρ = min ρ₁ δ₀, so closedBall x ρ ⊆ closedBall x ρ₁ ∩ closedBall x δ₀
  -- We work on closedBall x ρ where ρ = min ρ₁ δ₀
  set ρ := min ρ₁ δ₀ with hρ_def
  -- Actually, y ∈ closedBall x ρ, but we applied MVT on closedBall x δ₀
  -- We need the bound on closedBall x ρ. Let's apply MVT on closedBall x ρ instead.
  have hρ_pos : 0 < ρ := lt_min hρ₁ hδ₀
  have hball_ρ_sub : closedBall x ρ ⊆ closedBall x δ₀ :=
    closedBall_subset_closedBall (min_le_right _ _)
  have hyball_ρ : y ∈ closedBall x ρ := by
    rw [mem_closedBall, dist_eq_norm]; exact hy
  have hxball_ρ : x ∈ closedBall x ρ := mem_closedBall_self hρ_pos.le
  -- HasFDerivWithinAt on closedBall x ρ (by mono)
  have hrem_deriv_ρ : ∀ z ∈ closedBall x ρ,
      HasFDerivWithinAt (fun z => f z - f x - (fderiv ℝ f x) (z - x))
        (fderiv ℝ f z - fderiv ℝ f x) (closedBall x ρ) z := by
    intro z hz
    exact (hrem_deriv z (hball_ρ_sub hz)).mono hball_ρ_sub
  -- Bound on the derivative norm on closedBall x ρ
  have hbound : ∀ z ∈ closedBall x ρ, ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ ε := by
    intro z hz
    have hz_thick : z ∈ cthickening δ₀ K := hball_thick (hball_ρ_sub hz)
    have hz_dist : dist x z ≤ ρ₁ := by
      rw [dist_comm]; exact (mem_closedBall.mp hz).trans (min_le_left _ _)
    -- ‖fderiv ℝ f z - fderiv ℝ f x‖ = dist (fderiv ℝ f z) (fderiv ℝ f x)
    rw [← dist_eq_norm]
    rw [dist_comm]
    exact huc x hx_thick z hz_thick hz_dist
  -- Apply MVT
  have hconv : Convex ℝ (closedBall x ρ) := convex_closedBall x ρ
  -- MVT: ‖h(y) - h(x)‖ ≤ ε * ‖y - x‖
  have hmvt := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hrem_deriv_ρ hbound hxball_ρ hyball_ρ
  -- h(x) = f x - f x - (fderiv ℝ f x)(x - x) = 0
  simp only [sub_self, map_zero, sub_zero] at hmvt
  exact hmvt

/-- Variant: if `f` is globally `C¹`, the compact-thickening bookkeeping simplifies. -/
theorem uniform_firstOrder_remainder_of_contDiff [FiniteDimensional ℝ E]
    {f : E → F}
    (hf : ContDiff ℝ 1 f)
    {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ x ∈ K, ∀ y : E, ‖y - x‖ ≤ ρ →
      ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖ :=
  uniform_firstOrder_remainder isOpen_univ hf.contDiffOn hK (subset_univ _) hε

/-- **Tube remainder estimate.** For a `C¹` vector field and a continuous reference trajectory
`γ : [a,b] → E`, the first-order remainder is uniformly small near the trajectory. -/
theorem tube_remainder_estimate [FiniteDimensional ℝ E]
    {f : E → E}
    (hf : ContDiff ℝ 1 f)
    {γ : ℝ → E} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ∀ t ∈ Icc a b, ∀ y : E, ‖y - γ t‖ ≤ ρ →
      ‖f y - f (γ t) - (fderiv ℝ f (γ t)) (y - γ t)‖ ≤ ε * ‖y - γ t‖ := by
  have hcomp : IsCompact (γ '' Icc a b) := (isCompact_Icc).image_of_continuousOn hγ
  obtain ⟨ρ, hρ, hrem⟩ := uniform_firstOrder_remainder_of_contDiff hf hcomp hε
  exact ⟨ρ, hρ, fun t ht y hy => hrem (γ t) ⟨t, ht, rfl⟩ y hy⟩

end ODE.Autonomous
