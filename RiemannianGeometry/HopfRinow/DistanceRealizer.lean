import HopfRinow.MinExistence

/-! Design-stage skeleton for the purely metric distance-realizer layer.

This file is intended to stay independent of the local Riemannian geometry used later in the
Hopf–Rinow proof. It should own the first reusable metric lemmas for geodesic segments. -/

namespace HopfRinow

universe u

/-!
Planned contents:

- restriction lemmas for `IsGeodesicOnWithSpeed`,
- small endpoint / subsegment helper lemmas used by later minimizer arguments.

Target theorem inventory:

```lean
theorem IsGeodesicOnWithSpeed.mono

theorem IsGeodesicOnWithSpeed.restrict_Icc

theorem IsGeodesicLineWithSpeed.restrict_Icc

theorem IsMinimizingGeodesicBetween.toIsDistanceRealizerBetween

theorem IsDistanceRealizerBetween.isGeodesicOnWithSpeed_of_lipschitz

theorem IsDistanceRealizerBetween.toIsMinimizingGeodesicBetween_of_lipschitz

theorem isMinimizingGeodesicBetween_iff_distanceRealizer_and_geodesic
```
-/

theorem IsGeodesicOnWithSpeed.mono
    {M : Type u} [PseudoMetricSpace M]
    {γ : ℝ → M} {c : ℝ} {s t : Set ℝ}
    (hγ : IsGeodesicOnWithSpeed M γ c s)
    (hst : t ⊆ s) :
    IsGeodesicOnWithSpeed M γ c t := by
  rcases hγ with ⟨hc, hdist⟩
  exact ⟨hc, fun t₁ t₂ ht₁ ht₂ => hdist (hst ht₁) (hst ht₂)⟩

/-- Restrict a constant-speed geodesic segment to a smaller interval. -/
theorem IsGeodesicOnWithSpeed.restrict_Icc
    {M : Type u} [PseudoMetricSpace M]
    {γ : ℝ → M} {c a b a' b' : ℝ}
    (hγ : IsGeodesicOnWithSpeed M γ c (Set.Icc a b))
    (hsub : Set.Icc a' b' ⊆ Set.Icc a b) :
    IsGeodesicOnWithSpeed M γ c (Set.Icc a' b') :=
  hγ.mono hsub

/-- Restrict a global geodesic line to a compact subinterval. -/
theorem IsGeodesicLineWithSpeed.restrict_Icc
    {M : Type u} [PseudoMetricSpace M]
    {γ : ℝ → M} {c a b : ℝ}
    (hγ : IsGeodesicLineWithSpeed M γ c) :
    IsGeodesicOnWithSpeed M γ c (Set.Icc a b) := by
  exact hγ.mono (by intro t ht; simp)

/-- A minimizing geodesic determines the endpoint distance-realizer data. -/
theorem IsMinimizingGeodesicBetween.toIsDistanceRealizerBetween
    {M : Type u} [PseudoMetricSpace M]
    {p q : M} {γ : ℝ → M}
    (hγ : IsMinimizingGeodesicBetween M p q γ) :
    IsDistanceRealizerBetween M p q γ := by
  rcases hγ with ⟨hp, hq, hgeo⟩
  rcases hgeo with ⟨hc, hdist⟩
  refine ⟨hp, hq, ?_⟩
  intro t ht
  constructor
  · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have habs0 : |t - 0| = t := by
      simpa using (abs_of_nonneg ht.1 : |t| = t)
    calc
      dist p (γ t) = dist (γ t) p := dist_comm _ _
      _ = dist (γ t) (γ 0) := by rw [← hp]
      _ = dist p q * |t - 0| := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hdist ht h0
      _ = t * dist p q := by
        rw [habs0, mul_comm]
  · have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
    have habs1 : |t - 1| = 1 - t := by
      simpa [sub_eq_add_neg] using
        (abs_of_nonpos (sub_nonpos.mpr ht.2) : |t - 1| = -(t - 1))
    calc
      dist (γ t) q = dist (γ t) (γ 1) := by rw [← hq]
      _ = dist p q * |t - 1| := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hdist ht h1
      _ = (1 - t) * dist p q := by
        rw [habs1, mul_comm]

/-- A distance realizer records the exact distance to the source endpoint. -/
theorem IsDistanceRealizerBetween.dist_source
    {M : Type u} [PseudoMetricSpace M]
    {p q : M} {γ : ℝ → M}
    (hγ : IsDistanceRealizerBetween M p q γ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist p (γ t) = t * dist p q :=
  (hγ.2.2 t ht).1

/-- A distance realizer records the exact distance to the target endpoint. -/
theorem IsDistanceRealizerBetween.dist_target
    {M : Type u} [PseudoMetricSpace M]
    {p q : M} {γ : ℝ → M}
    (hγ : IsDistanceRealizerBetween M p q γ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (γ t) q = (1 - t) * dist p q :=
  (hγ.2.2 t ht).2

/-- A minimizing curve chosen from the existence package already realizes the endpoint distance. -/
theorem someMinimizingCurve_toIsDistanceRealizerBetween
    {M : Type u} [PseudoMetricSpace M]
    (h : MinimizingGeodesicsExist M) (p q : M) :
    IsDistanceRealizerBetween M p q (someMinimizingCurve h p q) :=
  (someMinimizingCurve_isMinimizingGeodesicBetween h p q).toIsDistanceRealizerBetween

/-- Endpoint distance-realizer data yields the expected lower bound on subsegment distances. -/
theorem IsDistanceRealizerBetween.lowerDistBound
    {M : Type u} [PseudoMetricSpace M]
    {p q : M} {γ : ℝ → M}
    (hγ : IsDistanceRealizerBetween M p q γ)
    {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (t - s) * dist p q ≤ dist (γ s) (γ t) := by
  have htriangle :
      dist p q ≤ dist p (γ s) + dist (γ s) (γ t) + dist (γ t) q := by
    nlinarith [dist_triangle p (γ s) q, dist_triangle (γ s) (γ t) q]
  have hineq :
      dist p q ≤ s * dist p q + dist (γ s) (γ t) + (1 - t) * dist p q := by
    simpa [hγ.dist_source hs, hγ.dist_target ht] using htriangle
  nlinarith

/-- A distance realizer becomes a constant-speed metric geodesic once the same speed-Lipschitz
bound is known. The extra Lipschitz hypothesis is necessary at the current `PseudoMetricSpace`
generality. -/
theorem IsDistanceRealizerBetween.isGeodesicOnWithSpeed_of_lipschitz
    {M : Type u} [PseudoMetricSpace M]
    {p q : M} {γ : ℝ → M}
    (hγ : IsDistanceRealizerBetween M p q γ)
    (hlip : LipschitzWith ⟨dist p q, dist_nonneg⟩ γ) :
    IsGeodesicOnWithSpeed M γ (dist p q) (Set.Icc (0 : ℝ) 1) := by
  refine ⟨dist_nonneg, ?_⟩
  intro s t hs ht
  rcases le_total s t with hst | hts
  · have hlower := hγ.lowerDistBound hs ht
    have hupper : dist (γ s) (γ t) ≤ (t - s) * dist p q := by
      simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), mul_comm, mul_left_comm,
        mul_assoc] using hlip.dist_le_mul s t
    have heq : dist (γ s) (γ t) = (t - s) * dist p q :=
      le_antisymm hupper hlower
    simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), mul_comm, mul_left_comm,
      mul_assoc] using heq
  · have hlower := hγ.lowerDistBound ht hs
    have hupper : dist (γ t) (γ s) ≤ (s - t) * dist p q := by
      simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hts), mul_comm, mul_left_comm,
        mul_assoc] using hlip.dist_le_mul t s
    have heq : dist (γ t) (γ s) = (s - t) * dist p q :=
      le_antisymm hupper hlower
    calc
      dist (γ s) (γ t) = dist (γ t) (γ s) := dist_comm _ _
      _ = (s - t) * dist p q := heq
      _ = dist p q * |s - t| := by
            rw [abs_of_nonneg (sub_nonneg.mpr hts)]
            ring

/-- The corrected metric conversion theorem: endpoint distance-realizer data plus the matching
Lipschitz bound yields a minimizing geodesic on `[0,1]`. -/
theorem IsDistanceRealizerBetween.toIsMinimizingGeodesicBetween_of_lipschitz
    {M : Type u} [PseudoMetricSpace M]
    {p q : M} {γ : ℝ → M}
    (hγ : IsDistanceRealizerBetween M p q γ)
    (hlip : LipschitzWith ⟨dist p q, dist_nonneg⟩ γ) :
    IsMinimizingGeodesicBetween M p q γ := by
  exact ⟨hγ.1, hγ.2.1, hγ.isGeodesicOnWithSpeed_of_lipschitz hlip⟩

/-- The minimizing-geodesic interface is exactly the endpoint distance-realizer data together
with the constant-speed geodesic package. -/
theorem isMinimizingGeodesicBetween_iff_distanceRealizer_and_geodesic
    {M : Type u} [PseudoMetricSpace M]
    {p q : M} {γ : ℝ → M} :
    IsMinimizingGeodesicBetween M p q γ ↔
      IsDistanceRealizerBetween M p q γ ∧
        IsGeodesicOnWithSpeed M γ (dist p q) (Set.Icc (0 : ℝ) 1) := by
  constructor
  · intro hγ
    exact ⟨IsMinimizingGeodesicBetween.toIsDistanceRealizerBetween hγ, hγ.2.2⟩
  · rintro ⟨hrealizer, hgeo⟩
    exact ⟨hrealizer.1, hrealizer.2.1, hgeo⟩

end HopfRinow
