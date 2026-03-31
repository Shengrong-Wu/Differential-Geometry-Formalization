import Mathlib.Analysis.ConstantSpeed
import Mathlib.Topology.ContinuousMap.Interval
import HopfRinow.LengthCompactness
import HopfRinow.DistanceRealizer

/-! Design-stage skeleton for the metric-length infrastructure used by the corrected
complete→proper and complete→minimizers arguments. -/

namespace HopfRinow

open Filter
open scoped Topology ENNReal

universe u

/-!
Planned contents:

- almost-minimizing unit-interval curves,
- reparametrization to controlled Lipschitz constants,
- prefix-length continuity and intermediate-point lemmas,
- limit-of-Lipschitz-constants lemmas for compactness arguments.

Target theorem inventory:

```lean
theorem exists_almostMinimizing_curve
theorem exists_reparam_lipschitz_of_length_le
theorem exists_point_at_prefixLength

theorem endpoints_of_uniformLimit
theorem lipschitz_limit_of_uniformLimit
theorem endpoint_lipschitz_eq_distance_implies_distanceRealizer
```
-/

noncomputable def unitIntervalZero : UnitInterval := ⟨0, by simp⟩

noncomputable def unitIntervalOne : UnitInterval := ⟨1, by simp⟩

/-- Two unit-interval curves have the same endpoints if they agree at `0` and `1`. -/
def sameEndpoints
    {X : Type u} [TopologicalSpace X]
    (γ₁ γ₂ : UnitIntervalCurve X) : Prop :=
  γ₁ unitIntervalZero = γ₂ unitIntervalZero ∧
    γ₁ unitIntervalOne = γ₂ unitIntervalOne

namespace MetricPathLength

section Basic

variable {X : Type u} [PseudoMetricSpace X]

/-- Extend a unit-interval curve to all of `ℝ` by clamping the parameter to `[0,1]`. -/
noncomputable def curveLift (γ : UnitIntervalCurve X) : C(ℝ, X) := by
  letI : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩
  exact ContinuousMap.IccExtendCM (a := (0 : ℝ)) (b := (1 : ℝ)) γ

@[simp]
theorem curveLift_apply (γ : UnitIntervalCurve X) (t : UnitInterval) :
    curveLift γ t = γ t := by
  letI : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩
  simpa [curveLift] using
    (ContinuousMap.IccExtendCM_of_mem (f := γ) (x := (t : ℝ)) t.2)

@[simp]
theorem curveLift_zero (γ : UnitIntervalCurve X) :
    curveLift γ 0 = γ unitIntervalZero := by
  simpa [unitIntervalZero] using curveLift_apply γ unitIntervalZero

@[simp]
theorem curveLift_one (γ : UnitIntervalCurve X) :
    curveLift γ 1 = γ unitIntervalOne := by
  simpa [unitIntervalOne] using curveLift_apply γ unitIntervalOne

/-- Extended variation of a unit-interval curve on `[0,1]`. -/
noncomputable def lengthENN (γ : UnitIntervalCurve X) : ℝ≥0∞ :=
  eVariationOn (curveLift γ) (Set.Icc (0 : ℝ) 1)

/-- A unit-interval curve has finite metric length when its total variation on `[0,1]` is finite.
This is the hypothesis under which the real-valued `length` API is semantically meaningful. -/
def HasFiniteLength (γ : UnitIntervalCurve X) : Prop :=
  BoundedVariationOn (curveLift γ) (Set.Icc (0 : ℝ) 1)

/-- `HasFiniteLength` is exactly finiteness of the extended variation on `[0,1]`. -/
theorem hasFiniteLength_iff (γ : UnitIntervalCurve X) :
    HasFiniteLength γ ↔ lengthENN γ ≠ ∞ := by
  rfl

/-- Real-valued metric length extracted from `lengthENN`. This is only meaningful when the
variation on `[0,1]` is finite, which will later be ensured by explicit hypotheses. -/
noncomputable def length (γ : UnitIntervalCurve X) : ℝ :=
  (lengthENN γ).toReal

theorem length_nonneg (γ : UnitIntervalCurve X) :
    0 ≤ length γ := by
  simp [length]

/-- Prefix length up to a parameter `t ∈ [0,1]`. As with `length`, its geometric meaning is used
only under finite-variation hypotheses. -/
noncomputable def prefixLength (γ : UnitIntervalCurve X) (t : UnitInterval) : ℝ :=
  variationOnFromTo (curveLift γ) (Set.Icc (0 : ℝ) 1) (0 : ℝ) t

@[simp]
theorem prefixLength_zero (γ : UnitIntervalCurve X) :
    prefixLength γ unitIntervalZero = 0 := by
  simpa [prefixLength, unitIntervalZero] using
    (variationOnFromTo.self (f := curveLift γ) (s := Set.Icc (0 : ℝ) 1) (a := (0 : ℝ)))

@[simp]
theorem prefixLength_one (γ : UnitIntervalCurve X) :
    prefixLength γ unitIntervalOne = length γ := by
  simp [prefixLength, length, lengthENN, unitIntervalOne, variationOnFromTo.eq_of_le, zero_le_one]

theorem prefixLength_nonneg (γ : UnitIntervalCurve X) (t : UnitInterval) :
    0 ≤ prefixLength γ t := by
  simpa [prefixLength] using
    (variationOnFromTo.nonneg_of_le (f := curveLift γ) (s := Set.Icc (0 : ℝ) 1) t.2.1)

theorem locallyBoundedVariationOn_curveLift_of_hasFiniteLength
    {γ : UnitIntervalCurve X} (hγ : HasFiniteLength γ) :
    LocallyBoundedVariationOn (curveLift γ) (Set.Icc (0 : ℝ) 1) :=
  hγ.locallyBoundedVariationOn

theorem eVariationOn_id_Icc {a b : ℝ} (hab : a ≤ b) :
    eVariationOn (fun t : ℝ => t) (Set.Icc a b) = ENNReal.ofReal (b - a) := by
  refine le_antisymm ?_ ?_
  · simpa using MonotoneOn.eVariationOn_le
      (f := fun t : ℝ => t) (s := Set.Icc a b) (hf := monotone_id.monotoneOn (s := Set.Icc a b))
      (a := a) (b := b) (by simp [hab]) (by simp [hab])
  · have hdist : ENNReal.ofReal (b - a) = edist a b := by
      rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    rw [hdist]
    exact eVariationOn.edist_le (fun t : ℝ => t) (by simp [hab]) (by simp [hab])

theorem eVariationOn_Icc_le_of_lipschitz
    {f : ℝ → X} {L : NNReal} {a b : ℝ}
    (hf : LipschitzWith L f) (hab : a ≤ b) :
    eVariationOn f (Set.Icc a b) ≤ (L : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  calc
    eVariationOn f (Set.Icc a b) = eVariationOn (f ∘ fun t : ℝ => t) (Set.Icc a b) := by rfl
    _ ≤ (L : ℝ≥0∞) * eVariationOn (fun t : ℝ => t) (Set.Icc a b) := by
      simpa using
        LipschitzOnWith.comp_eVariationOn_le (f := f) (C := L) hf.lipschitzOnWith
          (g := fun t : ℝ => t) (s := Set.Icc a b) (Set.mapsTo_univ _ _)
    _ = (L : ℝ≥0∞) * ENNReal.ofReal (b - a) := by rw [eVariationOn_id_Icc hab]

theorem curveLift_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) :
    LipschitzWith L (curveLift γ) := by
  letI : Fact ((0 : ℝ) ≤ 1) := ⟨zero_le_one⟩
  simpa [curveLift] using
    hlip.comp (LipschitzWith.projIcc (a := (0 : ℝ)) (b := (1 : ℝ)) zero_le_one)

theorem lengthENN_le_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) :
    lengthENN γ ≤ (L : ℝ≥0∞) := by
  have h :=
    eVariationOn_Icc_le_of_lipschitz (f := curveLift γ) (L := L)
      (curveLift_lipschitz hlip) zero_le_one
  simpa [lengthENN] using h

theorem hasFiniteLength_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) :
    HasFiniteLength γ := by
  exact ne_top_of_le_ne_top (by simp) (lengthENN_le_of_lipschitz hlip)

theorem length_le_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) :
    length γ ≤ (L : ℝ) := by
  have hle : lengthENN γ ≤ (L : ℝ≥0∞) := lengthENN_le_of_lipschitz hlip
  simpa [length] using ENNReal.toReal_mono (show (L : ℝ≥0∞) ≠ ∞ by simp) hle

theorem monotone_prefixLength_of_hasFiniteLength
    {γ : UnitIntervalCurve X}
    (hγ : HasFiniteLength γ) :
    Monotone (prefixLength γ) := by
  have hmono :=
    variationOnFromTo.monotoneOn
      (locallyBoundedVariationOn_curveLift_of_hasFiniteLength hγ)
      (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  intro s t hst
  simpa [prefixLength] using hmono s.2 t.2 hst

theorem prefixLength_le_length_of_hasFiniteLength
    {γ : UnitIntervalCurve X}
    (hγ : HasFiniteLength γ) (t : UnitInterval) :
    prefixLength γ t ≤ length γ := by
  have hmono := monotone_prefixLength_of_hasFiniteLength hγ
  have hle : prefixLength γ t ≤ prefixLength γ unitIntervalOne := hmono t.2.2
  simpa [prefixLength, length, lengthENN, variationOnFromTo.eq_of_le, zero_le_one,
    unitIntervalOne] using
      hle

theorem prefixLength_le_length_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) (t : UnitInterval) :
    prefixLength γ t ≤ length γ := by
  exact prefixLength_le_length_of_hasFiniteLength (hasFiniteLength_of_lipschitz hlip) t

theorem curveLift_variationOnFromTo_le_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X} {a b : ℝ}
    (hlip : LipschitzWith L γ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hab : a ≤ b) :
    variationOnFromTo (curveLift γ) (Set.Icc (0 : ℝ) 1) a b ≤ (L : ℝ) * (b - a) := by
  have hset : Set.Icc (0 : ℝ) 1 ∩ Set.Icc a b = Set.Icc a b := by
    ext x
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨⟨ha.1.trans hx.1, hx.2.trans hb.2⟩, hx⟩
  have hbound :
      eVariationOn (curveLift γ) (Set.Icc (0 : ℝ) 1 ∩ Set.Icc a b) ≤
        (L : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
    simpa [hset] using
      eVariationOn_Icc_le_of_lipschitz (f := curveLift γ) (L := L)
        (curveLift_lipschitz hlip) hab
  rw [variationOnFromTo.eq_of_le _ _ hab]
  refine (ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hbound).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  simp

theorem monotone_prefixLength_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) :
    Monotone (prefixLength γ) := by
  exact monotone_prefixLength_of_hasFiniteLength (hasFiniteLength_of_lipschitz hlip)

theorem prefixLength_lipschitz_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) :
    LipschitzWith L (prefixLength γ) := by
  refine LipschitzWith.of_le_add_mul L ?_
  intro s t
  rcases le_total s t with hst | hts
  · exact le_trans (monotone_prefixLength_of_lipschitz hlip hst)
      (le_add_of_nonneg_right (by positivity))
  · have hloc :
        LocallyBoundedVariationOn (curveLift γ) (Set.Icc (0 : ℝ) 1) :=
      (curveLift_lipschitz hlip).locallyBoundedVariationOn _
    have hadd :
        prefixLength γ t +
            variationOnFromTo (curveLift γ) (Set.Icc (0 : ℝ) 1) t s =
          prefixLength γ s := by
      simpa [prefixLength] using
        (variationOnFromTo.add hloc (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) t.2 s.2)
    have hvar :
        variationOnFromTo (curveLift γ) (Set.Icc (0 : ℝ) 1) t s ≤
          (L : ℝ) * dist s t := by
      have hvar' :=
        curveLift_variationOnFromTo_le_of_lipschitz hlip t.2 s.2 hts
      have hdist : dist s t = (s : ℝ) - t := by
        rw [Subtype.dist_eq, Real.dist_eq]
        rw [abs_of_nonneg (show 0 ≤ (s : ℝ) - (t : ℝ) from
          sub_nonneg.mpr (show (t : ℝ) ≤ (s : ℝ) from hts))]
      calc
        variationOnFromTo (curveLift γ) (Set.Icc (0 : ℝ) 1) t s ≤
            (L : ℝ) * ((s : ℝ) - t) := hvar'
        _ = (L : ℝ) * dist s t := by rw [hdist]
    linarith

theorem exists_point_at_prefixLength_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) {a : ℝ}
    (ha0 : 0 ≤ a) (haL : a ≤ length γ) :
    ∃ t : UnitInterval, prefixLength γ t = a := by
  have hcont : Continuous (prefixLength γ) :=
    (prefixLength_lipschitz_of_lipschitz hlip).continuous
  have hsurj :
      Set.SurjOn (prefixLength γ) (Set.univ : Set UnitInterval)
        (Set.Icc (prefixLength γ unitIntervalZero) (prefixLength γ unitIntervalOne)) :=
    hcont.continuousOn.surjOn_Icc (s := (Set.univ : Set UnitInterval))
      (a := unitIntervalZero) (b := unitIntervalOne) (by simp) (by simp)
  have ha_mem : a ∈ Set.Icc (prefixLength γ unitIntervalZero) (prefixLength γ unitIntervalOne) := by
    simpa using ⟨ha0, haL⟩
  rcases hsurj ha_mem with ⟨t, -, ht⟩
  exact ⟨t, ht⟩

theorem surjOn_prefixLength_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) :
    Set.SurjOn (prefixLength γ) (Set.univ : Set UnitInterval) (Set.Icc 0 (length γ)) := by
  intro a ha
  rcases exists_point_at_prefixLength_of_lipschitz hlip ha.1 ha.2 with ⟨t, ht⟩
  exact ⟨t, by simp, ht⟩

end Basic

section Reparam

variable {X : Type u} [MetricSpace X]

private theorem lipschitzOnWith_of_hasConstantSpeedOnWith
    {f : ℝ → X} {s : Set ℝ} {l : NNReal}
    (h : HasConstantSpeedOnWith f s l) :
    LipschitzOnWith l f s := by
  rw [hasConstantSpeedOnWith_iff_ordered] at h
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · have hedist :
        edist (f x) (f y) ≤ ENNReal.ofReal ((l : ℝ) * (y - x)) := by
      calc
        edist (f x) (f y) ≤ eVariationOn f (s ∩ Set.Icc x y) := by
          exact eVariationOn.edist_le f (by simp [hx, hy, hxy]) (by simp [hx, hy, hxy])
        _ = ENNReal.ofReal ((l : ℝ) * (y - x)) := h hx hy hxy
    have hdist : dist (f x) (f y) ≤ (l : ℝ) * (y - x) := by
      simpa [edist_dist, ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] using
        ENNReal.toReal_mono (show ENNReal.ofReal ((l : ℝ) * (y - x)) ≠ ∞ from
          ENNReal.ofReal_ne_top) hedist
    simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)] using hdist
  · have hedist :
        edist (f y) (f x) ≤ ENNReal.ofReal ((l : ℝ) * (x - y)) := by
      calc
        edist (f y) (f x) ≤ eVariationOn f (s ∩ Set.Icc y x) := by
          exact eVariationOn.edist_le f (by simp [hx, hy, hyx]) (by simp [hx, hy, hyx])
        _ = ENNReal.ofReal ((l : ℝ) * (x - y)) := h hy hx hyx
    have hdist : dist (f x) (f y) ≤ (l : ℝ) * (x - y) := by
      simpa [dist_comm, edist_dist, ENNReal.toReal_ofReal (sub_nonneg.mpr hyx)] using
        ENNReal.toReal_mono (show ENNReal.ofReal ((l : ℝ) * (x - y)) ≠ ∞ from
          ENNReal.ofReal_ne_top) hedist
    simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)] using hdist

/-- Honest current reparametrization package: a curve that is already `L`-Lipschitz can be
reparametrized into another unit-interval curve with the same endpoints and the same global
Lipschitz bound. This is the boundary-safe owner theorem available before the full
length-only reparametrization theorem is proved. -/
theorem exists_reparam_lipschitz_of_lipschitz
    {L : NNReal} {γ : UnitIntervalCurve X}
    (hlip : LipschitzWith L γ) :
    ∃ γ' : UnitIntervalCurve X, HopfRinow.sameEndpoints γ γ' ∧ LipschitzWith L γ' := by
  let η : ℝ → X :=
    naturalParameterization (curveLift γ) (Set.Icc (0 : ℝ) 1) (0 : ℝ)
  have hγfin : HasFiniteLength γ := hasFiniteLength_of_lipschitz hlip
  have hunit :
      HasUnitSpeedOn η (Set.range (prefixLength γ)) := by
    have hraw :
        HasUnitSpeedOn η
          (variationOnFromTo (curveLift γ) (Set.Icc (0 : ℝ) 1) (0 : ℝ) '' Set.Icc (0 : ℝ) 1) :=
      has_unit_speed_naturalParameterization (f := curveLift γ)
        (s := Set.Icc (0 : ℝ) 1)
        (hf := locallyBoundedVariationOn_curveLift_of_hasFiniteLength hγfin)
        (a := (0 : ℝ)) (by simp)
    have hrange :
        variationOnFromTo (curveLift γ) (Set.Icc (0 : ℝ) 1) (0 : ℝ) '' Set.Icc (0 : ℝ) 1 =
          Set.range (prefixLength γ) := by
      ext a
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, by simp [prefixLength]⟩
      · rintro ⟨t, rfl⟩
        exact ⟨(t : ℝ), t.2, by simp [prefixLength]⟩
    simpa [η, hrange]
      using hraw
  have hηlip :
      LipschitzOnWith 1 η (Set.range (prefixLength γ)) :=
    lipschitzOnWith_of_hasConstantSpeedOnWith hunit
  let σ : UnitInterval → X := fun t => η (length γ * (t : ℝ))
  have hσlen : LipschitzWith ⟨length γ, length_nonneg γ⟩ σ := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    have hs_Icc : length γ * (s : ℝ) ∈ Set.Icc 0 (length γ) := by
      constructor
      · nlinarith [length_nonneg γ, s.2.1]
      · nlinarith [length_nonneg γ, s.2.2]
    have ht_Icc : length γ * (t : ℝ) ∈ Set.Icc 0 (length γ) := by
      constructor
      · nlinarith [length_nonneg γ, t.2.1]
      · nlinarith [length_nonneg γ, t.2.2]
    have hs_mem : length γ * (s : ℝ) ∈ Set.range (prefixLength γ) := by
      rcases surjOn_prefixLength_of_lipschitz hlip hs_Icc with ⟨u, -, hu⟩
      exact ⟨u, hu⟩
    have ht_mem : length γ * (t : ℝ) ∈ Set.range (prefixLength γ) := by
      rcases surjOn_prefixLength_of_lipschitz hlip ht_Icc with ⟨u, -, hu⟩
      exact ⟨u, hu⟩
    have hdist :=
      hηlip.dist_le_mul (length γ * (s : ℝ)) hs_mem (length γ * (t : ℝ)) ht_mem
    calc
      dist (σ s) (σ t) ≤ dist (length γ * (s : ℝ)) (length γ * (t : ℝ)) := by
        simpa [σ, one_mul] using hdist
      _ = length γ * dist s t := by
        rw [Subtype.dist_eq, Real.dist_eq, Real.dist_eq, ← mul_sub_left_distrib, abs_mul,
          abs_of_nonneg (length_nonneg γ), mul_comm]
      _ = (⟨length γ, length_nonneg γ⟩ : NNReal) * dist s t := by simp
  refine ⟨⟨σ, hσlen.continuous⟩, ?_, ?_⟩
  · constructor
    · have h0η : η 0 = γ unitIntervalZero := by
        simpa [η, curveLift_zero, variationOnFromTo.self] using
          (edist_naturalParameterization_eq_zero
            (f := curveLift γ) (s := Set.Icc (0 : ℝ) 1)
            (hf := locallyBoundedVariationOn_curveLift_of_hasFiniteLength hγfin)
            (a := (0 : ℝ)) (as := by simp) (b := (0 : ℝ)) (by simp))
      have h0σ : σ unitIntervalZero = γ unitIntervalZero := by
        simpa [σ, unitIntervalZero] using h0η
      exact h0σ.symm
    · have h1η : η (length γ) = γ unitIntervalOne := by
        simpa [η, curveLift_one, length, lengthENN, variationOnFromTo.eq_of_le, zero_le_one] using
          (edist_naturalParameterization_eq_zero
            (f := curveLift γ) (s := Set.Icc (0 : ℝ) 1)
            (hf := locallyBoundedVariationOn_curveLift_of_hasFiniteLength hγfin)
            (a := (0 : ℝ)) (as := by simp) (b := (1 : ℝ)) (by simp))
      have h1σ : σ unitIntervalOne = γ unitIntervalOne := by
        simpa [σ, unitIntervalOne] using h1η
      exact h1σ.symm
  · exact hσlen.weaken (show (⟨length γ, length_nonneg γ⟩ : NNReal) ≤ L by
      exact_mod_cast length_le_of_lipschitz hlip)

end Reparam

end MetricPathLength

theorem exists_point_at_prefixLength
    {X : Type u} [PseudoMetricSpace X]
    {L : NNReal} {γ : UnitIntervalCurve X} {a : ℝ}
    (hlip : LipschitzWith L γ)
    (ha0 : 0 ≤ a) (haL : a ≤ MetricPathLength.length γ) :
    ∃ t : UnitInterval, MetricPathLength.prefixLength γ t = a :=
  MetricPathLength.exists_point_at_prefixLength_of_lipschitz hlip ha0 haL

theorem endpoints_of_uniformLimit
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {X : Type u} [PseudoMetricSpace X] [T2Space X]
    {γn : ι → UnitIntervalCurve X} {γ : UnitIntervalCurve X} {p q : X}
    (hconv : Tendsto γn l (𝓝 γ))
    (h0 : ∀ᶠ n in l, γn n unitIntervalZero = p)
    (h1 : ∀ᶠ n in l, γn n unitIntervalOne = q) :
    γ unitIntervalZero = p ∧ γ unitIntervalOne = q := by
  have hzero :
      Tendsto (fun n => γn n unitIntervalZero) l (𝓝 (γ unitIntervalZero)) :=
    ((continuous_eval_const (F := UnitIntervalCurve X) unitIntervalZero).tendsto γ).comp hconv
  have hone :
      Tendsto (fun n => γn n unitIntervalOne) l (𝓝 (γ unitIntervalOne)) :=
    ((continuous_eval_const (F := UnitIntervalCurve X) unitIntervalOne).tendsto γ).comp hconv
  refine ⟨?_, ?_⟩
  · exact tendsto_nhds_unique_of_eventuallyEq hzero tendsto_const_nhds
      (show (fun n => γn n unitIntervalZero) =ᶠ[l] fun _ => p from h0)
  · exact tendsto_nhds_unique_of_eventuallyEq hone tendsto_const_nhds
      (show (fun n => γn n unitIntervalOne) =ᶠ[l] fun _ => q from h1)

private theorem isClosed_uniformLipschitzCurve
    (X : Type u) [PseudoMetricSpace X] (L : NNReal) :
    IsClosed {γ : UnitIntervalCurve X | LipschitzWith L γ} := by
  change IsClosed
    ((ContinuousMap.isometryEquivBoundedOfCompact UnitInterval X) ⁻¹'
      {γ : BoundedContinuousFunction UnitInterval X | LipschitzWith L γ})
  simpa using
    ((isClosed_setOf_lipschitzWith (α := UnitInterval) (β := X) (K := L)).preimage
      BoundedContinuousFunction.uniformContinuous_coe.continuous).preimage
      (ContinuousMap.isometryEquivBoundedOfCompact UnitInterval X).continuous

theorem lipschitz_limit_of_uniformLimit
    {ι : Type*} {l : Filter ι} [Filter.NeBot l]
    {X : Type u} [PseudoMetricSpace X]
    {γn : ι → UnitIntervalCurve X} {γ : UnitIntervalCurve X} {L : NNReal}
    (hconv : Tendsto γn l (𝓝 γ))
    (hlip : ∀ᶠ n in l, LipschitzWith L (γn n)) :
    LipschitzWith L γ := by
  exact (isClosed_uniformLipschitzCurve X L).mem_of_tendsto hconv hlip

theorem endpoint_lipschitz_eq_distance_implies_distanceRealizer
    {X : Type u} [PseudoMetricSpace X]
    {p q : X} {γ : ℝ → X}
    (h0 : γ 0 = p) (h1 : γ 1 = q)
    (hlip : LipschitzWith ⟨dist p q, dist_nonneg⟩ γ) :
    IsDistanceRealizerBetween X p q γ := by
  refine ⟨h0, h1, ?_⟩
  intro t ht
  have hp_le : dist p (γ t) ≤ t * dist p q := by
    calc
      dist p (γ t) = dist (γ 0) (γ t) := by rw [h0]
      _ ≤ dist p q * dist (0 : ℝ) t := by
        simpa [h0] using hlip.dist_le_mul 0 t
      _ = dist p q * t := by
        rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht.1]
      _ = t * dist p q := by ring
  have hq_le : dist (γ t) q ≤ (1 - t) * dist p q := by
    calc
      dist (γ t) q = dist (γ t) (γ 1) := by rw [h1]
      _ ≤ dist p q * dist t 1 := by
        simpa [h1] using hlip.dist_le_mul t 1
      _ = dist p q * (1 - t) := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
        ring
      _ = (1 - t) * dist p q := by ring
  have htriangle : dist p q ≤ dist p (γ t) + dist (γ t) q := dist_triangle _ _ _
  have hsum_le : dist p (γ t) + dist (γ t) q ≤ dist p q := by
    calc
      dist p (γ t) + dist (γ t) q ≤ t * dist p q + (1 - t) * dist p q :=
        add_le_add hp_le hq_le
      _ = dist p q := by ring
  have hsum_eq : dist p (γ t) + dist (γ t) q = dist p q :=
    le_antisymm hsum_le htriangle
  have hp_eq : dist p (γ t) = t * dist p q := by
    nlinarith [hp_le, hq_le, hsum_eq]
  have hq_eq : dist (γ t) q = (1 - t) * dist p q := by
    nlinarith [hp_le, hq_le, hsum_eq]
  exact ⟨hp_eq, hq_eq⟩

theorem endpoint_lipschitz_eq_distance_implies_minimizingGeodesic
    {X : Type u} [PseudoMetricSpace X]
    {p q : X} {γ : ℝ → X}
    (h0 : γ 0 = p) (h1 : γ 1 = q)
    (hlip : LipschitzWith ⟨dist p q, dist_nonneg⟩ γ) :
    IsMinimizingGeodesicBetween X p q γ := by
  exact
    IsDistanceRealizerBetween.toIsMinimizingGeodesicBetween_of_lipschitz
      (endpoint_lipschitz_eq_distance_implies_distanceRealizer h0 h1 hlip) hlip

end HopfRinow
