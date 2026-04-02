import Geodesic
import Exponential.RadialGaussLemma
import HopfRinow.CompleteProper
import ODE.Core

/-! # Smooth geodesic completeness

This file defines smooth geodesic completeness (every coordinate geodesic extends for all time)
and provides the key ODE-based infrastructure for the smooth side of Hopf-Rinow.

## Architecture

The smooth geodesic completeness argument requires:
1. Local existence from Picard-Lindelöf (`geodesic_exists_on_symmetric_interval`).
2. The ODE continuation argument: speed bound → bounded state → compact containment →
   uniform extension time → finite iteration to reach any target time.

The owner layer in this file now factors step 2 through a uniform-step package and derives
completeness from that owner theorem. The remaining external content is the endpoint compact-
containment package needed to instantiate the uniform step.

Important boundary note: this compact-containment input does not follow from bare
`SmoothChristoffelField` or even bare `LocalRiemannianData`. Incomplete metrics on `ℝ^n` can have
finite-time geodesics whose endpoints escape to infinity, so the finite-horizon compact-shell
statement must be treated as an additional hypothesis (or proved under genuinely stronger global
coercivity/properness assumptions). -/

namespace HopfRinow

open Geodesic.Coordinate Set

variable {n : ℕ}

/-! ### Coordinate geodesics on intervals -/

/-- A coordinate geodesic through `z₀` at time `t₀`, defined on `[t₀, T]`. -/
structure CoordinateGeodesicOnInterval
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (z₀ : Geodesic.Coordinate.State n) (t₀ T : ℝ) where
  gamma : ℝ → Geodesic.Coordinate.State n
  hab : t₀ ≤ T
  initial : gamma t₀ = z₀
  isGeodesic : IsCoordinateGeodesicOn (christoffelFieldOfSmooth Gamma) gamma (Icc t₀ T)

/-- Smooth geodesic completeness at the coordinate level:
every initial state generates a geodesic defined on any time interval containing the initial time. -/
def HasCoordinateGeodesicCompleteness
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) : Prop :=
  ∀ (z₀ : Geodesic.Coordinate.State n) (t₀ T : ℝ),
    t₀ ≤ T → Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ T)

/-! ### Local existence from the geodesic flow -/

/-- Local existence gives a forward coordinate geodesic on `[t₀, t₀ + ε]`. -/
theorem geodesic_exists_forward
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (t₀ : ℝ) (z₀ : Geodesic.Coordinate.State n) :
    ∃ ε > 0, Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ (t₀ + ε)) := by
  let data := localCoordinateGeodesicFlowData (n := n) Gamma t₀ z₀
  refine ⟨data.ε, data.hε, ⟨{
    gamma := localCoordinateGeodesic (n := n) Gamma t₀ z₀
    hab := by linarith [data.hε]
    initial := localCoordinateGeodesic_initial (n := n) Gamma t₀ z₀
    isGeodesic := (localCoordinateGeodesic_isGeodesic (n := n) Gamma t₀ z₀).mono
      (Icc_subset_Icc (by linarith [data.hε]) le_rfl)
  }⟩⟩

/-- At the coordinate level, the state space `State n = (Fin n → ℝ) × (Fin n → ℝ)` is
automatically proper (finite-dimensional normed space). -/
instance coordinate_state_properSpace :
    ProperSpace (Geodesic.Coordinate.State n) :=
  inferInstance

/-! ### Geodesic patching: extend a geodesic segment by one step

This is the key ODE infrastructure lemma: any `CoordinateGeodesicOnInterval` on `[t₀, T']`
can be extended to `[t₀, T' + ε]` for some `ε > 0`, by patching the existing geodesic with a
local geodesic produced by `geodesic_exists_forward` at the endpoint `T'`.

The proof follows the pattern of `ODE.Autonomous.linearizedSolutionData_extend`:
- interior points: `EventuallyEq.hasDerivWithinAt_iff` with `HasDerivAt` from interior
- junction point `T'`: `HasDerivWithinAt.union` on left and right halves
-/

set_option maxHeartbeats 8000000 in
theorem coordinateGeodesicOnInterval_append
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {z₀ : Geodesic.Coordinate.State n} {t₀ T' T'' : ℝ}
    (J : CoordinateGeodesicOnInterval Gamma z₀ t₀ T')
    (η : CoordinateGeodesicOnInterval Gamma (J.gamma T') T' T'') :
    Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ T'') := by
  by_cases hT'eq : T' = t₀
  · subst hT'eq
    exact ⟨{
      gamma := η.gamma
      hab := by simpa using η.hab
      initial := by rw [η.initial, J.initial]
      isGeodesic := η.isGeodesic
    }⟩
  have hT'lt : t₀ < T' := lt_of_le_of_ne J.hab (fun h => hT'eq h.symm)
  let gamma' : ℝ → State n := fun t => if t ≤ T' then J.gamma t else η.gamma t
  have eqL : ∀ t, t ≤ T' → gamma' t = J.gamma t :=
    fun t h => show (if t ≤ T' then J.gamma t else η.gamma t) = _ by simp [h]
  have eqR : ∀ t, T' < t → gamma' t = η.gamma t :=
    fun t h => show (if t ≤ T' then J.gamma t else η.gamma t) = _ by simp [not_le.mpr h]
  have hgT' : gamma' T' = J.gamma T' := eqL T' le_rfl
  have hjunc : gamma' T' = η.gamma T' := by rw [hgT', η.initial]
  have hinit : gamma' t₀ = z₀ := by rw [eqL t₀ J.hab]; exact J.initial
  let Gamma' := christoffelFieldOfSmooth Gamma
  let v := geodesicVectorField Gamma'
  have hgeod : IsCoordinateGeodesicOn Gamma' gamma' (Icc t₀ T'') := by
    intro s hs
    by_cases hsT : s < T'
    · rw [eqL s hsT.le]
      have hJs : HasDerivWithinAt J.gamma (v s (J.gamma s)) (Icc t₀ T') s :=
        J.isGeodesic s ⟨hs.1, hsT.le⟩
      have h1 : HasDerivWithinAt gamma' (v s (J.gamma s)) (Icc t₀ T') s :=
        hJs.congr (fun x hx => eqL x hx.2) (eqL s hsT.le)
      by_cases hs₀ : t₀ < s
      · exact (h1.hasDerivAt (Icc_mem_nhds hs₀ hsT)).hasDerivWithinAt
      · push_neg at hs₀
        have hseq : s = t₀ := le_antisymm hs₀ hs.1
        rw [hseq] at h1 ⊢
        exact h1.congr_set ((Filter.eventually_of_mem
          (Ioo_mem_nhds (by linarith : t₀ - 1 < t₀) hT'lt)
          (fun x hx => by
            rw [mem_Ioo] at hx
            simp only [mem_Icc]
            exact ⟨fun ⟨h1, h2⟩ => ⟨h1, le_trans h2 η.hab⟩,
              fun ⟨h1, _⟩ => ⟨h1, by linarith [hx.2]⟩⟩)).set_eq)
    · push_neg at hsT
      by_cases hsT' : s = T'
      · rw [hsT'] at hs ⊢
        rw [hgT']
        have hleft : HasDerivWithinAt gamma' (v T' (J.gamma T')) (Icc t₀ T') T' :=
          (J.isGeodesic T' ⟨J.hab, le_rfl⟩).congr
            (fun x hx => eqL x hx.2) (eqL T' le_rfl)
        have hright : HasDerivWithinAt gamma' (v T' (J.gamma T')) (Icc T' T'') T' := by
          rw [show v T' (J.gamma T') = v T' (η.gamma T') by rw [η.initial]]
          exact (η.isGeodesic T' ⟨le_rfl, η.hab⟩).congr
            (fun x hx => by
              rcases eq_or_lt_of_le hx.1 with hxeq | hxgt
              · rw [← hxeq]
                exact hjunc
              · exact eqR x hxgt)
            hjunc
        rw [← Icc_union_Icc_eq_Icc J.hab η.hab]
        exact hleft.union hright
      · have hsT'' : T' < s := lt_of_le_of_ne hsT (Ne.symm hsT')
        rw [eqR s hsT'']
        have hηs : HasDerivWithinAt η.gamma (v s (η.gamma s)) (Icc T' T'') s :=
          η.isGeodesic s ⟨hsT''.le, hs.2⟩
        have h1 : HasDerivWithinAt gamma' (v s (η.gamma s)) (Icc T' T'') s :=
          hηs.congr
            (fun x hx => by
              rcases eq_or_lt_of_le hx.1 with hxeq | hxgt
              · rw [← hxeq]
                exact hjunc
              · exact eqR x hxgt)
            (eqR s hsT'')
        by_cases hsε : s < T''
        · exact (h1.hasDerivAt (Icc_mem_nhds hsT'' hsε)).hasDerivWithinAt
        · push_neg at hsε
          have hseq : s = T'' := le_antisymm hs.2 hsε
          rw [hseq] at h1 ⊢
          exact h1.congr_set ((Filter.eventually_of_mem
            (Ioo_mem_nhds (by linarith : T' < T'') (by linarith : T'' < T'' + 1))
            (fun x hx => by
              rw [mem_Ioo] at hx
              simp only [mem_Icc]
              exact ⟨fun ⟨_, h2⟩ => ⟨by linarith [hx.1], h2⟩,
                fun ⟨_, h2⟩ => ⟨by linarith [hx.1], h2⟩⟩)).set_eq)
  exact ⟨{
    gamma := gamma'
    hab := le_trans J.hab η.hab
    initial := hinit
    isGeodesic := hgeod
  }⟩

set_option maxHeartbeats 8000000 in
theorem coordinateGeodesicOnInterval_step
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {z₀ : Geodesic.Coordinate.State n} {t₀ T' : ℝ}
    (J : CoordinateGeodesicOnInterval Gamma z₀ t₀ T') :
    ∃ ε > 0, Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ (T' + ε)) := by
  obtain ⟨ε, hε, ⟨η⟩⟩ := geodesic_exists_forward Gamma T' (J.gamma T')
  refine ⟨ε, hε, ?_⟩
  exact coordinateGeodesicOnInterval_append Gamma J η

/-- Restrict a coordinate geodesic on `[t₀, T]` to a shorter interval `[t₀, T']`. -/
def CoordinateGeodesicOnInterval.restrict
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {z₀ : State n} {t₀ T : ℝ}
    (J : CoordinateGeodesicOnInterval Gamma z₀ t₀ T)
    {T' : ℝ} (hT'₀ : t₀ ≤ T') (hT'T : T' ≤ T) :
    CoordinateGeodesicOnInterval Gamma z₀ t₀ T' where
  gamma := J.gamma
  hab := hT'₀
  initial := J.initial
  isGeodesic := J.isGeodesic.mono fun t ht => ⟨ht.1, le_trans ht.2 hT'T⟩

set_option maxHeartbeats 4000000 in
theorem coordinateGeodesicOnInterval_eqOn
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {z₀ : State n} {t₀ T : ℝ}
    (J J' : CoordinateGeodesicOnInterval Gamma z₀ t₀ T) :
    EqOn J.gamma J'.gamma (Icc t₀ T) := by
  by_cases hdeg : T = t₀
  · intro t ht
    have htright : t ≤ t₀ := by simpa [hdeg] using ht.2
    have ht0 : t = t₀ := le_antisymm htright ht.1
    subst ht0
    exact J.initial.trans J'.initial.symm
  have hlt : t₀ < T := lt_of_le_of_ne J.hab (fun h => hdeg h.symm)
  have hJcont : ContinuousOn J.gamma (Icc t₀ T) := HasDerivWithinAt.continuousOn J.isGeodesic
  have hJ'cont : ContinuousOn J'.gamma (Icc t₀ T) := HasDerivWithinAt.continuousOn J'.isGeodesic
  let Kset : Set (State n) := J.gamma '' Icc t₀ T ∪ J'.gamma '' Icc t₀ T
  have hKset :
      IsCompact Kset := by
    refine (isCompact_Icc.image_of_continuousOn hJcont).union ?_
    exact isCompact_Icc.image_of_continuousOn hJ'cont
  obtain ⟨R, hR⟩ := hKset.exists_bound_of_continuousOn (f := fun z : State n => z) continuousOn_id
  let R' : ℝ := max R 0
  have hstayJ : ∀ t ∈ Ico t₀ T, J.gamma t ∈ Metric.closedBall (0 : State n) R' := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (hR _ (Or.inl ⟨t, ⟨ht.1, le_of_lt ht.2⟩, rfl⟩)) (le_max_left _ _)
  have hstayJ' : ∀ t ∈ Ico t₀ T, J'.gamma t ∈ Metric.closedBall (0 : State n) R' := by
    intro t ht
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact le_trans (hR _ (Or.inr ⟨t, ⟨ht.1, le_of_lt ht.2⟩, rfl⟩)) (le_max_left _ _)
  obtain ⟨K, hK⟩ :=
    ((contDiff_geodesicSpray (n := n) Gamma).of_le (by simp)).contDiffOn.exists_lipschitzOnWith
      (n := (1 : WithTop ℕ∞)) one_ne_zero
      (convex_closedBall (0 : State n) R') (isCompact_closedBall (0 : State n) R')
  let Gamma' := christoffelFieldOfSmooth Gamma
  have hv :
      ∀ t ∈ Ico t₀ T,
        LipschitzOnWith K (geodesicVectorField Gamma' t) (Metric.closedBall (0 : State n) R') := by
    intro t ht
    simpa [Gamma', geodesicVectorField] using hK
  have hJd :
      ∀ t ∈ Ico t₀ T,
        HasDerivWithinAt J.gamma (geodesicVectorField Gamma' t (J.gamma t)) (Ici t) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht₀
    · exact ODE.Autonomous.hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc_left
        (J.isGeodesic t₀ ⟨le_rfl, le_of_lt ht.2⟩) hlt
    · exact ODE.Autonomous.hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc
        (J.isGeodesic t ⟨ht.1, le_of_lt ht.2⟩) ht₀ ht.2
  have hJ'd :
      ∀ t ∈ Ico t₀ T,
        HasDerivWithinAt J'.gamma (geodesicVectorField Gamma' t (J'.gamma t)) (Ici t) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with rfl | ht₀
    · exact ODE.Autonomous.hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc_left
        (J'.isGeodesic t₀ ⟨le_rfl, le_of_lt ht.2⟩) hlt
    · exact ODE.Autonomous.hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc
        (J'.isGeodesic t ⟨ht.1, le_of_lt ht.2⟩) ht₀ ht.2
  exact ODE_solution_unique_of_mem_Icc_right hv hJcont hJd hstayJ hJ'cont hJ'd hstayJ' <|
    J.initial.trans J'.initial.symm

theorem coordinateGeodesicOnInterval_endpoint_eq
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {z₀ : State n} {t₀ T : ℝ}
    (J J' : CoordinateGeodesicOnInterval Gamma z₀ t₀ T) :
    J.gamma T = J'.gamma T :=
  coordinateGeodesicOnInterval_eqOn Gamma J J' ⟨J.hab, le_rfl⟩

theorem coordinateGeodesicOnInterval_eqOn_overlap
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {z₀ : State n} {t₀ T₁ T₂ : ℝ}
    (J₁ : CoordinateGeodesicOnInterval Gamma z₀ t₀ T₁)
    (J₂ : CoordinateGeodesicOnInterval Gamma z₀ t₀ T₂) :
    EqOn J₁.gamma J₂.gamma (Icc t₀ (min T₁ T₂)) := by
  let T' := min T₁ T₂
  have hT' : t₀ ≤ T' := le_min J₁.hab J₂.hab
  simpa [T'] using coordinateGeodesicOnInterval_eqOn Gamma
    (J₁.restrict (T' := T') hT' (min_le_left _ _))
    (J₂.restrict (T' := T') hT' (min_le_right _ _))

theorem coordinateGeodesicOnInterval_endpoint_eq_overlap
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {z₀ : State n} {t₀ T₁ T₂ : ℝ}
    (J₁ : CoordinateGeodesicOnInterval Gamma z₀ t₀ T₁)
    (J₂ : CoordinateGeodesicOnInterval Gamma z₀ t₀ T₂) :
    J₁.gamma (min T₁ T₂) = J₂.gamma (min T₁ T₂) :=
  coordinateGeodesicOnInterval_eqOn_overlap Gamma J₁ J₂ ⟨le_min J₁.hab J₂.hab, le_rfl⟩

theorem coordinateGeodesicOnInterval_endpoint_mem_of_witness
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {K : Set (State n)} {z₀ : State n} {t₀ T : ℝ}
    (hwitness :
      Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ T) →
        ∃ J : CoordinateGeodesicOnInterval Gamma z₀ t₀ T, J.gamma T ∈ K)
    (J : CoordinateGeodesicOnInterval Gamma z₀ t₀ T) :
    J.gamma T ∈ K := by
  obtain ⟨Jw, hJwK⟩ := hwitness ⟨J⟩
  simpa [coordinateGeodesicOnInterval_endpoint_eq Gamma J Jw] using hJwK

/-- If the base positions of an interval geodesic stay in a compact position set `K`, then the
full state stays in one compact shell over `K`. This is the interval-facing wrapper around the
owner theorem in `Exponential/RadialGaussLemma.lean`. -/
theorem CoordinateGeodesicOnInterval.exists_stateCompactShell_of_position_isCompact
    {data : Exponential.Coordinate.LocalRiemannianData n}
    {z₀ : State n} {t₀ T : ℝ}
    (J : CoordinateGeodesicOnInterval data.Gamma z₀ t₀ T)
    {K : Set (Exponential.Coordinate.Position n)}
    (hK : IsCompact K)
    (hbase : ∀ t ∈ Icc t₀ T, Geodesic.Coordinate.statePosition n (J.gamma t) ∈ K) :
    ∃ R : ℝ, 0 ≤ R ∧
      IsCompact (K ×ˢ Metric.closedBall (0 : Geodesic.Coordinate.Velocity n) R) ∧
      ∀ t ∈ Icc t₀ T, J.gamma t ∈ K ×ˢ Metric.closedBall (0 : Geodesic.Coordinate.Velocity n) R := by
  exact Exponential.Coordinate.exists_stateCompactShell_of_isCoordinateGeodesicOn_of_position_isCompact
    (n := n) data J.hab J.isGeodesic hK hbase

/-! ### Iteration: from uniform extension time to global existence

Given a uniform step size `δ > 0` with a guarantee that any existing geodesic on `[t₀, T']`
(with `T' ≤ T`) can be extended to `[t₀, min(T' + δ, T)]`, iterate `⌈(T − t₀)/δ⌉` times
to produce a geodesic on `[t₀, T]`. -/

set_option maxHeartbeats 4000000 in
theorem coordinateGeodesicOnInterval_of_uniform_step
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    {z₀ : State n} {t₀ T : ℝ} (hT : t₀ ≤ T)
    {δ : ℝ} (hδ : 0 < δ)
    (hstep : ∀ (T' : ℝ), t₀ ≤ T' → T' ≤ T →
      CoordinateGeodesicOnInterval Gamma z₀ t₀ T' →
        Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ (min (T' + δ) T))) :
    Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ T) := by
  set N := Nat.ceil ((T - t₀) / δ)
  suffices ∀ k : ℕ, Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ (min (t₀ + ↑k * δ) T)) by
    have hNδ : T ≤ t₀ + ↑N * δ := by
      have h := Nat.le_ceil ((T - t₀) / δ)
      rw [div_le_iff₀ hδ] at h
      linarith
    have := this N
    rwa [min_eq_right hNδ] at this
  intro k
  induction k with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero, min_eq_left hT]
      exact ⟨⟨fun _ => z₀, le_rfl, rfl, fun t ht => by
        have hteq : t = t₀ := le_antisymm ht.2 ht.1
        rw [hteq, show Icc t₀ t₀ = {t₀} from Icc_self t₀] at ht ⊢
        exact HasFDerivWithinAt.of_subsingleton Set.subsingleton_singleton⟩⟩
  | succ k ih =>
      obtain ⟨Jk⟩ := ih
      have hsucc_eq : t₀ + ↑(k + 1) * δ = (t₀ + ↑k * δ) + δ := by push_cast; ring
      by_cases hreach : T ≤ t₀ + ↑k * δ
      · have hmin_prev : min (t₀ + ↑k * δ) T = T := min_eq_right hreach
        have hmin_succ : min (t₀ + ↑(k + 1) * δ) T = T :=
          min_eq_right (le_trans hreach (by linarith))
        rw [hmin_prev] at Jk; rw [hmin_succ]
        exact ⟨Jk⟩
      · push_neg at hreach
        have hmin_prev : min (t₀ + ↑k * δ) T = t₀ + ↑k * δ :=
          min_eq_left hreach.le
        rw [hmin_prev] at Jk
        have hkδ_pos : t₀ ≤ t₀ + ↑k * δ := by
          have : (0 : ℝ) ≤ ↑k * δ := mul_nonneg (Nat.cast_nonneg k) hδ.le
          linarith
        obtain ⟨Jk'⟩ := hstep (t₀ + ↑k * δ) hkδ_pos hreach.le Jk
        rw [hsucc_eq]
        exact ⟨Jk'⟩

/-! ### Factored completeness: patching + uniform step → completeness -/

/-- Completeness data factored through a uniform extension step.

The `uniformStep` field asserts that for any initial state `z₀`, initial time `t₀`, and
target time `T`, there exists a uniform step size `δ > 0` such that any existing geodesic
on `[t₀, T']` with `T' ≤ T` can be extended to `[t₀, min(T' + δ, T)]`.

This is a weaker claim than `HasCoordinateGeodesicCompleteness`: it reduces the full ODE
global-existence problem to providing a uniform step size, which in turn follows from
a priori speed bounds + compact containment. -/
structure GeodesicUniformStepData
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) where
  uniformStep :
    ∀ (z₀ : State n) (t₀ T : ℝ), t₀ ≤ T →
      ∃ δ > 0, ∀ (T' : ℝ), t₀ ≤ T' → T' ≤ T →
        CoordinateGeodesicOnInterval Gamma z₀ t₀ T' →
          Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ (min (T' + δ) T))

/-- Endpoint compact-containment data for the smooth completeness argument.

For fixed initial state `z₀` and finite horizon `[t₀, T]`, every partial geodesic endpoint
`J.gamma T'` is required to lie in one compact subset of state space. By interval uniqueness, it
suffices to provide one witness endpoint in that compact set whenever a partial geodesic to `T'`
exists. Combined with the compact-uniform local-existence theorem from
`Geodesic/LocalExistence.lean`, this is enough to produce a uniform extension step.

This structure is intentionally an input interface: the corresponding compact-containment theorem is
not available in this file for arbitrary smooth coordinate Levi-Civita data. -/
structure GeodesicEndpointCompactContainmentData
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) where
  compact_endpoints :
    ∀ (z₀ : State n) (t₀ T : ℝ), t₀ ≤ T →
      ∃ K : Set (State n), IsCompact K ∧
        ∀ (T' : ℝ), t₀ ≤ T' → T' ≤ T →
          Nonempty (CoordinateGeodesicOnInterval Gamma z₀ t₀ T') →
            ∃ J : CoordinateGeodesicOnInterval Gamma z₀ t₀ T', J.gamma T' ∈ K

/-- A global lower metric bound gives finite-horizon endpoint compact containment for the
associated Levi-Civita spray. This is a corrected smooth-side completeness input: unlike the false
generic theorem, it works only under a genuine global nonescape hypothesis. -/
theorem geodesicEndpointCompactContainmentData_of_globalMetricLowerBound
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (hbound : data.HasGlobalMetricLowerBound) :
    GeodesicEndpointCompactContainmentData data.Gamma := by
  refine ⟨?_⟩
  intro z₀ t₀ T hT
  obtain ⟨m₀, hm₀_pos, hmetric_lower₀⟩ := hbound
  let E : ℝ := Exponential.Coordinate.stateEnergy (n := n) data z₀
  let Rpos : ℝ := Real.sqrt (E / m₀) * (T - t₀)
  let B : Set (Position n) := Metric.closedBall (statePosition n z₀) Rpos
  have hBcompact : IsCompact B := by
    simpa [B] using isCompact_closedBall (statePosition n z₀) Rpos
  obtain ⟨mB, MB, hmB_pos, hMB_pos, hmetricB⟩ :=
    data.exists_uniform_metric_normComparisonOn_isCompact hBcompact
  let Rvel : ℝ := Real.sqrt (E / mB)
  let K : Set (State n) := B ×ˢ Metric.closedBall (0 : Velocity n) Rvel
  refine ⟨K, hBcompact.prod (isCompact_closedBall (0 : Velocity n) Rvel), ?_⟩
  intro T' hT'₀ hT'T hJ
  rcases hJ with ⟨J⟩
  refine ⟨J, ?_⟩
  have hbase_small :
      statePosition n (J.gamma T') ∈
        Metric.closedBall
          (statePosition n (J.gamma t₀))
          (Real.sqrt
              (Exponential.Coordinate.stateEnergy (n := n) data (J.gamma t₀) / m₀) *
            (T' - t₀)) := by
    exact Exponential.Coordinate.statePosition_mem_closedBall_of_metricLowerBound
      (n := n) data hm₀_pos hmetric_lower₀ J.hab J.isGeodesic T' ⟨J.hab, le_rfl⟩
  have hbase :
      statePosition n (J.gamma T') ∈ B := by
    have hbase_small' :
        dist (statePosition n (J.gamma T')) (statePosition n z₀) ≤
          Real.sqrt (E / m₀) * (T' - t₀) := by
      simpa [Metric.mem_closedBall, J.initial, E] using hbase_small
    have hrad :
        Real.sqrt (E / m₀) * (T' - t₀) ≤ Rpos := by
      dsimp [Rpos]
      have hsub : T' - t₀ ≤ T - t₀ := sub_le_sub_right hT'T t₀
      exact mul_le_mul_of_nonneg_left hsub (Real.sqrt_nonneg _)
    simpa [B, Metric.mem_closedBall] using le_trans hbase_small' hrad
  have henergy :
      Exponential.Coordinate.stateEnergy (n := n) data (J.gamma T') = E := by
    simpa [E, J.initial] using
      Exponential.Coordinate.stateEnergy_eq_initial_of_isCoordinateGeodesicOn
        (n := n) data J.hab J.isGeodesic T' ⟨J.hab, le_rfl⟩
  constructor
  · exact hbase
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    let v := stateVelocity n (J.gamma T')
    have hmetric_lower :
        mB * Metric.Coordinate.supNormSq v ≤
          Metric.Coordinate.quadraticForm
            (data.metricField (statePosition n (J.gamma T'))) v :=
      (hmetricB _ hbase v).1
    have hsq_le : Metric.Coordinate.supNormSq v ≤ E / mB := by
      rw [le_div_iff₀ hmB_pos]
      calc
        Metric.Coordinate.supNormSq v * mB = mB * Metric.Coordinate.supNormSq v := by ring
        _ ≤ Metric.Coordinate.quadraticForm
              (data.metricField (statePosition n (J.gamma T'))) v :=
            hmetric_lower
        _ = Exponential.Coordinate.stateEnergy (n := n) data (J.gamma T') := by
              rfl
        _ = E := henergy
    have hnorm_sq : ‖v‖ ^ 2 ≤ E / mB := by
      simpa [Metric.Coordinate.supNormSq, pow_two] using hsq_le
    calc
      ‖v‖ = Real.sqrt (‖v‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ ≤ Real.sqrt (E / mB) := by
        exact Real.sqrt_le_sqrt hnorm_sq
      _ = Rvel := by
        rfl

/-- Compact containment of all reachable endpoint states on `[t₀, T]` implies the uniform step
property. This isolates the remaining smooth-side work to the geometric shell theorem producing the
compact set. -/
theorem geodesicUniformStepData_of_endpointCompactContainment
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (hK : GeodesicEndpointCompactContainmentData Gamma) :
    GeodesicUniformStepData Gamma := by
  refine ⟨?_⟩
  intro z₀ t₀ T hT
  rcases hK.compact_endpoints z₀ t₀ T hT with ⟨K, hKcompact, hKmem⟩
  obtain ⟨δ, hδ, hlocal0⟩ :=
    Geodesic.Coordinate.exists_uniform_coordinateGeodesicOn_zero_of_isCompact
      (n := n) Gamma hKcompact
  refine ⟨δ, hδ, ?_⟩
  intro T' hT'₀ hT'T J
  have hzK : J.gamma T' ∈ K :=
    coordinateGeodesicOnInterval_endpoint_mem_of_witness Gamma
      (K := K) (hwitness := hKmem T' hT'₀ hT'T) J
  rcases hlocal0 (J.gamma T') hzK with ⟨γloc, hγloc0, hγloc_geod⟩
  let η : ℝ → State n := timeTranslateStateCurve (n := n) T' γloc
  have hηinit : η T' = J.gamma T' := by
    simpa [η, timeTranslateStateCurve] using hγloc0
  have hηgeod_full :
      IsCoordinateGeodesicOn (christoffelFieldOfSmooth Gamma) η (Icc (T' - δ) (T' + δ)) := by
    simpa [η, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (isCoordinateGeodesicOn_timeTranslate (n := n)
        (Gamma := christoffelFieldOfSmooth Gamma) (a := (-δ)) (b := δ) (c := T') hγloc_geod)
  have hηsubset : Icc T' (min (T' + δ) T) ⊆ Icc (T' - δ) (T' + δ) := by
    intro s hs
    constructor
    · have hleft : T' - δ ≤ T' := by linarith [hδ]
      exact le_trans hleft hs.1
    · exact le_trans hs.2 (min_le_left _ _)
  let ηseg : CoordinateGeodesicOnInterval Gamma (J.gamma T') T' (min (T' + δ) T) := {
    gamma := η
    hab := by
      refine le_min ?_ hT'T
      linarith [hδ]
    initial := hηinit
    isGeodesic := hηgeod_full.mono hηsubset
  }
  exact coordinateGeodesicOnInterval_append Gamma J ηseg

/-- Geodesic completeness follows from the uniform step data via iteration. -/
theorem hasCoordinateGeodesicCompleteness_of_uniformStep
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (h : GeodesicUniformStepData Gamma) :
    HasCoordinateGeodesicCompleteness Gamma := by
  intro z₀ t₀ T hT
  obtain ⟨δ, hδ, hstep⟩ := h.uniformStep z₀ t₀ T hT
  exact coordinateGeodesicOnInterval_of_uniform_step Gamma hT hδ hstep

/-- Smooth geodesic completeness data at the coordinate level.

This owner package carries the uniform step, and the actual completeness statement is derived by
`hasCoordinateGeodesicCompleteness_of_uniformStep`. This keeps the remaining external content
focused on endpoint compact containment rather than a duplicated top-level completeness field. -/
structure SmoothGeodesicCompletenessData
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) where
  step : GeodesicUniformStepData Gamma

/-- Recover coordinate geodesic completeness from the owner-layer uniform step package. -/
theorem SmoothGeodesicCompletenessData.completeness
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    (h : SmoothGeodesicCompletenessData Gamma) :
    HasCoordinateGeodesicCompleteness Gamma :=
  hasCoordinateGeodesicCompleteness_of_uniformStep Gamma h.step

theorem smoothGeodesicCompletenessData_of_uniformStep
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (h : GeodesicUniformStepData Gamma) :
    SmoothGeodesicCompletenessData Gamma where
  step := h

/-- Endpoint compact containment is sufficient to build the smooth completeness data. -/
theorem smoothGeodesicCompletenessData_of_endpointCompactContainment
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (h : GeodesicEndpointCompactContainmentData Gamma) :
    SmoothGeodesicCompletenessData Gamma :=
  smoothGeodesicCompletenessData_of_uniformStep Gamma
    (geodesicUniformStepData_of_endpointCompactContainment Gamma h)

/-- A global lower metric bound is enough to build the owner-layer smooth completeness data for the
associated Levi-Civita spray. -/
theorem smoothGeodesicCompletenessData_of_globalMetricLowerBound
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (hbound : data.HasGlobalMetricLowerBound) :
    SmoothGeodesicCompletenessData data.Gamma :=
  smoothGeodesicCompletenessData_of_endpointCompactContainment data.Gamma
    (geodesicEndpointCompactContainmentData_of_globalMetricLowerBound (n := n) data hbound)

/-! ### Interface for the smooth → metric bridge -/

/-- The smooth-to-metric bridge: smooth geodesic completeness implies metric geodesic extension.

This requires:
1. Inside a strongly convex ball, every metric geodesic segment is the unique smooth radial geodesic.
2. Patch the local smooth pieces using ODE uniqueness on overlaps.
3. A smooth geodesic line is locally minimizing → metric geodesic line.

The bridge is carried as an input function. -/
def coordinate_geodesicExtensionData_of_smooth_and_bridge
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (hsmooth : SmoothGeodesicCompletenessData Gamma)
    (hbridge :
      HasCoordinateGeodesicCompleteness Gamma →
        HasGeodesicExtension (Exponential.Coordinate.Position n)) :
    GeodesicExtensionData (Exponential.Coordinate.Position n) where
  complete_geodesic := fun _ =>
    hbridge hsmooth.completeness

/-- Combine the smooth completeness and bridge into the full geodesic extension data.
This is the composition:
  SmoothGeodesicCompletenessData → (bridge) → GeodesicExtensionData
The bridge function captures the metric recognition step. -/
def coordinate_geodesicExtensionData_of_completeness_bridge
    (_Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (h : RiemannianComplete (Exponential.Coordinate.Position n) →
           HasGeodesicExtension (Exponential.Coordinate.Position n)) :
    GeodesicExtensionData (Exponential.Coordinate.Position n) where
  complete_geodesic := h

end HopfRinow
