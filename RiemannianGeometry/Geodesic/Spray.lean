import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring
import Geodesic.CoordinateEquation

/-! The spray layer owns the scaling and time-rescaling lemmas used by the current radial-source
story for coordinate exponential maps. -/

namespace Geodesic.Coordinate

open Set Filter
open scoped Topology

variable {n : ℕ}

/-- The time-independent first-order geodesic spray associated to a Christoffel field. -/
def geodesicSpray (Gamma : ChristoffelField n) (z : State n) : State n :=
  (stateVelocity n z, geodesicAcceleration Gamma (statePosition n z) (stateVelocity n z))

/-- The spray, seen as a time-dependent ODE right-hand side. -/
def geodesicVectorField (Gamma : ChristoffelField n) : ℝ → State n → State n :=
  fun _ => geodesicSpray Gamma

/-- A coordinate geodesic on a set is a state-space solution of the first-order spray equation. -/
def IsCoordinateGeodesicOn
    (Gamma : ChristoffelField n) (gamma : ℝ → State n) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt gamma ((geodesicVectorField Gamma) t (gamma t)) s t

/-- A coordinate geodesic at `t₀` solves the spray equation on some neighborhood of `t₀`. -/
def IsCoordinateGeodesicAt
    (Gamma : ChristoffelField n) (gamma : ℝ → State n) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasDerivAt gamma ((geodesicVectorField Gamma) t (gamma t)) t

@[simp] theorem geodesicVectorField_apply
    (Gamma : ChristoffelField n) (t : ℝ) (z : State n) :
    geodesicVectorField Gamma t z = geodesicSpray Gamma z :=
  rfl

@[simp] theorem geodesicSpray_fst
    (Gamma : ChristoffelField n) (z : State n) :
    (geodesicSpray Gamma z).1 = stateVelocity n z :=
  rfl

@[simp] theorem geodesicSpray_snd
    (Gamma : ChristoffelField n) (z : State n) :
    (geodesicSpray Gamma z).2 =
      geodesicAcceleration Gamma (statePosition n z) (stateVelocity n z) :=
  rfl

@[simp] theorem geodesicAcceleration_smul
    (Gamma : ChristoffelField n) (x : Position n) (c : ℝ) (v : Velocity n) :
    geodesicAcceleration Gamma x (c • v) = (c ^ 2) • geodesicAcceleration Gamma x v := by
  funext i
  unfold geodesicAcceleration
  have hsum :
      ∑ j : Fin n, ∑ k : Fin n, Gamma x i j k * (c • v) j * (c • v) k =
        c ^ 2 * ∑ j : Fin n, ∑ k : Fin n, Gamma x i j k * v j * v k := by
    rw [Finset.mul_sum]
    congr 1
    ext j
    rw [Finset.mul_sum]
    congr 1
    ext k
    simp [Pi.smul_apply]
    ring
  simpa [smul_eq_mul, mul_neg] using congrArg Neg.neg hsum

/-- Reparametrize a state curve by scaling time and velocity by the same factor. -/
def timeRescaleStateCurve (a : ℝ) (gamma : ℝ → State n) : ℝ → State n :=
  fun t => (statePosition n (gamma (a * t)), a • stateVelocity n (gamma (a * t)))

/-- Translate a state curve in time by `c`. -/
def timeTranslateStateCurve (c : ℝ) (gamma : ℝ → State n) : ℝ → State n :=
  fun t => gamma (t - c)

@[simp] theorem statePosition_timeRescaleStateCurve
    (a : ℝ) (gamma : ℝ → State n) (t : ℝ) :
    statePosition n (timeRescaleStateCurve (n := n) a gamma t) =
      statePosition n (gamma (a * t)) :=
  rfl

@[simp] theorem stateVelocity_timeRescaleStateCurve
    (a : ℝ) (gamma : ℝ → State n) (t : ℝ) :
    stateVelocity n (timeRescaleStateCurve (n := n) a gamma t) =
      a • stateVelocity n (gamma (a * t)) :=
  rfl

theorem IsCoordinateGeodesicOn.mono
    {Gamma : ChristoffelField n} {gamma : ℝ → State n} {s t : Set ℝ}
    (h : IsCoordinateGeodesicOn Gamma gamma s) (hts : t ⊆ s) :
    IsCoordinateGeodesicOn Gamma gamma t := by
  intro τ hτ
  exact (h τ (hts hτ)).mono hts

theorem isCoordinateGeodesicOn_iff_secondOrder
    {Gamma : ChristoffelField n} {gamma : ℝ → State n} {s : Set ℝ} :
    IsCoordinateGeodesicOn Gamma gamma s ↔
      (∀ t ∈ s,
        HasDerivWithinAt (fun τ => statePosition n (gamma τ))
          (stateVelocity n (gamma t)) s t) ∧
      ∀ t ∈ s,
        HasDerivWithinAt (fun τ => stateVelocity n (gamma τ))
          (geodesicAcceleration Gamma (statePosition n (gamma t)) (stateVelocity n (gamma t))) s t := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro t ht
      simpa [statePosition, geodesicVectorField, geodesicSpray] using
        (ContinuousLinearMap.fst ℝ (Position n) (Velocity n)).hasFDerivAt.comp_hasDerivWithinAt t
          (h t ht)
    · intro t ht
      simpa [stateVelocity, geodesicVectorField, geodesicSpray] using
        (ContinuousLinearMap.snd ℝ (Position n) (Velocity n)).hasFDerivAt.comp_hasDerivWithinAt t
          (h t ht)
  · rintro ⟨hpos, hvel⟩ t ht
    simpa [statePosition, stateVelocity, geodesicVectorField, geodesicSpray] using
      (hpos t ht).prodMk (hvel t ht)

theorem isCoordinateGeodesicAt_iff_secondOrder
    {Gamma : ChristoffelField n} {gamma : ℝ → State n} {t₀ : ℝ} :
    IsCoordinateGeodesicAt Gamma gamma t₀ ↔
      (∀ᶠ t in 𝓝 t₀,
        HasDerivAt (fun τ => statePosition n (gamma τ))
          (stateVelocity n (gamma t)) t) ∧
      ∀ᶠ t in 𝓝 t₀,
        HasDerivAt (fun τ => stateVelocity n (gamma τ))
          (geodesicAcceleration Gamma (statePosition n (gamma t)) (stateVelocity n (gamma t))) t := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · filter_upwards [h] with t ht
      simpa [statePosition, geodesicVectorField, geodesicSpray] using
        (ContinuousLinearMap.fst ℝ (Position n) (Velocity n)).hasFDerivAt.comp_hasDerivAt t ht
    · filter_upwards [h] with t ht
      simpa [stateVelocity, geodesicVectorField, geodesicSpray] using
        (ContinuousLinearMap.snd ℝ (Position n) (Velocity n)).hasFDerivAt.comp_hasDerivAt t ht
  · rintro ⟨hpos, hvel⟩
    filter_upwards [hpos, hvel] with t htpos htvel
    simpa [statePosition, stateVelocity, geodesicVectorField, geodesicSpray] using
      htpos.prodMk htvel

theorem isCoordinateGeodesicOn_timeRescale
    {Gamma : ChristoffelField n} {gamma : ℝ → State n} {ε : ℝ}
    (hε : 0 < ε)
    (hgamma : IsCoordinateGeodesicOn Gamma gamma (Set.Icc (-ε) ε)) :
    IsCoordinateGeodesicOn Gamma
      (timeRescaleStateCurve (n := n) ε gamma)
      (Set.Icc (-1 : ℝ) 1) := by
  rcases (isCoordinateGeodesicOn_iff_secondOrder (n := n) (Gamma := Gamma)
    (gamma := gamma) (s := Set.Icc (-ε) ε)).mp hgamma with ⟨hpos, hvel⟩
  have hmap : MapsTo (fun t : ℝ => ε * t) (Set.Icc (-1 : ℝ) 1) (Set.Icc (-ε) ε) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, hε]
  have hscale :
      ∀ t : ℝ,
        HasDerivWithinAt (fun τ : ℝ => ε * τ) ε (Set.Icc (-1 : ℝ) 1) t := by
    intro t
    simpa using (hasDerivAt_const_mul (x := t) ε).hasDerivWithinAt
  refine (isCoordinateGeodesicOn_iff_secondOrder (n := n) (Gamma := Gamma)
    (gamma := timeRescaleStateCurve (n := n) ε gamma) (s := Set.Icc (-1 : ℝ) 1)).2 ?_
  refine ⟨?_, ?_⟩
  · intro t ht
    have ht' : ε * t ∈ Set.Icc (-ε) ε := hmap ht
    simpa [timeRescaleStateCurve] using
      (hpos (ε * t) ht').scomp t (hscale t) hmap
  · intro t ht
    have ht' : ε * t ∈ Set.Icc (-ε) ε := hmap ht
    have hcomp :
        HasDerivWithinAt
          (fun τ => stateVelocity n (gamma (ε * τ)))
          (ε •
            geodesicAcceleration Gamma (statePosition n (gamma (ε * t)))
              (stateVelocity n (gamma (ε * t))))
          (Set.Icc (-1 : ℝ) 1) t := by
      exact (hvel (ε * t) ht').scomp t (hscale t) hmap
    have hconst :
        HasDerivWithinAt (fun _ : ℝ => ε) 0 (Set.Icc (-1 : ℝ) 1) t :=
      hasDerivWithinAt_const t (Set.Icc (-1 : ℝ) 1) ε
    simpa [timeRescaleStateCurve, smul_smul, pow_two] using HasDerivWithinAt.smul hconst hcomp

theorem isCoordinateGeodesicOn_timeRescale_interval
    {Gamma : ChristoffelField n} {gamma : ℝ → State n} {a ε : ℝ}
    (ha : 0 < a)
    (hgamma : IsCoordinateGeodesicOn Gamma gamma (Set.Icc (-(a * ε)) (a * ε))) :
    IsCoordinateGeodesicOn Gamma
      (timeRescaleStateCurve (n := n) a gamma)
      (Set.Icc (-ε) ε) := by
  rcases (isCoordinateGeodesicOn_iff_secondOrder (n := n) (Gamma := Gamma)
    (gamma := gamma) (s := Set.Icc (-(a * ε)) (a * ε))).mp hgamma with ⟨hpos, hvel⟩
  have hmap : MapsTo (fun t : ℝ => a * t) (Set.Icc (-ε) ε) (Set.Icc (-(a * ε)) (a * ε)) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha]
  have hscale :
      ∀ t : ℝ,
        HasDerivWithinAt (fun τ : ℝ => a * τ) a (Set.Icc (-ε) ε) t := by
    intro t
    simpa using (hasDerivAt_const_mul (x := t) a).hasDerivWithinAt
  refine (isCoordinateGeodesicOn_iff_secondOrder (n := n) (Gamma := Gamma)
    (gamma := timeRescaleStateCurve (n := n) a gamma) (s := Set.Icc (-ε) ε)).2 ?_
  refine ⟨?_, ?_⟩
  · intro t ht
    have ht' : a * t ∈ Set.Icc (-(a * ε)) (a * ε) := hmap ht
    simpa [timeRescaleStateCurve] using
      (hpos (a * t) ht').scomp t (hscale t) hmap
  · intro t ht
    have ht' : a * t ∈ Set.Icc (-(a * ε)) (a * ε) := hmap ht
    have hcomp :
        HasDerivWithinAt
          (fun τ => stateVelocity n (gamma (a * τ)))
          (a •
            geodesicAcceleration Gamma (statePosition n (gamma (a * t)))
              (stateVelocity n (gamma (a * t))))
          (Set.Icc (-ε) ε) t := by
      exact (hvel (a * t) ht').scomp t (hscale t) hmap
    have hconst :
        HasDerivWithinAt (fun _ : ℝ => a) 0 (Set.Icc (-ε) ε) t :=
      hasDerivWithinAt_const t (Set.Icc (-ε) ε) a
    simpa [timeRescaleStateCurve, smul_smul, pow_two] using HasDerivWithinAt.smul hconst hcomp

theorem isCoordinateGeodesicOn_timeTranslate
    {Gamma : ChristoffelField n} {gamma : ℝ → State n} {a b c : ℝ}
    (hgamma : IsCoordinateGeodesicOn Gamma gamma (Set.Icc a b)) :
    IsCoordinateGeodesicOn Gamma
      (timeTranslateStateCurve (n := n) c gamma)
      (Set.Icc (a + c) (b + c)) := by
  intro t ht
  have hmap :
      MapsTo (fun s : ℝ => s - c) (Set.Icc (a + c) (b + c)) (Set.Icc a b) := by
    intro s hs
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hs
  have hinner :
      HasDerivWithinAt (fun s : ℝ => s - c) 1 (Set.Icc (a + c) (b + c)) t := by
    have hinner_id :
        HasDerivWithinAt (fun s : ℝ => s) 1 (Set.Icc (a + c) (b + c)) t :=
      (hasDerivAt_id t).hasDerivWithinAt
    have hconst :
        HasDerivWithinAt (fun _ : ℝ => -c) 0 (Set.Icc (a + c) (b + c)) t :=
      hasDerivWithinAt_const t (Set.Icc (a + c) (b + c)) (-c)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hinner_id.add hconst
  have houter :
      HasDerivWithinAt gamma ((geodesicVectorField Gamma) (t - c) (gamma (t - c)))
        (Set.Icc a b) (t - c) :=
    hgamma (t - c) (hmap ht)
  simpa [timeTranslateStateCurve, geodesicVectorField] using
    (houter.hasFDerivWithinAt.comp_hasDerivWithinAt (x := t) hinner hmap)

end Geodesic.Coordinate
