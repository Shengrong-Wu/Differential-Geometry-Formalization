import HopfRinow.CompleteProper
import HopfRinow.DistanceRealizer
import HopfRinow.LengthCompactness
import HopfRinow.MetricLength
import HopfRinow.MinExistence

/-! # Complete → minimizing geodesics

This file owns the corrected complete→minimizers direction used by the live Hopf-Rinow assembly.
At the coordinate level the result is immediate: straight lines in `Fin n → ℝ` are minimizing
metric geodesics. The general metric compactness lemmas remain here because they are natural owner
infrastructure for future non-coordinate versions. -/

namespace HopfRinow

universe u

theorem compactSuperset_of_commonSource_uniformLipschitz
    {X : Type u} [PseudoMetricSpace X]
    (hcompact : HasLengthCompactness X)
    {S : Set (UnitIntervalCurve X)} {p : X} {L : NNReal}
    (h0 : ∀ ⦃γ⦄, γ ∈ S → γ ⟨0, by simp⟩ = p)
    (hlip : ∀ ⦃γ⦄, γ ∈ S → UniformLipschitzBound X L γ) :
    ∃ K : Set (UnitIntervalCurve X), IsCompact K ∧ S ⊆ K :=
  hcompact S (isLengthCompactFamily_of_commonSource_uniformLipschitz h0 hlip)

/-- Export the intended owner theorem name from the minimizing-geodesic input package. -/
theorem complete_implies_minimizers
    {M : Type u} [PseudoMetricSpace M]
    (input : MinExistenceData M) :
    RiemannianComplete M → MinimizingGeodesicsExist M :=
  input.complete_minimizers

/-- Package a proved complete-to-minimizers theorem back into the input layer. -/
def minExistenceData_of_complete_implies_minimizers
    {M : Type u} [PseudoMetricSpace M]
    (h : RiemannianComplete M → MinimizingGeodesicsExist M) :
    MinExistenceData M where
  complete_minimizers := h

/-! ### Coordinate-level minimizer existence

In `Position n = Fin n → ℝ` (a normed vector space), the straight-line path between any two
points is a minimizing geodesic. This makes `MinimizingGeodesicsExist` immediate. -/

/-- The straight-line path between two points in coordinate space. -/
noncomputable def coordinateStraightLine {n : ℕ}
    (p q : Exponential.Coordinate.Position n) : ℝ → Exponential.Coordinate.Position n :=
  fun t => (1 - t) • p + t • q

@[simp] theorem coordinateStraightLine_zero {n : ℕ}
    {p q : Exponential.Coordinate.Position n} :
    coordinateStraightLine p q 0 = p := by
  simp [coordinateStraightLine]

@[simp] theorem coordinateStraightLine_one {n : ℕ}
    {p q : Exponential.Coordinate.Position n} :
    coordinateStraightLine p q 1 = q := by
  simp [coordinateStraightLine]

theorem coordinateStraightLine_sub {n : ℕ}
    {p q : Exponential.Coordinate.Position n} (t₁ t₂ : ℝ) :
    coordinateStraightLine p q t₁ - coordinateStraightLine p q t₂ = (t₁ - t₂) • (q - p) := by
  simp only [coordinateStraightLine]
  ext i
  simp
  ring

theorem coordinateStraightLine_dist {n : ℕ}
    {p q : Exponential.Coordinate.Position n} (t₁ t₂ : ℝ) :
    dist (coordinateStraightLine p q t₁) (coordinateStraightLine p q t₂) =
      dist p q * |t₁ - t₂| := by
  rw [dist_eq_norm, coordinateStraightLine_sub, norm_smul, Real.norm_eq_abs]
  rw [← dist_eq_norm q p, dist_comm q p]
  ring

theorem coordinateStraightLine_isMinimizingGeodesicBetween {n : ℕ}
    (p q : Exponential.Coordinate.Position n) :
    IsMinimizingGeodesicBetween (Exponential.Coordinate.Position n) p q
      (coordinateStraightLine p q) := by
  refine ⟨coordinateStraightLine_zero, coordinateStraightLine_one, dist_nonneg, ?_⟩
  intro t₁ t₂ _ _
  exact coordinateStraightLine_dist t₁ t₂

/-- In coordinate space, minimizing geodesics always exist (straight lines). -/
theorem coordinate_minimizingGeodesicsExist {n : ℕ} :
    MinimizingGeodesicsExist (Exponential.Coordinate.Position n) :=
  fun p q => ⟨coordinateStraightLine p q,
    coordinateStraightLine_isMinimizingGeodesicBetween p q⟩

/-- At the coordinate level, completeness implies minimizing geodesics exist.
Straight lines in `Position n` are minimizing; no Christoffel data is needed. -/
theorem coordinate_complete_implies_minimizers {n : ℕ} :
    RiemannianComplete (Exponential.Coordinate.Position n) →
      MinimizingGeodesicsExist (Exponential.Coordinate.Position n) :=
  fun _ => coordinate_minimizingGeodesicsExist

/-- Package the coordinate-level complete→minimizers result into the `MinExistenceData` interface. -/
def coordinate_minExistenceData
    {n : ℕ} :
    MinExistenceData (Exponential.Coordinate.Position n) where
  complete_minimizers := coordinate_complete_implies_minimizers

/-! ### Geodesic extension for Position n (L∞ metric)

The proof uses the "active coordinate" method: near the endpoint of a geodesic segment,
at least one coordinate moves at full speed. Extending that coordinate linearly (while
freezing the others) produces a local geodesic extension. -/

section GeodesicExtension

variable {n : ℕ}

private theorem constant_isGeodesicLineWithSpeed_zero
    (p : Exponential.Coordinate.Position n) :
    IsGeodesicLineWithSpeed (Exponential.Coordinate.Position n) (fun _ => p) 0 := by
  refine ⟨le_rfl, ?_⟩
  intro t₁ t₂ _ _
  simp

private theorem norm_coordinateBasisVector
    (i : Fin n) :
    ‖ParallelTransport.coordinateBasisVector (n := n) i‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    by_cases h : j = i
    · subst h
      simp [ParallelTransport.coordinateBasisVector]
    · simp [ParallelTransport.coordinateBasisVector, h]
  · have h := norm_le_pi_norm (ParallelTransport.coordinateBasisVector (n := n) i) i
    simpa [ParallelTransport.coordinateBasisVector] using h

private theorem exists_norm_eq_coordinate
    (hn : Nonempty (Fin n))
    (x : Exponential.Coordinate.Position n) :
    ∃ i : Fin n, ‖x i‖ = ‖x‖ := by
  classical
  let s : Finset (Fin n) := Finset.univ
  have hs : s.Nonempty := by simp [s]
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup' (s := s) hs (fun j => ‖x j‖)
  refine ⟨i, le_antisymm ?_ ?_⟩
  · exact norm_le_pi_norm x i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 ?_
    intro j
    rw [← hsup]
    exact Finset.le_sup' (f := fun k => ‖x k‖) (by simp [s])

private noncomputable def coordSign (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

private theorem abs_coordSign (x : ℝ) :
    |coordSign x| = 1 := by
  unfold coordSign
  split_ifs <;> simp

private theorem coordSign_sq (x : ℝ) :
    coordSign x ^ 2 = 1 := by
  unfold coordSign
  split_ifs <;> ring

private theorem coordSign_mul_eq_abs (x : ℝ) :
    coordSign x * x = |x| := by
  unfold coordSign
  split_ifs with hx
  · rw [abs_of_nonneg hx]
    ring
  · rw [abs_of_neg (lt_of_not_ge hx)]
    ring

private theorem coord_lipschitz_of_geodesic
    {γ : ℝ → Exponential.Coordinate.Position n} {a b c : ℝ}
    (hγ : IsGeodesicOnWithSpeed (Exponential.Coordinate.Position n) γ c (Set.Icc a b))
    {i : Fin n} {s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) :
    |γ s i - γ t i| ≤ c * |s - t| := by
  calc
    |γ s i - γ t i| = ‖(γ s - γ t) i‖ := by simp
    _ ≤ ‖γ s - γ t‖ := norm_le_pi_norm _ i
    _ = dist (γ s) (γ t) := by rw [dist_eq_norm]
    _ = c * |s - t| := hγ.2 hs ht

/-- Lipschitz squeeze: if f is L-Lipschitz on an interval and achieves |f(s₀) - f(b)| = L(b - s₀)
with a definite sign, then f(s) - f(b) = L(b - s) for all s between s₀ and b.

Proof: Lipschitz gives f(s)-f(b) ≤ L(b-s) (upper from (s,b) pair).
And f(s₀)-f(s) ≤ L(s-s₀) (from (s₀,s) pair), combined with the known
f(s₀)-f(b) = L(b-s₀), gives f(s)-f(b) ≥ L(b-s). -/
private theorem lipschitz_squeeze_right
    {f : ℝ → ℝ} {L : ℝ} (_hL : 0 ≤ L)
    (hLip : ∀ s t : ℝ, |f s - f t| ≤ L * |s - t|)
    {s₀ b : ℝ} (_hs₀b : s₀ ≤ b)
    (hval : f s₀ - f b = L * (b - s₀)) :
    ∀ s, s₀ ≤ s → s ≤ b → f s - f b = L * (b - s) := by
  intro s hs₀s hsb
  have hupper : f s - f b ≤ L * (b - s) := by
    have := hLip s b
    have habs : |f s - f b| ≤ L * (b - s) := by
      calc |f s - f b| ≤ L * |s - b| := this
        _ = L * (b - s) := by rw [abs_of_nonpos (by linarith)]; ring
    linarith [le_abs_self (f s - f b)]
  have hlower : L * (b - s) ≤ f s - f b := by
    have h1 : f s₀ - f s ≤ L * (s - s₀) := by
      have := hLip s₀ s
      have : |f s₀ - f s| ≤ L * (s - s₀) := by
        calc |f s₀ - f s| ≤ L * |s₀ - s| := this
          _ = L * (s - s₀) := by rw [abs_of_nonpos (by linarith)]; ring
      linarith [le_abs_self (f s₀ - f s)]
    -- f(s₀) - f(b) = L(b - s₀) and f(s₀) - f(s) ≤ L(s - s₀)
    -- so f(s) - f(b) = f(s₀) - f(b) - (f(s₀) - f(s)) ≥ L(b - s₀) - L(s - s₀) = L(b - s)
    linarith
  linarith

private theorem lipschitz_squeeze_right_on
    {f : ℝ → ℝ} {L s₀ b : ℝ} (_hL : 0 ≤ L)
    (hLip : ∀ ⦃s t : ℝ⦄, s₀ ≤ s → s ≤ b → s₀ ≤ t → t ≤ b → |f s - f t| ≤ L * |s - t|)
    (hs₀b : s₀ ≤ b)
    (hval : f s₀ - f b = L * (b - s₀)) :
    ∀ s, s₀ ≤ s → s ≤ b → f s - f b = L * (b - s) := by
  intro s hs₀s hsb
  have hupper : f s - f b ≤ L * (b - s) := by
    have habs : |f s - f b| ≤ L * (b - s) := by
      calc
        |f s - f b| ≤ L * |s - b| := hLip hs₀s hsb hs₀b le_rfl
        _ = L * (b - s) := by rw [abs_of_nonpos (by linarith)]; ring
    linarith [le_abs_self (f s - f b)]
  have hlower : L * (b - s) ≤ f s - f b := by
    have h1 : f s₀ - f s ≤ L * (s - s₀) := by
      have habs : |f s₀ - f s| ≤ L * (s - s₀) := by
        calc
          |f s₀ - f s| ≤ L * |s₀ - s| := hLip le_rfl hs₀b hs₀s hsb
          _ = L * (s - s₀) := by rw [abs_of_nonpos (by linarith)]; ring
      linarith [le_abs_self (f s₀ - f s)]
    linarith
  linarith

private theorem lipschitz_squeeze_left_on
    {f : ℝ → ℝ} {L a t₁ : ℝ} (_hL : 0 ≤ L)
    (hLip : ∀ ⦃s t : ℝ⦄, a ≤ s → s ≤ t₁ → a ≤ t → t ≤ t₁ → |f s - f t| ≤ L * |s - t|)
    (hat₁ : a ≤ t₁)
    (hval : f t₁ - f a = L * (t₁ - a)) :
    ∀ s, a ≤ s → s ≤ t₁ → f s - f a = L * (s - a) := by
  intro s has hst₁
  have hupper : f s - f a ≤ L * (s - a) := by
    have habs : |f s - f a| ≤ L * (s - a) := by
      calc
        |f s - f a| ≤ L * |s - a| := hLip has hst₁ le_rfl hat₁
        _ = L * (s - a) := by rw [abs_of_nonneg (by linarith)]
    linarith [le_abs_self (f s - f a)]
  have hlower : L * (s - a) ≤ f s - f a := by
    have h1 : f t₁ - f s ≤ L * (t₁ - s) := by
      have habs : |f t₁ - f s| ≤ L * (t₁ - s) := by
        calc
          |f t₁ - f s| ≤ L * |t₁ - s| := hLip hat₁ le_rfl has hst₁
          _ = L * (t₁ - s) := by rw [abs_of_nonneg (by linarith)]
      linarith [le_abs_self (f t₁ - f s)]
    linarith
  linarith

private def coordinateRayFrom
    (p : Exponential.Coordinate.Position n)
    (i : Fin n) (v t₀ : ℝ) :
    ℝ → Exponential.Coordinate.Position n :=
  fun t =>
    p + (t - t₀) • (v • ParallelTransport.coordinateBasisVector (n := n) i)

@[simp] private theorem coordinateRayFrom_apply_eq
    (p : Exponential.Coordinate.Position n)
    (i : Fin n) (v t₀ t : ℝ) :
    coordinateRayFrom (n := n) p i v t₀ t i = p i + (t - t₀) * v := by
  simp [coordinateRayFrom, ParallelTransport.coordinateBasisVector]

@[simp] private theorem coordinateRayFrom_apply_ne
    (p : Exponential.Coordinate.Position n)
    {i j : Fin n} (h : j ≠ i) (v t₀ t : ℝ) :
    coordinateRayFrom (n := n) p i v t₀ t j = p j := by
  simp [coordinateRayFrom, ParallelTransport.coordinateBasisVector, h]

private theorem coordinateRayFrom_sub
    (p : Exponential.Coordinate.Position n)
    (i : Fin n) (v t₀ t₁ t₂ : ℝ) :
    coordinateRayFrom (n := n) p i v t₀ t₁ -
      coordinateRayFrom (n := n) p i v t₀ t₂ =
        (t₁ - t₂) • (v • ParallelTransport.coordinateBasisVector (n := n) i) := by
  ext j
  by_cases h : j = i
  · subst h
    simp [coordinateRayFrom, ParallelTransport.coordinateBasisVector]
    ring
  · simp [coordinateRayFrom, ParallelTransport.coordinateBasisVector, h]

private theorem coordinateRayFrom_isGeodesicLineWithSpeed
    (p : Exponential.Coordinate.Position n)
    (i : Fin n) {v c t₀ : ℝ}
    (hc : 0 ≤ c) (hv : |v| = c) :
    IsGeodesicLineWithSpeed
      (Exponential.Coordinate.Position n)
      (coordinateRayFrom (n := n) p i v t₀) c := by
  refine ⟨hc, ?_⟩
  intro t₁ t₂ _ _
  rw [dist_eq_norm, coordinateRayFrom_sub]
  calc
    ‖(t₁ - t₂) • (v • ParallelTransport.coordinateBasisVector (n := n) i)‖
      = |t₁ - t₂| * ‖v • ParallelTransport.coordinateBasisVector (n := n) i‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = |t₁ - t₂| * (|v| * ‖ParallelTransport.coordinateBasisVector (n := n) i‖) := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = |t₁ - t₂| * c := by rw [norm_coordinateBasisVector, hv, mul_one]
    _ = c * |t₁ - t₂| := by ring


/-- Active coordinate squeeze for a geodesic on [a,b]: the coordinate i₀ that achieves the
L∞ distance between γ(a) and γ(b) satisfies the Lipschitz equality throughout [a,b].

Specifically, if `σ * (γ a i₀ - γ b i₀) = c(b-a)`, then
`σ * (γ s i₀ - γ b i₀) = c(b-s)` for all s ∈ [a,b]. -/
private theorem active_coord_squeeze
    {γ : ℝ → Exponential.Coordinate.Position n} {a b c : ℝ}
    (hc : 0 ≤ c)
    (hγ : IsGeodesicOnWithSpeed (Exponential.Coordinate.Position n) γ c (Set.Icc a b))
    (hab : a ≤ b)
    {i₀ : Fin n} {σ : ℝ} (hσ : |σ| = 1)
    (hval : σ * (γ a i₀ - γ b i₀) = c * (b - a)) :
    ∀ s, a ≤ s → s ≤ b → σ * (γ s i₀ - γ b i₀) = c * (b - s) := by
  -- Use lipschitz_squeeze_right_on with f = fun t => σ * (γ t i₀ - γ b i₀)
  -- which is L-Lipschitz with L = c (since each coordinate is c-Lipschitz and σ has abs 1)
  -- and f(a) - f(b) = σ * (γ a i₀ - γ b i₀) - 0 = c * (b - a) = c * (b - a)
  have hLip : ∀ ⦃s t : ℝ⦄, a ≤ s → s ≤ b → a ≤ t → t ≤ b →
      |σ * (γ s i₀ - γ b i₀) - σ * (γ t i₀ - γ b i₀)| ≤ c * |s - t| := by
    intro s t has hsb hat htb
    rw [show σ * (γ s i₀ - γ b i₀) - σ * (γ t i₀ - γ b i₀) = σ * (γ s i₀ - γ t i₀) from by ring]
    rw [abs_mul, hσ, one_mul]
    exact coord_lipschitz_of_geodesic hγ ⟨has, hsb⟩ ⟨hat, htb⟩
  have hfb : σ * (γ b i₀ - γ b i₀) = 0 := by ring
  -- Apply right squeeze: f(a) - f(b) = c(b-a), so f(s) - f(b) = c(b-s)
  intro s has hsb
  have hsq := lipschitz_squeeze_right_on hc hLip hab
    (by rw [hval]; rw [hfb]; ring) s has hsb
  linarith

/-- Value form of active coordinate squeeze: the active coordinate of γ at time s equals
the coordinate ray value. -/
private theorem active_coord_value
    {γ : ℝ → Exponential.Coordinate.Position n} {a b c : ℝ}
    (hc : 0 ≤ c)
    (hγ : IsGeodesicOnWithSpeed (Exponential.Coordinate.Position n) γ c (Set.Icc a b))
    (hab : a ≤ b)
    {i₀ : Fin n} {σ : ℝ} (hσsq : σ ^ 2 = 1)
    (hval : σ * (γ a i₀ - γ b i₀) = c * (b - a)) :
    ∀ s, a ≤ s → s ≤ b →
      γ s i₀ = γ b i₀ + σ * c * (b - s) := by
  intro s has hsb
  have hσσ : σ * σ = 1 := by nlinarith
  have hσne : σ ≠ 0 := by intro h; simp [h] at hσsq
  have hσabs : |σ| = 1 := by
    have habs_sq : |σ| ^ 2 = 1 := by rw [sq_abs]; exact hσsq
    have habs_nn : 0 ≤ |σ| := abs_nonneg σ
    nlinarith [sq_nonneg (|σ| - 1)]
  have hsq := active_coord_squeeze hc hγ hab hσabs hval s has hsb
  -- σ * (γ s i₀ - γ b i₀) = c * (b - s), goal: γ s i₀ = γ b i₀ + σ * c * (s - b)
  -- From hsq: γ s i₀ - γ b i₀ = (1/σ) * c * (b - s) = σ * c * (b - s) since σ² = 1
  have key : γ s i₀ - γ b i₀ = σ * c * (b - s) := by
    have := congr_arg (σ * ·) hsq
    simp only [← mul_assoc] at this
    rw [show σ * σ = (1 : ℝ) from hσσ, one_mul] at this
    linarith
  linarith


/-- Subsegment calibration: the active coordinate calibrates EVERY subsegment [s,t] ⊆ [a,b].
Specifically, `σ(γ s j - γ t j) = c(t - s)` for all a ≤ s ≤ t ≤ b. -/
private theorem active_coord_subsegment
    {γ : ℝ → Exponential.Coordinate.Position n} {a b c : ℝ}
    (hc : 0 ≤ c)
    (hγ : IsGeodesicOnWithSpeed (Exponential.Coordinate.Position n) γ c (Set.Icc a b))
    (hab : a ≤ b)
    {i₀ : Fin n} {σ : ℝ} (hσ : |σ| = 1)
    (hval : σ * (γ a i₀ - γ b i₀) = c * (b - a))
    {s t : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    σ * (γ s i₀ - γ t i₀) = c * (t - s) := by
  have hs := active_coord_squeeze hc hγ hab hσ hval s has (le_trans hst htb)
  have ht := active_coord_squeeze hc hγ hab hσ hval t (le_trans has hst) htb
  -- σ(γ s j - γ b j) = c(b-s) and σ(γ t j - γ b j) = c(b-t)
  -- Subtract: σ(γ s j - γ t j) = c(b-s) - c(b-t) = c(t-s)
  linarith

/-- The chord tail: extending a geodesic beyond b by the chord direction γ(b) - γ(a). -/
private noncomputable def chordExtension
    (γ : ℝ → Exponential.Coordinate.Position n)
    (a b : ℝ) :
    ℝ → Exponential.Coordinate.Position n :=
  fun t => γ b + ((t - b) / (b - a)) • (γ b - γ a)

@[simp] private theorem chordExtension_at_b
    {γ : ℝ → Exponential.Coordinate.Position n} {a b : ℝ} :
    chordExtension (n := n) γ a b b = γ b := by
  simp [chordExtension]

private theorem chordExtension_coord
    {γ : ℝ → Exponential.Coordinate.Position n} {a b : ℝ} (i : Fin n) (t : ℝ) :
    chordExtension (n := n) γ a b t i = γ b i + ((t - b) / (b - a)) * (γ b i - γ a i) := by
  simp [chordExtension, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]

private theorem chordExtension_coord_left
    {γ : ℝ → Exponential.Coordinate.Position n} {a b : ℝ}
    (hab : a < b) (i : Fin n) (t : ℝ) :
    chordExtension (n := n) γ a b t i =
      γ a i + ((t - a) / (b - a)) * (γ b i - γ a i) := by
  have hne : b - a ≠ 0 := by linarith
  rw [chordExtension_coord]
  field_simp [hne]
  ring

@[simp] private theorem chordExtension_at_a
    {γ : ℝ → Exponential.Coordinate.Position n} {a b : ℝ}
    (hab : a < b) :
    chordExtension (n := n) γ a b a = γ a := by
  ext i
  rw [chordExtension_coord_left hab]
  simp

/-- Crossing distance at the right junction: for s ∈ [a,b] and t ≥ b, the distance between
the original geodesic and the chord extension equals c(t-s).

Key idea: the active coordinate achieves c(t-s) (lower bound), and the triangle
inequality gives the upper bound. -/
private theorem crossing_dist_chord_right
    {γ : ℝ → Exponential.Coordinate.Position n} {a b c : ℝ}
    (hc : 0 ≤ c) (hab : a < b)
    (hγ : IsGeodesicOnWithSpeed (Exponential.Coordinate.Position n) γ c (Set.Icc a b))
    {i₀ : Fin n} {σ : ℝ} (hσ : |σ| = 1)
    (hσval : σ * (γ a i₀ - γ b i₀) = c * (b - a))
    {s t : ℝ} (has : a ≤ s) (hsb : s ≤ b) (hbt : b ≤ t) :
    dist (γ s) (chordExtension (n := n) γ a b t) = c * (t - s) := by
  have hba : (0 : ℝ) < b - a := by linarith
  -- Lower bound: the active coordinate achieves c(t-s)
  have hlower : c * (t - s) ≤ dist (γ s) (chordExtension (n := n) γ a b t) := by
    rw [dist_eq_norm]
    -- The active coordinate difference
    have hcoord : σ * ((γ s - chordExtension (n := n) γ a b t) i₀) = c * (t - s) := by
      simp only [Pi.sub_apply, chordExtension_coord]
      have hsq_s := active_coord_squeeze hc hγ hab.le hσ hσval s has hsb
      -- σ(γ s i₀ - γ b i₀) = c(b-s), σ(γ a i₀ - γ b i₀) = c(b-a)
      -- σ * ((γ s i₀ - γ b i₀) - ((t-b)/(b-a)) * (γ b i₀ - γ a i₀))
      -- = c(b-s) - ((t-b)/(b-a)) * σ(γ b i₀ - γ a i₀)
      -- = c(b-s) - ((t-b)/(b-a)) * (-(c(b-a)))
      -- = c(b-s) + c(t-b) = c(t-s)
      have hσΔ : σ * (γ b i₀ - γ a i₀) = -(c * (b - a)) := by linarith
      have hne : (b - a) ≠ 0 := by linarith
      rw [show σ * (γ s i₀ - (γ b i₀ + (t - b) / (b - a) * (γ b i₀ - γ a i₀))) =
        σ * (γ s i₀ - γ b i₀) - (t - b) / (b - a) * (σ * (γ b i₀ - γ a i₀)) from by ring]
      rw [hsq_s, hσΔ]
      field_simp
      ring
    have habs : |(γ s - chordExtension (n := n) γ a b t) i₀| = c * (t - s) := by
      have h1 : |σ| * |(γ s - chordExtension (n := n) γ a b t) i₀| = c * (t - s) := by
        rw [← abs_mul, hcoord, abs_of_nonneg (by nlinarith)]
      rwa [hσ, one_mul] at h1
    linarith [norm_le_pi_norm (γ s - chordExtension (n := n) γ a b t) i₀,
      (Real.norm_eq_abs ((γ s - chordExtension (n := n) γ a b t) i₀)).symm ▸ habs]
  -- Upper bound: triangle inequality through γ(b)
  have hdist_sb : dist (γ s) (γ b) = c * (b - s) := by
    have := hγ.2 ⟨has, hsb⟩ ⟨hab.le, le_rfl⟩
    rwa [abs_of_nonpos (by linarith : s - b ≤ 0), neg_sub] at this
  have hdist_ab : dist (γ a) (γ b) = c * (b - a) := by
    have := hγ.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
    rwa [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at this
  have hdist_bt : dist (γ b) (chordExtension (n := n) γ a b t) = c * (t - b) := by
    rw [dist_eq_norm]
    have : γ b - chordExtension (n := n) γ a b t =
        -(((t - b) / (b - a)) • (γ b - γ a)) := by
      ext i; simp [chordExtension_coord, Pi.sub_apply, smul_eq_mul]
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_nonneg (by linarith), abs_of_pos hba, ← dist_eq_norm, dist_comm]
    rw [hdist_ab]; field_simp
  have hupper : dist (γ s) (chordExtension (n := n) γ a b t) ≤ c * (t - s) := by
    calc dist (γ s) (chordExtension (n := n) γ a b t)
        ≤ dist (γ s) (γ b) + dist (γ b) (chordExtension (n := n) γ a b t) :=
          dist_triangle _ _ _
      _ = c * (b - s) + c * (t - b) := by rw [hdist_sb, hdist_bt]
      _ = c * (t - s) := by ring
  linarith

/-- Crossing distance at the left junction: for s ≤ a and t ∈ [a,b], the distance between
the chord extension and the original geodesic equals c(t-s). -/
private theorem crossing_dist_chord_left
    {γ : ℝ → Exponential.Coordinate.Position n} {a b c : ℝ}
    (hc : 0 ≤ c) (hab : a < b)
    (hγ : IsGeodesicOnWithSpeed (Exponential.Coordinate.Position n) γ c (Set.Icc a b))
    {i₀ : Fin n} {σ : ℝ} (hσ : |σ| = 1)
    (hσval : σ * (γ a i₀ - γ b i₀) = c * (b - a))
    {s t : ℝ} (hsa : s ≤ a) (hat : a ≤ t) (htb : t ≤ b) :
    dist (chordExtension (n := n) γ a b s) (γ t) = c * (t - s) := by
  have hlower : c * (t - s) ≤ dist (chordExtension (n := n) γ a b s) (γ t) := by
    rw [dist_eq_norm]
    have hcoord : σ * ((chordExtension (n := n) γ a b s - γ t) i₀) = c * (t - s) := by
      simp only [Pi.sub_apply, chordExtension_coord_left hab]
      have hsq_t : σ * (γ a i₀ - γ t i₀) = c * (t - a) := by
        simpa using active_coord_subsegment hc hγ hab.le hσ hσval le_rfl hat htb
      have hσΔ : σ * (γ b i₀ - γ a i₀) = -(c * (b - a)) := by
        linarith
      have hne : (b - a) ≠ 0 := by
        linarith
      rw [show σ * (γ a i₀ + (s - a) / (b - a) * (γ b i₀ - γ a i₀) - γ t i₀) =
          σ * (γ a i₀ - γ t i₀) + (s - a) / (b - a) * (σ * (γ b i₀ - γ a i₀)) from by ring]
      rw [hsq_t, hσΔ]
      field_simp [hne]
      ring
    have habs : |(chordExtension (n := n) γ a b s - γ t) i₀| = c * (t - s) := by
      have h1 : |σ| * |(chordExtension (n := n) γ a b s - γ t) i₀| = c * (t - s) := by
        rw [← abs_mul, hcoord, abs_of_nonneg (by nlinarith)]
      rwa [hσ, one_mul] at h1
    linarith [norm_le_pi_norm (chordExtension (n := n) γ a b s - γ t) i₀,
      (Real.norm_eq_abs ((chordExtension (n := n) γ a b s - γ t) i₀)).symm ▸ habs]
  have hba : (0 : ℝ) < b - a := by
    linarith
  have hdist_ab : dist (γ a) (γ b) = c * (b - a) := by
    have := hγ.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
    rwa [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at this
  have hdist_sa : dist (chordExtension (n := n) γ a b s) (γ a) = c * (a - s) := by
    rw [dist_eq_norm]
    have : chordExtension (n := n) γ a b s - γ a =
        ((s - a) / (b - a)) • (γ b - γ a) := by
      ext i
      simp [chordExtension_coord_left hab, smul_eq_mul]
    rw [this, norm_smul, Real.norm_eq_abs, abs_div,
      abs_of_nonpos (by linarith : s - a ≤ 0), abs_of_pos hba,
      ← dist_eq_norm, dist_comm, hdist_ab]
    field_simp
    ring
  have hdist_at : dist (γ a) (γ t) = c * (t - a) := by
    have := hγ.2 ⟨le_rfl, hab.le⟩ ⟨hat, htb⟩
    rwa [abs_of_nonpos (by linarith : a - t ≤ 0), neg_sub] at this
  have hupper : dist (chordExtension (n := n) γ a b s) (γ t) ≤ c * (t - s) := by
    calc
      dist (chordExtension (n := n) γ a b s) (γ t)
          ≤ dist (chordExtension (n := n) γ a b s) (γ a) + dist (γ a) (γ t) :=
            dist_triangle _ _ _
      _ = c * (a - s) + c * (t - a) := by rw [hdist_sa, hdist_at]
      _ = c * (t - s) := by ring
  linarith

/-- The chord extension is a global geodesic line with speed c. -/
private theorem chordExtension_isGeodesicLineWithSpeed
    {γ : ℝ → Exponential.Coordinate.Position n} {a b c : ℝ}
    (hc : 0 ≤ c) (hab : a < b)
    (hγ : IsGeodesicOnWithSpeed (Exponential.Coordinate.Position n) γ c (Set.Icc a b)) :
    IsGeodesicLineWithSpeed (Exponential.Coordinate.Position n)
      (chordExtension (n := n) γ a b) c := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hdist_ab : dist (γ a) (γ b) = c * (b - a) := by
    have := hγ.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
    rwa [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at this
  refine ⟨hc, fun t₁ t₂ _ _ => ?_⟩
  rw [dist_eq_norm]
  have : chordExtension (n := n) γ a b t₁ - chordExtension (n := n) γ a b t₂ =
      ((t₁ - t₂) / (b - a)) • (γ b - γ a) := by
    ext i; simp [chordExtension_coord, smul_eq_mul]; ring
  rw [this, norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hba,
    ← dist_eq_norm, dist_comm, hdist_ab]
  rw [show |t₁ - t₂| / (b - a) * (c * (b - a)) = c * |t₁ - t₂| from by
    field_simp]

private noncomputable def segmentChordExtension
    (γ : ℝ → Exponential.Coordinate.Position n)
    (a b : ℝ) :
    ℝ → Exponential.Coordinate.Position n :=
  fun t => if _h : t ∈ Set.Icc a b then γ t else chordExtension (n := n) γ a b t

@[simp] private theorem segmentChordExtension_of_mem
    {γ : ℝ → Exponential.Coordinate.Position n} {a b t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    segmentChordExtension (n := n) γ a b t = γ t := by
  simp [segmentChordExtension, ht]

@[simp] private theorem segmentChordExtension_of_not_mem
    {γ : ℝ → Exponential.Coordinate.Position n} {a b t : ℝ}
    (ht : t ∉ Set.Icc a b) :
    segmentChordExtension (n := n) γ a b t = chordExtension (n := n) γ a b t := by
  simp [segmentChordExtension, ht]

@[simp] private theorem segmentChordExtension_of_lt_a
    {γ : ℝ → Exponential.Coordinate.Position n} {a b t : ℝ}
    (ht : t < a) :
    segmentChordExtension (n := n) γ a b t = chordExtension (n := n) γ a b t := by
  refine segmentChordExtension_of_not_mem (n := n) ?_
  intro hmem
  exact (not_le_of_gt ht) hmem.1

@[simp] private theorem segmentChordExtension_of_gt_b
    {γ : ℝ → Exponential.Coordinate.Position n} {a b t : ℝ}
    (ht : b < t) :
    segmentChordExtension (n := n) γ a b t = chordExtension (n := n) γ a b t := by
  refine segmentChordExtension_of_not_mem (n := n) ?_
  intro hmem
  exact (not_le_of_gt ht) hmem.2

@[simp] private theorem segmentChordExtension_of_Icc
    {γ : ℝ → Exponential.Coordinate.Position n} {a b t : ℝ}
    (hat : a ≤ t) (htb : t ≤ b) :
    segmentChordExtension (n := n) γ a b t = γ t := by
  exact segmentChordExtension_of_mem (n := n) ⟨hat, htb⟩

@[simp] private theorem segmentChordExtension_at_a
    {γ : ℝ → Exponential.Coordinate.Position n} {a b : ℝ}
    (hab : a < b) :
    segmentChordExtension (n := n) γ a b a = γ a := by
  simp [segmentChordExtension, hab.le]

@[simp] private theorem segmentChordExtension_at_b
    {γ : ℝ → Exponential.Coordinate.Position n} {a b : ℝ}
    (hab : a < b) :
    segmentChordExtension (n := n) γ a b b = γ b := by
  simp [segmentChordExtension, hab.le]

/-- At the coordinate level, every constant-speed geodesic segment in the L∞ metric extends
to a global local geodesic line.

The extension uses the **chord direction** `γ(b) - γ(a)`, not a local derivative.
The global active coordinate calibrates the full segment and the crossing distance
is proved via the calibration + triangle inequality. -/
theorem coordinate_hasGeodesicExtension :
    HasGeodesicExtension (Exponential.Coordinate.Position n) := by
  intro a b c hab hc γ hγ
  by_cases hn : Nonempty (Fin n)
  · obtain ⟨i₀, hi₀⟩ := exists_norm_eq_coordinate (n := n) hn (γ a - γ b)
    set σ : ℝ := coordSign ((γ a - γ b) i₀)
    have hσ : |σ| = 1 := by
      simpa [σ] using abs_coordSign ((γ a - γ b) i₀)
    have hdist_ab : dist (γ a) (γ b) = c * (b - a) := by
      have := hγ.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
      rwa [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at this
    have hσval : σ * (γ a i₀ - γ b i₀) = c * (b - a) := by
      calc
        σ * (γ a i₀ - γ b i₀)
            = |(γ a - γ b) i₀| := by
                simpa [σ, Pi.sub_apply] using coordSign_mul_eq_abs ((γ a - γ b) i₀)
        _ = ‖(γ a - γ b) i₀‖ := by simp
        _ = ‖γ a - γ b‖ := hi₀
        _ = dist (γ a) (γ b) := by rw [dist_eq_norm]
        _ = c * (b - a) := hdist_ab
    refine ⟨segmentChordExtension (n := n) γ a b, ?_, ?_⟩
    · have hchord := chordExtension_isGeodesicLineWithSpeed (n := n) hc hab hγ
      intro t
      by_cases hta : t < a
      · refine ⟨(a - t) / 2, by nlinarith, ?_⟩
        refine ⟨hchord.1, ?_⟩
        intro s u hs hu
        have hsa : s < a := by
          have hs_upper : s ≤ t + (a - t) / 2 := hs.2
          linarith
        have hua : u < a := by
          have hu_upper : u ≤ t + (a - t) / 2 := hu.2
          linarith
        calc
          dist (segmentChordExtension (n := n) γ a b s)
              (segmentChordExtension (n := n) γ a b u)
              = dist (chordExtension (n := n) γ a b s)
                  (chordExtension (n := n) γ a b u) := by
                    simp [hsa, hua]
          _ = c * |s - u| := hchord.2 (by simp) (by simp)
      · have hat : a ≤ t := le_of_not_gt hta
        by_cases hta_eq : t = a
        · subst t
          refine ⟨(b - a) / 2, by nlinarith, ?_⟩
          refine ⟨hc, ?_⟩
          intro s u hs hu
          have hupper : a + (b - a) / 2 < b := by
            nlinarith
          by_cases hsI : s ∈ Set.Icc a b
          case pos =>
            by_cases huI : u ∈ Set.Icc a b
            · simpa [segmentChordExtension_of_mem (n := n) hsI,
                segmentChordExtension_of_mem (n := n) huI] using hγ.2 hsI huI
            · have hua : u < a := by
                by_cases hua : u < a
                · exact hua
                · have hau : a ≤ u := le_of_not_gt hua
                  have hub : u ≤ b := le_trans hu.2 hupper.le
                  exact False.elim (huI ⟨hau, hub⟩)
              have hcross := crossing_dist_chord_left (n := n) hc hab hγ hσ hσval
                (show u ≤ a by linarith) hsI.1 hsI.2
              calc
                dist (segmentChordExtension (n := n) γ a b s)
                    (segmentChordExtension (n := n) γ a b u)
                    = dist (γ s) (chordExtension (n := n) γ a b u) := by
                        simp [hsI, hua]
                _ = dist (chordExtension (n := n) γ a b u) (γ s) := by rw [dist_comm]
                _ = c * (s - u) := hcross
                _ = c * |s - u| := by
                    have hsu : 0 ≤ s - u := by
                      linarith [hsI.1, hua]
                    rw [abs_of_nonneg hsu]
          case neg =>
            have hsa : s < a := by
              by_cases hsa : s < a
              · exact hsa
              · have has : a ≤ s := le_of_not_gt hsa
                have hsb : s ≤ b := le_trans hs.2 hupper.le
                exact False.elim (hsI ⟨has, hsb⟩)
            by_cases huI : u ∈ Set.Icc a b
            · have hcross := crossing_dist_chord_left (n := n) hc hab hγ hσ hσval
                (show s ≤ a by linarith) huI.1 huI.2
              calc
                dist (segmentChordExtension (n := n) γ a b s)
                    (segmentChordExtension (n := n) γ a b u)
                    = dist (chordExtension (n := n) γ a b s) (γ u) := by
                        simp [hsa, huI]
                _ = c * (u - s) := hcross
                _ = c * |s - u| := by
                    have hsu : s - u ≤ 0 := by
                      linarith [hsa, huI.1]
                    rw [abs_of_nonpos hsu]
                    ring
            · have hua : u < a := by
                by_cases hua : u < a
                · exact hua
                · have hau : a ≤ u := le_of_not_gt hua
                  have hub : u ≤ b := le_trans hu.2 hupper.le
                  exact False.elim (huI ⟨hau, hub⟩)
              calc
                dist (segmentChordExtension (n := n) γ a b s)
                    (segmentChordExtension (n := n) γ a b u)
                    = dist (chordExtension (n := n) γ a b s)
                        (chordExtension (n := n) γ a b u) := by
                            simp [hsa, hua]
                _ = c * |s - u| := hchord.2 (by simp) (by simp)
        · by_cases hbt : b < t
          · refine ⟨(t - b) / 2, by nlinarith, ?_⟩
            refine ⟨hchord.1, ?_⟩
            intro s u hs hu
            have hbs : b < s := by
              have hs_lower : t - (t - b) / 2 ≤ s := hs.1
              linarith
            have hbu : b < u := by
              have hu_lower : t - (t - b) / 2 ≤ u := hu.1
              linarith
            calc
              dist (segmentChordExtension (n := n) γ a b s)
                  (segmentChordExtension (n := n) γ a b u)
                  = dist (chordExtension (n := n) γ a b s)
                      (chordExtension (n := n) γ a b u) := by
                          simp [hbs, hbu]
              _ = c * |s - u| := hchord.2 (by simp) (by simp)
          · have htb : t ≤ b := le_of_not_gt hbt
            by_cases htb_eq : t = b
            · subst t
              refine ⟨(b - a) / 2, by nlinarith, ?_⟩
              refine ⟨hc, ?_⟩
              intro s u hs hu
              have hlower : a < b - (b - a) / 2 := by
                nlinarith
              by_cases hsI : s ∈ Set.Icc a b
              · by_cases huI : u ∈ Set.Icc a b
                · simpa [segmentChordExtension_of_mem (n := n) hsI,
                    segmentChordExtension_of_mem (n := n) huI] using hγ.2 hsI huI
                · have hbu : b < u := by
                    by_cases hbu : b < u
                    · exact hbu
                    · have hub : u ≤ b := le_of_not_gt hbu
                      have hau : a ≤ u := le_trans hlower.le hu.1
                      exact False.elim (huI ⟨hau, hub⟩)
                  have hcross := crossing_dist_chord_right (n := n) hc hab hγ hσ hσval
                    hsI.1 hsI.2 (show b ≤ u by linarith)
                  calc
                    dist (segmentChordExtension (n := n) γ a b s)
                        (segmentChordExtension (n := n) γ a b u)
                        = dist (γ s) (chordExtension (n := n) γ a b u) := by
                            simp [hsI, hbu]
                    _ = c * (u - s) := hcross
                    _ = c * |s - u| := by
                        have hsu : s - u ≤ 0 := by
                          linarith [hsI.2, hbu]
                        rw [abs_of_nonpos hsu]
                        ring
              · have hbs : b < s := by
                  by_cases hbs : b < s
                  · exact hbs
                  · have hsb : s ≤ b := le_of_not_gt hbs
                    have has : a ≤ s := le_trans hlower.le hs.1
                    exact False.elim (hsI ⟨has, hsb⟩)
                by_cases huI : u ∈ Set.Icc a b
                · have hcross := crossing_dist_chord_right (n := n) hc hab hγ hσ hσval
                    huI.1 huI.2 (show b ≤ s by linarith)
                  calc
                    dist (segmentChordExtension (n := n) γ a b s)
                        (segmentChordExtension (n := n) γ a b u)
                        = dist (chordExtension (n := n) γ a b s) (γ u) := by
                            simp [hbs, huI]
                    _ = dist (γ u) (chordExtension (n := n) γ a b s) := by rw [dist_comm]
                    _ = c * (s - u) := hcross
                    _ = c * |s - u| := by
                        have hsu : 0 ≤ s - u := by
                          linarith [hbs, huI.2]
                        rw [abs_of_nonneg hsu]
                · have hbu : b < u := by
                    by_cases hbu : b < u
                    · exact hbu
                    · have hub : u ≤ b := le_of_not_gt hbu
                      have hau : a ≤ u := le_trans hlower.le hu.1
                      exact False.elim (huI ⟨hau, hub⟩)
                  calc
                    dist (segmentChordExtension (n := n) γ a b s)
                        (segmentChordExtension (n := n) γ a b u)
                        = dist (chordExtension (n := n) γ a b s)
                            (chordExtension (n := n) γ a b u) := by
                                simp [hbs, hbu]
                    _ = c * |s - u| := hchord.2 (by simp) (by simp)
            · have hat_lt : a < t := lt_of_le_of_ne hat (Ne.symm hta_eq)
              have htb_lt : t < b := lt_of_le_of_ne htb htb_eq
              have hmin_pos : 0 < min (t - a) (b - t) := by
                apply lt_min <;> linarith
              have hleft : t - min (t - a) (b - t) / 2 > a := by
                have hlt : min (t - a) (b - t) / 2 < t - a := by
                  have hhalf : min (t - a) (b - t) / 2 < min (t - a) (b - t) := by
                    nlinarith
                  exact lt_of_lt_of_le hhalf (min_le_left _ _)
                linarith
              have hright : t + min (t - a) (b - t) / 2 < b := by
                have hlt : min (t - a) (b - t) / 2 < b - t := by
                  have hhalf : min (t - a) (b - t) / 2 < min (t - a) (b - t) := by
                    nlinarith
                  exact lt_of_lt_of_le hhalf (min_le_right _ _)
                linarith
              refine ⟨min (t - a) (b - t) / 2, by nlinarith, ?_⟩
              refine ⟨hc, ?_⟩
              intro s u hs hu
              have hsI : s ∈ Set.Icc a b := by
                constructor
                · linarith [hs.1, hleft]
                · linarith [hs.2, hright]
              have huI : u ∈ Set.Icc a b := by
                constructor
                · linarith [hu.1, hleft]
                · linarith [hu.2, hright]
              simpa [segmentChordExtension_of_mem (n := n) hsI,
                segmentChordExtension_of_mem (n := n) huI] using hγ.2 hsI huI
    · intro t ht
      simp [segmentChordExtension_of_mem (n := n) ht]
  · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    haveI : Subsingleton (Exponential.Coordinate.Position n) := by infer_instance
    have hdist_ab : dist (γ a) (γ b) = c * (b - a) := by
      have := hγ.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
      rwa [abs_of_nonpos (by linarith : a - b ≤ 0), neg_sub] at this
    have hc_zero : c = 0 := by
      have hsame : γ a = γ b := Subsingleton.elim _ _
      have hprod : c * (b - a) = 0 := by
        simpa [hsame] using hdist_ab.symm
      have hne : b - a ≠ 0 := by
        linarith
      exact (mul_eq_zero.mp hprod).resolve_right hne
    refine ⟨fun _ => γ a, ?_, ?_⟩
    · simpa [hc_zero] using
        (constant_isGeodesicLineWithSpeed_zero (n := n) (γ a)).isLocal
    · intro t ht
      exact Subsingleton.elim _ _

/-- Package the coordinate-level geodesic extension, eliminating both external claims. -/
def coordinate_geodesicExtensionData_direct :
    GeodesicExtensionData (Exponential.Coordinate.Position n) where
  complete_geodesic := fun _ => coordinate_hasGeodesicExtension

end GeodesicExtension

end HopfRinow
