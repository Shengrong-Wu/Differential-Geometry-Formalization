import Exponential.LocalInverse

/-! Normal-coordinate wrappers stay tied to the inverse-function-theorem source and target, while
the radial-source ownership remains in `Exponential/RadialBridge.lean`. -/

namespace Exponential.Coordinate

open scoped Topology
open Set

variable {n : ℕ}

/-- The partial homeomorphism furnished by the inverse function theorem for `coordinateExp Γ p`.
Its source is chosen to be a genuine ball around `0` contained in the spray-owned source
`coordinateExpSource`, so the downstream radial branch can use scaling arguments inside the
inverse-function-theorem chart. -/
noncomputable def coordinateExpPartialHomeomorph
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    OpenPartialHomeomorph (Velocity n) (Position n) := by
  let hf :=
    hasStrictFDerivAt_coordinateExp_at_zero (n := n) Gamma p
  let U : Set (Velocity n) := Classical.choose hf.approximates_deriv_on_open_nhds
  let hU := Classical.choose_spec hf.approximates_deriv_on_open_nhds
  have hU_nhds : U ∈ 𝓝 (0 : Velocity n) := hU.2.1.mem_nhds hU.1
  let ρ : ℝ := Classical.choose (Metric.mem_nhds_iff.mp hU_nhds)
  let hρ := Classical.choose_spec (Metric.mem_nhds_iff.mp hU_nhds)
  have hρ_pos : 0 < ρ := hρ.1
  have hρU : Metric.ball (0 : Velocity n) ρ ⊆ U := hρ.2
  let data :=
    Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 (baseState n p)
  let R : ℝ := data.ε * data.r
  have hR_pos : 0 < R := by
    dsimp [R]
    exact mul_pos data.hε data.hr
  let r : ℝ := min ρ R
  have hr_pos : 0 < r := by
    dsimp [r]
    exact lt_min hρ_pos hR_pos
  exact (hU.2.2.mono_set <| by
      intro x hx
      apply hρU
      rw [Metric.mem_ball] at hx ⊢
      exact lt_of_lt_of_le hx (by
        dsimp [r]
        exact min_le_left _ _)).toOpenPartialHomeomorph
    (coordinateExp (n := n) Gamma p)
    (Metric.ball (0 : Velocity n) r)
    (by
      exact
        (velocityPositionEquiv n).subsingleton_or_nnnorm_symm_pos.imp id fun h =>
          NNReal.half_lt_self <| ne_of_gt <| inv_pos.2 h)
    Metric.isOpen_ball

/-- The partial homeomorphism of normal coordinates, i.e. the local inverse of `coordinateExp Γ p`.
-/
noncomputable def normalCoordinateChart
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    OpenPartialHomeomorph (Position n) (Velocity n) :=
  (coordinateExpPartialHomeomorph (n := n) Gamma p).symm

/-- Normal coordinates near `p`: the local inverse of `coordinateExp Γ p`. Defined as the
symm of `coordinateExpPartialHomeomorph`, so that all roundtrip lemmas are consistent. -/
noncomputable def normalCoordinates
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    Position n → Velocity n :=
  (coordinateExpPartialHomeomorph (n := n) Gamma p).symm

@[simp] theorem zero_mem_coordinateExpPartialHomeomorph_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    (0 : Velocity n) ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source :=
by
  let data :=
    Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 (baseState n p)
  let R : ℝ := data.ε * data.r
  let hf := hasStrictFDerivAt_coordinateExp_at_zero (n := n) Gamma p
  let U : Set (Velocity n) := Classical.choose hf.approximates_deriv_on_open_nhds
  let hU := Classical.choose_spec hf.approximates_deriv_on_open_nhds
  have hU_nhds : U ∈ 𝓝 (0 : Velocity n) := hU.2.1.mem_nhds hU.1
  let ρ : ℝ := Classical.choose (Metric.mem_nhds_iff.mp hU_nhds)
  let hρ := Classical.choose_spec (Metric.mem_nhds_iff.mp hU_nhds)
  have hρ_pos : 0 < ρ := hρ.1
  have hρU : Metric.ball (0 : Velocity n) ρ ⊆ U := hρ.2
  let r : ℝ := min ρ R
  have hr_pos : 0 < r := by
    dsimp [r, R]
    exact lt_min hρ_pos (mul_pos data.hε data.hr)
  simpa [coordinateExpPartialHomeomorph, r, R, data, Metric.mem_ball, dist_eq_norm] using hr_pos

private theorem coordinateExpPartialHomeomorph_apply_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    (coordinateExpPartialHomeomorph (n := n) Gamma p) 0 = p := by
  simpa [coordinateExpPartialHomeomorph] using coordinateExp_zero (n := n) Gamma p

@[simp] theorem base_mem_coordinateExpPartialHomeomorph_target
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    p ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target := by
  have hmapped := (coordinateExpPartialHomeomorph (n := n) Gamma p).map_source
    (zero_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p)
  rwa [coordinateExpPartialHomeomorph_apply_zero (n := n) Gamma p] at hmapped

theorem normalCoordinates_base
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    normalCoordinates (n := n) Gamma p p = 0 := by
  show (coordinateExpPartialHomeomorph (n := n) Gamma p).symm p = 0
  have hleft := (coordinateExpPartialHomeomorph (n := n) Gamma p).left_inv
    (zero_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p)
  rwa [coordinateExpPartialHomeomorph_apply_zero (n := n) Gamma p] at hleft

theorem coordinateExp_mem_coordinateExpPartialHomeomorph_target
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    coordinateExp (n := n) Gamma p v ∈
      (coordinateExpPartialHomeomorph (n := n) Gamma p).target :=
by
  simpa [coordinateExpPartialHomeomorph] using
    (coordinateExpPartialHomeomorph (n := n) Gamma p).map_source hv

theorem normalCoordinates_mem_coordinateExpPartialHomeomorph_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {x : Position n}
    (hx : x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target) :
    normalCoordinates (n := n) Gamma p x ∈
      (coordinateExpPartialHomeomorph (n := n) Gamma p).source :=
  (coordinateExpPartialHomeomorph (n := n) Gamma p).map_target hx

theorem coordinateExp_normalCoordinates_roundtrip
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    Set.EqOn
      (fun x => coordinateExp (n := n) Gamma p (normalCoordinates (n := n) Gamma p x))
      id
      (normalCoordinateChart (n := n) Gamma p).source := by
  intro x hx
  simpa [normalCoordinates, coordinateExpPartialHomeomorph] using
    (coordinateExpPartialHomeomorph (n := n) Gamma p).right_inv hx

theorem coordinateExp_normalCoordinates
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {x : Position n}
    (hx : x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target) :
    coordinateExp (n := n) Gamma p (normalCoordinates (n := n) Gamma p x) = x :=
  coordinateExp_normalCoordinates_roundtrip (n := n) Gamma p hx

theorem normalCoordinates_exp_roundtrip
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    ∀ v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source,
      normalCoordinates (n := n) Gamma p (coordinateExp (n := n) Gamma p v) = v := by
  intro v hv
  simpa [normalCoordinates, coordinateExpPartialHomeomorph] using
    (coordinateExpPartialHomeomorph (n := n) Gamma p).left_inv hv

theorem normalCoordinates_coordinateExp
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    normalCoordinates (n := n) Gamma p (coordinateExp (n := n) Gamma p v) = v :=
  normalCoordinates_exp_roundtrip (n := n) Gamma p v hv

theorem normalCoordinates_zero_image
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    normalCoordinates (n := n) Gamma p (coordinateExp (n := n) Gamma p 0) = 0 := by
  exact
    normalCoordinates_coordinateExp (n := n) Gamma p
      (zero_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p)

theorem coordinateExp_mapsTo_coordinateExpPartialHomeomorph_target
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    Set.MapsTo
      (coordinateExp (n := n) Gamma p)
      (coordinateExpPartialHomeomorph (n := n) Gamma p).source
      (coordinateExpPartialHomeomorph (n := n) Gamma p).target :=
by
  simpa [coordinateExpPartialHomeomorph] using
    (coordinateExpPartialHomeomorph (n := n) Gamma p).mapsTo

theorem normalCoordinates_mapsTo_coordinateExpPartialHomeomorph_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    Set.MapsTo
      (normalCoordinates (n := n) Gamma p)
      (coordinateExpPartialHomeomorph (n := n) Gamma p).target
      (coordinateExpPartialHomeomorph (n := n) Gamma p).source := by
  intro x hx
  exact normalCoordinates_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p hx

/-- Source transport: the IFT partial homeomorphism source produced by
`localExpPartialHomeomorphOfStrict` is contained in the explicit Picard-Lindelöf exponential
source `coordinateExpSource`. Both are open neighborhoods of the origin in velocity space;
this lemma bridges the IFT-side and ODE-side source memberships. -/
theorem coordinateExpPartialHomeomorph_source_subset_coordinateExpSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    (coordinateExpPartialHomeomorph (n := n) Gamma p).source ⊆
      coordinateExpSource (n := n) Gamma p := by
  intro v hv
  let data :=
    Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 (baseState n p)
  let R : ℝ := data.ε * data.r
  let hf := hasStrictFDerivAt_coordinateExp_at_zero (n := n) Gamma p
  let U : Set (Velocity n) := Classical.choose hf.approximates_deriv_on_open_nhds
  let hU := Classical.choose_spec hf.approximates_deriv_on_open_nhds
  have hU_nhds : U ∈ 𝓝 (0 : Velocity n) := hU.2.1.mem_nhds hU.1
  let ρ : ℝ := Classical.choose (Metric.mem_nhds_iff.mp hU_nhds)
  let hρ := Classical.choose_spec (Metric.mem_nhds_iff.mp hU_nhds)
  have hρ_pos : 0 < ρ := hρ.1
  have hρU : Metric.ball (0 : Velocity n) ρ ⊆ U := hρ.2
  let r : ℝ := min ρ R
  have hball : v ∈ Metric.ball (0 : Velocity n) r := by
    simpa [coordinateExpPartialHomeomorph, r, R, data] using hv
  rw [coordinateExpSource, localCoordinateExponentialSource, Metric.mem_ball] at ⊢
  rw [Metric.mem_ball] at hball
  exact lt_of_lt_of_le hball (by
    dsimp [r, R]
    exact min_le_right _ _)

/-- The chosen inverse-function-theorem source for `coordinateExp` is radial on `[0,1]`. -/
theorem smul_mem_coordinateExpPartialHomeomorph_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source := by
  let data :=
    Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 (baseState n p)
  let R : ℝ := data.ε * data.r
  let hf := hasStrictFDerivAt_coordinateExp_at_zero (n := n) Gamma p
  let U : Set (Velocity n) := Classical.choose hf.approximates_deriv_on_open_nhds
  let hU := Classical.choose_spec hf.approximates_deriv_on_open_nhds
  have hU_nhds : U ∈ 𝓝 (0 : Velocity n) := hU.2.1.mem_nhds hU.1
  let ρ : ℝ := Classical.choose (Metric.mem_nhds_iff.mp hU_nhds)
  let hρ := Classical.choose_spec (Metric.mem_nhds_iff.mp hU_nhds)
  have hρ_pos : 0 < ρ := hρ.1
  have hρU : Metric.ball (0 : Velocity n) ρ ⊆ U := hρ.2
  let r : ℝ := min ρ R
  have hv' : v ∈ Metric.ball (0 : Velocity n) r := by
    simpa [coordinateExpPartialHomeomorph, r, R, data] using hv
  have hsmul_ball : t • v ∈ Metric.ball (0 : Velocity n) r := by
    rw [Metric.mem_ball] at hv' ⊢
    calc
      dist (t • v) 0 = ‖t • v‖ := by rw [dist_eq_norm, sub_zero]
      _ = |t| * ‖v‖ := by simpa [Real.norm_eq_abs] using norm_smul t v
      _ ≤ ‖v‖ := by
        have habs : |t| ≤ 1 := by
          rcases ht with ⟨ht0, ht1⟩
          simpa [abs_of_nonneg ht0] using ht1
        nlinarith [norm_nonneg v]
      _ = dist v 0 := by rw [dist_eq_norm, sub_zero]
      _ < r := hv'
  simpa [coordinateExpPartialHomeomorph, r, R, data] using hsmul_ball

end Exponential.Coordinate
