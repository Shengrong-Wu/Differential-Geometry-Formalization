import Exponential.DexpContinuity

/-! # Differentiability of normal coordinates

This file proves that the normal coordinate map `normalCoordinates Γ p`
(the local inverse of `coordinateExp Γ p`) is differentiable at points in
the normal neighborhood. The key tool is the inverse function theorem:
since `coordinateExp` has an invertible strict derivative at the origin,
`normalCoordinates` inherits differentiability.

## Main results

* `hasFDerivAt_normalCoordinates_at_base` — `HasFDerivAt` for `normalCoordinates` at the base
  point, with derivative `(velocityPositionEquiv n).symm`
* `differentiableAt_normalCoordinates_at_base` — `DifferentiableAt` corollary at the base
* `hasFDerivAt_normalCoordinates` — `HasFDerivAt` at any target point where the forward
  derivative is a continuous linear equivalence
* `coordinateExp_fderiv_isUnit_nhds_zero` — derivative of `coordinateExp` is invertible in a
  neighborhood of `0`
* `normalCoordinates_differentiableAt_nhds_base` — `normalCoordinates` is differentiable
  in a neighborhood of the base point
-/

namespace Exponential.Coordinate

open Set Filter
open scoped Topology

variable {n : ℕ}

/-! ### Continuity and roundtrip -/

/-- `normalCoordinates` is continuous at any point in the chart target, since it is
the symm of a partial homeomorphism. -/
theorem continuousAt_normalCoordinates
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {x : Position n}
    (hx : x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target) :
    ContinuousAt (normalCoordinates (n := n) Gamma p) x :=
  (coordinateExpPartialHomeomorph (n := n) Gamma p).continuousAt_symm hx

/-- The roundtrip `coordinateExp ∘ normalCoordinates = id` holds eventually near any
target point, since the target is open. -/
theorem coordinateExp_normalCoordinates_eventually
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {x : Position n}
    (hx : x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target) :
    ∀ᶠ y in 𝓝 x,
      coordinateExp (n := n) Gamma p (normalCoordinates (n := n) Gamma p y) = y := by
  have htarget_open := (coordinateExpPartialHomeomorph (n := n) Gamma p).open_target
  filter_upwards [htarget_open.mem_nhds hx] with y hy
  exact coordinateExp_normalCoordinates (n := n) Gamma p hy

/-! ### HasFDerivAt at the base point -/

/-- `normalCoordinates Γ p` has Fréchet derivative `(velocityPositionEquiv n).symm` at the base
point `p`. This follows from the inverse function theorem: `coordinateExp` has strict derivative
`velocityPositionEquiv n` at `0`, and `normalCoordinates` is a local left inverse. -/
theorem hasFDerivAt_normalCoordinates_at_base
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    HasFDerivAt (normalCoordinates (n := n) Gamma p)
      ((velocityPositionEquiv n).symm : Position n →L[ℝ] Velocity n) p := by
  apply HasFDerivAt.of_local_left_inverse
  · exact continuousAt_normalCoordinates (n := n) Gamma p
      (base_mem_coordinateExpPartialHomeomorph_target (n := n) Gamma p)
  · rw [normalCoordinates_base (n := n) Gamma p]
    exact (hasStrictFDerivAt_coordinateExp_at_zero (n := n) Gamma p).hasFDerivAt
  · exact coordinateExp_normalCoordinates_eventually (n := n) Gamma p
      (base_mem_coordinateExpPartialHomeomorph_target (n := n) Gamma p)

/-- `normalCoordinates Γ p` is differentiable at the base point. -/
theorem differentiableAt_normalCoordinates_at_base
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    DifferentiableAt ℝ (normalCoordinates (n := n) Gamma p) p :=
  (hasFDerivAt_normalCoordinates_at_base (n := n) Gamma p).differentiableAt

/-! ### HasFDerivAt at general target points -/

/-- `normalCoordinates Γ p` has `HasFDerivAt` at any point `x` in the chart target,
provided the forward derivative of `coordinateExp` at `normalCoordinates x` is given
as a continuous linear equivalence `L`. The derivative of `normalCoordinates` is then
`L.symm`. -/
theorem hasFDerivAt_normalCoordinates
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {x : Position n}
    (hx : x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target)
    {L : Velocity n ≃L[ℝ] Position n}
    (hL : HasFDerivAt (coordinateExp (n := n) Gamma p) (L : Velocity n →L[ℝ] Position n)
      (normalCoordinates (n := n) Gamma p x)) :
    HasFDerivAt (normalCoordinates (n := n) Gamma p)
      (L.symm : Position n →L[ℝ] Velocity n) x :=
  HasFDerivAt.of_local_left_inverse
    (continuousAt_normalCoordinates (n := n) Gamma p hx)
    hL
    (coordinateExp_normalCoordinates_eventually (n := n) Gamma p hx)

/-- `normalCoordinates Γ p` is differentiable at any target point where the forward derivative
is a continuous linear equivalence. -/
theorem differentiableAt_normalCoordinates_of_equiv
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {x : Position n}
    (hx : x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target)
    {L : Velocity n ≃L[ℝ] Position n}
    (hL : HasFDerivAt (coordinateExp (n := n) Gamma p) (L : Velocity n →L[ℝ] Position n)
      (normalCoordinates (n := n) Gamma p x)) :
    DifferentiableAt ℝ (normalCoordinates (n := n) Gamma p) x :=
  (hasFDerivAt_normalCoordinates (n := n) Gamma p hx hL).differentiableAt

/-! ### Derivative invertibility -/

/-- The Fréchet derivative of `coordinateExp` is invertible in a neighborhood of `0`.
This follows from:
1. The derivative at `0` is `ContinuousLinearMap.id`, which is a unit.
2. The derivative is continuous (from C¹ regularity of `coordinateExp`).
3. The set of units in a complete normed ring is open. -/
theorem coordinateExp_fderiv_isUnit_nhds_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    ∀ᶠ v in 𝓝 (0 : Velocity n),
      v ∈ coordinateExpSource (n := n) Gamma p ∧
        IsUnit (fderiv ℝ (coordinateExp (n := n) Gamma p) v) := by
  have h0_source : (0 : Velocity n) ∈ coordinateExpSource (n := n) Gamma p :=
    zero_mem_coordinateExpSource (n := n) Gamma p
  have hca : ContinuousAt (fderiv ℝ (coordinateExp (n := n) Gamma p)) 0 :=
    (contDiffAt_coordinateExp (n := n) Gamma p h0_source).continuousAt_fderiv (by simp)
  have hunit0 : IsUnit (fderiv ℝ (coordinateExp (n := n) Gamma p) 0) := by
    rw [fderiv_coordinateExp_at_zero (n := n) Gamma p]
    exact isUnit_one
  have hunit_mem : {L : (Velocity n) →L[ℝ] (Position n) | IsUnit L} ∈
      𝓝 (fderiv ℝ (coordinateExp (n := n) Gamma p) 0) :=
    Units.isOpen.mem_nhds hunit0
  filter_upwards [hca.preimage_mem_nhds hunit_mem,
    (isOpen_coordinateExpSource (n := n) Gamma p).mem_nhds h0_source]
    with v hunit hsource
  exact ⟨hsource, hunit⟩

/-- From `IsUnit` of a continuous linear endomorphism, produce a `ContinuousLinearEquiv`. -/
private noncomputable def equivOfIsUnit
    {L : (Velocity n) →L[ℝ] (Position n)}
    (hunit : IsUnit L) :
    Velocity n ≃L[ℝ] Position n :=
  ContinuousLinearEquiv.unitsEquiv ℝ (Velocity n) hunit.unit

private theorem equivOfIsUnit_coe
    {L : (Velocity n) →L[ℝ] (Position n)}
    (hunit : IsUnit L) :
    (equivOfIsUnit hunit : Velocity n →L[ℝ] Position n) = L := by
  simp [equivOfIsUnit, ContinuousLinearEquiv.unitsEquiv]
  exact rfl

/-- `normalCoordinates` is differentiable at any target point whose preimage has
invertible forward derivative. -/
theorem differentiableAt_normalCoordinates_of_fderiv_isUnit
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {x : Position n}
    (hx : x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target)
    (hunit : IsUnit (fderiv ℝ (coordinateExp (n := n) Gamma p)
      (normalCoordinates (n := n) Gamma p x))) :
    DifferentiableAt ℝ (normalCoordinates (n := n) Gamma p) x := by
  have hv_source := normalCoordinates_mem_coordinateExpPartialHomeomorph_source
    (n := n) Gamma p hx
  let L := equivOfIsUnit hunit
  have hL : HasFDerivAt (coordinateExp (n := n) Gamma p) (L : Velocity n →L[ℝ] Position n)
      (normalCoordinates (n := n) Gamma p x) := by
    convert hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source
      (n := n) Gamma p hv_source using 1
  exact differentiableAt_normalCoordinates_of_equiv (n := n) Gamma p hx hL

/-! ### Operator norm bound from ApproximatesLinearOn -/

/-- If `f` approximates `f'` on an open set `U` with constant `c`, and `f` has Fréchet derivative
`L` at `v ∈ U`, then `‖L - f'‖ ≤ c`. This is the pointwise derivative bound from the
approximation property.

Proof: for any `h` and `ε > 0`, setting `x = v + ε • h` (in U for small ε by openness),
the approximation gives `‖f(x) - f(v) - f'(εh)‖ ≤ c * ‖εh‖ = cε‖h‖`, and HasFDerivAt gives
`f(x) - f(v) = L(εh) + o(ε)`. Triangle gives `‖(L - f')(εh)‖ ≤ cε‖h‖ + o(ε)`.
Dividing by ε: `‖(L - f')h‖ ≤ c‖h‖ + o(1)`, hence `‖(L - f')h‖ ≤ c‖h‖`. -/
private theorem opNorm_fderiv_sub_le_of_approximatesLinearOn
    {f : Velocity n → Position n} {f' : Velocity n →L[ℝ] Position n}
    {U : Set (Velocity n)} {c : NNReal}
    (happrox : ApproximatesLinearOn f f' U c)
    (hopen : IsOpen U)
    {v : Velocity n} (hv : v ∈ U)
    {L : Velocity n →L[ℝ] Position n}
    (hfd : HasFDerivAt f L v) :
    ‖L - f'‖ ≤ c := by
  -- For any h and any ε > 0 with v + ε•h ∈ U:
  -- ApproximatesLinearOn: ‖f(v+εh) - f(v) - f'(εh)‖ ≤ c‖εh‖
  -- HasFDerivAt: f(v+εh) - f(v) = L(εh) + o(ε)
  -- So ‖L(εh) - f'(εh) + o(ε)‖ ≤ c‖εh‖
  -- i.e. ε‖(L-f')h‖ - o(ε) ≤ cε‖h‖
  -- Divide by ε: ‖(L-f')h‖ ≤ c‖h‖ + o(1), and let ε → 0.
  apply ContinuousLinearMap.opNorm_le_bound _ c.coe_nonneg
  intro h
  -- Suffices: for all η > 0, ‖(L-f')h‖ ≤ c‖h‖ + η
  suffices ∀ η > 0, ‖(L - f') h‖ ≤ (↑c + η) * ‖h‖ by
    by_contra hlt
    push_neg at hlt
    by_cases hhn : ‖h‖ = 0
    · simp [norm_eq_zero.mp hhn, ContinuousLinearMap.map_zero] at hlt
    · have hh_pos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg h) (Ne.symm hhn)
      have hgap : 0 < ‖(L - f') h‖ / ‖h‖ - ↑c := by
        rw [sub_pos]; exact (lt_div_iff₀ hh_pos).mpr (by linarith)
      have hkey := this ((‖(L - f') h‖ / ‖h‖ - ↑c) / 2) (by linarith)
      -- hkey : ‖(L-f')h‖ ≤ (↑c + (‖(L-f')h‖/‖h‖ - ↑c)/2) * ‖h‖
      -- = (↑c + ‖(L-f')h‖/(2*‖h‖) - ↑c/2) * ‖h‖
      -- = (↑c/2 + ‖(L-f')h‖/(2*‖h‖)) * ‖h‖
      -- = ↑c*‖h‖/2 + ‖(L-f')h‖/2
      -- So ‖(L-f')h‖ ≤ ↑c*‖h‖/2 + ‖(L-f')h‖/2
      -- Hence ‖(L-f')h‖/2 ≤ ↑c*‖h‖/2, i.e. ‖(L-f')h‖ ≤ ↑c*‖h‖. Contradiction!
      nlinarith [div_mul_cancel₀ (‖(L - f') h‖) (ne_of_gt hh_pos)]
  intro η hη_pos
  -- Get ε₀ > 0 such that v + w ∈ U for ‖w‖ < ε₀
  obtain ⟨ε₀, hε₀_pos, hε₀U⟩ := Metric.isOpen_iff.mp hopen v hv
  -- Get ε₁ > 0 such that ‖f(v+w) - f(v) - L(w)‖ ≤ η * ‖w‖ for ‖w‖ < ε₁
  -- (use η/(‖h‖+1) as the little-o bound to make the final estimate work)
  have hsmall := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hfd).def (by positivity : (0 : ℝ) < η)
  rw [Filter.eventually_iff_exists_mem] at hsmall
  obtain ⟨S, hS_mem, hS⟩ := hsmall
  obtain ⟨ε₁, hε₁_pos, hε₁S⟩ := Metric.mem_nhds_iff.mp hS_mem
  -- Choose ε < min(ε₀, ε₁) / (‖h‖ + 1)
  set ε := min ε₀ ε₁ / (2 * (‖h‖ + 1))
  have hε_pos : 0 < ε := by positivity
  have hεh_lt : ‖ε • h‖ < min ε₀ ε₁ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε_pos]
    calc ε * ‖h‖ ≤ ε * (‖h‖ + 1) := by nlinarith [norm_nonneg h]
      _ = min ε₀ ε₁ / (2 * (‖h‖ + 1)) * (‖h‖ + 1) := rfl
      _ = min ε₀ ε₁ / 2 := by field_simp
      _ < min ε₀ ε₁ := by linarith [lt_min hε₀_pos hε₁_pos]
  -- v + ε•h ∈ U
  have hv_εh_U : v + ε • h ∈ U := by
    apply hε₀U; rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact lt_of_lt_of_le hεh_lt (min_le_left _ _)
  -- ApproximatesLinearOn bound
  have h_approx : ‖f (v + ε • h) - f v - f' (ε • h)‖ ≤ ↑c * ‖ε • h‖ := by
    have : ‖f (v + ε • h) - f v - f' ((v + ε • h) - v)‖ ≤ ↑c * ‖(v + ε • h) - v‖ :=
      happrox (x := v + ε • h) hv_εh_U (y := v) hv
    simp only [add_sub_cancel_left] at this
    exact this
  -- HasFDerivAt bound
  have h_fderiv : ‖f (v + ε • h) - f v - L (ε • h)‖ ≤ η * ‖ε • h‖ := by
    apply hS; apply hε₁S; rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hεh_lt (min_le_right _ _)
  -- Triangle
  have h_tri : ‖(L - f') (ε • h)‖ ≤ (↑c + η) * ‖ε • h‖ := by
    calc ‖(L - f') (ε • h)‖
        = ‖(f (v + ε • h) - f v - f' (ε • h)) - (f (v + ε • h) - f v - L (ε • h))‖ := by
          rw [ContinuousLinearMap.sub_apply]; congr 1; ring
      _ ≤ ‖f (v + ε • h) - f v - f' (ε • h)‖ + ‖f (v + ε • h) - f v - L (ε • h)‖ :=
          norm_sub_le _ _
      _ ≤ ↑c * ‖ε • h‖ + η * ‖ε • h‖ := add_le_add h_approx h_fderiv
      _ = (↑c + η) * ‖ε • h‖ := by ring
  -- Cancel ε from both sides
  rw [map_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hε_pos] at h_tri
  by_cases hh : h = 0
  · simp [hh, ContinuousLinearMap.map_zero]
  · -- h_tri : ε * ‖(L - f') h‖ ≤ (↑c + η) * (ε * ‖h‖)
    -- Divide by ε > 0: ‖(L-f')h‖ ≤ (c + η) * ‖h‖
    have key : ‖(L - f') h‖ ≤ (↑c + η) * ‖h‖ := by
      -- h_tri : ε * ‖(L-f')h‖ ≤ (c + η) * (ε * ‖h‖) = ε * ((c + η) * ‖h‖)
      have hrhs : (↑c + η) * (ε * ‖h‖) = ε * ((↑c + η) * ‖h‖) := by ring
      rw [hrhs] at h_tri
      exact le_of_mul_le_mul_left h_tri hε_pos
    linarith

/-- If `f` approximates the invertible CLM `f'` on an open set `U` with constant `c < ‖f'⁻¹‖⁻¹`,
and `f` has Fréchet derivative `L` at `v ∈ U`, then `L` is invertible. -/
private theorem fderiv_isUnit_of_approximatesLinearOn_hasFDerivAt
    {f : Velocity n → Position n} {f' : Velocity n ≃L[ℝ] Position n}
    {U : Set (Velocity n)} {c : NNReal}
    (happrox : ApproximatesLinearOn f (f' : Velocity n →L[ℝ] Position n) U c)
    (hc : (c : ℝ) < ‖(f'.symm : Position n →L[ℝ] Velocity n)‖⁻¹)
    (hopen : IsOpen U)
    {v : Velocity n} (hv : v ∈ U)
    {L : Velocity n →L[ℝ] Position n}
    (hfd : HasFDerivAt f L v) :
    IsUnit L := by
  have hbound := opNorm_fderiv_sub_le_of_approximatesLinearOn happrox hopen hv hfd
  -- ‖L - f'‖ ≤ c < ‖f'⁻¹‖⁻¹, so L is within perturbation distance of the unit f'
  -- Use Units.isOpen + the bound to show L is in the open set of units
  -- since dist(L, f') ≤ c < ‖f'⁻¹‖⁻¹ = radius of the invertibility ball around f'.
  -- Construct the unit from the CLE
  let f'_unit : (Velocity n →L[ℝ] Position n)ˣ :=
    { val := f'
      inv := f'.symm
      val_inv := by ext; simp
      inv_val := by ext; simp }
  have : ‖L - (↑f'_unit : Velocity n →L[ℝ] Position n)‖ < ‖(↑f'_unit⁻¹ : Velocity n →L[ℝ] Position n)‖⁻¹ := by
    change ‖L - (f' : Velocity n →L[ℝ] Position n)‖ < ‖(f'.symm : Position n →L[ℝ] Velocity n)‖⁻¹
    linarith
  exact (f'_unit.ofNearby L this).isUnit

/-! ### Differentiability neighborhood -/

/-- There exists a neighborhood of the base point `p` in the chart target on which
`normalCoordinates` is differentiable. This follows from the derivative of `coordinateExp`
being invertible near `0`, propagated through the homeomorphism. -/
theorem normalCoordinates_differentiableAt_nhds_base
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    ∀ᶠ x in 𝓝 p,
      x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target ∧
        DifferentiableAt ℝ (normalCoordinates (n := n) Gamma p) x := by
  have hcont := continuousAt_normalCoordinates (n := n) Gamma p
    (base_mem_coordinateExpPartialHomeomorph_target (n := n) Gamma p)
  have hbase : normalCoordinates (n := n) Gamma p p = 0 :=
    normalCoordinates_base (n := n) Gamma p
  -- Get the eventually filter for invertible derivative near 0
  have hunit_nhds : ∀ᶠ v in 𝓝 (0 : Velocity n),
      IsUnit (fderiv ℝ (coordinateExp (n := n) Gamma p) v) := by
    filter_upwards [coordinateExp_fderiv_isUnit_nhds_zero (n := n) Gamma p] with v hv
    exact hv.2
  -- Pull back through normalCoordinates (which is continuous at p, mapping p to 0)
  have hpull : ∀ᶠ x in 𝓝 p,
      IsUnit (fderiv ℝ (coordinateExp (n := n) Gamma p)
        (normalCoordinates (n := n) Gamma p x)) := by
    rw [← hbase] at hunit_nhds
    exact hcont.eventually hunit_nhds
  -- Combine with target membership
  have htarget_nhds :
      ∀ᶠ x in 𝓝 p, x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target :=
    (coordinateExpPartialHomeomorph (n := n) Gamma p).open_target.mem_nhds
      (base_mem_coordinateExpPartialHomeomorph_target (n := n) Gamma p)
  filter_upwards [htarget_nhds, hpull] with x htarget hunit
  exact ⟨htarget, differentiableAt_normalCoordinates_of_fderiv_isUnit
    (n := n) Gamma p htarget hunit⟩

/-- The Fréchet derivative of `coordinateExp` is invertible at every point in the
partial homeomorphism source. This follows from the IFT construction: the source is a ball
of radius ≤ ρ, where ρ is the invertibility radius from `coordinateExp_fderiv_isUnit_nhds_zero`.

The proof uses a topological argument: on the connected source ball, the set of source points
with invertible derivative is clopen (open by continuity of fderiv + openness of units;
closed because its complement — where the determinant vanishes — would force non-injectivity,
contradicting the homeomorphism). Since the set is nonempty (contains 0), it equals the whole
source. -/
theorem coordinateExp_fderiv_isUnit_of_mem_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    IsUnit (fderiv ℝ (coordinateExp (n := n) Gamma p) v) := by
  -- The source is contained in the invertibility neighborhood from
  -- coordinateExp_fderiv_isUnit_nhds_zero: both are produced from the same
  -- HasStrictFDerivAt data, and the source ball has radius r = min ρ R ≤ ρ.
  --
  -- We prove this by showing source ⊆ the filter set. The source is open and
  -- contained in coordinateExpSource (where coordinateExp is C^1). By C^1 regularity,
  -- fderiv is continuous. Since fderiv(0) = id is invertible and Units is open,
  -- there's an open neighborhood of 0 in the source where fderiv is invertible.
  --
  -- The key: the source of coordinateExpPartialHomeomorph is DEFINED as a subset of
  -- the ball where ApproximatesLinearOn holds, so every source point is within the
  -- approximation ball, hence has invertible derivative.
  -- The proof requires deriving ‖fderiv(v) - id‖ ≤ c < 1 from the ApproximatesLinearOn data.
  -- v ∈ U (the approximation set), and the bound c = ‖id⁻¹‖⁻¹ / 2 = 1/2.
  -- ApproximatesLinearOn at (v+h, v) + HasFDerivAt at v gives ‖(fderiv(v) - id)(h)‖ ≤ c‖h‖ + o(‖h‖).
  -- In the limit: ‖fderiv(v) - id‖_op ≤ c < 1, so fderiv(v) is invertible by Units.ofNearby.
  --
  -- Infrastructure in place:
  -- • coordinateExpPartialHomeomorph_source_mem_approxSet: v ∈ U (the ApproximatesLinearOn set)
  -- • hU_spec.2.2: ApproximatesLinearOn on U with constant c < ‖id⁻¹‖⁻¹
  -- • hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source: HasFDerivAt at v
  --
  -- Remaining formalization work: the ε-limit argument deriving the operator norm bound
  -- from ApproximatesLinearOn + HasFDerivAt, then applying Units.ofNearby.
  have hv_U := coordinateExpPartialHomeomorph_source_mem_approxSet (n := n) Gamma p hv
  let hf := hasStrictFDerivAt_coordinateExp_at_zero (n := n) Gamma p
  let hU_spec := Classical.choose_spec hf.approximates_deriv_on_open_nhds
  have hfd : HasFDerivAt (coordinateExp (n := n) Gamma p)
      (fderiv ℝ (coordinateExp (n := n) Gamma p) v) v :=
    hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source (n := n) Gamma p hv
  -- The derivative is invertible by the norm bound from ApproximatesLinearOn.
  -- Step 1: Show ‖fderiv(v) - f'‖ ≤ c where f' = velocityPositionEquiv n
  -- and c = ‖f'⁻¹‖₊⁻¹ / 2.
  -- From ApproximatesLinearOn: for all x ∈ U, ‖f(x) - f(v) - f'(x-v)‖ ≤ c * ‖x-v‖.
  -- From HasFDerivAt: ‖f(x) - f(v) - fderiv(v)(x-v)‖ = o(‖x-v‖).
  -- Triangle: ‖(fderiv(v) - f')(x-v)‖ ≤ c * ‖x-v‖ + o(‖x-v‖).
  -- By ContinuousLinearMap.opNorm_le_of_bound in the limit: ‖fderiv(v) - f'‖ ≤ c.
  -- Step 2: c < ‖f'⁻¹‖⁻¹, so Units.ofNearby gives the unit.
  -- hU_spec.2.2 : ApproximatesLinearOn ... U (‖(velocityPositionEquiv n).symm‖₊⁻¹ / 2)
  -- Need: ↑(‖f'.symm‖₊⁻¹ / 2) < ‖f'.symm‖⁻¹ where f' = velocityPositionEquiv n
  -- This is c/2 < c where c = ‖f'.symm‖⁻¹ > 0
  -- The constant c = ‖f'.symm‖₊⁻¹ / 2 satisfies c < ‖f'.symm‖⁻¹.
  -- Handle the Subsingleton case (n = 0) separately.
  rcases (velocityPositionEquiv n).subsingleton_or_nnnorm_symm_pos with hsub | hpos
  · -- Subsingleton case: Position n has at most one element, so all CLMs are units
    haveI := hsub
    haveI : Unique (Velocity n →L[ℝ] Position n) := ContinuousLinearMap.uniqueOfLeft
    exact isUnit_of_subsingleton _
  · -- Nontrivial case: ‖f'.symm‖₊ > 0, so c = ‖f'.symm‖₊⁻¹/2 < ‖f'.symm‖⁻¹
    have hpos_real : (0 : ℝ) < ‖((velocityPositionEquiv n).symm : Position n →L[ℝ] Velocity n)‖⁻¹ := by
      rw [inv_pos]; exact_mod_cast hpos
    have hc_lt : (↑(‖((velocityPositionEquiv n).symm : Position n →L[ℝ] Velocity n)‖₊⁻¹ / 2) : ℝ) <
        ‖((velocityPositionEquiv n).symm : Position n →L[ℝ] Velocity n)‖⁻¹ := by
      rw [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_inv, coe_nnnorm]
      exact half_lt_self hpos_real
    exact fderiv_isUnit_of_approximatesLinearOn_hasFDerivAt hU_spec.2.2 hc_lt hU_spec.2.1 hv_U hfd

/-- `normalCoordinates Γ p` is differentiable at every point in the chart target. -/
theorem differentiableAt_normalCoordinates_of_mem_target
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {x : Position n}
    (hx : x ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).target) :
    DifferentiableAt ℝ (normalCoordinates (n := n) Gamma p) x :=
  differentiableAt_normalCoordinates_of_fderiv_isUnit (n := n) Gamma p hx
    (coordinateExp_fderiv_isUnit_of_mem_source (n := n) Gamma p
      ((coordinateExpPartialHomeomorph (n := n) Gamma p).symm_mapsTo hx))

end Exponential.Coordinate
