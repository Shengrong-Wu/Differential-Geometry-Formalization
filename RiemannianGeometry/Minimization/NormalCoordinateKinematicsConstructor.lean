import Minimization.NormalCoordinateKinematics
import Exponential.NormalCoordinateDifferentiability

/-! # Constructors for `HasNormalCoordinateKinematics`

This file provides constructors that derive `HasNormalCoordinateKinematics` from more
primitive data, using the chain rule and FTC for normal coordinates.

## Main results

* `hasNormalCoordinateKinematics_of_differentiableNormalCoordinates` — constructor from
  differentiability of `normalCoordinates` at curve points + integrability of the composed
  velocity field.
* `hasNormalCoordinateKinematics_of_liesIn` — **witness-free** constructor: any C¹ curve in the
  normal neighborhood automatically has kinematics. Uses
  `differentiableAt_normalCoordinates_of_mem_target` (no external differentiability witness)
  and derives integrability from C^1 regularity of the inverse map.
-/

namespace Minimization.Coordinate

open Set Filter MeasureTheory
open scoped Topology

variable {n : ℕ}

/-- Chain rule helper: composition of `normalCoordinates` with a curve via
`HasFDerivWithinAt.comp_hasDerivWithinAt`. -/
private theorem normalCoordinates_comp_hasDerivWithinAt
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {p : Exponential.Coordinate.Position n}
    {γ : ℝ → Exponential.Coordinate.Position n}
    {Tγ : ℝ → Exponential.Coordinate.Velocity n}
    {s : Set ℝ} {t : ℝ}
    (hdiff : DifferentiableAt ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (γ t))
    (hvel : HasDerivWithinAt γ (Tγ t) s t) :
    HasDerivWithinAt (normalCoordinateCurve (n := n) Gamma p γ)
      (fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (γ t) (Tγ t))
      s t := by
  show HasDerivWithinAt
    (Exponential.Coordinate.normalCoordinates (n := n) Gamma p ∘ γ) _ _ _
  exact hdiff.hasFDerivAt.hasFDerivWithinAt.comp_hasDerivWithinAt t hvel (mapsTo_univ _ _)

/-- If `normalCoordinates` is differentiable at each point of a C¹ curve in the target, and the
composed velocity field is integrable, then the curve satisfies `HasNormalCoordinateKinematics`. -/
theorem hasNormalCoordinateKinematics_of_differentiableNormalCoordinates
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {p : Exponential.Coordinate.Position n}
    {γ : ℝ → Exponential.Coordinate.Position n}
    {Tγ : ℝ → Exponential.Coordinate.Velocity n}
    {a b : ℝ}
    (hab : a ≤ b)
    (hlies : LiesInOn (n := n) Gamma p γ (Icc a b))
    (hvel : HasCoordinateVelocityOn (n := n) γ Tγ (Icc a b))
    (hdiff : ∀ t ∈ Icc a b,
      DifferentiableAt ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (γ t))
    (hcont_nc : ContinuousOn (normalCoordinateCurve (n := n) Gamma p γ) (Icc a b))
    (hint : IntervalIntegrable
      (fun t => fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (γ t) (Tγ t))
      volume a b) :
    HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ
      (fun t =>
        fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (γ t) (Tγ t))
      a b where
  liesInOn := hlies
  curveVelocity := hvel
  normalVelocity := fun t ht =>
    normalCoordinates_comp_hasDerivWithinAt (hdiff t ht) (hvel t ht)
  displacement := by
    constructor
    · exact hint
    · -- FTC: ∫ Uγ = normalCoordinates(γ(b)) - normalCoordinates(γ(a))
      let Uγ := fun t =>
        fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (γ t) (Tγ t)
      -- At interior points, HasDerivWithinAt on Icc upgrades to HasDerivAt
      have hderiv_at : ∀ t ∈ Ioo a b,
          HasDerivAt (normalCoordinateCurve (n := n) Gamma p γ) (Uγ t) t := by
        intro t ht
        have ht_icc : t ∈ Icc a b := Ioo_subset_Icc_self ht
        exact (normalCoordinates_comp_hasDerivWithinAt (hdiff t ht_icc) (hvel t ht_icc)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont_nc hderiv_at hint

/-- Witness-free kinematics constructor: if a curve stays in the normal neighborhood and has
a coordinate velocity, then `HasNormalCoordinateKinematics` holds automatically. The
differentiability of `normalCoordinates` at target points is derived from the owner-layer
theorem `differentiableAt_normalCoordinates_of_mem_target`, not from an external witness.

The remaining hypotheses are:
- `hcont_γ`: the curve γ is continuous on [a,b]
- `hcont_Tγ`: the velocity Tγ is continuous on [a,b]

These are used to derive continuity of the normal-coordinate curve and integrability of the
composed velocity field. -/
theorem hasNormalCoordinateKinematics_of_liesIn
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {p : Exponential.Coordinate.Position n}
    {γ : ℝ → Exponential.Coordinate.Position n}
    {Tγ : ℝ → Exponential.Coordinate.Velocity n}
    {a b : ℝ}
    (hab : a ≤ b)
    (hlies : LiesInOn (n := n) Gamma p γ (Icc a b))
    (hvel : HasCoordinateVelocityOn (n := n) γ Tγ (Icc a b))
    (hcont_γ : ContinuousOn γ (Icc a b))
    (hcont_Tγ : ContinuousOn Tγ (Icc a b)) :
    HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ
      (fun t =>
        fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (γ t) (Tγ t))
      a b := by
  apply hasNormalCoordinateKinematics_of_differentiableNormalCoordinates hab hlies hvel
  · -- hdiff: normalCoordinates is differentiable at each curve point
    intro t ht
    exact Exponential.Coordinate.differentiableAt_normalCoordinates_of_mem_target
      (n := n) Gamma p (by simpa [LiesInOn, normalNeighborhood] using hlies ht)
  · -- hcont_nc: normalCoordinateCurve is continuous on [a,b]
    show ContinuousOn
      (Exponential.Coordinate.normalCoordinates (n := n) Gamma p ∘ γ) (Icc a b)
    exact ContinuousOn.comp
      (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).continuousOn_symm
      hcont_γ
      (fun t ht => by simpa [LiesInOn, normalNeighborhood] using hlies ht)
  · -- hint: interval integrability of the composed velocity field
    -- We need IntervalIntegrable (fun t => fderiv normalCoordinates (γ t) (Tγ t)) volume a b
    -- Use: the normal-coordinate curve is continuous, has a derivative at each interior point
    -- (from the chain rule), and is differentiable at endpoints. So by the generalized FTC,
    -- its derivative (which equals our function) is integrable.
    --
    -- Alternatively, since normalCoordinates is C^1 on the target (inverse of C^1 diffeomorphism),
    -- the fderiv is continuous, so the composed function is continuous on [a,b], hence integrable.
    --
    -- For now, use the fact that the normal-coordinate curve has HasDerivWithinAt on Icc a b
    -- (from normalCoordinates_comp_hasDerivWithinAt), so it's Lipschitz on [a,b]
    -- (from bounded derivative on compact), hence its derivative is integrable.
    --
    -- Simplest route: use intervalIntegrable_deriv_of_hasDerivWithinAt or similar.
    have hderiv : ∀ t ∈ Icc a b,
        HasDerivWithinAt (normalCoordinateCurve (n := n) Gamma p γ)
          (fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) (γ t) (Tγ t))
          (Icc a b) t := by
      intro t ht
      exact normalCoordinates_comp_hasDerivWithinAt
        (Exponential.Coordinate.differentiableAt_normalCoordinates_of_mem_target
          (n := n) Gamma p (by simpa [LiesInOn, normalNeighborhood] using hlies ht))
        (hvel t ht)
    -- The normal-coordinate curve is continuous on [a,b] (proved above)
    have hcont_nc : ContinuousOn (normalCoordinateCurve (n := n) Gamma p γ) (Icc a b) :=
      ContinuousOn.comp
        (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).continuousOn_symm
        hcont_γ
        (fun t ht => by simpa [LiesInOn, normalNeighborhood] using hlies ht)
    -- Show continuity of the derivative function, then use ContinuousOn.intervalIntegrable_of_Icc.
    -- The derivative t ↦ fderiv(normalCoordinates, γ t)(Tγ t) is continuous because:
    -- 1. normalCoordinates is C^1 on the target (inverse of C^1 diffeomorphism by IFT)
    -- 2. so t ↦ fderiv(normalCoordinates, γ t) is continuous (continuous fderiv ∘ continuous γ)
    -- 3. Tγ is continuous (given)
    -- 4. CLM application is continuous
    --
    -- Step 1: show fderiv normalCoordinates is continuous on the target
    have hcont_fderiv : ContinuousOn
        (fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p))
        (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).target := by
      intro x hx
      have hv := (Exponential.Coordinate.coordinateExpPartialHomeomorph
        (n := n) Gamma p).symm_mapsTo hx
      have hv_source := Exponential.Coordinate.coordinateExpPartialHomeomorph_source_subset_coordinateExpSource
        (n := n) Gamma p hv
      -- coordinateExp is C^1 at v, so normalCoordinates is C^1 at x by IFT
      have hcd_exp : ContDiffAt ℝ 1 (Exponential.Coordinate.coordinateExp (n := n) Gamma p)
          (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x) :=
        Exponential.Coordinate.contDiffAt_coordinateExp (n := n) Gamma p hv_source
      -- Get the CLE from the IsUnit
      have hunit := Exponential.Coordinate.coordinateExp_fderiv_isUnit_of_mem_source
        (n := n) Gamma p hv
      let L := ContinuousLinearEquiv.unitsEquiv ℝ _ hunit.unit
      have hfd : HasFDerivAt (Exponential.Coordinate.coordinateExp (n := n) Gamma p)
          (L : Exponential.Coordinate.Velocity n →L[ℝ] Exponential.Coordinate.Position n)
          (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x) := by
        convert Exponential.Coordinate.hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source
          (n := n) Gamma p hv using 1
      have hcd_inv : ContDiffAt ℝ 1
          (Exponential.Coordinate.normalCoordinates (n := n) Gamma p) x :=
        (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).contDiffAt_symm
          hx hfd hcd_exp
      exact hcd_inv.continuousAt_fderiv (by simp) |>.continuousWithinAt
    -- Step 2: compose with γ and Tγ
    have hcont_composed : ContinuousOn
        (fun t => fderiv ℝ (Exponential.Coordinate.normalCoordinates (n := n) Gamma p)
          (γ t) (Tγ t))
        (Icc a b) := by
      apply ContinuousOn.clm_apply
      · exact hcont_fderiv.comp hcont_γ
          (fun t ht => by simpa [LiesInOn, normalNeighborhood] using hlies ht)
      · exact hcont_Tγ
    exact hcont_composed.intervalIntegrable_of_Icc hab

end Minimization.Coordinate
