import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Variation.CurveLength
import Variation.FirstVariationEnergy

namespace Variation.Curve

open scoped BigOperators

variable {n : ℕ}

/-- Boundary term in the first variation of length, stated for unit-speed slices. -/
def lengthBoundaryTerm (Gamma : CovariantVariation n) (s t : ℝ) : ℝ :=
  pairing n (Gamma.variationField s t) (Gamma.tangentField s t)

/-- Interior term in the first variation of length, stated for unit-speed slices. -/
noncomputable def lengthInteriorTerm (Gamma : CovariantVariation n) (a b s : ℝ) : ℝ :=
  ∫ t in a..b, pairing n (Gamma.variationField s t) (Gamma.accelerationField s t)

/-- The value predicted by the first variation of length formula. -/
noncomputable def firstVariationLengthValue
    (Gamma : CovariantVariation n) (a b s : ℝ) : ℝ :=
  lengthBoundaryTerm (n := n) Gamma s b - lengthBoundaryTerm (n := n) Gamma s a
    - lengthInteriorTerm (n := n) Gamma a b s

/-- Under fixed endpoints, the boundary contribution in the first variation of length vanishes. -/
theorem firstVariationLengthValue_of_fixedEndpoints
    {Gamma : CovariantVariation n} {a b s : ℝ}
    (hfixed : FixedEndpointsAt n Gamma.toCurveVariation s a b)
    : firstVariationLengthValue (n := n) Gamma a b s =
        -lengthInteriorTerm (n := n) Gamma a b s := by
  rcases hfixed with ⟨ha, hb⟩
  simp [firstVariationLengthValue, lengthBoundaryTerm, lengthInteriorTerm, ha, hb]

/-- First variation of length for unit-speed slices: once the derivative formula is available and
the interior term detects geodesicity, vanishing first variation is equivalent to the geodesic
equation. -/
theorem firstVariationOfLength_unitSpeed
    {Gamma : CovariantVariation n} {a b s : ℝ}
    (_hunit : UnitSpeedAt Gamma.toCurveVariation s)
    (hfixed : FixedEndpointsAt n Gamma.toCurveVariation s a b)
    (hformula :
      HasDerivAt
        (fun s' => variationLength (n := n) Gamma.toCurveVariation a b s')
        (firstVariationLengthValue (n := n) Gamma a b s) s)
    (hdetect :
      lengthInteriorTerm (n := n) Gamma a b s = 0 ↔
        IsGeodesicSliceAt (n := n) Gamma s) :
    HasDerivAt (fun s' => variationLength (n := n) Gamma.toCurveVariation a b s') 0 s ↔
      IsGeodesicSliceAt (n := n) Gamma s := by
  have hvalue :
      firstVariationLengthValue (n := n) Gamma a b s =
        -lengthInteriorTerm (n := n) Gamma a b s :=
    firstVariationLengthValue_of_fixedEndpoints (n := n) hfixed
  constructor
  · intro hzero
    have hderiv :
        firstVariationLengthValue (n := n) Gamma a b s = 0 :=
      HasDerivAt.unique hformula hzero
    have hinterior : lengthInteriorTerm (n := n) Gamma a b s = 0 := by
      rw [hvalue] at hderiv
      linarith
    exact hdetect.mp hinterior
  · intro hgeod
    have hinterior : lengthInteriorTerm (n := n) Gamma a b s = 0 :=
      hdetect.mpr hgeod
    simpa [hvalue, hinterior] using hformula

/-- A fixed-endpoint unit-speed geodesic slice is critical for length once the first variation
formula is identified. -/
theorem lengthCritical_of_geodesic
    {Gamma : CovariantVariation n} {a b s : ℝ}
    (hunit : UnitSpeedAt Gamma.toCurveVariation s)
    (hfixed : FixedEndpointsAt n Gamma.toCurveVariation s a b)
    (hformula :
      HasDerivAt
        (fun s' => variationLength (n := n) Gamma.toCurveVariation a b s')
        (firstVariationLengthValue (n := n) Gamma a b s) s)
    (hdetect :
      lengthInteriorTerm (n := n) Gamma a b s = 0 ↔
        IsGeodesicSliceAt (n := n) Gamma s)
    (hgeod : IsGeodesicSliceAt (n := n) Gamma s) :
    HasDerivAt (fun s' => variationLength (n := n) Gamma.toCurveVariation a b s') 0 s :=
  (firstVariationOfLength_unitSpeed (n := n) hunit hfixed hformula hdetect).2 hgeod

/-- Conversely, a vanishing first variation of length forces the geodesic equation whenever the
interior term detects geodesicity. -/
theorem geodesic_of_lengthCritical
    {Gamma : CovariantVariation n} {a b s : ℝ}
    (hunit : UnitSpeedAt Gamma.toCurveVariation s)
    (hfixed : FixedEndpointsAt n Gamma.toCurveVariation s a b)
    (hformula :
      HasDerivAt
        (fun s' => variationLength (n := n) Gamma.toCurveVariation a b s')
        (firstVariationLengthValue (n := n) Gamma a b s) s)
    (hdetect :
      lengthInteriorTerm (n := n) Gamma a b s = 0 ↔
        IsGeodesicSliceAt (n := n) Gamma s)
    (hzero :
      HasDerivAt (fun s' => variationLength (n := n) Gamma.toCurveVariation a b s') 0 s) :
    IsGeodesicSliceAt (n := n) Gamma s :=
  (firstVariationOfLength_unitSpeed (n := n) hunit hfixed hformula hdetect).1 hzero

/-- Public criticality predicate for the first variation of length on a chosen reference slice.
The unit-speed and formula/detection hypotheses remain explicit at the admissible-variation level;
only the quantification over all endpoint-fixed variations is bundled here. -/
def LengthCriticalSlice
    (Gamma₀ : CovariantVariation n) (s₀ a b : ℝ) : Prop :=
  ∀ (Gamma : CovariantVariation n) (s : ℝ),
    AdmissibleVariationAt (n := n) Gamma₀ s₀ a b Gamma s →
    UnitSpeedAt Gamma.toCurveVariation s →
    ∀ (_hformula :
        HasDerivAt
          (fun s' => variationLength (n := n) Gamma.toCurveVariation a b s')
          (firstVariationLengthValue (n := n) Gamma a b s) s)
      (_hdetect :
        lengthInteriorTerm (n := n) Gamma a b s = 0 ↔
          IsGeodesicSliceAt (n := n) Gamma s),
      HasDerivAt (fun s' => variationLength (n := n) Gamma.toCurveVariation a b s') 0 s

/-- A unit-speed geodesic reference slice is length-critical for every admissible endpoint-fixed
variation through that slice. As on the energy side, the converse is kept separate until a real
variation-field realizability theorem is available. -/
theorem lengthCriticalSlice_of_geodesic
    {Gamma₀ : CovariantVariation n} {s₀ a b : ℝ}
    (hgeod :
      ∀ {Gamma : CovariantVariation n} {s : ℝ},
        SameSliceAt (n := n) Gamma.toCurveVariation Gamma₀.toCurveVariation s s₀ →
          IsGeodesicSliceAt (n := n) Gamma s) :
    LengthCriticalSlice (n := n) Gamma₀ s₀ a b := by
  intro Gamma s hadm hunit hformula hdetect
  exact
    lengthCritical_of_geodesic (n := n) hunit hadm.2 hformula hdetect
      (hgeod hadm.1)

end Variation.Curve
