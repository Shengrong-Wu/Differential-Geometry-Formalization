import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Variation.CurveEnergy

namespace Variation.Curve

open scoped BigOperators

variable {n : ℕ}

/-- Two variations share the same reference slice when their base curves agree pointwise. -/
def SameSliceAt
    (Gamma Gamma' : CurveVariation n)
    (s s' : ℝ) : Prop :=
  ∀ t, Gamma.family s t = Gamma'.family s' t

theorem sameSliceAt_iff
    {Gamma Gamma' : CurveVariation n} {s s' : ℝ} :
    SameSliceAt (n := n) Gamma Gamma' s s' ↔
      ∀ t, Gamma.family s t = Gamma'.family s' t :=
  Iff.rfl

/-- A covariant variation is admissible for the chosen reference slice when it runs through the
same curve and fixes the endpoints on the comparison interval. -/
def AdmissibleVariationAt
    (Gamma₀ : CovariantVariation n) (s₀ a b : ℝ)
    (Gamma : CovariantVariation n) (s : ℝ) : Prop :=
  SameSliceAt (n := n) Gamma.toCurveVariation Gamma₀.toCurveVariation s s₀ ∧
    FixedEndpointsAt n Gamma.toCurveVariation s a b

/-- Boundary term in the first variation of energy. -/
def energyBoundaryTerm (Gamma : CovariantVariation n) (s t : ℝ) : ℝ :=
  pairing n (Gamma.variationField s t) (Gamma.tangentField s t)

/-- Interior term in the first variation of energy. -/
noncomputable def energyInteriorTerm (Gamma : CovariantVariation n) (a b s : ℝ) : ℝ :=
  ∫ t in a..b, pairing n (Gamma.variationField s t) (Gamma.accelerationField s t)

/-- The value predicted by the first variation of energy formula. -/
noncomputable def firstVariationEnergyValue
    (Gamma : CovariantVariation n) (a b s : ℝ) : ℝ :=
  energyBoundaryTerm (n := n) Gamma s b - energyBoundaryTerm (n := n) Gamma s a
    - energyInteriorTerm (n := n) Gamma a b s

/-- The geodesic condition for the `s`-slice of a covariant variation. -/
def IsGeodesicSliceAt (Gamma : CovariantVariation n) (s : ℝ) : Prop :=
  ∀ t, Gamma.accelerationField s t = 0

/-- Under fixed endpoints, the boundary contribution in the first variation of energy vanishes. -/
theorem firstVariationEnergyValue_of_fixedEndpoints
    {Gamma : CovariantVariation n} {a b s : ℝ}
    (hfixed : FixedEndpointsAt n Gamma.toCurveVariation s a b) :
    firstVariationEnergyValue (n := n) Gamma a b s =
      -energyInteriorTerm (n := n) Gamma a b s := by
  rcases hfixed with ⟨ha, hb⟩
  simp [firstVariationEnergyValue, energyBoundaryTerm, energyInteriorTerm, ha, hb]

/-- First variation of energy: once the derivative formula is available and the interior term
detects geodesicity, vanishing first variation is equivalent to the geodesic equation. -/
theorem firstVariationOfEnergy
    {Gamma : CovariantVariation n} {a b s : ℝ}
    (hfixed : FixedEndpointsAt n Gamma.toCurveVariation s a b)
    (hformula :
      HasDerivAt
        (fun s' => variationEnergy (n := n) Gamma.toCurveVariation a b s')
        (firstVariationEnergyValue (n := n) Gamma a b s) s)
    (hdetect :
      energyInteriorTerm (n := n) Gamma a b s = 0 ↔
        IsGeodesicSliceAt (n := n) Gamma s) :
    HasDerivAt (fun s' => variationEnergy (n := n) Gamma.toCurveVariation a b s') 0 s ↔
      IsGeodesicSliceAt (n := n) Gamma s := by
  have hvalue :
      firstVariationEnergyValue (n := n) Gamma a b s =
        -energyInteriorTerm (n := n) Gamma a b s :=
    firstVariationEnergyValue_of_fixedEndpoints (n := n) hfixed
  constructor
  · intro hzero
    have hderiv :
        firstVariationEnergyValue (n := n) Gamma a b s = 0 :=
      HasDerivAt.unique hformula hzero
    have hinterior : energyInteriorTerm (n := n) Gamma a b s = 0 := by
      rw [hvalue] at hderiv
      linarith
    exact hdetect.mp hinterior
  · intro hgeod
    have hinterior : energyInteriorTerm (n := n) Gamma a b s = 0 :=
      hdetect.mpr hgeod
    simpa [hvalue, hinterior] using hformula

/-- A fixed-endpoint slice satisfying the geodesic equation is critical for the energy
functional once the first variation formula is identified. -/
theorem energyCritical_of_geodesic
    {Gamma : CovariantVariation n} {a b s : ℝ}
    (hfixed : FixedEndpointsAt n Gamma.toCurveVariation s a b)
    (hformula :
      HasDerivAt
        (fun s' => variationEnergy (n := n) Gamma.toCurveVariation a b s')
        (firstVariationEnergyValue (n := n) Gamma a b s) s)
    (hdetect :
      energyInteriorTerm (n := n) Gamma a b s = 0 ↔
        IsGeodesicSliceAt (n := n) Gamma s)
    (hgeod : IsGeodesicSliceAt (n := n) Gamma s) :
    HasDerivAt (fun s' => variationEnergy (n := n) Gamma.toCurveVariation a b s') 0 s :=
  (firstVariationOfEnergy (n := n) hfixed hformula hdetect).2 hgeod

/-- Conversely, a zero first variation forces the geodesic equation whenever the interior term
detects geodesicity. -/
theorem geodesic_of_energyCritical
    {Gamma : CovariantVariation n} {a b s : ℝ}
    (hfixed : FixedEndpointsAt n Gamma.toCurveVariation s a b)
    (hformula :
      HasDerivAt
        (fun s' => variationEnergy (n := n) Gamma.toCurveVariation a b s')
        (firstVariationEnergyValue (n := n) Gamma a b s) s)
    (hdetect :
      energyInteriorTerm (n := n) Gamma a b s = 0 ↔
        IsGeodesicSliceAt (n := n) Gamma s)
    (hzero :
      HasDerivAt (fun s' => variationEnergy (n := n) Gamma.toCurveVariation a b s') 0 s) :
    IsGeodesicSliceAt (n := n) Gamma s :=
  (firstVariationOfEnergy (n := n) hfixed hformula hdetect).1 hzero

/-- Public criticality predicate for a chosen reference slice: every admissible fixed-endpoint
variation through that slice has vanishing first variation of energy, provided the formula-level
helper hypotheses are available for that variation. -/
def EnergyCriticalSlice
    (Gamma₀ : CovariantVariation n) (s₀ a b : ℝ) : Prop :=
  ∀ (Gamma : CovariantVariation n) (s : ℝ),
    AdmissibleVariationAt (n := n) Gamma₀ s₀ a b Gamma s →
    ∀ (_hformula :
        HasDerivAt
          (fun s' => variationEnergy (n := n) Gamma.toCurveVariation a b s')
          (firstVariationEnergyValue (n := n) Gamma a b s) s)
      (_hdetect :
        energyInteriorTerm (n := n) Gamma a b s = 0 ↔
          IsGeodesicSliceAt (n := n) Gamma s),
      HasDerivAt (fun s' => variationEnergy (n := n) Gamma.toCurveVariation a b s') 0 s

/-- A geodesic reference slice is energy-critical for every admissible endpoint-fixed variation
through that slice. The converse still requires a separate realizability input and is intentionally
left downstream. -/
theorem energyCriticalSlice_of_geodesic
    {Gamma₀ : CovariantVariation n} {s₀ a b : ℝ}
    (hgeod :
      ∀ {Gamma : CovariantVariation n} {s : ℝ},
        SameSliceAt (n := n) Gamma.toCurveVariation Gamma₀.toCurveVariation s s₀ →
          IsGeodesicSliceAt (n := n) Gamma s) :
    EnergyCriticalSlice (n := n) Gamma₀ s₀ a b := by
  intro Gamma s hadm hformula hdetect
  exact
    energyCritical_of_geodesic (n := n) hadm.2 hformula hdetect
      (hgeod hadm.1)

end Variation.Curve
