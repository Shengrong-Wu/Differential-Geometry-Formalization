import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Geodesic
import HopfRinow.Properness

/-! Geodesic extension definitions and the interface boundary for the complete→extension
direction.

Design note for the copy:
- the public metric-geodesic API stays here,
- the future owner proof is expected to factor through a smooth-geodesic continuation theorem and
  a metric-geodesic bridge,
- this copy remains intentionally thin. -/

namespace HopfRinow

universe u

/-- Metric geodesic segments with constant speed `c` on a time set `s`. -/
def IsGeodesicOnWithSpeed
    (M : Type u) [PseudoMetricSpace M]
    (γ : ℝ → M) (c : ℝ) (s : Set ℝ) : Prop :=
  0 ≤ c ∧ ∀ ⦃t₁ t₂ : ℝ⦄, t₁ ∈ s → t₂ ∈ s → dist (γ t₁) (γ t₂) = c * |t₁ - t₂|

/-- A global constant-speed metric geodesic line. -/
def IsGeodesicLineWithSpeed
    (M : Type u) [PseudoMetricSpace M]
    (γ : ℝ → M) (c : ℝ) : Prop :=
  IsGeodesicOnWithSpeed M γ c Set.univ

/-- A geodesic segment on `[a,b]` extends to a global geodesic line with the same speed. -/
def GeodesicExtendsToAllTime
    (M : Type u) [PseudoMetricSpace M]
    (γ : ℝ → M) (c a b : ℝ) : Prop :=
  ∃ γ' : ℝ → M, IsGeodesicLineWithSpeed M γ' c ∧ Set.EqOn γ' γ (Set.Icc a b)

/-- Package-level geodesic completeness stated as extension of metric geodesic segments. -/
def HasGeodesicExtension (M : Type u) [PseudoMetricSpace M] : Prop :=
  ∀ ⦃a b c : ℝ⦄, a ≤ b → 0 ≤ c → ∀ γ : ℝ → M,
    IsGeodesicOnWithSpeed M γ c (Set.Icc a b) →
    GeodesicExtendsToAllTime M γ c a b

/-- Package-owned geodesic completeness interface. -/
abbrev GeodesicallyComplete (M : Type u) [PseudoMetricSpace M] : Prop :=
  HasGeodesicExtension M

theorem geodesicallyComplete_iff_hasGeodesicExtension
    {M : Type u} [PseudoMetricSpace M] :
    GeodesicallyComplete M ↔ HasGeodesicExtension M :=
  Iff.rfl

theorem geodesicallyComplete_of_hasGeodesicExtension
    {M : Type u} [PseudoMetricSpace M] (h : HasGeodesicExtension M) :
    GeodesicallyComplete M :=
  h

theorem hasGeodesicExtension_of_geodesicallyComplete
    {M : Type u} [PseudoMetricSpace M] (h : GeodesicallyComplete M) :
    HasGeodesicExtension M :=
  h

/-- Choose one global extension for a geodesic segment from the extension property. -/
noncomputable def someGeodesicExtension
    {M : Type u} [PseudoMetricSpace M]
    (h : HasGeodesicExtension M)
    {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) (γ : ℝ → M)
    (hγ : IsGeodesicOnWithSpeed M γ c (Set.Icc a b)) :
    ℝ → M :=
  Classical.choose (h hab hc γ hγ)

theorem someGeodesicExtension_isGeodesicLineWithSpeed
    {M : Type u} [PseudoMetricSpace M]
    (h : HasGeodesicExtension M)
    {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) (γ : ℝ → M)
    (hγ : IsGeodesicOnWithSpeed M γ c (Set.Icc a b)) :
    IsGeodesicLineWithSpeed M (someGeodesicExtension h hab hc γ hγ) c :=
  (Classical.choose_spec (h hab hc γ hγ)).1

theorem someGeodesicExtension_eqOn
    {M : Type u} [PseudoMetricSpace M]
    (h : HasGeodesicExtension M)
    {a b c : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) (γ : ℝ → M)
    (hγ : IsGeodesicOnWithSpeed M γ c (Set.Icc a b)) :
    Set.EqOn (someGeodesicExtension h hab hc γ hγ) γ (Set.Icc a b) :=
  (Classical.choose_spec (h hab hc γ hγ)).2

/-- Data package for the complete→geodesic-extension direction. -/
structure GeodesicExtensionData (M : Type u) [PseudoMetricSpace M] : Prop where
  complete_geodesic : RiemannianComplete M → HasGeodesicExtension M

/-
Future owner theorem expected outside this file:

theorem smoothGeodesicComplete_implies_metricGeodesicExtension
    ... :
    HasSmoothGeodesicExtension M → HasGeodesicExtension M

and then

theorem complete_implies_geodesicExtension
    ... :
    RiemannianComplete M → HasGeodesicExtension M
-/

theorem hasGeodesicExtension_of_complete
    {M : Type u} [PseudoMetricSpace M]
    (input : GeodesicExtensionData M) :
    RiemannianComplete M → HasGeodesicExtension M :=
  input.complete_geodesic

end HopfRinow
