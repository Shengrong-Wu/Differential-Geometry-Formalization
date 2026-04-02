import HopfRinow.GeodesicExtension
import HopfRinow.InputConstruction
import HopfRinow.MinExistence
import HopfRinow.Properness
import HopfRinow.CompleteProper
import HopfRinow.MinimizerExistence

/-! # Corrected public Hopf-Rinow theorem

This file assembles the live corrected theorem spine:

- `Complete → HasGeodesicExtension`
- `Complete → MinimizingGeodesicsExist`
- `Complete → RiemannianProper`
- `Proper → Complete`

The false bridge `MinimizingGeodesicsExist → RiemannianProper` is intentionally not part of this
assembly. The coordinate-level assembly near the end of the file wires the finished coordinate
properness, minimizer-existence, and direct metric geodesic-extension directions together.

Relevant owner files include:

- `HopfRinow/CompleteProper.lean`
- `HopfRinow/MinimizerExistence.lean`
-/

namespace HopfRinow

universe u

abbrev CompleteImpliesGeodesicallyComplete (M : Type u) [PseudoMetricSpace M] : Prop :=
  RiemannianComplete M → GeodesicallyComplete M

abbrev CompleteImpliesMinimizers (M : Type u) [PseudoMetricSpace M] : Prop :=
  RiemannianComplete M → MinimizingGeodesicsExist M

abbrev CompleteImpliesProper (M : Type u) [PseudoMetricSpace M] : Prop :=
  RiemannianComplete M → RiemannianProper M

abbrev ProperImpliesComplete (M : Type u) [PseudoMetricSpace M] : Prop :=
  RiemannianProper M → RiemannianComplete M

/-- The package-level Hopf-Rinow statement. -/
structure HopfRinowTheorem (M : Type u) [PseudoMetricSpace M] : Prop where
  complete_geodesic : CompleteImpliesGeodesicallyComplete M
  complete_minimizers : CompleteImpliesMinimizers M
  complete_proper : CompleteImpliesProper M
  proper_complete : ProperImpliesComplete M

theorem hopfRinowTheorem_iff
    {M : Type u} [PseudoMetricSpace M] :
    HopfRinowTheorem M ↔
      CompleteImpliesGeodesicallyComplete M ∧
        CompleteImpliesMinimizers M ∧
        CompleteImpliesProper M ∧
        ProperImpliesComplete M := by
  constructor
  · intro h
    exact ⟨h.complete_geodesic, h.complete_minimizers, h.complete_proper, h.proper_complete⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, h₄⟩

theorem completeImpliesGeodesicallyComplete
    {M : Type u} [PseudoMetricSpace M]
    (h : HopfRinowTheorem M) :
    CompleteImpliesGeodesicallyComplete M :=
  h.complete_geodesic

theorem completeImpliesMinimizers
    {M : Type u} [PseudoMetricSpace M]
    (h : HopfRinowTheorem M) :
    CompleteImpliesMinimizers M :=
  h.complete_minimizers

theorem completeImpliesProper
    {M : Type u} [PseudoMetricSpace M]
    (h : HopfRinowTheorem M) :
    CompleteImpliesProper M :=
  h.complete_proper

theorem properImpliesComplete
    {M : Type u} [PseudoMetricSpace M]
    (h : HopfRinowTheorem M) :
    ProperImpliesComplete M :=
  h.proper_complete

/-- The proper-implies-complete direction from mathlib. -/
theorem properImpliesComplete_standard
    {M : Type u} [PseudoMetricSpace M] :
    ProperImpliesComplete M := by
  intro hproper
  letI : ProperSpace M := hproper
  exact riemannianComplete_of_proper

/-- Package the three geometric Hopf-Rinow directions together with the standard metric-space
properness consequence. -/
def hopfRinowTheoremOfGeometricDirections
    {M : Type u} [PseudoMetricSpace M]
    (hgeod : CompleteImpliesGeodesicallyComplete M)
    (hmin : CompleteImpliesMinimizers M)
    (hproper : CompleteImpliesProper M) :
    HopfRinowTheorem M where
  complete_geodesic := hgeod
  complete_minimizers := hmin
  complete_proper := hproper
  proper_complete := properImpliesComplete_standard

/-- Assembly from the explicit input data package. -/
theorem hopfRinowTheorem_of_input
    {M : Type u} [PseudoMetricSpace M]
    (input : HopfRinowData M) :
    HopfRinowTheorem M where
  complete_geodesic := hasGeodesicExtension_of_complete input.geodesicExtension
  complete_minimizers := minimizingGeodesicsExist_of_complete input.minimizers
  complete_proper := input.completeProper.complete_proper
  proper_complete := properImpliesComplete_standard

/-- Assembly from the bridge layer. -/
theorem hopfRinowTheorem_of_bridge
    {M : Type u} [PseudoMetricSpace M]
    (bridge : CompleteToHopfRinowData M) :
    HopfRinowTheorem M :=
  hopfRinowTheorem_of_input (hopfRinowDataOfBridge bridge)

/-- Export the four Hopf-Rinow implications as a conjunction. -/
theorem hopfRinow_equivalences
    {M : Type u} [PseudoMetricSpace M]
    (h : HopfRinowTheorem M) :
    CompleteImpliesGeodesicallyComplete M ∧
      CompleteImpliesMinimizers M ∧
      CompleteImpliesProper M ∧
      ProperImpliesComplete M :=
  ⟨h.complete_geodesic, h.complete_minimizers, h.complete_proper, h.proper_complete⟩

/-! ### Coordinate-level assembly

Wire the three proved directions into the full `HopfRinowTheorem` for `Position n`. -/

/-- Coordinate-level Hopf-Rinow data package, assembling the three directions. -/
def coordinate_hopfRinowData
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    HopfRinowData (Exponential.Coordinate.Position n) where
  geodesicExtension := coordinate_geodesicExtensionData_direct
  minimizers := coordinate_minExistenceData Gamma
  completeProper := coordinate_completeProperData Gamma

/-- Coordinate-level Hopf-Rinow theorem, assembling from the data package. -/
theorem coordinate_hopfRinowTheorem
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    HopfRinowTheorem (Exponential.Coordinate.Position n) :=
  hopfRinowTheorem_of_input (coordinate_hopfRinowData Gamma)

end HopfRinow
