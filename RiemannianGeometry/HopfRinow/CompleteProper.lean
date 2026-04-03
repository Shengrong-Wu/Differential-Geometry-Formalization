import HopfRinow.LocalCompactness
import HopfRinow.MetricLength
import HopfRinow.Properness
import HopfRinow.InputConstruction

/-! # Complete → Proper

This file owns the corrected complete→proper direction used by the live Hopf-Rinow assembly.
At the coordinate level the final result is immediate because `Position n = Fin n → ℝ` is a
finite-dimensional normed space and hence a `ProperSpace`. The auxiliary compact-ball lemmas are
kept here because they are also useful for local compactness packaging. -/

namespace HopfRinow

open Metric

theorem exists_compact_mem_nhds_of_exists_isCompact_closedBall
    {X : Type u} [PseudoMetricSpace X] {x : X}
    (h : ∃ r, 0 < r ∧ IsCompact (Metric.closedBall x r)) :
    ∃ K, IsCompact K ∧ K ∈ nhds x := by
  rcases h with ⟨r, hr_pos, hcompact⟩
  exact ⟨Metric.closedBall x r, hcompact, Metric.closedBall_mem_nhds x hr_pos⟩

theorem weaklyLocallyCompactSpace_of_exists_isCompact_closedBall
    {X : Type u} [PseudoMetricSpace X]
    (h : ∀ x : X, ∃ r, 0 < r ∧ IsCompact (Metric.closedBall x r)) :
    WeaklyLocallyCompactSpace X := by
  refine ⟨fun x => ?_⟩
  exact exists_compact_mem_nhds_of_exists_isCompact_closedBall (h x)

theorem locallyCompactSpace_of_exists_isCompact_closedBall
    {X : Type u} [PseudoMetricSpace X]
    (h : ∀ x : X, ∃ r, 0 < r ∧ IsCompact (Metric.closedBall x r)) :
    LocallyCompactSpace X := by
  letI := weaklyLocallyCompactSpace_of_exists_isCompact_closedBall h
  infer_instance

theorem exists_isOpen_mem_isCompact_closure_of_exists_isCompact_closedBall
    {X : Type u} [PseudoMetricSpace X]
    (h : ∀ x : X, ∃ r, 0 < r ∧ IsCompact (Metric.closedBall x r))
    (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsCompact (closure U) := by
  letI := weaklyLocallyCompactSpace_of_exists_isCompact_closedBall h
  simpa using exists_isOpen_mem_isCompact_closure x

theorem coordinate_exists_isCompact_closedBall
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    ∃ r, 0 < r ∧ IsCompact (Metric.closedBall p r) := by
  rcases exists_compact_small_closedBall (n := n) Gamma p with ⟨r, hr_pos, hcompact, _⟩
  exact ⟨r, hr_pos, hcompact⟩

theorem coordinate_weaklyLocallyCompactSpace
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    WeaklyLocallyCompactSpace (Exponential.Coordinate.Position n) := by
  exact weaklyLocallyCompactSpace_of_exists_isCompact_closedBall fun p =>
    coordinate_exists_isCompact_closedBall (n := n) Gamma p

theorem coordinate_locallyCompactSpace
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n) :
    LocallyCompactSpace (Exponential.Coordinate.Position n) := by
  exact locallyCompactSpace_of_exists_isCompact_closedBall fun p =>
    coordinate_exists_isCompact_closedBall (n := n) Gamma p

theorem coordinate_exists_isOpen_mem_isCompact_closure
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    ∃ U : Set (Exponential.Coordinate.Position n), IsOpen U ∧ p ∈ U ∧ IsCompact (closure U) := by
  exact exists_isOpen_mem_isCompact_closure_of_exists_isCompact_closedBall
    (fun q => coordinate_exists_isCompact_closedBall (n := n) Gamma q) p

/-! ### Coordinate-level Complete → Proper

`Position n = Fin n → ℝ` is a finite-dimensional normed space over `ℝ`, hence `ProperSpace`
by Mathlib's instance resolution. The complete→proper direction is therefore immediate. -/

instance coordinate_properSpace {n : ℕ} :
    ProperSpace (Exponential.Coordinate.Position n) :=
  inferInstance

/-- At the coordinate level, completeness implies properness. This is immediate because
`Fin n → ℝ` is always proper (finite-dimensional normed space). No Christoffel data is needed. -/
theorem coordinate_complete_implies_proper
    {n : ℕ} :
    RiemannianComplete (Exponential.Coordinate.Position n) →
      RiemannianProper (Exponential.Coordinate.Position n) :=
  fun _ => riemannianProper_of_properSpace

/-- Package the coordinate-level complete→proper result into the `CompleteProperData` interface. -/
def coordinate_completeProperData
    {n : ℕ} :
    CompleteProperData (Exponential.Coordinate.Position n) where
  complete_proper := coordinate_complete_implies_proper

end HopfRinow
