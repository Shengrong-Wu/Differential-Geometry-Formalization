import HopfRinow.LocalCompactness
import HopfRinow.MetricLength
import HopfRinow.StronglyConvex
import HopfRinow.Properness

/-! Design-stage skeleton for the corrected complete→proper direction.

This file is intended to own the theorem that replaces the false minimizers→proper bridge in the
current public Hopf–Rinow packaging. -/

namespace HopfRinow

open Metric

/-!
Target theorem inventory:

```lean
theorem compact_closedBall_step

theorem compact_closedBall_of_supRadius

theorem complete_implies_proper
    (hcomplete : RiemannianComplete M) :
    RiemannianProper M
```

Future bridge output:

```lean
structure CompleteProperData (M : Type u) [PseudoMetricSpace M] : Prop where
  complete_proper : RiemannianComplete M → RiemannianProper M
```

In this copy the structure itself is already recorded in `InputConstruction.lean`; the final live
module should decide whether to move the definition here or merely instantiate it here.
-/

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

end HopfRinow
