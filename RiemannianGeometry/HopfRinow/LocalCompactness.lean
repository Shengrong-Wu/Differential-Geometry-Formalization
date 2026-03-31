import HopfRinow.MetricLength
import Minimization.NormalNeighborhoods

/-! Design-stage skeleton for the local compactness layer.

This file should stay local: it is meant to show that every point has some sufficiently small
compact closed metric ball, without yet doing any global completeness argument. -/

namespace HopfRinow

open Metric

/-!
Target theorem inventory:

```lean
theorem exists_compact_small_closedBall
```

Possible future support lemmas:

- local chart containment for small closed balls,
- compactness transfer from Euclidean closed balls in coordinates,
- small normal-neighborhood compactness wrappers.
-/

theorem exists_compact_small_closedBall
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    ∃ r > 0, IsCompact (Metric.closedBall p r) ∧
      Metric.closedBall p r ⊆ Minimization.Coordinate.normalNeighborhood (n := n) Gamma p := by
  have hopen := Minimization.Coordinate.normalNeighborhood_open (n := n) Gamma p
  have hp : p ∈ Minimization.Coordinate.normalNeighborhood (n := n) Gamma p :=
    Minimization.Coordinate.base_mem_normalNeighborhood (n := n) Gamma p
  rcases Metric.isOpen_iff.mp hopen p hp with ⟨r, hr_pos, hr_ball⟩
  refine ⟨r / 2, half_pos hr_pos, isCompact_closedBall p (r / 2), ?_⟩
  intro x hx
  have hx' : dist p x ≤ r / 2 := by
    simpa [Metric.mem_closedBall, dist_comm] using hx
  apply hr_ball
  exact Metric.mem_ball'.2 <|
    lt_of_le_of_lt hx' (half_lt_self hr_pos)

end HopfRinow
