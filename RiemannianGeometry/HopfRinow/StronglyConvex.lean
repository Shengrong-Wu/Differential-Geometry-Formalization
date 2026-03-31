import HopfRinow.DistanceRealizer
import HopfRinow.LocalCompactness
import Minimization

/-! Design-stage skeleton for strongly convex normal neighborhoods.

This file is where the local analytic results from the minimization branch are supposed to be
repackaged into a global small-ball interface usable by Hopf–Rinow. -/

namespace HopfRinow

/-!
Planned contents:

- a small-ball wrapper such as `StronglyConvexBall`,
- existence of strongly convex normal balls around every point,
- uniqueness and minimizing properties of short geodesics inside such balls,
- recognition of metric geodesics as the unique local smooth/radial geodesics in those balls.

Target theorem inventory:

```lean
structure StronglyConvexBall ...

theorem exists_stronglyConvexBall

theorem metric_geodesic_is_smooth_on_stronglyConvexBall
```
-/

open Metric

/-- A small closed ball around `center` that lies inside the normal neighborhood package already
exported by the local exponential chart. Later minimizing/uniqueness consequences should attach to
this wrapper instead of reopening the local compactness argument. -/
structure StronglyConvexBall
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (center : Exponential.Coordinate.Position n) where
  radius : ℝ
  radius_pos : 0 < radius
  isCompact_closedBall : IsCompact (Metric.closedBall center radius)
  closedBall_subset_normalNeighborhood :
    Metric.closedBall center radius ⊆
      Minimization.Coordinate.normalNeighborhood (n := n) Gamma center

theorem exists_stronglyConvexBall
    {n : ℕ}
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (center : Exponential.Coordinate.Position n) :
    Nonempty (StronglyConvexBall (n := n) Gamma center) := by
  rcases exists_compact_small_closedBall (n := n) Gamma center with
    ⟨r, hr_pos, hcompact, hsubset⟩
  exact ⟨⟨r, hr_pos, hcompact, hsubset⟩⟩

theorem StronglyConvexBall.mem_normalNeighborhood
    {n : ℕ}
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {center x : Exponential.Coordinate.Position n}
    (ball : StronglyConvexBall (n := n) Gamma center)
    (hx : x ∈ Metric.closedBall center ball.radius) :
    x ∈ Minimization.Coordinate.normalNeighborhood (n := n) Gamma center :=
  ball.closedBall_subset_normalNeighborhood hx

end HopfRinow
