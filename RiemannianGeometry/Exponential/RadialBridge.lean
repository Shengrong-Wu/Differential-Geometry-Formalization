import Exponential.NormalCoordinates

/-! This owner file keeps `radialSource` as the spray-owned source of truth for the line-segment
arguments used by the radial geodesic branch. -/

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

/-- The spray-owned radial source domain for scaling arguments. This is the honest radial domain
coming from the uniform local geodesic flow, as opposed to the inverse-function-theorem source of
`coordinateExpPartialHomeomorph`. -/
abbrev radialSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) : Set (Velocity n) :=
  coordinateExpSource (n := n) Gamma p

theorem isOpen_radialSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    IsOpen (radialSource (n := n) Gamma p) :=
  isOpen_coordinateExpSource (n := n) Gamma p

theorem zero_mem_radialSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    (0 : Velocity n) ∈ radialSource (n := n) Gamma p :=
  zero_mem_coordinateExpSource (n := n) Gamma p

/-- The spray-owned radial source is star-shaped along every segment from the origin to a source
velocity. This is the domain statement needed by the radial geodesic branch. -/
theorem smul_mem_radialSource_of_mem
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ radialSource (n := n) Gamma p)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • v ∈ radialSource (n := n) Gamma p := by
  classical
  let data :=
    Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 (baseState n p)
  have hvnorm : ‖v‖ < data.ε * data.r := by
    simpa [radialSource, coordinateExpSource, localCoordinateExponentialSource, data,
      Metric.mem_ball, dist_eq_norm] using hv
  have htnorm : ‖t • v‖ < data.ε * data.r := by
    calc
      ‖t • v‖ = |t| * ‖v‖ := by simpa [Real.norm_eq_abs] using norm_smul t v
      _ ≤ ‖v‖ := by
        have habs : |t| ≤ 1 := by
          rcases ht with ⟨ht0, ht1⟩
          simpa [abs_of_nonneg ht0] using ht1
        nlinarith [norm_nonneg v]
      _ < data.ε * data.r := hvnorm
  simpa [radialSource, coordinateExpSource, localCoordinateExponentialSource, data,
    Metric.mem_ball, dist_eq_norm] using htnorm

/-- The radial scaling path stays inside the spray-owned source domain on the unit interval. -/
theorem mapsTo_line_radialSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ radialSource (n := n) Gamma p) :
    Set.MapsTo (fun t : ℝ => t • v) (Set.Icc (0 : ℝ) 1) (radialSource (n := n) Gamma p) := by
  intro t ht
  exact smul_mem_radialSource_of_mem (n := n) Gamma p hv ht

end Exponential.Coordinate
