import Exponential.NormalCoordinates

namespace Minimization.Coordinate

open scoped Topology

variable {n : ℕ}

/-- The normal neighborhood around `p` given by the target of the coordinate exponential chart. -/
noncomputable def normalNeighborhood
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    Set (Exponential.Coordinate.Position n) :=
  (Exponential.Coordinate.normalCoordinateChart (n := n) Gamma p).source

/-- The normal neighborhood is exactly the target of the coordinate exponential partial
homeomorphism. -/
@[simp] theorem normalNeighborhood_eq
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    normalNeighborhood (n := n) Gamma p =
      (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).target :=
  rfl

/-- Normal neighborhoods are open because they are chart domains. -/
theorem normalNeighborhood_open
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    IsOpen (normalNeighborhood (n := n) Gamma p) :=
  (Exponential.Coordinate.normalCoordinateChart (n := n) Gamma p).open_source

/-- The coordinate exponential map recovers points from their normal coordinates on the normal
neighborhood. -/
theorem coordinateExp_normalCoordinates_eq
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    Set.EqOn
      (fun x =>
        Exponential.Coordinate.coordinateExp (n := n) Gamma p
          (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x))
      id
      (normalNeighborhood (n := n) Gamma p) := by
  simpa [normalNeighborhood] using
    Exponential.Coordinate.coordinateExp_normalCoordinates_roundtrip (n := n) Gamma p

/-- The base point lies in its normal neighborhood. -/
theorem base_mem_normalNeighborhood
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    p ∈ normalNeighborhood (n := n) Gamma p := by
  change p ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).target
  exact Exponential.Coordinate.base_mem_coordinateExpPartialHomeomorph_target (n := n) Gamma p

/-- The normal coordinates of the base point are zero. -/
theorem normalCoordinates_base
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    Exponential.Coordinate.normalCoordinates (n := n) Gamma p p = 0 :=
  Exponential.Coordinate.normalCoordinates_base (n := n) Gamma p

/-- The coordinate exponential map inverts the normal-coordinate chart on the chart source. -/
theorem normalCoordinates_coordinateExp_eq
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    Exponential.Coordinate.normalCoordinates (n := n) Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) = v :=
  Exponential.Coordinate.normalCoordinates_coordinateExp (n := n) Gamma p hv

/-- The normal radius of a point is the Euclidean norm of its normal coordinates. -/
noncomputable def normalRadius
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) : ℝ :=
  ‖WithLp.toLp 2 (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x)‖

@[simp] theorem normalRadius_eq
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) :
    normalRadius (n := n) Gamma p x =
      ‖WithLp.toLp 2 (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x)‖ :=
  rfl

end Minimization.Coordinate
