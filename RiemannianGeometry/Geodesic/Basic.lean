import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic

namespace Geodesic.Coordinate

variable (n : ℕ)

/-- Coordinate position vectors in `Fin n` coordinates. -/
abbrev Position := Fin n → ℝ

/-- Coordinate velocity vectors in `Fin n` coordinates. -/
abbrev Velocity := Fin n → ℝ

/-- First-order phase-space states `(x, v)` for the geodesic ODE. -/
abbrev State := Position n × Velocity n

/-- Bundle the initial position and velocity for a coordinate geodesic problem. -/
structure InitialConditions where
  position : Position n
  velocity : Velocity n

def mkState (ic : InitialConditions n) : State n :=
  (ic.position, ic.velocity)

def statePosition (z : State n) : Position n :=
  z.1

def stateVelocity (z : State n) : Velocity n :=
  z.2

@[simp] theorem mkState_position (ic : InitialConditions n) :
    statePosition n (mkState n ic) = ic.position :=
  rfl

@[simp] theorem mkState_velocity (ic : InitialConditions n) :
    stateVelocity n (mkState n ic) = ic.velocity :=
  rfl

@[simp] theorem statePosition_mk (x : Position n) (v : Velocity n) :
    statePosition n (x, v) = x :=
  rfl

@[simp] theorem stateVelocity_mk (x : Position n) (v : Velocity n) :
    stateVelocity n (x, v) = v :=
  rfl

end Geodesic.Coordinate
