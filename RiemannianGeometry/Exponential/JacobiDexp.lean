import Exponential.Differentiability
import Exponential.LocalRiemannianData
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! This file is the unique adapter from differentiability of the coordinate exponential map to
`HasDirectionalDexp`. It provides both witness-based and witness-free constructors. -/

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

/-- Constructor: pointwise Fréchet differentiability of the coordinate exponential map on the
chart source yields the directional `dexp` package. -/
noncomputable def hasDirectionalDexp_of_coordinateExpDifferentiability
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    (hdiff :
      ∀ v : Velocity n,
        v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source →
          HasFDerivAt (coordinateExp (n := n) Gamma p)
            (fderiv ℝ (coordinateExp (n := n) Gamma p) v) v) :
    HasDirectionalDexp (n := n) Gamma p where
  dexpDir v w := (fderiv ℝ (coordinateExp (n := n) Gamma p) v) w
  comp_hasDerivWithinAt := by
    intro α U s t hα hmem
    have hfd :
        HasFDerivAt (coordinateExp (n := n) Gamma p)
          (fderiv ℝ (coordinateExp (n := n) Gamma p) (α t))
          (α t) :=
      hdiff (α t) hmem
    simpa [Function.comp] using hfd.comp_hasDerivWithinAt t hα

/-- Convenience constructor from `LocalRiemannianData` plus an explicit differentiability
witness. The witness is required because `LocalRiemannianData` carries only metric data. -/
noncomputable def hasDirectionalDexp_of_localRiemannianData
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Position n)
    (hdiff : CoordinateExpHasFDerivAtOnSource (n := n) data.Gamma p) :
    HasDirectionalDexp (n := n) data.Gamma p :=
  hasDirectionalDexp_of_coordinateExpDifferentiability (n := n) data.Gamma p
    (fun v hv => hdiff hv)

/-- **Witness-free** constructor for `HasDirectionalDexp` from a smooth Christoffel field.
The differentiability of `coordinateExp` is now proved (Issue 7), so no explicit witness
is needed. -/
noncomputable def hasDirectionalDexp_of_smoothChristoffel
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    HasDirectionalDexp (n := n) Gamma p :=
  hasDirectionalDexp_of_coordinateExpDifferentiability (n := n) Gamma p
    (fun v hv => coordinateExpHasFDerivAtOnSource_of_smoothChristoffel (n := n) Gamma p hv)

end Exponential.Coordinate
