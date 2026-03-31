import Exponential.NormalCoordinates
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The directional-`dexp` layer remains intentionally small: it records the along-curve
derivative interface used by the local minimization spine. -/

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

/-- A directional `dexp` package for the coordinate exponential map. This is the smaller interface
needed by the current local minimization branch: directional derivatives along one-parameter
velocity families, not a global `HasFDerivAt` theorem for `coordinateExp`. A future owner theorem
can construct this data from the actual geodesic variation/Jacobi package. -/
structure HasDirectionalDexp
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) where
  dexpDir : Velocity n → Velocity n → Velocity n
  comp_hasDerivWithinAt :
    ∀ {α : ℝ → Velocity n} {U : ℝ → Velocity n} {s : Set ℝ} {t : ℝ},
      HasDerivWithinAt α (U t) s t →
      α t ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source →
      HasDerivWithinAt
        (fun τ => coordinateExp (n := n) Gamma p (α τ))
        (dexpDir (α t) (U t)) s t

theorem hasDerivWithinAt_coordinateExp_comp
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    (dexp : HasDirectionalDexp (n := n) Gamma p)
    {α : ℝ → Velocity n} {U : ℝ → Velocity n} {s : Set ℝ} {t : ℝ}
    (hα : HasDerivWithinAt α (U t) s t)
    (hmem : α t ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    HasDerivWithinAt
      (fun τ => coordinateExp (n := n) Gamma p (α τ))
      (dexp.dexpDir (α t) (U t)) s t :=
  dexp.comp_hasDerivWithinAt hα hmem

theorem hasDerivAt_coordinateExp_line
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    (dexp : HasDirectionalDexp (n := n) Gamma p)
    {v w : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    HasDerivAt
      (fun s : ℝ => coordinateExp (n := n) Gamma p (v + s • w))
      (dexp.dexpDir v w)
      (0 : ℝ) := by
  simpa [one_smul] using
    (dexp.comp_hasDerivWithinAt
      (α := fun s : ℝ => v + s • w)
      (U := fun _ : ℝ => (1 : ℝ) • w)
      (s := Set.univ)
      ((((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v).hasDerivWithinAt)
      (by simpa))

theorem dexpDir_eq_fderiv_of_hasFDerivAt
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    (dexp : HasDirectionalDexp (n := n) Gamma p)
    {v w : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (hfd :
      HasFDerivAt (coordinateExp (n := n) Gamma p)
        (fderiv ℝ (coordinateExp (n := n) Gamma p) v) v) :
    dexp.dexpDir v w = (fderiv ℝ (coordinateExp (n := n) Gamma p) v) w := by
  have hdexp :
      HasDerivAt
        (fun s : ℝ => coordinateExp (n := n) Gamma p (v + s • w))
        (dexp.dexpDir v w)
        0 :=
    hasDerivAt_coordinateExp_line (n := n) Gamma p dexp hv
  have hfd_line :
      HasDerivAt
        (fun s : ℝ => coordinateExp (n := n) Gamma p (v + s • w))
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w)
        0 := by
    have hfd' :
        HasFDerivAt (coordinateExp (n := n) Gamma p)
          (fderiv ℝ (coordinateExp (n := n) Gamma p) v)
          (v + (0 : ℝ) • w) := by
      simpa [zero_smul, add_zero] using hfd
    simpa [Function.comp, one_smul] using
      hfd'.comp_hasDerivAt (0 : ℝ)
        (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
  exact HasDerivAt.unique hdexp hfd_line

end Exponential.Coordinate
