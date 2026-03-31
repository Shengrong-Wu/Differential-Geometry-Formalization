import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import CurvatureFormalization.CoordinateBianchi

open BigOperators Finset

namespace CurvatureFormalization.Coordinate

variable {n : ℕ}

/--
`PartialTerm n` represents the directional derivative contribution
`∂_dir R^i_{j,kl}` in coordinates.
-/
abbrev PartialTerm (n : ℕ) := Form2 n → Fin n → Fin n → Fin n → Fin n → Fin n → ℝ

def covariantDerivative
    (pderiv : PartialTerm n) (A : Form1 n) (R : Form2 n)
    (dir i j k l : Fin n) : ℝ :=
  pderiv R dir i j k l +
    ∑ m : Fin n,
      (A i m dir * R m j k l
        - R i m k l * A m j dir
        - A m k dir * R i j m l
        - A m l dir * R i j k m)

def cyclicCovariantDerivative
    (pderiv : PartialTerm n) (A : Form1 n) (R : Form2 n)
    (i j e k l : Fin n) : ℝ :=
  covariantDerivative pderiv A R e i j k l +
    covariantDerivative pderiv A R k i j l e +
    covariantDerivative pderiv A R l i j e k

/--
Specialized bridge theorem: once you prove that the cyclic covariant derivative
matches the already-formalized component expression for `(d_∇ R)^i_{j,ekl}`,
the classical indexed second Bianchi identity follows immediately.
-/
theorem classical_second_bianchi_cyclic_of_bridge
    (D : CoordDiffData n) (pderiv : PartialTerm n)
    (A : Form1 n)
    (hbridge :
      ∀ i j e k l : Fin n,
        cyclicCovariantDerivative pderiv A (curvature (coordAlgebra n D) ⟨A⟩) i j e k l =
          D.d2 (curvature (coordAlgebra n D) ⟨A⟩) i j e k l
            + ∑ m : Fin n,
                (A i m e * curvature (coordAlgebra n D) ⟨A⟩ m j k l
                  + A i m k * curvature (coordAlgebra n D) ⟨A⟩ m j l e
                  + A i m l * curvature (coordAlgebra n D) ⟨A⟩ m j e k)
            - ∑ m : Fin n,
                (curvature (coordAlgebra n D) ⟨A⟩ i m e k * A m j l
                  + curvature (coordAlgebra n D) ⟨A⟩ i m k l * A m j e
                  + curvature (coordAlgebra n D) ⟨A⟩ i m l e * A m j k)) :
    ∀ i j e k l : Fin n,
      cyclicCovariantDerivative pderiv A (curvature (coordAlgebra n D) ⟨A⟩) i j e k l = 0 := by
  intro i j e k l
  rw [hbridge i j e k l]
  exact classical_second_bianchi (n := n) D A i j e k l

end CurvatureFormalization.Coordinate
