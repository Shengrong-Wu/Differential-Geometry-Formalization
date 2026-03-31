import Bochner.Bochner

namespace Bochner

universe u v

/--
`ComponentProjection` packages the operation of reading off a chosen coefficient
from an `E`-valued 2-form.
-/
structure ComponentProjection (A : BundleConnectionAlgebra) (Index : Type u) (Coeff : Type v) where
  proj : A.ΩE2 → Index → Coeff

theorem covariant_square_through
    (A : BundleConnectionAlgebra) (conn : ConnectionForm A) (s : A.ΩE0)
    {β : Type u} (φ : A.ΩE2 → β) :
    φ (covariantDeriv1 A conn (covariantDeriv0 A conn s)) = φ (curvatureAction A conn s) := by
  rw [covariant_square_eq_curvature_action]

theorem covariant_square_in_components
    (A : BundleConnectionAlgebra) (conn : ConnectionForm A) (s : A.ΩE0)
    {Index : Type u} {Coeff : Type v} (P : ComponentProjection A Index Coeff) :
    ∀ idx,
      P.proj (covariantDeriv1 A conn (covariantDeriv0 A conn s)) idx =
        P.proj (curvatureAction A conn s) idx := by
  intro idx
  exact covariant_square_through A conn s (fun ω => P.proj ω idx)

/--
Bridge theorem for the covector commutator: once the left-hand side is
identified with the antisymmetrized second covariant derivative and the
right-hand side with the curvature action, the indexed identity follows.
-/
theorem covector_commutator_from_bridge
    (A : BundleConnectionAlgebra) (conn : ConnectionForm A) (α : A.ΩE0)
    {Index : Type u} {Coeff : Type v} (P : ComponentProjection A Index Coeff)
    (commutatorComponent curvatureComponent : Index → Coeff)
    (hcomm :
      ∀ idx,
        P.proj (covariantDeriv1 A conn (covariantDeriv0 A conn α)) idx =
          commutatorComponent idx)
    (hcurv :
      ∀ idx,
        P.proj (curvatureAction A conn α) idx = curvatureComponent idx) :
    ∀ idx, commutatorComponent idx = curvatureComponent idx := by
  intro idx
  rw [← hcomm idx, ← hcurv idx]
  exact covariant_square_in_components A conn α P idx

end Bochner
