import Variation.Variation

namespace Variation

universe u v

structure ComponentProjection (A : LocalConnectionVariationAlgebra) (Index : Type u)
    (Coeff : Type v) where
  proj : A.Ω2 → Index → Coeff

theorem curvature_variation_through
    (A : LocalConnectionVariationAlgebra) (conn : ConnectionForm A)
    {β : Type u} (φ : A.Ω2 → β) :
    φ (A.deriv2 (curvature A conn)) =
      φ (covariantVariation A conn (connectionVariation A conn)) := by
  rw [curvature_variation_identity]

theorem curvature_variation_in_components
    (A : LocalConnectionVariationAlgebra) (conn : ConnectionForm A)
    {Index : Type u} {Coeff : Type v} (P : ComponentProjection A Index Coeff) :
    ∀ idx,
      P.proj (A.deriv2 (curvature A conn)) idx =
        P.proj (covariantVariation A conn (connectionVariation A conn)) idx := by
  intro idx
  exact curvature_variation_through A conn (fun ω => P.proj ω idx)

theorem indexed_curvature_variation
    (A : LocalConnectionVariationAlgebra) (conn : ConnectionForm A)
    {Index : Type u} {Coeff : Type v} (P : ComponentProjection A Index Coeff)
    (lhs rhs : Index → Coeff)
    (hlhs : ∀ idx, P.proj (A.deriv2 (curvature A conn)) idx = lhs idx)
    (hrhs : ∀ idx, P.proj (covariantVariation A conn (connectionVariation A conn)) idx = rhs idx) :
    ∀ idx, lhs idx = rhs idx := by
  intro idx
  rw [← hlhs idx, ← hrhs idx]
  exact curvature_variation_in_components A conn P idx

end Variation
