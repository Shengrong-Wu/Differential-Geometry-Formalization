import Weitzenbock.Weitzenbock

namespace Weitzenbock

universe u v

structure ComponentProjection (A : OneFormHodgeAlgebra) (Index : Type u) (Coeff : Type v) where
  proj : A.Ω1 → Index → Coeff

theorem weitzenbock_through
    (A : OneFormHodgeAlgebra) (α : A.Ω1)
    {β : Type u} (φ : A.Ω1 → β) :
    φ (hodgeLaplacian A α) = φ (A.rough α + A.curvatureTerm α) := by
  rw [weitzenbock_identity]

theorem weitzenbock_in_components
    (A : OneFormHodgeAlgebra) (α : A.Ω1)
    {Index : Type u} {Coeff : Type v} (P : ComponentProjection A Index Coeff) :
    ∀ idx, P.proj (hodgeLaplacian A α) idx = P.proj (A.rough α + A.curvatureTerm α) idx := by
  intro idx
  exact weitzenbock_through A α (fun ω => P.proj ω idx)

theorem indexed_weitzenbock
    (A : OneFormHodgeAlgebra) (α : A.Ω1)
    {Index : Type u} {Coeff : Type v} (P : ComponentProjection A Index Coeff)
    (hodgeComponent roughCurvatureComponent : Index → Coeff)
    (hhodge : ∀ idx, P.proj (hodgeLaplacian A α) idx = hodgeComponent idx)
    (hrhs : ∀ idx, P.proj (A.rough α + A.curvatureTerm α) idx = roughCurvatureComponent idx) :
    ∀ idx, hodgeComponent idx = roughCurvatureComponent idx := by
  intro idx
  rw [← hhodge idx, ← hrhs idx]
  exact weitzenbock_in_components A α P idx

end Weitzenbock
