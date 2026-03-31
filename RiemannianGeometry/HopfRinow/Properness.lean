import Mathlib.Topology.MetricSpace.ProperSpace

/-! Properness and completeness are kept as the stable metric-space side of the current
Hopf-Rinow assembly. -/

namespace HopfRinow

universe u

/-- Package-level properness interface for the Riemannian distance. -/
def RiemannianProper (X : Type u) [PseudoMetricSpace X] : Prop :=
  ProperSpace X

/-- Package-level completeness interface for the Riemannian distance. -/
def RiemannianComplete (X : Type u) [PseudoMetricSpace X] : Prop :=
  CompleteSpace X

theorem riemannianComplete_of_proper
    {X : Type u} [PseudoMetricSpace X] [ProperSpace X] :
    RiemannianComplete X := by
  show CompleteSpace X
  infer_instance

theorem riemannianProper_iff_properSpace
    {X : Type u} [PseudoMetricSpace X] :
    RiemannianProper X ↔ ProperSpace X :=
  Iff.rfl

theorem riemannianProper_of_properSpace
    {X : Type u} [PseudoMetricSpace X] [ProperSpace X] :
    RiemannianProper X :=
  by
    show ProperSpace X
    infer_instance

end HopfRinow
