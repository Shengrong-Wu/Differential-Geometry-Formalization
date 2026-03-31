import Mathlib.Algebra.Group.Basic
import Metric.Musical

namespace LeviCivita

universe u v

/-- Minimal ambient data for Levi-Civita statements: a bracket on vector fields and a derivation on
scalar fields. This keeps the API abstract and reusable across bundled/global and local/coordinate
presentations. -/
structure ConnectionContext (V : Type u) (S : Type v) where
  bracket : V → V → V
  deriv : V → S → S

/-- An abstract affine connection on vector fields, encoded as a bilinear operator satisfying the
Leibniz rule in the second argument. -/
structure CovariantDerivative (V : Type u) (S : Type v)
    [Add V] [SMul S V] (C : ConnectionContext V S) where
  toFun : V → V → V
  add_left : ∀ (X Y Z : V), toFun (X + Y) Z = toFun X Z + toFun Y Z
  smul_left : ∀ (f : S) (X Y : V), toFun (f • X) Y = f • toFun X Y
  add_right : ∀ (X Y Z : V), toFun X (Y + Z) = toFun X Y + toFun X Z
  leibniz : ∀ (X Y : V) (f : S), toFun X (f • Y) = C.deriv X f • Y + f • toFun X Y

instance {V : Type u} {S : Type v} [Add V] [SMul S V] (C : ConnectionContext V S) :
    CoeFun (@CovariantDerivative V S _ _ C) (fun _ => V → V → V) where
  coe := CovariantDerivative.toFun

/-- A metric pairing on vector fields with values in scalar fields. -/
abbrev MetricPairing (V : Type u) (S : Type v) := V → V → S

/-- The family of covariant derivatives over a fixed ambient connection context. -/
abbrev DerivType
    {V : Type u} {S : Type v} [Add V] [SMul S V] (C : ConnectionContext V S) : Type _ :=
  @CovariantDerivative V S _ _ C

/-- Metric compatibility for an abstract connection. -/
def MetricCompatible
    {V : Type u} {S : Type v}
    [Add V] [SMul S V] [Add S]
    (g : MetricPairing V S) (C : ConnectionContext V S)
    (nabla : DerivType C) : Prop :=
  ∀ X Y Z, C.deriv X (g Y Z) = g (nabla X Y) Z + g Y (nabla X Z)

/-- Torsion freeness for an abstract connection. -/
def TorsionFree
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V]
    (C : ConnectionContext V S)
    (nabla : DerivType C) : Prop :=
  ∀ X Y, nabla X Y - nabla Y X = C.bracket X Y

/-- The bundled Levi-Civita predicate. -/
def IsLeviCivita
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S]
    (g : MetricPairing V S) (C : ConnectionContext V S)
    (nabla : DerivType C) : Prop :=
  MetricCompatible g C nabla ∧ TorsionFree C nabla

/-- Nondegeneracy/extensionality of the metric pairing in the first slot. -/
def MetricExtensional
    {V : Type u} {S : Type v} (g : MetricPairing V S) : Prop :=
  ∀ U V', (∀ W, g U W = g V' W) → U = V'

theorem isLeviCivita_metricCompatible
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S]
    {g : MetricPairing V S} {C : ConnectionContext V S} {nabla : DerivType C}
    (h : IsLeviCivita g C nabla) :
    MetricCompatible g C nabla :=
  h.1

theorem isLeviCivita_torsionFree
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S]
    {g : MetricPairing V S} {C : ConnectionContext V S} {nabla : DerivType C}
    (h : IsLeviCivita g C nabla) :
    TorsionFree C nabla :=
  h.2

theorem mk_isLeviCivita
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S]
    {g : MetricPairing V S} {C : ConnectionContext V S} {nabla : DerivType C}
    (hmetric : MetricCompatible g C nabla) (htorsion : TorsionFree C nabla) :
    IsLeviCivita g C nabla :=
  ⟨hmetric, htorsion⟩

theorem two_smul_cancel_real {a b : ℝ} (h : (2 : ℝ) • a = (2 : ℝ) • b) : a = b := by
  have h' : (2 : ℝ) * a = (2 : ℝ) * b := by
    simpa [two_smul, two_mul] using h
  linarith

section TangentMetric

open scoped Bundle
open Bundle

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

/-- The Riemannian metric on a tangent space is extensional in the sense required by the abstract
Koszul uniqueness argument. -/
theorem tangentMetricExtensional (x : M) :
    MetricExtensional (fun v w : TangentSpace I x => Metric.tangentInner x v w) := by
  intro U V h
  exact Metric.ext_of_flat (I := I) (M := M) x h

end TangentMetric

end LeviCivita
