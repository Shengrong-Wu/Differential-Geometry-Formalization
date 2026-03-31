import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Geodesic.Basic

open scoped BigOperators

namespace Variation.Curve

variable (n : ℕ)

abbrev Point := Geodesic.Coordinate.Position n
abbrev Vector := Geodesic.Coordinate.Velocity n
abbrev CurvePath := ℝ → Point n
abbrev TwoParameterFamily := ℝ → ℝ → Point n
abbrev FieldAlongVariation := ℝ → ℝ → Vector n

/-- A two-parameter variation of curves together with its `t` and `s` vector fields. -/
structure CurveVariation where
  family : TwoParameterFamily n
  tangentField : FieldAlongVariation n
  variationField : FieldAlongVariation n

theorem curveVariation_ext
    {Γ Γ' : CurveVariation n}
    (hfamily : ∀ s t, Γ.family s t = Γ'.family s t)
    (htangent : ∀ s t, Γ.tangentField s t = Γ'.tangentField s t)
    (hvariation : ∀ s t, Γ.variationField s t = Γ'.variationField s t) :
    Γ = Γ' := by
  cases Γ with
  | mk family tangent variation =>
      cases Γ' with
      | mk family' tangent' variation' =>
          have hfamily' : family = family' := by
            funext s t
            exact hfamily s t
          have htangent' : tangent = tangent' := by
            funext s t
            exact htangent s t
          have hvariation' : variation = variation' := by
            funext s t
            exact hvariation s t
          simp [hfamily', htangent', hvariation']

theorem curveVariation_ext_iff
    {Γ Γ' : CurveVariation n} :
    Γ = Γ' ↔
      (∀ s t, Γ.family s t = Γ'.family s t) ∧
      (∀ s t, Γ.tangentField s t = Γ'.tangentField s t) ∧
      ∀ s t, Γ.variationField s t = Γ'.variationField s t := by
  constructor
  · intro h
    subst h
    simp
  · intro h
    exact curveVariation_ext (n := n) h.1 h.2.1 h.2.2

/-- Fixed-endpoint variations have vanishing variation field at the endpoints. -/
def FixedEndpointsAt (Gamma : CurveVariation n) (s0 a b : ℝ) : Prop :=
  Gamma.variationField s0 a = 0 ∧ Gamma.variationField s0 b = 0

theorem fixedEndpointsAt_iff
    {Gamma : CurveVariation n} {s0 a b : ℝ} :
    FixedEndpointsAt n Gamma s0 a b ↔
      Gamma.variationField s0 a = 0 ∧ Gamma.variationField s0 b = 0 :=
  Iff.rfl

/-- Euclidean pairing on coordinate vector fields. -/
def pairing (v w : Vector n) : ℝ :=
  ∑ i : Fin n, v i * w i

theorem pairing_comm (v w : Vector n) :
    pairing n v w = pairing n w v := by
  simp [pairing, mul_comm]

theorem pairing_add_left (u v w : Vector n) :
    pairing n (u + v) w = pairing n u w + pairing n v w := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (u v w : Vector n) :
    pairing n u (v + w) = pairing n u v + pairing n u w := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_smul_left (a : ℝ) (v w : Vector n) :
    pairing n (a • v) w = a * pairing n v w := by
  calc
    pairing n (a • v) w = ∑ i : Fin n, (a * v i) * w i := by
      simp [pairing]
    _ = ∑ i : Fin n, a * (v i * w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = a * pairing n v w := by
      rw [pairing, Finset.mul_sum]

theorem pairing_smul_right (a : ℝ) (v w : Vector n) :
    pairing n v (a • w) = a * pairing n v w := by
  rw [pairing_comm, pairing_smul_left, pairing_comm]

theorem pairing_self_nonneg (v : Vector n) :
    0 ≤ pairing n v v := by
  rw [pairing]
  exact Finset.sum_nonneg fun i hi => mul_self_nonneg (v i)

@[simp] theorem pairing_zero_left (v : Vector n) :
    pairing n 0 v = 0 := by
  simp [pairing]

@[simp] theorem pairing_zero_right (v : Vector n) :
    pairing n v 0 = 0 := by
  simp [pairing]

/-- A variation equipped with the covariant derivatives needed for first variation formulas. -/
structure CovariantVariation extends CurveVariation n where
  nablaS_T : FieldAlongVariation n
  nablaT_V : FieldAlongVariation n
  accelerationField : FieldAlongVariation n

theorem covariantVariation_ext
    {Γ Γ' : CovariantVariation n}
    (hfamily : ∀ s t, Γ.family s t = Γ'.family s t)
    (htangent : ∀ s t, Γ.tangentField s t = Γ'.tangentField s t)
    (hvariation : ∀ s t, Γ.variationField s t = Γ'.variationField s t)
    (hnablaST : ∀ s t, Γ.nablaS_T s t = Γ'.nablaS_T s t)
    (hnablaTV : ∀ s t, Γ.nablaT_V s t = Γ'.nablaT_V s t)
    (haccel : ∀ s t, Γ.accelerationField s t = Γ'.accelerationField s t) :
    Γ = Γ' := by
  cases Γ with
  | mk toCurveVariation nablaS_T nablaT_V accelerationField =>
      cases Γ' with
      | mk toCurveVariation' nablaS_T' nablaT_V' accelerationField' =>
          have hcurve :
              toCurveVariation = toCurveVariation' := by
            apply curveVariation_ext (n := n)
            · exact hfamily
            · exact htangent
            · exact hvariation
          have hnablaST' : nablaS_T = nablaS_T' := by
            funext s t
            exact hnablaST s t
          have hnablaTV' : nablaT_V = nablaT_V' := by
            funext s t
            exact hnablaTV s t
          have haccel' : accelerationField = accelerationField' := by
            funext s t
            exact haccel s t
          simp [hcurve, hnablaST', hnablaTV', haccel']

/-- Torsion-free interchange identity along a variation. -/
def TorsionFreeInterchange (Gamma : CovariantVariation n) : Prop :=
  ∀ s t, Gamma.nablaS_T s t = Gamma.nablaT_V s t

theorem torsionFreeInterchange_iff
    {Gamma : CovariantVariation n} :
    TorsionFreeInterchange n Gamma ↔ ∀ s t, Gamma.nablaS_T s t = Gamma.nablaT_V s t :=
  Iff.rfl

end Variation.Curve
