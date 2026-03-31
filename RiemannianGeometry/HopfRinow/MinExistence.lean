import Minimization
import Variation.FirstVariationLength
import HopfRinow.GeodesicExtension
import HopfRinow.LengthCompactness

/-! Minimizing-geodesic existence definitions and the interface boundary for the
complete→minimizers direction.

Design note for the copy:
- this file keeps only the public minimizing-geodesic interface,
- the future owner proof is expected to live in `MinimizerExistence.lean`,
- the purely metric distance-realizer lemmas should live in `DistanceRealizer.lean`. -/

namespace HopfRinow

universe u

/-- A metric geodesic segment connecting `p` to `q` on `[0,1]`. -/
def IsMinimizingGeodesicBetween
    (M : Type u) [PseudoMetricSpace M]
    (p q : M) (γ : ℝ → M) : Prop :=
  γ 0 = p ∧
    γ 1 = q ∧
    IsGeodesicOnWithSpeed M γ (dist p q) (Set.Icc (0 : ℝ) 1)

/-- A pointwise metric realization of the distance along a chosen segment. -/
def IsDistanceRealizerBetween
    (M : Type u) [PseudoMetricSpace M]
    (p q : M) (γ : ℝ → M) : Prop :=
  γ 0 = p ∧
    γ 1 = q ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist p (γ t) = t * dist p q ∧ dist (γ t) q = (1 - t) * dist p q

/-- Existence of minimizing geodesics as a package export. -/
def MinimizingGeodesicsExist (M : Type u) [PseudoMetricSpace M] : Prop :=
  ∀ p q : M, ∃ γ : ℝ → M, IsMinimizingGeodesicBetween M p q γ

/-- A package-level criterion. -/
def MinimizerIsGeodesic (M : Type u) [PseudoMetricSpace M] : Prop :=
  ∀ p q : M, ∀ γ : ℝ → M,
    IsDistanceRealizerBetween M p q γ →
    IsMinimizingGeodesicBetween M p q γ

theorem minimizingGeodesicsExist_iff
    {M : Type u} [PseudoMetricSpace M] :
    MinimizingGeodesicsExist M ↔
      ∀ p q : M, ∃ γ : ℝ → M, IsMinimizingGeodesicBetween M p q γ :=
  Iff.rfl

/-- Choose one minimizing curve between two endpoints. -/
noncomputable def someMinimizingCurve
    {M : Type u} [PseudoMetricSpace M]
    (h : MinimizingGeodesicsExist M) (p q : M) :
    ℝ → M :=
  Classical.choose (h p q)

theorem someMinimizingCurve_isMinimizingGeodesicBetween
    {M : Type u} [PseudoMetricSpace M]
    (h : MinimizingGeodesicsExist M) (p q : M) :
    IsMinimizingGeodesicBetween M p q (someMinimizingCurve h p q) :=
  Classical.choose_spec (h p q)

theorem someMinimizingCurve_source
    {M : Type u} [PseudoMetricSpace M]
    (h : MinimizingGeodesicsExist M) (p q : M) :
    someMinimizingCurve h p q 0 = p :=
  (someMinimizingCurve_isMinimizingGeodesicBetween h p q).1

theorem someMinimizingCurve_target
    {M : Type u} [PseudoMetricSpace M]
    (h : MinimizingGeodesicsExist M) (p q : M) :
    someMinimizingCurve h p q 1 = q :=
  (someMinimizingCurve_isMinimizingGeodesicBetween h p q).2.1

theorem someMinimizingCurve_geodesic
    {M : Type u} [PseudoMetricSpace M]
    (h : MinimizingGeodesicsExist M) (p q : M) :
    IsGeodesicOnWithSpeed M (someMinimizingCurve h p q) (dist p q) (Set.Icc (0 : ℝ) 1) :=
  (someMinimizingCurve_isMinimizingGeodesicBetween h p q).2.2

/-- Data package for the complete→minimizers direction. -/
structure MinExistenceData (M : Type u) [PseudoMetricSpace M] : Prop where
  complete_minimizers : RiemannianComplete M → MinimizingGeodesicsExist M

/-
Future owner theorem expected outside this file:

theorem complete_implies_minimizers
    ... :
    RiemannianComplete M → MinimizingGeodesicsExist M
-/

theorem minimizingGeodesicsExist_of_complete
    {M : Type u} [PseudoMetricSpace M]
    (input : MinExistenceData M) :
    RiemannianComplete M → MinimizingGeodesicsExist M :=
  input.complete_minimizers

end HopfRinow
