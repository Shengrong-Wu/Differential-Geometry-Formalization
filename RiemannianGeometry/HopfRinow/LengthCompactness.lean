import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.UniformConvergence
import Variation.CurveLength
import HopfRinow.Properness

/-! The length-compactness layer follows the properness-first Arzela-Ascoli route.
`hasLengthCompactness_of_complete` is now derived from the chain:
complete → minimizers → proper → length compact, without external data packages. -/

namespace HopfRinow

open scoped Topology
open BoundedContinuousFunction

open Set Metric

universe u

abbrev UnitInterval : Type := ↥(Set.Icc (0 : ℝ) 1)

abbrev UnitIntervalCurve (X : Type u) [TopologicalSpace X] :=
  C(UnitInterval, X)

/-- A reparametrized curve family stays in a fixed closed ball. -/
def BoundedRange
    (X : Type u) [PseudoMetricSpace X]
    (x₀ : X) (R : NNReal) (γ : UnitIntervalCurve X) : Prop :=
  ∀ t, dist (γ t) x₀ ≤ R

/-- A reparametrized curve family has a uniform Lipschitz bound on `[0,1]`. -/
def UniformLipschitzBound
    (X : Type u) [PseudoMetricSpace X]
    (L : NNReal) (γ : UnitIntervalCurve X) : Prop :=
  LipschitzWith L γ

/-- The canonical Arzela-Ascoli container used by the length-compactness package. -/
def lengthCompactContainer
    (X : Type u) [PseudoMetricSpace X]
    (x₀ : X) (R L : NNReal) : Set (UnitIntervalCurve X) :=
  {γ | BoundedRange X x₀ R γ ∧ UniformLipschitzBound X L γ}

namespace LengthCompactness

private def boundedLengthCompactContainer
    (X : Type u) [PseudoMetricSpace X]
    (x₀ : X) (R L : NNReal) : Set (UnitInterval →ᵇ X) :=
  {γ | (∀ t, dist (γ t) x₀ ≤ R) ∧ LipschitzWith L γ}

private theorem isClosed_boundedRange
    (X : Type u) [PseudoMetricSpace X]
    (x₀ : X) (R : NNReal) :
    IsClosed {γ : UnitInterval →ᵇ X | ∀ t, dist (γ t) x₀ ≤ R} := by
  let S : Set (UnitInterval → X) := {f | ∀ t, dist (f t) x₀ ≤ R}
  have hS : IsClosed S := by
    rw [show S = ⋂ t, {f : UnitInterval → X | dist (f t) x₀ ≤ R} by
      ext f
      simp [S]]
    refine isClosed_iInter ?_
    intro t
    exact isClosed_le ((continuous_apply t).dist continuous_const) continuous_const
  simpa [S] using hS.preimage BoundedContinuousFunction.uniformContinuous_coe.continuous

private theorem isClosed_uniformLipschitz
    (X : Type u) [PseudoMetricSpace X]
    (L : NNReal) :
    IsClosed {γ : UnitInterval →ᵇ X | LipschitzWith L γ} := by
  simpa using
    (isClosed_setOf_lipschitzWith (α := UnitInterval) (β := X) (K := L)).preimage
      BoundedContinuousFunction.uniformContinuous_coe.continuous

private theorem isClosed_boundedLengthCompactContainer
    (X : Type u) [PseudoMetricSpace X]
    (x₀ : X) (R L : NNReal) :
    IsClosed (boundedLengthCompactContainer X x₀ R L) := by
  exact (isClosed_boundedRange X x₀ R).inter (isClosed_uniformLipschitz X L)

private theorem equicontinuous_boundedLengthCompactContainer
    (X : Type u) [PseudoMetricSpace X]
    (x₀ : X) (R L : NNReal) :
    Equicontinuous ((↑) : boundedLengthCompactContainer X x₀ R L → UnitInterval → X) := by
  have huniform :
      UniformEquicontinuous
        ((↑) : boundedLengthCompactContainer X x₀ R L → UnitInterval → X) :=
    LipschitzWith.uniformEquicontinuous
      ((↑) : boundedLengthCompactContainer X x₀ R L → UnitInterval → X) L
      (fun γ => γ.2.2)
  exact huniform.equicontinuous

private theorem boundedLengthCompactContainer_mapsTo_closedBall
    (X : Type u) [PseudoMetricSpace X]
    (x₀ : X) (R L : NNReal) :
    ∀ (γ : UnitInterval →ᵇ X) (t : UnitInterval),
      γ ∈ boundedLengthCompactContainer X x₀ R L → γ t ∈ closedBall x₀ R := by
  intro γ t hγ
  simpa [Metric.mem_closedBall] using hγ.1 t

private theorem toContinuousMap_image_boundedLengthCompactContainer
    (X : Type u) [PseudoMetricSpace X]
    (x₀ : X) (R L : NNReal) :
    (fun f : UnitInterval →ᵇ X => f.toContinuousMap) ''
        boundedLengthCompactContainer X x₀ R L =
      lengthCompactContainer X x₀ R L := by
  ext γ
  constructor
  · rintro ⟨f, hf, rfl⟩
    simpa [boundedLengthCompactContainer, lengthCompactContainer, BoundedRange,
      UniformLipschitzBound] using hf
  · intro hγ
    refine ⟨BoundedContinuousFunction.mkOfCompact γ, ?_, ?_⟩
    simpa [boundedLengthCompactContainer, lengthCompactContainer, BoundedRange,
      UniformLipschitzBound, BoundedContinuousFunction.mkOfCompact_apply] using hγ
    ext t
    rfl

end LengthCompactness

/-- A family of reparametrized curves is in the Hopf-Rinow compactness regime. -/
def IsLengthCompactFamily
    (X : Type u) [PseudoMetricSpace X]
    (S : Set (UnitIntervalCurve X)) : Prop :=
  ∃ x₀ : X, ∃ R L : NNReal, S ⊆ lengthCompactContainer X x₀ R L

/-- Compactness package for families of almost-minimizing curves. -/
def HasLengthCompactness (X : Type u) [PseudoMetricSpace X] : Prop :=
  ∀ S : Set (UnitIntervalCurve X), IsLengthCompactFamily X S →
    ∃ K : Set (UnitIntervalCurve X), IsCompact K ∧ S ⊆ K

theorem boundedRange_of_source_uniformLipschitz
    {X : Type u} [PseudoMetricSpace X]
    {p : X} {L : NNReal} {γ : UnitIntervalCurve X}
    (h0 : γ ⟨0, by simp⟩ = p)
    (hlip : UniformLipschitzBound X L γ) :
    BoundedRange X p L γ := by
  intro t
  have hdist0 : dist t (⟨0, by simp⟩ : UnitInterval) = (t : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg t.2.1]
  calc
    dist (γ t) p = dist (γ t) (γ ⟨0, by simp⟩) := by rw [h0]
    _ ≤ (L : ℝ) * dist t (⟨0, by simp⟩ : UnitInterval) := by
      simpa [UniformLipschitzBound] using hlip.dist_le_mul t (⟨0, by simp⟩ : UnitInterval)
    _ = (L : ℝ) * (t : ℝ) := by rw [hdist0]
    _ ≤ (L : ℝ) := by
      nlinarith [show 0 ≤ (L : ℝ) from L.2, t.2.1, t.2.2]

theorem mem_lengthCompactContainer_of_source_uniformLipschitz
    {X : Type u} [PseudoMetricSpace X]
    {p : X} {L : NNReal} {γ : UnitIntervalCurve X}
    (h0 : γ ⟨0, by simp⟩ = p)
    (hlip : UniformLipschitzBound X L γ) :
    γ ∈ lengthCompactContainer X p L L := by
  exact ⟨boundedRange_of_source_uniformLipschitz h0 hlip, hlip⟩

theorem isLengthCompactFamily_of_commonSource_uniformLipschitz
    {X : Type u} [PseudoMetricSpace X]
    {S : Set (UnitIntervalCurve X)} {p : X} {L : NNReal}
    (h0 : ∀ ⦃γ⦄, γ ∈ S → γ ⟨0, by simp⟩ = p)
    (hlip : ∀ ⦃γ⦄, γ ∈ S → UniformLipschitzBound X L γ) :
    IsLengthCompactFamily X S := by
  refine ⟨p, L, L, ?_⟩
  intro γ hγ
  exact mem_lengthCompactContainer_of_source_uniformLipschitz (h0 hγ) (hlip hγ)

theorem hasLengthCompactness_iff
    {X : Type u} [PseudoMetricSpace X] :
    HasLengthCompactness X ↔
      ∀ S : Set (UnitIntervalCurve X), IsLengthCompactFamily X S →
        ∃ K : Set (UnitIntervalCurve X), IsCompact K ∧ S ⊆ K :=
  Iff.rfl

theorem hasLengthCompactness_of_compactSuperset
    {X : Type u} [PseudoMetricSpace X]
    (h : ∀ S : Set (UnitIntervalCurve X), IsLengthCompactFamily X S →
      ∃ K : Set (UnitIntervalCurve X), IsCompact K ∧ S ⊆ K) :
    HasLengthCompactness X :=
  h

noncomputable def compactSuperset
    {X : Type u} [PseudoMetricSpace X]
    (h : HasLengthCompactness X) (S : Set (UnitIntervalCurve X))
    (hS : IsLengthCompactFamily X S) :
    Set (UnitIntervalCurve X) :=
  Classical.choose (h S hS)

theorem isCompact_compactSuperset
    {X : Type u} [PseudoMetricSpace X]
    (h : HasLengthCompactness X) (S : Set (UnitIntervalCurve X))
    (hS : IsLengthCompactFamily X S) :
    IsCompact (compactSuperset h S hS) :=
  (Classical.choose_spec (h S hS)).1

theorem subset_compactSuperset
    {X : Type u} [PseudoMetricSpace X]
    (h : HasLengthCompactness X) (S : Set (UnitIntervalCurve X))
    (hS : IsLengthCompactFamily X S) :
  S ⊆ compactSuperset h S hS :=
  (Classical.choose_spec (h S hS)).2

/-- The Arzela-Ascoli owner theorem: in a proper metric space, a uniformly Lipschitz family of
reparametrized curves with common bounded range has a compact superset. -/
theorem isCompact_lengthCompactContainer
    {X : Type u} [PseudoMetricSpace X]
    (hproper : RiemannianProper X)
    (x₀ : X) (R L : NNReal) :
    IsCompact (lengthCompactContainer X x₀ R L) := by
  letI : ProperSpace X := hproper
  have hbounded :
      IsCompact (LengthCompactness.boundedLengthCompactContainer X x₀ R L) :=
    BoundedContinuousFunction.arzela_ascoli₂
      (s := closedBall x₀ R)
      (hs := isCompact_closedBall x₀ R)
      (A := LengthCompactness.boundedLengthCompactContainer X x₀ R L)
      (closed := LengthCompactness.isClosed_boundedLengthCompactContainer X x₀ R L)
      (in_s := LengthCompactness.boundedLengthCompactContainer_mapsTo_closedBall X x₀ R L)
      (H := LengthCompactness.equicontinuous_boundedLengthCompactContainer X x₀ R L)
  simpa [LengthCompactness.toContinuousMap_image_boundedLengthCompactContainer X x₀ R L] using
    hbounded.image (ContinuousMap.isometryEquivBoundedOfCompact UnitInterval X).symm.continuous

/-- Properness gives the compactness package required by the Hopf-Rinow length-compactness layer. -/
theorem hasLengthCompactness_of_proper
    {X : Type u} [PseudoMetricSpace X]
    (hproper : RiemannianProper X) :
    HasLengthCompactness X := by
  intro S hS
  rcases hS with ⟨x₀, R, L, hsub⟩
  refine ⟨lengthCompactContainer X x₀ R L, ?_, hsub⟩
  exact isCompact_lengthCompactContainer hproper x₀ R L

end HopfRinow
