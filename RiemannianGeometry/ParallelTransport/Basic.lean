import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open Set
open scoped BigOperators Topology
open BigOperators Finset

namespace ParallelTransport

universe u

/-- A field along a fixed parameter interval in a chosen trivialized fiber.

This file intentionally works in a fixed model fiber `V`; it is the coordinate/trivialized layer,
not a dependent tangent-bundle formulation. -/
abbrev FieldAlong (V : Type u) := ℝ → V

/-- An along-curve first-order ODE in a fixed trivialized fiber. -/
structure AlongDerivative (V : Type u) where
  domain : Set ℝ
  rhs : ℝ → V → V

instance {V : Type u} : CoeFun (AlongDerivative V) (fun _ => ℝ → V → V) where
  coe := AlongDerivative.rhs

/-- A field is parallel along `nablaT` when it solves the corresponding first-order ODE on the
declared time domain. -/
def IsParallelAlong
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (nablaT : AlongDerivative V) (W : FieldAlong V) : Prop :=
  ∀ t ∈ nablaT.domain, HasDerivWithinAt W (nablaT t (W t)) nablaT.domain t

theorem isParallelAlong_iff
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {nablaT : AlongDerivative V} {W : FieldAlong V} :
    IsParallelAlong nablaT W ↔
      ∀ t ∈ nablaT.domain, HasDerivWithinAt W (nablaT t (W t)) nablaT.domain t :=
  Iff.rfl

theorem continuousOn_of_isParallelAlong
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {nablaT : AlongDerivative V} {W : FieldAlong V}
    (hW : IsParallelAlong nablaT W) :
    ContinuousOn W nablaT.domain := by
  intro t ht
  exact (hW t ht).continuousWithinAt

/-- A transport operator assigns to each initial vector a field on a common time domain. -/
structure TransportOperator (V : Type u) where
  domain : Set ℝ
  transport : V → FieldAlong V

instance {V : Type u} : CoeFun (TransportOperator V) (fun _ => V → FieldAlong V) where
  coe := TransportOperator.transport

theorem transportOperator_ext
    {V : Type u} {T T' : TransportOperator V}
    (hdom : T.domain = T'.domain)
    (h : ∀ v t, T v t = T' v t) :
    T = T' := by
  cases T with
  | mk dom f =>
      cases T' with
      | mk dom' g =>
          simp at hdom
          subst hdom
          have hfun : f = g := by
            funext v t
            exact h v t
          simp [hfun]

theorem transportOperator_ext_iff
    {V : Type u} {T T' : TransportOperator V} :
    T = T' ↔ T.domain = T'.domain ∧ ∀ v t, T v t = T' v t := by
  constructor
  · intro h
    subst h
    simp
  · rintro ⟨hdom, h⟩
    exact transportOperator_ext hdom h

/-- The transported field obtained from `T` and initial value `v0`. -/
abbrev transportedField {V : Type u} (T : TransportOperator V) (v0 : V) : FieldAlong V :=
  T v0

@[simp] theorem transportedField_apply
    {V : Type u} (T : TransportOperator V) (v0 : V) (t : ℝ) :
    transportedField T v0 t = T v0 t :=
  rfl

/-- The theorem-level specification of a genuine transport operator on a fixed interval. -/
def IsTransportOperator
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (nablaT : AlongDerivative V) (T : TransportOperator V) : Prop :=
  T.domain = nablaT.domain ∧
    0 ∈ T.domain ∧
    ∀ v0 : V,
      T v0 0 = v0 ∧
        IsParallelAlong nablaT (T v0) ∧
        ∀ W : FieldAlong V, W 0 = v0 → IsParallelAlong nablaT W → EqOn W (T v0) T.domain

theorem isTransportOperator_iff
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {nablaT : AlongDerivative V} {T : TransportOperator V} :
    IsTransportOperator nablaT T ↔
      T.domain = nablaT.domain ∧
        0 ∈ T.domain ∧
        ∀ v0 : V,
          T v0 0 = v0 ∧
            IsParallelAlong nablaT (T v0) ∧
            ∀ W : FieldAlong V, W 0 = v0 → IsParallelAlong nablaT W → EqOn W (T v0) T.domain :=
  Iff.rfl

theorem isTransportOperator_spec
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {nablaT : AlongDerivative V} {T : TransportOperator V}
    (hT : IsTransportOperator nablaT T) (v0 : V) :
    T.domain = nablaT.domain ∧
      0 ∈ T.domain ∧
      T v0 0 = v0 ∧
      IsParallelAlong nablaT (T v0) := by
  refine ⟨hT.1, hT.2.1, (hT.2.2 v0).1, (hT.2.2 v0).2.1⟩

theorem eqOn_of_isTransportOperator
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {nablaT : AlongDerivative V} {T : TransportOperator V}
    (hT : IsTransportOperator nablaT T)
    {v0 : V} {W : FieldAlong V}
    (hW0 : W 0 = v0)
    (hW : IsParallelAlong nablaT W) :
    EqOn W (T v0) T.domain :=
  (hT.2.2 v0).2.2 W hW0 hW

section Coordinate

variable {n : ℕ}

/-- The fixed model fiber `ℝ^n` used in the coordinate/trivialized transport layer. -/
abbrev CoordinateVector (n : ℕ) := Fin n → ℝ

/-- The `i`-th coordinate basis vector in `ℝ^n`. -/
def coordinateBasisVector (i : Fin n) : CoordinateVector n :=
  Pi.single i 1

/-- The coefficientwise `ℓ¹` bound of a matrix, used as a concrete Lipschitz constant for the
sup-norm on `Fin n → ℝ`. -/
def coordinateCoeffBound (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, |A i j|

theorem coordinateCoeffBound_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ coordinateCoeffBound A := by
  refine Finset.sum_nonneg ?_
  intro i hi
  exact Finset.sum_nonneg fun j hj => abs_nonneg _

theorem sum_smul_coordinateBasisVector (v : CoordinateVector n) :
    (∑ i : Fin n, v i • coordinateBasisVector i) = v := by
  funext j
  classical
  calc
    (∑ i : Fin n, v i • coordinateBasisVector i) j
        = ∑ i : Fin n, v i * coordinateBasisVector i j := by
            simp
    _ = ∑ i : Fin n, if i = j then v j else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hij : i = j
            · subst hij
              simp [coordinateBasisVector]
            · simp [coordinateBasisVector, hij]
    _ = v j := by simp

theorem coordinateBasisVector_mem_closedBall (i : Fin n) :
    coordinateBasisVector (n := n) i ∈ Metric.closedBall (0 : CoordinateVector n) 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  by_cases h : j = i
  · subst h
    simp [coordinateBasisVector]
  · simp [coordinateBasisVector, h]

theorem norm_mulVec_le_coordinateCoeffBound
    (A : Matrix (Fin n) (Fin n) ℝ) (v : CoordinateVector n) :
    ‖Matrix.mulVec A v‖ ≤ coordinateCoeffBound A * ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg (coordinateCoeffBound_nonneg A) (norm_nonneg _))]
  intro i
  calc
    ‖(Matrix.mulVec A v) i‖ = ‖∑ j : Fin n, A i j * v j‖ := by
      rfl
    _ ≤ ∑ j : Fin n, ‖A i j * v j‖ := norm_sum_le _ _
    _ = ∑ j : Fin n, |A i j| * ‖v j‖ := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_mul]
    _ ≤ ∑ j : Fin n, |A i j| * ‖v‖ := by
      refine Finset.sum_le_sum ?_
      intro j hj
      gcongr
      exact norm_le_pi_norm v j
    _ = (∑ j : Fin n, |A i j|) * ‖v‖ := by
      rw [Finset.sum_mul]
    _ ≤ coordinateCoeffBound A * ‖v‖ := by
      have hrow :
          ∑ j : Fin n, |A i j| ≤ coordinateCoeffBound A := by
        simpa [coordinateCoeffBound] using
          (Finset.single_le_sum
            (f := fun k : Fin n => ∑ j : Fin n, |A k j|)
            (fun k hk => Finset.sum_nonneg fun j hj => abs_nonneg _)
            (by simp : i ∈ (Finset.univ : Finset (Fin n))))
      gcongr

/-- The linear ODE governing coordinate parallel transport in a fixed trivialized fiber. -/
def coordinateParallelRhs
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) :
    ℝ → CoordinateVector n → CoordinateVector n :=
  fun t v => -(Matrix.mulVec (A t) v)

theorem lipschitzWith_coordinateParallelRhs
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) {t K : ℝ}
    (hK : coordinateCoeffBound (A t) ≤ K) :
    LipschitzWith ⟨K, le_trans (coordinateCoeffBound_nonneg _) hK⟩ (coordinateParallelRhs A t) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hsub :
      Matrix.mulVec (A t) (v - w) = Matrix.mulVec (A t) v - Matrix.mulVec (A t) w := by
    simpa [Matrix.mulVec] using Matrix.mulVec_sub (A t) v w
  have hdist :
      coordinateParallelRhs A t v - coordinateParallelRhs A t w =
        -(Matrix.mulVec (A t) v - Matrix.mulVec (A t) w) := by
    simp [coordinateParallelRhs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  calc
    dist (coordinateParallelRhs A t v) (coordinateParallelRhs A t w)
        = ‖-(Matrix.mulVec (A t) v - Matrix.mulVec (A t) w)‖ := by
            rw [dist_eq_norm, hdist]
    _ = ‖Matrix.mulVec (A t) v - Matrix.mulVec (A t) w‖ := by
          rw [norm_neg]
    _ = ‖Matrix.mulVec (A t) (v - w)‖ := by rw [hsub]
    _ ≤ coordinateCoeffBound (A t) * ‖v - w‖ :=
          norm_mulVec_le_coordinateCoeffBound (A t) (v - w)
    _ ≤ K * dist v w := by
          simp [dist_eq_norm]
          gcongr

theorem continuous_coordinateCoeffBound
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j) :
    Continuous fun t => coordinateCoeffBound (A t) := by
  refine continuous_finset_sum Finset.univ ?_
  intro i hi
  refine continuous_finset_sum Finset.univ ?_
  intro j hj
  simpa [coordinateCoeffBound] using (hAcont i j).abs

theorem continuous_coordinateParallelRhs_apply
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (x : CoordinateVector n) :
    Continuous fun t => coordinateParallelRhs A t x := by
  apply continuous_pi
  intro i
  refine Continuous.neg ?_
  simpa [coordinateParallelRhs, Matrix.mulVec, dotProduct] using
    continuous_finset_sum Finset.univ (fun j hj => (hAcont i j).mul continuous_const)

/-- A concrete coordinate along-derivative on the symmetric interval `[-ε, ε]`. -/
def coordinateAlongDerivative
    (ε : ℝ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) :
    AlongDerivative (CoordinateVector n) where
  domain := Set.Icc (-ε) ε
  rhs := coordinateParallelRhs A

/-- The initial time `0` viewed as a point of `[-ε, ε]`. -/
def coordinateInitialPoint (ε : ℝ) (hε : 0 < ε) : Set.Icc (-ε) ε :=
  ⟨0, by linarith, by linarith⟩

theorem exists_coordinateTransportData
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ K : NNReal,
      (∀ t ∈ Set.Icc (-ε) ε, coordinateCoeffBound (A t) ≤ K) ∧
      IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
        (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K := by
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn
      (continuous_coordinateCoeffBound A hAcont).continuousOn
  let Kreal : ℝ := max C 1
  let K : NNReal := ⟨Kreal, by
    dsimp [Kreal]
    exact le_trans zero_le_one (le_max_right C 1)⟩
  let ε : ℝ := min (1 : ℝ) (1 / (2 * Kreal + 1))
  have hεpos : 0 < ε := by
    have hden : 0 < 2 * Kreal + 1 := by
      positivity
    positivity
  have hεle1 : ε ≤ 1 := min_le_left _ _
  have hcoeff : ∀ t ∈ Set.Icc (-ε) ε, coordinateCoeffBound (A t) ≤ K := by
    intro t ht
    have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor
      · have : -1 ≤ -ε := by linarith
        linarith [ht.1]
      · linarith [hεle1, ht.2]
    have hCt : coordinateCoeffBound (A t) ≤ C := by
      simpa [abs_of_nonneg (coordinateCoeffBound_nonneg (A t))] using hC t ht'
    exact le_trans hCt (by
      change C ≤ Kreal
      exact le_max_left _ _)
  have hnorm :
      ∀ t ∈ Set.Icc (-ε) ε, ∀ x ∈ Metric.closedBall (0 : CoordinateVector n) 2,
        ‖coordinateParallelRhs A t x‖ ≤ ((2 : NNReal) * K : NNReal) := by
    intro t ht x hx
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
    calc
      ‖coordinateParallelRhs A t x‖ = ‖Matrix.mulVec (A t) x‖ := by
        simp [coordinateParallelRhs]
      _ ≤ coordinateCoeffBound (A t) * ‖x‖ := norm_mulVec_le_coordinateCoeffBound (A t) x
      _ ≤ K * 2 := by
            exact mul_le_mul (hcoeff t ht) hx (by positivity) (by positivity)
      _ = ((2 : NNReal) * K : NNReal) := by
            simp [mul_comm]
  have hsmall : ((2 : ℝ) * Kreal) * ε ≤ 1 := by
    have hεbound : ε ≤ 1 / (2 * Kreal + 1) := min_le_right _ _
    have hk : 0 ≤ Kreal := by
      dsimp [Kreal]
      exact le_trans zero_le_one (le_max_right C 1)
    have hden : 0 < 2 * Kreal + 1 := by positivity
    have hεbound' : ε * (2 * Kreal + 1) ≤ 1 := by
      exact (le_div_iff₀ hden).mp (by simpa [one_mul] using hεbound)
    nlinarith
  refine ⟨ε, hεpos, K, hcoeff, ?_⟩
  refine
    { lipschitzOnWith := ?_
      continuousOn := ?_
      norm_le := hnorm
      mul_max_le := ?_ }
  · intro t ht
    exact (lipschitzWith_coordinateParallelRhs A (hcoeff t <| by simpa using ht)).lipschitzOnWith
  · intro x hx
    exact (continuous_coordinateParallelRhs_apply A hAcont x).continuousOn
  · have hsmall' : 1 + Kreal * (2 * ε) ≤ 2 := by
      linarith
    simpa [coordinateInitialPoint, K, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hsmall'

/-- The `i`-th transported coordinate basis vector on the common local time interval. -/
noncomputable def coordinateBasisField
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K)
    (i : Fin n) : FieldAlong (CoordinateVector n) :=
  Classical.choose <|
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (coordinateBasisVector_mem_closedBall (n := n) i)

theorem coordinateBasisField_initial
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K)
    (i : Fin n) :
    coordinateBasisField A ε hε K hpl i 0 = coordinateBasisVector i :=
  (Classical.choose_spec <|
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (coordinateBasisVector_mem_closedBall (n := n) i)).1

theorem coordinateBasisField_isParallel
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K)
    (i : Fin n) :
    IsParallelAlong (coordinateAlongDerivative ε A)
      (coordinateBasisField A ε hε K hpl i) := by
  intro t ht
  simpa [coordinateAlongDerivative, coordinateBasisField] using
    (Classical.choose_spec <|
      hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
        (coordinateBasisVector_mem_closedBall (n := n) i)).2 t ht

/-- Coordinate parallel transport on a fixed trivialized fiber, constructed from the genuine linear
ODE on the symmetric interval `[-ε, ε]`. -/
noncomputable def coordinateParallelTransportOn
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K) :
    TransportOperator (CoordinateVector n) where
  domain := Set.Icc (-ε) ε
  transport v t := ∑ i : Fin n, v i • coordinateBasisField A ε hε K hpl i t

theorem coordinateParallelTransportOn_zero_mem
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    {ε : ℝ} (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K) :
    0 ∈ (coordinateParallelTransportOn A ε hε K hpl).domain := by
  constructor <;> linarith

theorem coordinateParallelTransportOn_initial
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K)
    (v0 : CoordinateVector n) :
    coordinateParallelTransportOn A ε hε K hpl v0 0 = v0 := by
  simp [coordinateParallelTransportOn, coordinateBasisField_initial, sum_smul_coordinateBasisVector]

theorem coordinateParallelTransportOn_isParallel
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K)
    (v0 : CoordinateVector n) :
    IsParallelAlong (coordinateAlongDerivative ε A)
      (coordinateParallelTransportOn A ε hε K hpl v0) := by
  intro t ht
  have hsum :
      HasDerivWithinAt
        (fun s => ∑ i : Fin n, v0 i • coordinateBasisField A ε hε K hpl i s)
        (∑ i : Fin n, v0 i • coordinateParallelRhs A t (coordinateBasisField A ε hε K hpl i t))
        (Set.Icc (-ε) ε) t := by
    have hsum' :
        HasDerivWithinAt
          (∑ i : Fin n, fun s => v0 i • coordinateBasisField A ε hε K hpl i s)
          (∑ i : Fin n, v0 i • coordinateParallelRhs A t (coordinateBasisField A ε hε K hpl i t))
          (Set.Icc (-ε) ε) t := by
      simpa [coordinateAlongDerivative] using
        (HasDerivWithinAt.sum (u := Finset.univ)
          (fun i _ => (coordinateBasisField_isParallel A ε hε K hpl i t ht).const_smul (v0 i)))
    have hfun :
        (∑ i : Fin n, fun s => v0 i • coordinateBasisField A ε hε K hpl i s) =
          (fun s => ∑ i : Fin n, v0 i • coordinateBasisField A ε hε K hpl i s) := by
      funext s
      simp
    simpa [hfun] using hsum'
  have hmul :
      Matrix.mulVec (A t) (∑ i : Fin n, v0 i • coordinateBasisField A ε hε K hpl i t) =
        ∑ i : Fin n, v0 i • Matrix.mulVec (A t) (coordinateBasisField A ε hε K hpl i t) := by
    classical
    refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?_ ?_
    · simp [Matrix.mulVec]
    · intro i s his hs
      simp [Finset.sum_insert his, Matrix.mulVec_add, Matrix.mulVec_smul, hs]
  have hrhs :
      (∑ i : Fin n, v0 i • coordinateParallelRhs A t (coordinateBasisField A ε hε K hpl i t)) =
        coordinateParallelRhs A t (coordinateParallelTransportOn A ε hε K hpl v0 t) := by
    calc
      ∑ i : Fin n, v0 i • coordinateParallelRhs A t (coordinateBasisField A ε hε K hpl i t)
          = ∑ i : Fin n, -(v0 i • Matrix.mulVec (A t) (coordinateBasisField A ε hε K hpl i t)) := by
              simp [coordinateParallelRhs, smul_neg]
      _ = -(∑ i : Fin n, v0 i • Matrix.mulVec (A t) (coordinateBasisField A ε hε K hpl i t)) := by
              simp
      _ = coordinateParallelRhs A t (coordinateParallelTransportOn A ε hε K hpl v0 t) := by
              simp [coordinateParallelTransportOn, coordinateParallelRhs, hmul]
  simpa [coordinateAlongDerivative, coordinateParallelTransportOn, hrhs] using hsum

theorem coordinateParallelTransportOn_linear
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K)
    (a : ℝ) (v w : CoordinateVector n) (t : ℝ) :
    coordinateParallelTransportOn A ε hε K hpl (a • v + w) t =
      a • coordinateParallelTransportOn A ε hε K hpl v t +
        coordinateParallelTransportOn A ε hε K hpl w t := by
  ext k
  calc
    coordinateParallelTransportOn A ε hε K hpl (a • v + w) t k
        = ∑ x : Fin n, ((a * v x) + w x) * coordinateBasisField A ε hε K hpl x t k := by
            simp [coordinateParallelTransportOn]
    _ = ∑ x : Fin n, (a * v x) * coordinateBasisField A ε hε K hpl x t k +
          ∑ x : Fin n, w x * coordinateBasisField A ε hε K hpl x t k := by
            calc
              ∑ x : Fin n, ((a * v x) + w x) * coordinateBasisField A ε hε K hpl x t k
                  = ∑ x : Fin n,
                      ((a * v x) * coordinateBasisField A ε hε K hpl x t k +
                        w x * coordinateBasisField A ε hε K hpl x t k) := by
                          apply Finset.sum_congr rfl
                          intro x hx
                          ring
              _ = ∑ x : Fin n, (a * v x) * coordinateBasisField A ε hε K hpl x t k +
                    ∑ x : Fin n, w x * coordinateBasisField A ε hε K hpl x t k := by
                          rw [Finset.sum_add_distrib]
    _ = a * ∑ x : Fin n, v x * coordinateBasisField A ε hε K hpl x t k +
          ∑ x : Fin n, w x * coordinateBasisField A ε hε K hpl x t k := by
            congr 1
            calc
              ∑ x : Fin n, (a * v x) * coordinateBasisField A ε hε K hpl x t k
                  = ∑ x : Fin n, a * (v x * coordinateBasisField A ε hε K hpl x t k) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring
              _ = a * ∑ x : Fin n, v x * coordinateBasisField A ε hε K hpl x t k := by
                      rw [← Finset.mul_sum]
    _ = (a • coordinateParallelTransportOn A ε hε K hpl v t +
          coordinateParallelTransportOn A ε hε K hpl w t) k := by
            simp [coordinateParallelTransportOn]

theorem coordinateParallelTransportOn_unique
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    {ε : ℝ} (hε : 0 < ε) {K : NNReal}
    (hcoeff : ∀ t ∈ Set.Icc (-ε) ε, coordinateCoeffBound (A t) ≤ K)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K)
    {v0 : CoordinateVector n} {W : FieldAlong (CoordinateVector n)}
    (hW0 : W 0 = v0)
    (hW : IsParallelAlong (coordinateAlongDerivative ε A) W) :
    EqOn W (coordinateParallelTransportOn A ε hε K hpl v0)
      (coordinateParallelTransportOn A ε hε K hpl).domain := by
  have hcontW : ContinuousOn W (Set.Icc (-ε) ε) :=
    continuousOn_of_isParallelAlong hW
  have hcontT : ContinuousOn (coordinateParallelTransportOn A ε hε K hpl v0) (Set.Icc (-ε) ε) :=
    continuousOn_of_isParallelAlong (coordinateParallelTransportOn_isParallel A ε hε K hpl v0)
  have hderivW :
      ∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt W (coordinateParallelRhs A t (W t)) t := by
    intro t ht
    exact (hW t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hderivT :
      ∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt (coordinateParallelTransportOn A ε hε K hpl v0)
          (coordinateParallelRhs A t ((coordinateParallelTransportOn A ε hε K hpl v0) t)) t := by
    intro t ht
    exact
      (coordinateParallelTransportOn_isParallel A ε hε K hpl v0 t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
  have hv :
      ∀ t ∈ Set.Ioo (-ε) ε,
        LipschitzOnWith K (coordinateParallelRhs A t) (Set.univ : Set (CoordinateVector n)) := by
    intro t ht
    exact (lipschitzWith_coordinateParallelRhs A (hcoeff t (Ioo_subset_Icc_self ht))).lipschitzOnWith
  have heq :
      EqOn W (coordinateParallelTransportOn A ε hε K hpl v0) (Set.Icc (-ε) ε) := by
    apply (ODE_solution_unique_of_mem_Icc (t₀ := 0))
    · exact hv
    · constructor <;> linarith
    · exact hcontW
    · exact hderivW
    · intro t ht
      trivial
    · exact hcontT
    · exact hderivT
    · intro t ht
      trivial
    · simpa [coordinateParallelTransportOn_initial A ε hε K hpl v0] using hW0
  simpa [coordinateParallelTransportOn] using heq

theorem coordinateParallelTransportOn_isTransportOperator
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    {ε : ℝ} (hε : 0 < ε) {K : NNReal}
    (hcoeff : ∀ t ∈ Set.Icc (-ε) ε, coordinateCoeffBound (A t) ≤ K)
    (hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K) :
    IsTransportOperator
      (coordinateAlongDerivative ε A)
      (coordinateParallelTransportOn A ε hε K hpl) := by
  refine ⟨rfl, coordinateParallelTransportOn_zero_mem A hε K hpl, ?_⟩
  intro v0
  refine ⟨coordinateParallelTransportOn_initial A ε hε K hpl v0,
    coordinateParallelTransportOn_isParallel A ε hε K hpl v0, ?_⟩
  intro W hW0 hW
  exact coordinateParallelTransportOn_unique A hε hcoeff hpl hW0 hW

/-- Auxiliary Picard-Lindelof data for the exported coordinate transport operator. -/
structure CoordinateTransportData
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) where
  ε : ℝ
  hε : 0 < ε
  K : NNReal
  hcoeff : ∀ t ∈ Set.Icc (-ε) ε, coordinateCoeffBound (A t) ≤ K
  hpl : IsPicardLindelof (coordinateParallelRhs A) (coordinateInitialPoint ε hε)
    (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K

/-- Choose one local interval and one Picard-Lindelof witness for the coordinate transport ODE. -/
theorem exists_coordinateTransportData_struct
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j) :
    ∃ data : CoordinateTransportData A, True := by
  rcases exists_coordinateTransportData A hAcont with ⟨ε, hε, K, hcoeff, hpl⟩
  exact ⟨⟨ε, hε, K, hcoeff, hpl⟩, trivial⟩

/-- Choose one local interval and one Picard-Lindelof witness for the coordinate transport ODE. -/
noncomputable def coordinateTransportData
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j) :
    CoordinateTransportData A := by
  classical
  exact Classical.choose (exists_coordinateTransportData_struct A hAcont)

/-- The chosen along-curve covariant derivative attached to the local coordinate ODE. -/
noncomputable def coordinateParallelAlongDerivative
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j) :
    AlongDerivative (CoordinateVector n) :=
  let data := coordinateTransportData A hAcont
  coordinateAlongDerivative data.ε A

/-- Coordinate parallel transport along a fixed curve, constructed from the along-curve ODE. -/
noncomputable def coordinateParallelTransport
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j) :
    TransportOperator (CoordinateVector n) :=
  let data := coordinateTransportData A hAcont
  coordinateParallelTransportOn A data.ε data.hε data.K data.hpl

theorem coordinateParallelTransport_initial
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (v0 : CoordinateVector n) :
    coordinateParallelTransport A hAcont v0 0 = v0 := by
  classical
  cases hdata : coordinateTransportData A hAcont with
  | mk ε hε K hcoeff hpl =>
      simpa [coordinateParallelTransport, hdata] using
        (coordinateParallelTransportOn_initial A ε hε K hpl v0)

theorem coordinateParallelTransport_isParallel
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (v0 : CoordinateVector n) :
    IsParallelAlong (coordinateParallelAlongDerivative A hAcont)
      (coordinateParallelTransport A hAcont v0) := by
  classical
  cases hdata : coordinateTransportData A hAcont with
  | mk ε hε K hcoeff hpl =>
      simpa [coordinateParallelTransport, coordinateParallelAlongDerivative, hdata] using
        (coordinateParallelTransportOn_isParallel A ε hε K hpl v0)

theorem coordinateParallelTransport_unique
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    {v0 : CoordinateVector n} {W : FieldAlong (CoordinateVector n)}
    (hW0 : W 0 = v0)
    (hW : IsParallelAlong (coordinateParallelAlongDerivative A hAcont) W) :
    EqOn W (coordinateParallelTransport A hAcont v0)
      (coordinateParallelTransport A hAcont).domain := by
  classical
  cases hdata : coordinateTransportData A hAcont with
  | mk ε hε K hcoeff hpl =>
      simpa [coordinateParallelTransport, coordinateParallelAlongDerivative, hdata] using
        (coordinateParallelTransportOn_unique A hε hcoeff hpl hW0
          (by simpa [coordinateParallelAlongDerivative, hdata] using hW))

theorem coordinateParallelTransport_linear
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (a : ℝ) (v w : CoordinateVector n) (t : ℝ) :
    coordinateParallelTransport A hAcont (a • v + w) t =
      a • coordinateParallelTransport A hAcont v t +
        coordinateParallelTransport A hAcont w t := by
  classical
  cases hdata : coordinateTransportData A hAcont with
  | mk ε hε K hcoeff hpl =>
      simpa [coordinateParallelTransport, hdata] using
        (coordinateParallelTransportOn_linear A ε hε K hpl a v w t)

theorem coordinateParallelTransport_isTransportOperator
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j) :
    IsTransportOperator (coordinateParallelAlongDerivative A hAcont)
      (coordinateParallelTransport A hAcont) := by
  classical
  cases hdata : coordinateTransportData A hAcont with
  | mk ε hε K hcoeff hpl =>
      simpa [coordinateParallelTransport, coordinateParallelAlongDerivative, hdata] using
        (coordinateParallelTransportOn_isTransportOperator A hε hcoeff hpl)

end Coordinate

end ParallelTransport
