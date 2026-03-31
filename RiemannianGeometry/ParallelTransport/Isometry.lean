import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.ODE.Gronwall
import ParallelTransport.Basic

open Set
open scoped BigOperators Topology
open BigOperators Finset

namespace ParallelTransport

universe u

/-- A time-dependent pairing on a fixed trivialized fiber. -/
abbrev PairingAlong (V : Type u) := ℝ → V → V → ℝ

/-- Pairing preservation is stated on the declared time domain of the transport operator.

This remains a coordinate/trivialized notion: the ambient fiber type `V` is fixed. -/
def transportDomain {V : Type u} (T : TransportOperator V) : Set ℝ :=
  TransportOperator.rec (fun s _ => s) T

/-- Pairing preservation is stated on the declared time domain of the transport operator.

This remains a coordinate/trivialized notion: the ambient fiber type `V` is fixed. -/
def PreservesPairing
    {V : Type u}
    (g : PairingAlong V) (T : TransportOperator V) : Prop :=
  0 ∈ transportDomain T ∧
    ∀ v w t, t ∈ transportDomain T → g t (T v t) (T w t) = g 0 v w

/-- Levi-Civita parallel transport is an isometry for the time-dependent metric pairing. -/
def IsometryAlong
    {V : Type u}
    (g : PairingAlong V) (T : TransportOperator V) : Prop :=
  PreservesPairing g T

theorem isometryAlong_iff
    {V : Type u}
    {g : PairingAlong V} {T : TransportOperator V} :
    IsometryAlong g T ↔ PreservesPairing g T :=
  Iff.rfl

theorem preservesPairing_of_isometryAlong
    {V : Type u}
    {g : PairingAlong V} {T : TransportOperator V}
    (hT : IsometryAlong g T) :
    PreservesPairing g T :=
  hT

theorem isometryAlong_of_preservesPairing
    {V : Type u}
    {g : PairingAlong V} {T : TransportOperator V}
    (hT : PreservesPairing g T) :
    IsometryAlong g T :=
  hT

section Coordinate

variable {n : ℕ}

/-- The coordinate metric pairing defined by a matrix of coefficients. -/
def coordinatePairingAt
    (g : Matrix (Fin n) (Fin n) ℝ)
    (v w : CoordinateVector n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v i * g i j * w j

/-- A time-dependent coordinate pairing along the chosen curve parameter. -/
def coordinatePairing
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ) :
    PairingAlong (CoordinateVector n) :=
  fun t v w => coordinatePairingAt (g t) v w

theorem coordinatePairingAt_eq_dotProduct_mulVec
    (g : Matrix (Fin n) (Fin n) ℝ)
    (v w : CoordinateVector n) :
    coordinatePairingAt g v w = dotProduct v (Matrix.mulVec g w) := by
  simp [coordinatePairingAt, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem continuousOn_coordinatePairing
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hgcont : ∀ i j, Continuous fun t => g t i j)
    {s : Set ℝ}
    {Y Z : FieldAlong (CoordinateVector n)}
    (hY : ContinuousOn Y s)
    (hZ : ContinuousOn Z s) :
    ContinuousOn (fun t => coordinatePairing g t (Y t) (Z t)) s := by
  unfold coordinatePairing coordinatePairingAt
  refine continuousOn_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro i hi
  refine continuousOn_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro j hj
  have hYi : ContinuousOn (fun t => Y t i) s := by
    intro t ht
    simpa [Function.comp] using
      (continuous_apply i).continuousWithinAt.comp (hY t ht) (by
        intro x hx
        exact mem_univ _)
  have hZj : ContinuousOn (fun t => Z t j) s := by
    intro t ht
    simpa [Function.comp] using
      (continuous_apply j).continuousWithinAt.comp (hZ t ht) (by
        intro x hx
        exact mem_univ _)
  exact (hYi.mul (hgcont i j).continuousOn).mul hZj

theorem hasDerivAt_coordinatePairing
    {g dg : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Y Z : FieldAlong (CoordinateVector n)}
    {y' z' : CoordinateVector n}
    {t : ℝ}
    (hg : ∀ i j, HasDerivAt (fun s => g s i j) (dg t i j) t)
    (hY : HasDerivAt Y y' t)
    (hZ : HasDerivAt Z z' t) :
    HasDerivAt (fun s => coordinatePairing g s (Y s) (Z s))
      (coordinatePairingAt (dg t) (Y t) (Z t) +
        coordinatePairingAt (g t) y' (Z t) +
        coordinatePairingAt (g t) (Y t) z') t := by
  have hsum :
      HasDerivAt (fun s => ∑ i : Fin n, ∑ j : Fin n, Y s i * g s i j * Z s j)
        (∑ i : Fin n,
          Finset.sum (Finset.univ : Finset (Fin n))
            (fun j : Fin n => y' i * g t i j * Z t j + Y t i * dg t i j * Z t j + Y t i * g t i j * z' j)) t := by
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
      (A := fun i s => ∑ j : Fin n, Y s i * g s i j * Z s j)
      (A' := fun i =>
        Finset.sum (Finset.univ : Finset (Fin n))
          (fun j : Fin n => y' i * g t i j * Z t j + Y t i * dg t i j * Z t j + Y t i * g t i j * z' j)) ?_
    intro i hi
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
      (A := fun j s => Y s i * g s i j * Z s j)
      (A' := fun j => y' i * g t i j * Z t j + Y t i * dg t i j * Z t j + Y t i * g t i j * z' j) ?_
    intro j hj
    have hYi : HasDerivAt (fun s => Y s i) (y' i) t := by
      simpa [Function.comp] using
        (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) i :
            CoordinateVector n →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivAt t hY)
    have hZj : HasDerivAt (fun s => Z s j) (z' j) t := by
      simpa [Function.comp] using
        (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) j :
            CoordinateVector n →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivAt t hZ)
    have hgij : HasDerivAt (fun s => g s i j) (dg t i j) t := hg i j
    convert (hYi.mul hgij).mul hZj using 1 <;> simp <;> ring_nf
  simpa [coordinatePairing, coordinatePairingAt, Finset.sum_add_distrib, add_assoc, add_left_comm,
    add_comm] using hsum

theorem coordinatePairingAt_parallel_deriv_eq_zero
    (A g dg : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (y z : CoordinateVector n)
    (hcompat : dg t = Matrix.transpose (A t) * g t + g t * A t) :
      coordinatePairingAt (dg t) y z +
      coordinatePairingAt (g t) (coordinateParallelRhs A t y) z +
      coordinatePairingAt (g t) y (coordinateParallelRhs A t z) = 0 := by
  rw [hcompat]
  repeat rw [coordinatePairingAt_eq_dotProduct_mulVec]
  have hmul₁ :
      Matrix.mulVec ((Matrix.transpose (A t)) * g t) z =
        Matrix.mulVec (Matrix.transpose (A t)) (Matrix.mulVec (g t) z) := by
    simpa [Matrix.mulVec] using Matrix.mulVec_mulVec z (Matrix.transpose (A t)) (g t)
  have hmul₂ :
      Matrix.mulVec (g t * A t) z =
        Matrix.mulVec (g t) (Matrix.mulVec (A t) z) := by
    simpa [Matrix.mulVec] using Matrix.mulVec_mulVec z (g t) (A t)
  have hadd :
      Matrix.mulVec ((Matrix.transpose (A t)) * g t + g t * A t) z =
        Matrix.mulVec ((Matrix.transpose (A t)) * g t) z +
          Matrix.mulVec (g t * A t) z := by
    simpa [Matrix.mulVec] using Matrix.add_mulVec ((Matrix.transpose (A t)) * g t) (g t * A t) z
  rw [hadd, dotProduct_add, hmul₁, hmul₂]
  have hdot₁ :
      dotProduct y (Matrix.mulVec (Matrix.transpose (A t)) (Matrix.mulVec (g t) z)) =
        dotProduct (Matrix.mulVec (A t) y) (Matrix.mulVec (g t) z) := by
    simpa [Matrix.vecMul, Matrix.mulVec, dotProduct] using
      (Matrix.dotProduct_mulVec y (Matrix.transpose (A t)) (Matrix.mulVec (g t) z)).trans
        (by
          congr 1
          simpa [Matrix.vecMul, Matrix.mulVec, dotProduct] using Matrix.vecMul_transpose (A t) y)
  rw [hdot₁]
  simp [coordinateParallelRhs, Matrix.mulVec_neg]

theorem eqOn_const_of_zero_deriv
    {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ} {c : ℝ}
    (hfcont : ContinuousOn f (Set.Icc (-ε) ε))
    (hfderiv : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt f 0 t)
    (hf0 : f 0 = c) :
    EqOn f (fun _ => c) (Set.Icc (-ε) ε) := by
  have hv :
      ∀ t ∈ Set.Ioo (-ε) ε,
        LipschitzOnWith (0 : NNReal) (fun _ : ℝ => (0 : ℝ)) (Set.univ : Set ℝ) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x y
    simp
  have hconstDeriv :
      ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt (fun _ : ℝ => c) 0 t := by
    intro t ht
    simpa using hasDerivAt_const t c
  apply (ODE_solution_unique_of_mem_Icc (v := fun _ _ => (0 : ℝ)) (s := fun _ => Set.univ)
      (K := (0 : NNReal)) (t₀ := 0))
  · exact hv
  · constructor <;> linarith
  · exact hfcont
  · exact hfderiv
  · intro t ht
    trivial
  · exact continuous_const.continuousOn
  · exact hconstDeriv
  · intro t ht
    trivial
  · simpa using hf0

theorem coordinateParallelTransportOn_preservesPairing
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (hε : 0 < ε) (K : NNReal)
    (hpl : IsPicardLindelof (coordinateParallelRhs A)
      (coordinateInitialPoint ε hε)
      (0 : CoordinateVector n) 2 1 ((2 : NNReal) * K) K)
    (g dg : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hgcont : ∀ i j, Continuous fun t => g t i j)
    (hdg : ∀ t i j, HasDerivAt (fun s => g s i j) (dg t i j) t)
    (hcompat : ∀ t ∈ Set.Ioo (-ε) ε, dg t = Matrix.transpose (A t) * g t + g t * A t) :
    PreservesPairing (coordinatePairing g)
      (coordinateParallelTransportOn A ε hε K hpl) := by
  refine ⟨coordinateParallelTransportOn_zero_mem A hε K hpl, ?_⟩
  intro v w t ht
  let q : ℝ → ℝ :=
    fun s =>
      coordinatePairing g s
        (coordinateParallelTransportOn A ε hε K hpl v s)
        (coordinateParallelTransportOn A ε hε K hpl w s)
  have hqcont : ContinuousOn q (Set.Icc (-ε) ε) := by
    refine continuousOn_coordinatePairing g hgcont ?_ ?_
    · exact continuousOn_of_isParallelAlong
        (coordinateParallelTransportOn_isParallel A ε hε K hpl v)
    · exact continuousOn_of_isParallelAlong
        (coordinateParallelTransportOn_isParallel A ε hε K hpl w)
  have hqderiv : ∀ s ∈ Set.Ioo (-ε) ε, HasDerivAt q 0 s := by
    intro s hs
    have hv' :
        HasDerivAt (coordinateParallelTransportOn A ε hε K hpl v)
          (coordinateParallelRhs A s
            ((coordinateParallelTransportOn A ε hε K hpl v) s)) s := by
      exact
        (coordinateParallelTransportOn_isParallel A ε hε K hpl v s
          (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hw' :
        HasDerivAt (coordinateParallelTransportOn A ε hε K hpl w)
          (coordinateParallelRhs A s
            ((coordinateParallelTransportOn A ε hε K hpl w) s)) s := by
      exact
        (coordinateParallelTransportOn_isParallel A ε hε K hpl w s
          (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have hpair :=
      hasDerivAt_coordinatePairing (g := g) (dg := dg)
        (Y := coordinateParallelTransportOn A ε hε K hpl v)
        (Z := coordinateParallelTransportOn A ε hε K hpl w)
        (t := s) (fun i j => hdg s i j) hv' hw'
    have hzero :
        coordinatePairingAt (dg s)
            ((coordinateParallelTransportOn A ε hε K hpl v) s)
            ((coordinateParallelTransportOn A ε hε K hpl w) s) +
          coordinatePairingAt (g s)
            (coordinateParallelRhs A s
              ((coordinateParallelTransportOn A ε hε K hpl v) s))
            ((coordinateParallelTransportOn A ε hε K hpl w) s) +
          coordinatePairingAt (g s)
            ((coordinateParallelTransportOn A ε hε K hpl v) s)
            (coordinateParallelRhs A s
              ((coordinateParallelTransportOn A ε hε K hpl w) s)) = 0 := by
      exact coordinatePairingAt_parallel_deriv_eq_zero A g dg s _ _ (hcompat s hs)
    simpa [q, hzero] using hpair
  have hq0 : q 0 = coordinatePairing g 0 v w := by
    simp [q, coordinateParallelTransportOn_initial A ε hε K hpl]
  exact (eqOn_const_of_zero_deriv hε hqcont hqderiv hq0) ht

theorem coordinateParallelTransport_preservesPairing
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (g dg : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hgcont : ∀ i j, Continuous fun t => g t i j)
    (hdg : ∀ t i j, HasDerivAt (fun s => g s i j) (dg t i j) t)
    (hcompat :
      ∀ t ∈ Set.Ioo (-(coordinateTransportData A hAcont).ε)
          (coordinateTransportData A hAcont).ε,
        dg t = Matrix.transpose (A t) * g t + g t * A t) :
    PreservesPairing (coordinatePairing g)
      (coordinateParallelTransport A hAcont) := by
  classical
  cases hdata : coordinateTransportData A hAcont with
  | mk ε hε K hcoeff hpl =>
      simpa [coordinateParallelTransport, hdata] using
        (coordinateParallelTransportOn_preservesPairing A ε hε K hpl g dg hgcont hdg
          (by simpa [hdata] using hcompat))

end Coordinate

end ParallelTransport
