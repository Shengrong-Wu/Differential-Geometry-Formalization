import Metric.CoordinateMetric
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Metric.Coordinate

variable {n : ℕ}

/-- The entrywise `ℓ¹` coefficient sum of a coordinate tensor. -/
def entryAbsSum (g : Tensor2 n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, |g i j|

/-- The square of the ambient sup norm on coordinate vectors. -/
def supNormSq (v : Fin n → ℝ) : ℝ :=
  ‖v‖ * ‖v‖

theorem entryAbsSum_nonneg (g : Tensor2 n) :
    0 ≤ entryAbsSum g := by
  unfold entryAbsSum
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

theorem supNormSq_nonneg (v : Fin n → ℝ) :
    0 ≤ supNormSq v := by
  unfold supNormSq
  positivity

/-- The entrywise `ℓ¹` coefficient sum varies continuously along any continuous family of
coordinate tensors. -/
theorem continuousOn_entryAbsSum
    {α : Type*} [TopologicalSpace α]
    {s : Set α} {g : α → Tensor2 n}
    (hg : ContinuousOn g s) :
    ContinuousOn (fun x => entryAbsSum (g x)) s := by
  unfold entryAbsSum
  refine continuousOn_finset_sum _ ?_
  intro i hi
  refine continuousOn_finset_sum _ ?_
  intro j hj
  have hgij : ContinuousOn (fun x => g x i j) s := by
    exact (continuousOn_pi.1 ((continuousOn_pi.1 hg) i)) j
  have hnorm : ContinuousOn (fun x => ‖g x i j‖) s := hgij.norm
  simpa [Real.norm_eq_abs] using hnorm

private theorem quadraticForm_add_smul
    {g : Tensor2 n}
    (hsymm : IsSymmetric g)
    (u w : Fin n → ℝ) (c : ℝ) :
    quadraticForm g (u + c • w) =
      quadraticForm g u +
        2 * c * bilinForm g u w +
        c ^ 2 * quadraticForm g w := by
  calc
    quadraticForm g (u + c • w)
      = quadraticForm g u +
          c * bilinForm g u w +
          c * bilinForm g w u +
          c ^ 2 * quadraticForm g w := by
            simp [quadraticForm, bilinForm, Finset.sum_add_distrib, Finset.mul_sum,
              mul_add, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
            ring_nf
    _ = quadraticForm g u +
          2 * c * bilinForm g u w +
          c ^ 2 * quadraticForm g w := by
            rw [bilinForm_comm hsymm w u]
            ring

/-- Cauchy-Schwarz for the bilinear form of a positive-definite coordinate metric tensor. -/
theorem metric_bilin_sq_le
    {g : Tensor2 n}
    (hg : IsPositiveDefinite g)
    (u w : Fin n → ℝ) :
    (bilinForm g u w) ^ 2 ≤ quadraticForm g u * quadraticForm g w := by
  by_cases hw : w = 0
  · simp [hw, bilinForm, quadraticForm]
  have hwpos : 0 < quadraticForm g w := hg.2 w hw
  let c : ℝ := -(bilinForm g u w) / quadraticForm g w
  have hnonneg :
      0 ≤ quadraticForm g (u + c • w) :=
    quadraticForm_nonneg hg (u + c • w)
  have hmain :
      0 ≤ quadraticForm g u * quadraticForm g w - (bilinForm g u w) ^ 2 := by
    have htmp := hnonneg
    rw [quadraticForm_add_smul hg.1 u w c] at htmp
    have hwne : quadraticForm g w ≠ 0 := ne_of_gt hwpos
    dsimp [c] at htmp
    field_simp [hwne] at htmp
    nlinarith [htmp, hwpos]
  linarith

/-- Cauchy-Schwarz for the bilinear form of a positive-definite coordinate metric tensor. -/
theorem metric_bilin_abs_le
    {g : Tensor2 n}
    (hg : IsPositiveDefinite g)
    (u w : Fin n → ℝ) :
    |bilinForm g u w| ≤
      Real.sqrt (quadraticForm g u) * Real.sqrt (quadraticForm g w) := by
  have hu_nonneg : 0 ≤ quadraticForm g u :=
    quadraticForm_nonneg hg u
  have hw_nonneg : 0 ≤ quadraticForm g w :=
    quadraticForm_nonneg hg w
  have hsq :
      |bilinForm g u w| ^ 2 ≤
        (Real.sqrt (quadraticForm g u) * Real.sqrt (quadraticForm g w)) ^ 2 := by
    calc
      |bilinForm g u w| ^ 2
        = (bilinForm g u w) ^ 2 := by simp [sq_abs]
      _ ≤ quadraticForm g u * quadraticForm g w :=
        metric_bilin_sq_le hg u w
      _ = (Real.sqrt (quadraticForm g u) *
            Real.sqrt (quadraticForm g w)) ^ 2 := by
            calc
              quadraticForm g u * quadraticForm g w
                = (Real.sqrt (quadraticForm g u)) ^ 2 *
                    (Real.sqrt (quadraticForm g w)) ^ 2 := by
                      rw [Real.sq_sqrt hu_nonneg, Real.sq_sqrt hw_nonneg]
              _ = (Real.sqrt (quadraticForm g u) *
                    Real.sqrt (quadraticForm g w)) ^ 2 := by
                      ring
  have hright_nonneg :
      0 ≤ Real.sqrt (quadraticForm g u) * Real.sqrt (quadraticForm g w) := by
    positivity
  exact (sq_le_sq₀ (abs_nonneg _) hright_nonneg).mp hsq

private theorem quadraticForm_eq_dotProduct_mulVec
    (g : Tensor2 n)
    (z : Fin n → ℝ) :
    quadraticForm g z = dotProduct z (Matrix.mulVec g z) := by
  simp [quadraticForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- A crude but reusable Euclidean upper bound for a coordinate metric quadratic form in terms of
the sup norm and the entrywise `ℓ¹` sum of the matrix coefficients. -/
theorem quadraticForm_le_card_mul_entryAbsSum_mul_sq_norm
    (g : Tensor2 n)
    (z : Fin n → ℝ) :
    quadraticForm g z ≤
      ((Fintype.card (Fin n) : ℝ) * entryAbsSum g) * supNormSq z := by
  have hdot :
      |dotProduct z (Matrix.mulVec g z)| ≤
        (Fintype.card (Fin n) : ℝ) * (‖z‖ * ‖Matrix.mulVec g z‖) := by
    calc
      |dotProduct z (Matrix.mulVec g z)|
        = |∑ i : Fin n, z i * Matrix.mulVec g z i| := by
            simp [dotProduct]
      _ ≤ ∑ i : Fin n, |z i * Matrix.mulVec g z i| := by
            simpa using
              (Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun i : Fin n => z i * Matrix.mulVec g z i))
      _ = ∑ i : Fin n, |z i| * |Matrix.mulVec g z i| := by
            simp [abs_mul]
      _ ≤ ∑ i : Fin n, ‖z‖ * ‖Matrix.mulVec g z‖ := by
            refine Finset.sum_le_sum fun i _ => ?_
            gcongr
            · simpa [Pi.norm_def', Real.norm_eq_abs] using
                (show (‖z i‖₊ : ℝ) ≤ ‖z‖₊ from
                  Finset.le_sup (s := Finset.univ) (f := fun b : Fin n => ‖z b‖₊)
                    (Finset.mem_univ i))
            · simpa [Pi.norm_def', Real.norm_eq_abs] using
                (show (‖Matrix.mulVec g z i‖₊ : ℝ) ≤ ‖Matrix.mulVec g z‖₊ from
                  Finset.le_sup (s := Finset.univ)
                    (f := fun b : Fin n => ‖Matrix.mulVec g z b‖₊)
                    (Finset.mem_univ i))
      _ = (Fintype.card (Fin n) : ℝ) * (‖z‖ * ‖Matrix.mulVec g z‖) := by
            simp [Finset.card_univ]
  have hmul :
      ‖Matrix.mulVec g z‖ ≤ entryAbsSum g * ‖z‖ := by
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg (entryAbsSum_nonneg g) (norm_nonneg _))]
    intro i
    calc
      ‖(Matrix.mulVec g z) i‖ = ‖∑ j : Fin n, g i j * z j‖ := by
        rfl
      _ ≤ ∑ j : Fin n, ‖g i j * z j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, |g i j| * ‖z j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa [Real.norm_eq_abs, abs_mul]
      _ ≤ ∑ j : Fin n, |g i j| * ‖z‖ := by
        refine Finset.sum_le_sum ?_
        intro j hj
        gcongr
        exact norm_le_pi_norm z j
      _ = (∑ j : Fin n, |g i j|) * ‖z‖ := by
        rw [Finset.sum_mul]
      _ ≤ entryAbsSum g * ‖z‖ := by
        have hrow :
            ∑ j : Fin n, |g i j| ≤ entryAbsSum g := by
          simpa [entryAbsSum] using
            (Finset.single_le_sum
              (f := fun k : Fin n => ∑ j : Fin n, |g k j|)
              (fun k hk => Finset.sum_nonneg fun j hj => abs_nonneg _)
              (by simp : i ∈ (Finset.univ : Finset (Fin n))))
        gcongr
  calc
    quadraticForm g z = dotProduct z (Matrix.mulVec g z) :=
      quadraticForm_eq_dotProduct_mulVec g z
    _ ≤ |dotProduct z (Matrix.mulVec g z)| := le_abs_self _
    _ ≤ (Fintype.card (Fin n) : ℝ) * (‖z‖ * ‖Matrix.mulVec g z‖) := hdot
    _ ≤ (Fintype.card (Fin n) : ℝ) * (‖z‖ * (entryAbsSum g * ‖z‖)) := by
          gcongr
    _ = ((Fintype.card (Fin n) : ℝ) * entryAbsSum g) * supNormSq z := by
          rw [supNormSq]
          ring

/-- Pairing against the `i`-th inverse row recovers the `i`-th coordinate. -/
theorem bilinForm_inverseRow_eq_coord
    {g : Tensor2 n} {gInv : InverseTensor2 n}
    (hsymm : IsSymmetric g)
    (hInv : IsInversePair g gInv)
    (v : Fin n → ℝ)
    (i : Fin n) :
    bilinForm g v (fun j => gInv i j) = v i := by
  unfold bilinForm
  calc
    ∑ j : Fin n, ∑ k : Fin n, v j * g j k * gInv i k
      = ∑ j : Fin n, v j * (∑ k : Fin n, gInv i k * g k j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hsymm j k]
          ring
    _ = ∑ j : Fin n, v j * (if i = j then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [inversePair_apply hInv i j]
    _ = v i := by
          simp

/-- The quadratic form of the `i`-th inverse row equals the `i`-th inverse diagonal entry. -/
theorem quadraticForm_inverseRow_eq_diag
    {g : Tensor2 n} {gInv : InverseTensor2 n}
    (hsymm : IsSymmetric g)
    (hInv : IsInversePair g gInv)
    (i : Fin n) :
    quadraticForm g (fun j => gInv i j) = gInv i i := by
  rw [quadraticForm_eq_bilinForm]
  simpa using bilinForm_inverseRow_eq_coord hsymm hInv (fun j => gInv i j) i

/-- The diagonal entries of an inverse pair are nonnegative when the base metric is positive
definite. -/
theorem inversePair_diag_nonneg
    {g : Tensor2 n} {gInv : InverseTensor2 n}
    (hg : IsPositiveDefinite g)
    (hInv : IsInversePair g gInv)
    (i : Fin n) :
    0 ≤ gInv i i := by
  have hq :
      0 ≤ quadraticForm g (fun j => gInv i j) :=
    quadraticForm_nonneg hg (fun j => gInv i j)
  simpa [quadraticForm_inverseRow_eq_diag hg.1 hInv i] using hq

/-- Euclidean velocity is controlled from above by the metric energy and the entrywise `ℓ¹` sum of
the inverse metric coefficients. This is the lower norm-comparison direction
`quadraticForm g v ≥ c * ‖v‖²` in a reusable algebraic form. -/
theorem sq_norm_le_entryAbsSum_mul_quadraticForm_of_inversePair
    {g : Tensor2 n} {gInv : InverseTensor2 n}
    (hg : IsPositiveDefinite g)
    (hInv : IsInversePair g gInv)
    (v : Fin n → ℝ) :
    supNormSq v ≤ entryAbsSum gInv * quadraticForm g v := by
  let C : ℝ := entryAbsSum gInv
  have hC_nonneg : 0 ≤ C := by
    simpa [C] using entryAbsSum_nonneg gInv
  have hq_nonneg : 0 ≤ quadraticForm g v :=
    quadraticForm_nonneg hg v
  have hcoord : ∀ i : Fin n, ‖v i‖ ≤ Real.sqrt (C * quadraticForm g v) := by
    intro i
    let row : Fin n → ℝ := fun j => gInv i j
    have hpair :
        |v i| ≤ Real.sqrt (quadraticForm g v) * Real.sqrt (quadraticForm g row) := by
      simpa [row, bilinForm_inverseRow_eq_coord hg.1 hInv v i] using
        metric_bilin_abs_le hg v row
    have hdiag_nonneg : 0 ≤ gInv i i := inversePair_diag_nonneg hg hInv i
    have hdiag_le : gInv i i ≤ C := by
      have habs_diag :
          |gInv i i| ≤ ∑ j : Fin n, |gInv i j| := by
        simpa using
          (Finset.single_le_sum
            (f := fun j : Fin n => |gInv i j|)
            (fun j hj => abs_nonneg _)
            (by simp : i ∈ (Finset.univ : Finset (Fin n))))
      have hrow_le :
          ∑ j : Fin n, |gInv i j| ≤ C := by
        simpa [C, entryAbsSum] using
          (Finset.single_le_sum
            (f := fun k : Fin n => ∑ j : Fin n, |gInv k j|)
            (fun k hk => Finset.sum_nonneg fun j hj => abs_nonneg _)
            (by simp : i ∈ (Finset.univ : Finset (Fin n))))
      exact le_trans (le_trans (le_abs_self _) habs_diag) hrow_le
    have hsqrt_le : Real.sqrt (gInv i i) ≤ Real.sqrt C := by
      apply Real.sqrt_le_sqrt <;> assumption
    calc
      ‖v i‖ = |v i| := by rw [Real.norm_eq_abs]
      _ ≤ Real.sqrt (quadraticForm g v) * Real.sqrt (quadraticForm g row) := hpair
      _ = Real.sqrt (quadraticForm g v) * Real.sqrt (gInv i i) := by
            rw [quadraticForm_inverseRow_eq_diag hg.1 hInv i]
      _ ≤ Real.sqrt (quadraticForm g v) * Real.sqrt C := by
            exact mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)
      _ = Real.sqrt (C * quadraticForm g v) := by
            symm
            rw [Real.sqrt_mul hC_nonneg, mul_comm]
  have hnorm : ‖v‖ ≤ Real.sqrt (C * quadraticForm g v) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    simpa using hcoord i
  have hsq :
      ‖v‖ * ‖v‖ ≤ (Real.sqrt (C * quadraticForm g v)) ^ 2 := by
    simpa [pow_two] using
      (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm
  calc
    supNormSq v ≤ (Real.sqrt (C * quadraticForm g v)) ^ 2 := by
      simpa [supNormSq] using hsq
    _ = C * quadraticForm g v := by
          rw [Real.sq_sqrt]
          positivity
    _ = entryAbsSum gInv * quadraticForm g v := by
          rfl

/-- A compact family of positive-definite coordinate metrics with continuous inverse field admits
uniform Euclidean norm comparison constants. This is the owner-layer compactness API used later by
the smooth Hopf-Rinow shell theorem. -/
theorem exists_uniform_metric_normComparisonOn_isCompact
    {α : Type*} [TopologicalSpace α]
    {K : Set α}
    (hK : IsCompact K)
    {g : α → Tensor2 n} {gInv : α → InverseTensor2 n}
    (hg : ContinuousOn g K)
    (hgInv : ContinuousOn gInv K)
    (hpos : ∀ x ∈ K, IsPositiveDefinite (g x))
    (hInv : ∀ x ∈ K, IsInversePair (g x) (gInv x)) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ x ∈ K, ∀ v : Fin n → ℝ,
        m * supNormSq v ≤ quadraticForm (g x) v ∧
        quadraticForm (g x) v ≤ M * supNormSq v := by
  obtain ⟨Cg, hCg⟩ := IsCompact.exists_bound_of_continuousOn hK
    (continuousOn_entryAbsSum (n := n) hg)
  obtain ⟨Cinv, hCinv⟩ := IsCompact.exists_bound_of_continuousOn hK
    (continuousOn_entryAbsSum (n := n) hgInv)
  let Cg' : ℝ := max Cg 1
  let Cinv' : ℝ := max Cinv 1
  let M0 : ℝ := (Fintype.card (Fin n) : ℝ) * Cg'
  let m : ℝ := 1 / Cinv'
  let M : ℝ := max M0 1
  have hCg'_pos : 0 < Cg' := by
    dsimp [Cg']
    exact lt_of_lt_of_le zero_lt_one (le_max_right Cg 1)
  have hCinv'_pos : 0 < Cinv' := by
    dsimp [Cinv']
    exact lt_of_lt_of_le zero_lt_one (le_max_right Cinv 1)
  have hm_pos : 0 < m := by
    dsimp [m]
    positivity
  have hM_pos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le zero_lt_one (le_max_right M0 1)
  refine ⟨m, M, hm_pos, hM_pos, ?_⟩
  intro x hx v
  have hentry_g : entryAbsSum (g x) ≤ Cg' := by
    have hxCg : entryAbsSum (g x) ≤ Cg := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (entryAbsSum_nonneg (g x))] using hCg x hx
    exact le_trans hxCg (le_max_left _ _)
  have hentry_gInv : entryAbsSum (gInv x) ≤ Cinv' := by
    have hxCinv : entryAbsSum (gInv x) ≤ Cinv := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (entryAbsSum_nonneg (gInv x))] using hCinv x hx
    exact le_trans hxCinv (le_max_left _ _)
  have hq_nonneg : 0 ≤ quadraticForm (g x) v :=
    quadraticForm_nonneg (hpos x hx) v
  have hupper0 :
      quadraticForm (g x) v ≤
        ((Fintype.card (Fin n) : ℝ) * entryAbsSum (g x)) * supNormSq v :=
    quadraticForm_le_card_mul_entryAbsSum_mul_sq_norm (g x) v
  have hcoeff_upper :
      (Fintype.card (Fin n) : ℝ) * entryAbsSum (g x) ≤ M0 := by
    dsimp [M0]
    exact mul_le_mul_of_nonneg_left hentry_g (by positivity)
  have hupper1 :
      ((Fintype.card (Fin n) : ℝ) * entryAbsSum (g x)) * supNormSq v ≤
        M0 * supNormSq v := by
    exact mul_le_mul_of_nonneg_right hcoeff_upper (supNormSq_nonneg v)
  have hupper2 :
      M0 * supNormSq v ≤ M * supNormSq v := by
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (supNormSq_nonneg v)
  have hlower0 :
      supNormSq v ≤ entryAbsSum (gInv x) * quadraticForm (g x) v :=
    sq_norm_le_entryAbsSum_mul_quadraticForm_of_inversePair (hpos x hx) (hInv x hx) v
  have hlower1 :
      supNormSq v ≤ Cinv' * quadraticForm (g x) v := by
    calc
      supNormSq v ≤ entryAbsSum (gInv x) * quadraticForm (g x) v := hlower0
      _ ≤ Cinv' * quadraticForm (g x) v := by
          exact mul_le_mul_of_nonneg_right hentry_gInv hq_nonneg
  constructor
  · dsimp [m]
    have hlower2 : supNormSq v / Cinv' ≤ quadraticForm (g x) v := by
      rw [div_le_iff₀ hCinv'_pos, mul_comm]
      exact hlower1
    simpa [m, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlower2
  · calc
      quadraticForm (g x) v ≤ ((Fintype.card (Fin n) : ℝ) * entryAbsSum (g x)) * supNormSq v :=
        hupper0
      _ ≤ M0 * supNormSq v := hupper1
      _ ≤ M * supNormSq v := hupper2

end Metric.Coordinate
