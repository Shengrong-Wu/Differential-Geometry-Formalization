import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Norm comparison: sup norm ≤ L² norm on `Fin n → ℝ`

For `x : Fin n → ℝ`, the sup (pi) norm `‖x‖_∞ = sup_i |x_i|` is bounded by the
Euclidean (L²) norm `‖x‖₂ = sqrt(∑_i x_i²)`.

This is immediate from `|x_j|² ≤ ∑_i x_i²` for each `j`. -/

open Finset

theorem pi_norm_le_l2_norm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖ ≤ ‖EuclideanSpace.equiv (Fin n) ℝ |>.symm x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [EuclideanSpace.norm_eq]
  calc ‖x i‖ = Real.sqrt (‖x i‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∑ j : Fin n, ‖x j‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        exact single_le_sum (fun j _ => sq_nonneg (‖x j‖)) (mem_univ i)

/-- The sup norm of a vector in `Fin n → ℝ` is bounded by its Euclidean norm,
expressed via `WithLp.toLp`. -/
theorem pi_norm_le_piLp_norm {n : ℕ} (x : Fin n → ℝ) :
    ‖x‖ ≤ ‖(WithLp.toLp (p := 2) x : PiLp 2 (fun _ : Fin n => ℝ))‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  rw [PiLp.norm_eq_of_L2]
  calc ‖x i‖ = Real.sqrt (‖x i‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (∑ j : Fin n, ‖WithLp.toLp (p := 2) x j‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply single_le_sum (fun j _ => sq_nonneg _) (mem_univ i)

/-- The Euclidean norm on `Fin n → ℝ` is bounded by `√n` times the sup norm. -/
theorem piLp_norm_le_sqrt_card_mul_pi_norm {n : ℕ} (x : Fin n → ℝ) :
    ‖(WithLp.toLp (p := 2) x : PiLp 2 (fun _ : Fin n => ℝ))‖ ≤
      Real.sqrt (Fintype.card (Fin n)) * ‖x‖ := by
  rw [PiLp.norm_eq_of_L2]
  have hsum :
      ∑ j : Fin n, ‖(WithLp.toLp (p := 2) x : PiLp 2 (fun _ : Fin n => ℝ)) j‖ ^ 2 ≤
        ∑ j : Fin n, ‖x‖ ^ 2 := by
    refine Finset.sum_le_sum ?_
    intro j _
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x j) 2
  calc
    Real.sqrt (∑ j : Fin n, ‖(WithLp.toLp (p := 2) x : PiLp 2 (fun _ : Fin n => ℝ)) j‖ ^ 2)
        ≤ Real.sqrt (∑ j : Fin n, ‖x‖ ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card (Fin n) * ‖x‖ ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = Real.sqrt (Fintype.card (Fin n)) * ‖x‖ := by
        rw [Real.sqrt_mul (show 0 ≤ (Fintype.card (Fin n) : ℝ) by positivity),
          Real.sqrt_sq (norm_nonneg _)]
