import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Bochner.ComponentBridge

open BigOperators Finset

namespace Bochner.Coordinate

variable (n : ℕ)

abbrev End1 := Fin n → Fin n → Fin n → ℝ
abbrev End2 := Fin n → Fin n → Fin n → Fin n → ℝ
abbrev Covector := Fin n → ℝ
abbrev Covector1 := Fin n → Fin n → ℝ
abbrev Covector2 := Fin n → Fin n → Fin n → ℝ

instance : AddCommGroup (End1 n) := inferInstance
instance : AddCommGroup (End2 n) := inferInstance
instance : AddCommGroup (Covector n) := inferInstance
instance : AddCommGroup (Covector1 n) := inferInstance
instance : AddCommGroup (Covector2 n) := inferInstance

def endWedge (A B : End1 n) : End2 n :=
  fun k l μ ν => ∑ m : Fin n, (A k m μ * B m l ν - A k m ν * B m l μ)

def act0 (A : End1 n) (α : Covector n) : Covector1 n :=
  fun μ k => ∑ l : Fin n, A k l μ * α l

def act1 (A : End1 n) (ω : Covector1 n) : Covector2 n :=
  fun μ ν k => ∑ l : Fin n, (A k l μ * ω ν l - A k l ν * ω μ l)

def act2 (F : End2 n) (α : Covector n) : Covector2 n :=
  fun μ ν k => ∑ l : Fin n, F k l μ ν * α l

private lemma act1_add_right' (A : End1 n) (ω₁ ω₂ : Covector1 n) :
    act1 n A (ω₁ + ω₂) = act1 n A ω₁ + act1 n A ω₂ := by
  ext μ ν k
  simp [act1, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

private lemma act2_add_left' (F₁ F₂ : End2 n) (α : Covector n) :
    act2 n (F₁ + F₂) α = act2 n F₁ α + act2 n F₂ α := by
  ext μ ν k
  simp [act2, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma mfs (a : ℝ) (f : Fin n → ℝ) :
    a * ∑ i : Fin n, f i = ∑ i : Fin n, a * f i := by
  rw [← smul_eq_mul a, Finset.smul_sum]
  simp [smul_eq_mul]

private lemma fsm (f : Fin n → ℝ) (c : ℝ) :
    (∑ i : Fin n, f i) * c = ∑ i : Fin n, f i * c := by
  rw [mul_comm]
  rw [← smul_eq_mul c, Finset.smul_sum]
  simp [smul_eq_mul, mul_comm c]

private lemma act_assoc' (A B : End1 n) (α : Covector n) :
    act1 n A (act0 n B α) = act2 n (endWedge n A B) α := by
  ext μ ν k
  calc
    act1 n A (act0 n B α) μ ν k
        = ∑ l : Fin n,
            ∑ m : Fin n,
              (A k l μ * (B l m ν * α m) - A k l ν * (B l m μ * α m)) := by
            unfold act1 act0
            apply Finset.sum_congr rfl
            intro l hl
            rw [mfs n (A k l μ) (fun m => B l m ν * α m)]
            rw [mfs n (A k l ν) (fun m => B l m μ * α m)]
            rw [← Finset.sum_sub_distrib]
    _ = ∑ m : Fin n,
          ∑ l : Fin n,
            (A k l μ * (B l m ν * α m) - A k l ν * (B l m μ * α m)) := by
          rw [sum_comm]
    _ = ∑ m : Fin n,
          ∑ l : Fin n, ((A k l μ * B l m ν - A k l ν * B l m μ) * α m) := by
          apply Finset.sum_congr rfl
          intro m hm
          apply Finset.sum_congr rfl
          intro l hl
          ring
    _ = ∑ m : Fin n, (∑ l : Fin n, (A k l μ * B l m ν - A k l ν * B l m μ)) * α m := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [fsm n (fun l => A k l μ * B l m ν - A k l ν * B l m μ) (α m)]
    _ = act2 n (endWedge n A B) α μ ν k := by
          rfl

structure CoordConnectionData (n : ℕ) where
  dEnd : End1 n → End2 n
  d0 : Covector n → Covector1 n
  d1 : Covector1 n → Covector2 n
  d1_add : ∀ ω₁ ω₂ : Covector1 n, d1 (ω₁ + ω₂) = d1 ω₁ + d1 ω₂
  d1_d0 : ∀ α : Covector n, d1 (d0 α) = 0
  d1_act0 :
    ∀ A : End1 n, ∀ α : Covector n,
      d1 (act0 n A α) = act2 n (dEnd A) α - act1 n A (d0 α)

def coordAlgebra (D : CoordConnectionData n) : BundleConnectionAlgebra where
  ΩEnd1 := End1 n
  ΩEnd2 := End2 n
  ΩE0 := Covector n
  ΩE1 := Covector1 n
  ΩE2 := Covector2 n
  dEnd := D.dEnd
  dE0 := D.d0
  dE1 := D.d1
  wedgeEnd := endWedge n
  act0 := act0 n
  act1 := act1 n
  act2 := act2 n
  dE1_add := D.d1_add
  act1_add_right := act1_add_right' n
  act2_add_left := act2_add_left' n
  dE1_dE0_eq_zero := D.d1_d0
  dE1_act0 := D.d1_act0
  act_assoc := act_assoc' n

def coordProjection (D : CoordConnectionData n) :
    ComponentProjection (coordAlgebra n D) (Fin n × Fin n × Fin n) ℝ where
  proj := fun ω ⟨μ, ν, k⟩ => ω μ ν k

def covectorCovariantDerivative (D : CoordConnectionData n) (A : End1 n) (α : Covector n) :
    Covector1 n :=
  covariantDeriv0 (coordAlgebra n D) ⟨A⟩ α

def covectorCommutator (D : CoordConnectionData n) (A : End1 n) (α : Covector n) :
    Covector2 n :=
  covariantDeriv1 (coordAlgebra n D) ⟨A⟩ (covectorCovariantDerivative n D A α)

theorem proj_covector_commutator_eq_explicit
    (D : CoordConnectionData n) (A : End1 n) (α : Covector n) (μ ν k : Fin n) :
    (coordProjection n D).proj (covectorCommutator n D A α) (μ, ν, k) =
      D.d1 (covectorCovariantDerivative n D A α) μ ν k
        + ∑ l : Fin n,
            (A k l μ * covectorCovariantDerivative n D A α ν l
              - A k l ν * covectorCovariantDerivative n D A α μ l) := by
  rfl

theorem proj_curvature_action_eq_explicit
    (D : CoordConnectionData n) (A : End1 n) (α : Covector n) (μ ν k : Fin n) :
    (coordProjection n D).proj (curvatureAction (coordAlgebra n D) ⟨A⟩ α) (μ, ν, k) =
      ∑ l : Fin n, curvature (coordAlgebra n D) ⟨A⟩ k l μ ν * α l := by
  rfl

theorem covector_commutator_eq_curvature_action
    (D : CoordConnectionData n) (A : End1 n) (α : Covector n) :
    covectorCommutator n D A α = curvatureAction (coordAlgebra n D) ⟨A⟩ α := by
  simpa [covectorCommutator, covectorCovariantDerivative] using
    covariant_square_eq_curvature_action (coordAlgebra n D) ⟨A⟩ α

theorem classical_covector_commutator
    (D : CoordConnectionData n) (A : End1 n) (α : Covector n) :
    ∀ μ ν k : Fin n,
      D.d1 (covectorCovariantDerivative n D A α) μ ν k
        + ∑ l : Fin n,
            (A k l μ * covectorCovariantDerivative n D A α ν l
              - A k l ν * covectorCovariantDerivative n D A α μ l)
        = ∑ l : Fin n, curvature (coordAlgebra n D) ⟨A⟩ k l μ ν * α l := by
  intro μ ν k
  have h :=
    covariant_square_in_components (coordAlgebra n D) ⟨A⟩ α (coordProjection n D) (μ, ν, k)
  have h' :
      D.d1 (covectorCovariantDerivative n D A α) μ ν k
        + ((∑ l : Fin n, A k l μ * covectorCovariantDerivative n D A α ν l)
            - ∑ l : Fin n, A k l ν * covectorCovariantDerivative n D A α μ l)
        = ∑ l : Fin n, curvature (coordAlgebra n D) ⟨A⟩ k l μ ν * α l := by
    simpa [coordAlgebra, coordProjection, covectorCommutator, covectorCovariantDerivative,
      covariantDeriv0, covariantDeriv1, act1, curvatureAction, act2] using h
  simpa [Finset.sum_sub_distrib] using h'

end Bochner.Coordinate
