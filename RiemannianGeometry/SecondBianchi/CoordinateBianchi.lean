import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import SecondBianchi.ComponentBridge

/-!
# Coordinate Bridge for the Second Bianchi Identity

Concrete `LocalConnectionAlgebra` over `Fin n`-indexed tensor components:

* `Form1 n = Fin n → Fin n → Fin n → ℝ`            (connection 1-form `A^i_{j,μ}`)
* `Form2 n = Fin n → Fin n → Fin n → Fin n → ℝ`    (curvature 2-form `R^i_{j,μν}`)
* `Form3 n = Fin n → Fin n → Fin n → Fin n → Fin n → ℝ` (3-form)

Index convention: the first two `Fin n` slots are the gl(n) matrix indices
`(i, j)` and the remaining slots are (antisymmetric) form indices.

`d1`, `d2` are left as parameters in `CoordDiffData` because they encode the
Poincaré lemma and Leibniz rule — properties requiring a smooth structure.

**Main result** (`classical_second_bianchi`): for any `CoordDiffData D` and
any connection 1-form `A`, with `R = d1 A + A ∧ A`, for all `i j e k l : Fin n`,

  `(d2 R) i j e k l`
  `+ Σ_m (A i m e · R m j k l + A i m k · R m j l e + A i m l · R m j e k)`
  `− Σ_m (R i m e k · A m j l + R i m k l · A m j e + R i m l e · A m j k) = 0`.

This is `(d_∇ R)^i_{j,ekl} = 0`.  When `d2` is the standard exterior derivative
`(d2 Ω) i j e k l = ∂_e Ω i j k l + ∂_k Ω i j l e + ∂_l Ω i j e k`, one
algebraic regrouping identifies this with the classical cyclic covariant-derivative
sum `∇_e R^i_{j,kl} + ∇_k R^i_{j,le} + ∇_l R^i_{j,ek} = 0`.
-/

open BigOperators Finset

namespace SecondBianchi.Coordinate

variable (n : ℕ)

/-! ## Form types and instances -/

abbrev Form1 := Fin n → Fin n → Fin n → ℝ
abbrev Form2 := Fin n → Fin n → Fin n → Fin n → ℝ
abbrev Form3 := Fin n → Fin n → Fin n → Fin n → Fin n → ℝ

instance : AddCommGroup (Form1 n) := inferInstance
instance : AddCommGroup (Form2 n) := inferInstance
instance : AddCommGroup (Form3 n) := inferInstance

/-! ## Wedge products -/

def wedge11 (A B : Form1 n) : Form2 n :=
  fun i j μ ν => ∑ k : Fin n, (A i k μ * B k j ν - A i k ν * B k j μ)

def wedge12 (A : Form1 n) (Ω : Form2 n) : Form3 n :=
  fun i j e k l =>
    ∑ m : Fin n, (A i m e * Ω m j k l + A i m k * Ω m j l e + A i m l * Ω m j e k)

def wedge21 (Ω : Form2 n) (A : Form1 n) : Form3 n :=
  fun i j e k l =>
    ∑ m : Fin n, (Ω i m e k * A m j l + Ω i m k l * A m j e + Ω i m l e * A m j k)

/-! ## Helper lemmas for distributing multiplication over sums -/

private lemma mfs (a : ℝ) (f : Fin n → ℝ) :
    a * ∑ i : Fin n, f i = ∑ i : Fin n, a * f i := by
  rw [← smul_eq_mul a, Finset.smul_sum]; simp [smul_eq_mul]

private lemma fsm (f : Fin n → ℝ) (c : ℝ) :
    (∑ m : Fin n, f m) * c = ∑ m : Fin n, f m * c := by
  rw [mul_comm]; rw [← smul_eq_mul c, Finset.smul_sum]; simp [smul_eq_mul, mul_comm c]

/-! ## Algebraic axioms proved from definitions -/

private lemma wedge12_add_right' (A : Form1 n) (Ω₁ Ω₂ : Form2 n) :
    wedge12 n A (Ω₁ + Ω₂) = wedge12 n A Ω₁ + wedge12 n A Ω₂ := by
  ext i j e k l
  simp only [wedge12, Pi.add_apply, mul_add, sum_add_distrib]
  ring

private lemma wedge21_add_left' (Ω₁ Ω₂ : Form2 n) (A : Form1 n) :
    wedge21 n (Ω₁ + Ω₂) A = wedge21 n Ω₁ A + wedge21 n Ω₂ A := by
  ext i j e k l
  simp only [wedge21, Pi.add_apply, add_mul, sum_add_distrib]
  ring

private lemma wedge_assoc' (A B C : Form1 n) :
    wedge12 n A (wedge11 n B C) = wedge21 n (wedge11 n A B) C := by
  ext i j e k l
  simp only [wedge12, wedge11, wedge21]
  -- Distribute A * ∑ p → ∑ p, and combine inner sums
  simp_rw [mfs n _ _]
  simp_rw [← sum_add_distrib]
  -- Distribute ∑ m * C → ∑ m, and combine inner sums
  simp_rw [fsm n _ _]
  simp_rw [← sum_add_distrib]
  -- Swap summation order
  rw [sum_comm (s := univ) (t := univ)]
  -- Pointwise equality by ring
  congr 1; ext p; congr 1; ext m; ring

/-! ## Differential data (axiomatized) -/

/-- Parameters encoding the exterior derivatives `d1`, `d2` and the two axioms
that require a smooth structure: `d ∘ d = 0` and the Leibniz rule. -/
structure CoordDiffData (n : ℕ) where
  d1     : Form1 n → Form2 n
  d2     : Form2 n → Form3 n
  d2_add : ∀ Ω₁ Ω₂ : Form2 n, d2 (Ω₁ + Ω₂) = d2 Ω₁ + d2 Ω₂
  d2_d1  : ∀ A : Form1 n, d2 (d1 A) = 0
  d2_wdg : ∀ A B : Form1 n,
             d2 (wedge11 n A B) = wedge21 n (d1 A) B - wedge12 n A (d1 B)

/-! ## LocalConnectionAlgebra instance -/

def coordAlgebra (D : CoordDiffData n) : LocalConnectionAlgebra where
  Ω1                := Form1 n
  Ω2                := Form2 n
  Ω3                := Form3 n
  d1                := D.d1
  d2                := D.d2
  wedge11           := wedge11 n
  wedge12           := wedge12 n
  wedge21           := wedge21 n
  d2_add            := D.d2_add
  wedge12_add_right := wedge12_add_right' n
  wedge21_add_left  := wedge21_add_left' n
  d2_d1_eq_zero     := D.d2_d1
  d2_wedge11        := D.d2_wdg
  wedge_assoc       := wedge_assoc' n

/-! ## Component projection -/

def coordProjection (D : CoordDiffData n) :
    ComponentProjection (coordAlgebra n D)
      (Fin n × Fin n × Fin n × Fin n × Fin n) ℝ where
  proj      := fun ω ⟨i, j, e, k, l⟩ => ω i j e k l
  proj_zero := by intro ⟨_, _, _, _, _⟩; rfl

/-! ## Key definitional lemma -/

/-- The `(i, j, e, k, l)` component of `covariantExterior conn (curvature conn)` equals
the explicit expression `(d2 R) i j e k l + (A ∧ R − R ∧ A) terms`, by definition. -/
theorem proj_eq_explicit
    (D : CoordDiffData n) (A : Form1 n) (i j e k l : Fin n) :
    let conn : ConnectionForm (coordAlgebra n D) := ⟨A⟩
    let R    := curvature (coordAlgebra n D) conn
    (coordProjection n D).proj
        (covariantExterior (coordAlgebra n D) conn R) (i, j, e, k, l) =
      D.d2 R i j e k l
      + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
      - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k) := by
  simp [coordProjection, covariantExterior, coordAlgebra, wedge12, wedge21]

/-! ## Classical Second Bianchi Identity -/

/--
**Classical Second Bianchi Identity** (coordinate / component form).

For any dimension `n`, any `CoordDiffData D` satisfying `d ∘ d = 0` and the
Leibniz rule, and any connection 1-form `A : Form1 n`, with curvature
`R = d1 A + A ∧ A`, for all indices `i j e k l : Fin n`,

  `(d2 R) i j e k l`
  `+ Σ_m (A i m e · R m j k l + A i m k · R m j l e + A i m l · R m j e k)`
  `− Σ_m (R i m e k · A m j l + R i m k l · A m j e + R i m l e · A m j k)  =  0`

This is `(d_∇ R)^i_{j,ekl} = 0`, i.e. the covariant exterior derivative of
the curvature 2-form vanishes component-by-component.

**Proof**: By `proj_eq_explicit`, this equals the `(i,j,e,k,l)` component of
`covariantExterior conn (curvature conn)`.  The abstract `second_bianchi_identity`
gives `covariantExterior conn (curvature conn) = 0`, so every component is zero.
-/
theorem classical_second_bianchi
    (D : CoordDiffData n) (A : Form1 n) :
    let conn : ConnectionForm (coordAlgebra n D) := ⟨A⟩
    let R    := curvature (coordAlgebra n D) conn
    ∀ i j e k l : Fin n,
      D.d2 R i j e k l
      + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
      - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
      = 0 := by
  intro conn R i j e k l
  have h := second_bianchi_in_components
    (coordAlgebra n D) ⟨A⟩ (coordProjection n D) (i, j, e, k, l)
  rw [proj_eq_explicit n D A i j e k l] at h
  linarith

end SecondBianchi.Coordinate
