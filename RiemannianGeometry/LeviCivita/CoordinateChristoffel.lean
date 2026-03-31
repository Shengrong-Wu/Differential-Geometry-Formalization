import LeviCivita.Koszul
import Metric.CoordinateMetric
import Variation.LeviCivitaVariationBridge
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace LeviCivita.Coordinate

variable {n : ℕ}

/-- Coordinate derivatives of the metric coefficients. -/
abbrev MetricDerivative (n : ℕ) := Fin n → Fin n → Fin n → ℝ

/-- Christoffel symbols in `Fin n` coordinates. -/
abbrev ChristoffelSymbol (n : ℕ) := Fin n → Fin n → Fin n → ℝ

/-- The standard coordinate Levi-Civita Christoffel formula. -/
noncomputable def leviCivitaChristoffel
    (gInv : Metric.Coordinate.InverseTensor2 n) (dg : MetricDerivative n) :
    ChristoffelSymbol n :=
  fun k i j =>
    (1 / 2 : ℝ) * ∑ l : Fin n, gInv k l * (dg i j l + dg j i l - dg l i j)

/-- The coordinate Christoffel formula matches the variation bridge already present in the repo. -/
theorem leviCivitaChristoffel_eq_variation
    (gInv : Metric.Coordinate.InverseTensor2 n) (dg : MetricDerivative n) :
    leviCivitaChristoffel gInv dg = Variation.Coordinate.leviCivitaVariation gInv dg :=
  rfl

/-- Symmetry in the lower indices follows from symmetry of the metric derivatives. -/
theorem leviCivitaChristoffel_lower_symm
    (gInv : Metric.Coordinate.InverseTensor2 n) (dg : MetricDerivative n)
    (hmetric : ∀ μ i j, dg μ i j = dg μ j i) :
    ∀ k i j, leviCivitaChristoffel gInv dg k i j = leviCivitaChristoffel gInv dg k j i := by
  intro k i j
  simp [leviCivitaChristoffel, hmetric, add_comm]

/-- Lowering the upper index of the coordinate Levi-Civita symbols recovers the usual
Koszul-style expression. -/
theorem metric_contract_leviCivitaChristoffel
    (g : Metric.Coordinate.Tensor2 n)
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : MetricDerivative n)
    (hg : Metric.Coordinate.IsSymmetric g)
    (hgInv : Metric.Coordinate.IsSymmetric gInv)
    (hpair : Metric.Coordinate.IsInversePair g gInv) :
    ∀ m i j,
      ∑ k : Fin n, g m k * leviCivitaChristoffel gInv dg k i j =
        (1 / 2 : ℝ) * (dg i j m + dg j i m - dg m i j) := by
  intro m i j
  classical
  have hdelta :
      ∀ l : Fin n, ∑ k : Fin n, g m k * gInv k l = if m = l then 1 else 0 := by
    intro l
    calc
      ∑ k : Fin n, g m k * gInv k l
          = ∑ k : Fin n, gInv l k * g k m := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hg m k, hgInv k l]
              ring
      _ = if l = m then 1 else 0 := Metric.Coordinate.inversePair_apply hpair l m
      _ = if m = l then 1 else 0 := by
            by_cases hml : m = l
            · simp [hml]
            · simp [hml, eq_comm]
  calc
    ∑ k : Fin n, g m k * leviCivitaChristoffel gInv dg k i j
        = ∑ k : Fin n,
            ∑ l : Fin n,
              (g m k * ((1 / 2 : ℝ) * gInv k l))
                * (dg i j l + dg j i l - dg l i j) := by
            simp [leviCivitaChristoffel, mul_assoc, Finset.mul_sum]
    _ = ∑ l : Fin n,
          ∑ k : Fin n,
            (g m k * ((1 / 2 : ℝ) * gInv k l))
              * (dg i j l + dg j i l - dg l i j) := by
          rw [Finset.sum_comm]
    _ = ∑ l : Fin n,
          ((1 / 2 : ℝ) * (∑ k : Fin n, g m k * gInv k l))
            * (dg i j l + dg j i l - dg l i j) := by
          apply Finset.sum_congr rfl
          intro l hl
          calc
            ∑ k : Fin n, (g m k * ((1 / 2 : ℝ) * gInv k l)) * (dg i j l + dg j i l - dg l i j)
                = (∑ k : Fin n, g m k * ((1 / 2 : ℝ) * gInv k l))
                    * (dg i j l + dg j i l - dg l i j) := by
                      rw [Finset.sum_mul]
            _ = ((1 / 2 : ℝ) * (∑ k : Fin n, g m k * gInv k l))
                  * (dg i j l + dg j i l - dg l i j) := by
                    congr 1
                    calc
                      ∑ k : Fin n, g m k * ((1 / 2 : ℝ) * gInv k l)
                          = ∑ k : Fin n, (1 / 2 : ℝ) * (g m k * gInv k l) := by
                              apply Finset.sum_congr rfl
                              intro k hk
                              ring
                      _ = (1 / 2 : ℝ) * (∑ k : Fin n, g m k * gInv k l) := by
                            rw [Finset.mul_sum]
    _ = ∑ l : Fin n,
          ((1 / 2 : ℝ) * (if m = l then 1 else 0))
            * (dg i j l + dg j i l - dg l i j) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [hdelta l]
    _ = (1 / 2 : ℝ) * (dg i j m + dg j i m - dg m i j) := by
          simp

/-- The lowered Christoffel symbols satisfy the classical coordinate Koszul formula. -/
theorem metric_contract_leviCivitaChristoffel_eq_koszul
    (g : Metric.Coordinate.Tensor2 n)
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : MetricDerivative n)
    (hg : Metric.Coordinate.IsSymmetric g)
    (hgInv : Metric.Coordinate.IsSymmetric gInv)
    (hpair : Metric.Coordinate.IsInversePair g gInv) :
    ∀ m i j,
      (2 : ℝ) * (∑ k : Fin n, g m k * leviCivitaChristoffel gInv dg k i j) =
        dg i j m + dg j i m - dg m i j := by
  intro m i j
  rw [metric_contract_leviCivitaChristoffel g gInv dg hg hgInv hpair m i j]
  ring

/-!
## Lifting Christoffel symbols to abstract CovariantDerivative

A Christoffel symbol `Gamma : ChristoffelSymbol n` defines a bilinear operator on constant
vector fields in `Fin n → ℝ` by contraction: `(nabla_X Y)^k = ∑_{i,j} X i * Γ^k_{ij} * Y j`.
With the flat connection context (zero bracket and zero scalar derivation), all four
`CovariantDerivative` axioms reduce to linearity and ring arithmetic.
-/

/-- The flat connection context on `Fin n → ℝ`: zero Lie bracket and zero scalar derivation.
This represents constant vector fields on flat coordinate space. -/
def flatConnectionContext (n : ℕ) : ConnectionContext (Fin n → ℝ) ℝ where
  bracket _ _ := 0
  deriv _ _   := 0

/-- Lift a Christoffel symbol to an abstract `CovariantDerivative` via the contraction formula
`(nabla_X Y) k = ∑_{i,j} X i * Γ^k_{ij} * Y j`. -/
noncomputable def christoffelToCovariantDerivative
    (Gamma : ChristoffelSymbol n) :
    CovariantDerivative (Fin n → ℝ) ℝ (flatConnectionContext n) where
  toFun X Y k := ∑ i : Fin n, ∑ j : Fin n, X i * Gamma k i j * Y j
  add_left X Y Z := by
    funext k
    simp only [Pi.add_apply]
    simp_rw [add_mul, Finset.sum_add_distrib]
  smul_left f X Y := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc, ← Finset.mul_sum]
  add_right X Y Z := by
    funext k
    simp only [Pi.add_apply]
    simp_rw [mul_add, Finset.sum_add_distrib]
  leibniz X Y f := by
    funext k
    simp only [flatConnectionContext, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
               zero_smul, zero_add]
    -- Goal: ∑ i, ∑ j, X i * Γ k i j * (f * Y j) = f * ∑ i, ∑ j, X i * Γ k i j * Y j
    simp_rw [show ∀ (a b : ℝ), a * (f * b) = f * (a * b) from fun a b => by ring]
    simp_rw [← Finset.mul_sum]

/-- The lifted covariant derivative is torsion-free when the Christoffel symbol is
symmetric in its lower indices. -/
theorem christoffelToCovariantDerivative_torsionFree
    (Gamma : ChristoffelSymbol n)
    (hsymm : ∀ k i j, Gamma k i j = Gamma k j i) :
    TorsionFree (flatConnectionContext n) (christoffelToCovariantDerivative Gamma) := by
  intro X Y
  funext k
  simp only [christoffelToCovariantDerivative, CovariantDerivative.toFun,
             Pi.sub_apply, flatConnectionContext, Pi.zero_apply]
  -- ∑_{i,j} X i * Γ k i j * Y j  -  ∑_{i,j} Y i * Γ k i j * X j  =  0
  -- Reindex the second sum: swap i↔j and use Γ k j i = Γ k i j
  have : ∑ i : Fin n, ∑ j : Fin n, Y i * Gamma k i j * X j =
         ∑ i : Fin n, ∑ j : Fin n, X i * Gamma k i j * Y j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [hsymm k j i]; ring
  linarith [this]

end LeviCivita.Coordinate
