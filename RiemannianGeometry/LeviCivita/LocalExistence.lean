import LeviCivita.CoordinateChristoffel
import Mathlib.Tactic.Ring

namespace LeviCivita.Coordinate

variable {n : ℕ}

/-- The local coordinate Koszul/metric-contraction identity that characterizes the
coordinate Levi-Civita connection. -/
def SatisfiesMetricContraction
    (g : Metric.Coordinate.Tensor2 n) (dg : MetricDerivative n)
    (Gamma : ChristoffelSymbol n) : Prop :=
  ∀ m i j,
    ∑ k : Fin n, g m k * Gamma k i j =
      (1 / 2 : ℝ) * (dg i j m + dg j i m - dg m i j)

/-- The local coordinate Levi-Civita connection form attached to a metric. -/
noncomputable def localLeviCivitaConnection
    (gInv : Metric.Coordinate.InverseTensor2 n) (dg : MetricDerivative n) :
    Variation.Coordinate.Form1 n :=
  leviCivitaChristoffel gInv dg

@[simp] theorem localLeviCivitaConnection_eq_formula
    (gInv : Metric.Coordinate.InverseTensor2 n) (dg : MetricDerivative n) :
    localLeviCivitaConnection gInv dg = leviCivitaChristoffel gInv dg :=
  rfl

/-- In coordinates, the Levi-Civita formula is torsion free. -/
theorem localLeviCivitaConnection_torsionFree
    (gInv : Metric.Coordinate.InverseTensor2 n) (dg : MetricDerivative n)
    (hmetric : ∀ μ i j, dg μ i j = dg μ j i) :
    ∀ k i j,
      localLeviCivitaConnection gInv dg k i j =
        localLeviCivitaConnection gInv dg k j i := by
  simpa [localLeviCivitaConnection] using
    leviCivitaChristoffel_lower_symm gInv dg hmetric

/-- The local coordinate formula reuses the existing variation bridge without translation. -/
theorem localLeviCivitaConnection_eq_variation
    (gInv : Metric.Coordinate.InverseTensor2 n) (dg : MetricDerivative n) :
    localLeviCivitaConnection gInv dg = Variation.Coordinate.leviCivitaVariation gInv dg := by
  rfl

/-- The local coordinate formula satisfies the lowered-index metric-contraction identity. -/
theorem localLeviCivitaConnection_satisfiesMetricContraction
    (g : Metric.Coordinate.Tensor2 n)
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : MetricDerivative n)
    (hg : Metric.Coordinate.IsSymmetric g)
    (hgInv : Metric.Coordinate.IsSymmetric gInv)
    (hpair : Metric.Coordinate.IsInversePair g gInv) :
    SatisfiesMetricContraction g dg (localLeviCivitaConnection gInv dg) := by
  intro m i j
  simpa [SatisfiesMetricContraction, localLeviCivitaConnection] using
    metric_contract_leviCivitaChristoffel g gInv dg hg hgInv hpair m i j

/-- Any coordinate connection satisfying the same metric-contraction formula is uniquely
determined by the inverse metric. -/
theorem eq_of_satisfiesMetricContraction
    (g : Metric.Coordinate.Tensor2 n)
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : MetricDerivative n)
    (hpair : Metric.Coordinate.IsInversePair g gInv)
    {Gamma Gamma' : ChristoffelSymbol n}
    (hGamma : SatisfiesMetricContraction g dg Gamma)
    (hGamma' : SatisfiesMetricContraction g dg Gamma') :
    Gamma = Gamma' := by
  funext p i j
  have hrecover :
      ∀ Gamma : ChristoffelSymbol n,
        SatisfiesMetricContraction g dg Gamma →
          Gamma p i j =
            ∑ m : Fin n, gInv p m *
              ((1 / 2 : ℝ) * (dg i j m + dg j i m - dg m i j)) := by
    intro Gamma hΓ
    calc
      Gamma p i j
          = ∑ k : Fin n, (if p = k then 1 else 0) * Gamma k i j := by
              simp
      _ = ∑ k : Fin n, (∑ m : Fin n, gInv p m * g m k) * Gamma k i j := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Metric.Coordinate.inversePair_apply hpair p k]
      _ = ∑ m : Fin n, gInv p m * (∑ k : Fin n, g m k * Gamma k i j) := by
            calc
              ∑ k : Fin n, (∑ m : Fin n, gInv p m * g m k) * Gamma k i j
                  = ∑ k : Fin n, ∑ m : Fin n, (gInv p m * g m k) * Gamma k i j := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      rw [Finset.sum_mul]
              _ = ∑ m : Fin n, ∑ k : Fin n, (gInv p m * g m k) * Gamma k i j := by
                    rw [Finset.sum_comm]
              _ = ∑ m : Fin n, gInv p m * (∑ k : Fin n, g m k * Gamma k i j) := by
                    apply Finset.sum_congr rfl
                    intro m hm
                    symm
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k hk
                    ring
      _ = ∑ m : Fin n, gInv p m *
            ((1 / 2 : ℝ) * (dg i j m + dg j i m - dg m i j)) := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [hΓ m i j]
  rw [hrecover Gamma hGamma, hrecover Gamma' hGamma']

/-- Coordinate local existence and uniqueness of the Levi-Civita connection formula. -/
theorem existsUnique_localLeviCivitaConnection
    (g : Metric.Coordinate.Tensor2 n)
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : MetricDerivative n)
    (hg : Metric.Coordinate.IsSymmetric g)
    (hgInv : Metric.Coordinate.IsSymmetric gInv)
    (hpair : Metric.Coordinate.IsInversePair g gInv) :
    ∃! Gamma : ChristoffelSymbol n, SatisfiesMetricContraction g dg Gamma := by
  refine ⟨localLeviCivitaConnection gInv dg, ?_, ?_⟩
  · exact localLeviCivitaConnection_satisfiesMetricContraction g gInv dg hg hgInv hpair
  · intro Gamma hGamma
    exact eq_of_satisfiesMetricContraction g gInv dg hpair hGamma
      (localLeviCivitaConnection_satisfiesMetricContraction g gInv dg hg hgInv hpair)

/-!
## Abstract-level metric pairing from coordinate data

The coordinate bilinear form `Metric.Coordinate.bilinForm g` is an instance of the abstract
`MetricPairing` type. When the coordinate metric is positive definite, this pairing is
extensional (nondegenerate in the first slot) as required by the abstract uniqueness argument.
-/

/-- The coordinate bilinear form viewed as an abstract metric pairing. -/
def coordinateMetricPairing (g : Metric.Coordinate.Tensor2 n) :
    LeviCivita.MetricPairing (Fin n → ℝ) ℝ :=
  Metric.Coordinate.bilinForm g

/-- The coordinate metric pairing is symmetric when the metric coefficients are symmetric. -/
theorem coordinateMetricPairing_symm {g : Metric.Coordinate.Tensor2 n}
    (hg : Metric.Coordinate.IsSymmetric g) (U V : Fin n → ℝ) :
    coordinateMetricPairing g U V = coordinateMetricPairing g V U := by
  simpa [coordinateMetricPairing] using Metric.Coordinate.bilinForm_comm hg U V

/-- `coordinateMetricPairing g` is linear in the first argument under subtraction. -/
theorem coordinateMetricPairing_sub_left (g : Metric.Coordinate.Tensor2 n)
    (U V W : Fin n → ℝ) :
    coordinateMetricPairing g (U - V) W =
      coordinateMetricPairing g U W - coordinateMetricPairing g V W := by
  simp only [coordinateMetricPairing, Metric.Coordinate.bilinForm, Pi.sub_apply, sub_mul,
             Finset.sum_sub_distrib]

private theorem coordinateMetricPairing_basis_right (g : Metric.Coordinate.Tensor2 n)
    (v : Fin n → ℝ) (m : Fin n) :
    coordinateMetricPairing g v (Metric.Coordinate.basisVector m) =
      ∑ j : Fin n, v j * g j m := by
  simp only [coordinateMetricPairing, Metric.Coordinate.bilinForm,
    Metric.Coordinate.basisVector, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro j hj
  refine (Fintype.sum_eq_single m ?_).trans ?_
  · intro x hx
    simp [if_neg hx]
  · simp

/-- An inverse metric already implies the extensionality/nondegeneracy condition needed by the
abstract uniqueness argument. Symmetry is used to move the test vector into the second slot of the
coordinate bilinear form. -/
theorem coordinateMetricExtensional_of_inversePair
    (g : Metric.Coordinate.Tensor2 n)
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (hg : Metric.Coordinate.IsSymmetric g)
    (hpair : Metric.Coordinate.IsInversePair g gInv) :
    LeviCivita.MetricExtensional (coordinateMetricPairing g) := by
  intro U V h
  have hzero : ∀ W : Fin n → ℝ, coordinateMetricPairing g (U - V) W = 0 := by
    intro W
    rw [coordinateMetricPairing_sub_left]
    linarith [h W]
  apply sub_eq_zero.mp
  funext p
  calc
    (U - V) p
        = ∑ j : Fin n, (if p = j then 1 else 0) * (U - V) j := by
            simp
    _ = ∑ j : Fin n, (∑ m : Fin n, gInv p m * g m j) * (U - V) j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Metric.Coordinate.inversePair_apply hpair p j]
    _ = ∑ m : Fin n, gInv p m * (∑ j : Fin n, g m j * (U - V) j) := by
          calc
            ∑ j : Fin n, (∑ m : Fin n, gInv p m * g m j) * (U - V) j
                = ∑ j : Fin n, ∑ m : Fin n, (gInv p m * g m j) * (U - V) j := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [Finset.sum_mul]
            _ = ∑ m : Fin n, ∑ j : Fin n, (gInv p m * g m j) * (U - V) j := by
                  rw [Finset.sum_comm]
            _ = ∑ m : Fin n, gInv p m * (∑ j : Fin n, g m j * (U - V) j) := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  symm
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
    _ = ∑ m : Fin n, gInv p m *
          coordinateMetricPairing g (U - V) (Metric.Coordinate.basisVector m) := by
          apply Finset.sum_congr rfl
          intro m hm
          congr 1
          calc
            ∑ j : Fin n, g m j * (U - V) j
                = ∑ j : Fin n, (U - V) j * g j m := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [hg m j]
                    ring
            _ = coordinateMetricPairing g (U - V) (Metric.Coordinate.basisVector m) := by
                  rw [coordinateMetricPairing_basis_right]
    _ = ∑ m : Fin n, gInv p m * 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [hzero (Metric.Coordinate.basisVector m)]
    _ = 0 := by
          simp

/-- The coordinate metric pairing is extensional when the coordinate metric is positive
definite: equal inner products on all test vectors imply equal input vectors. -/
theorem coordinateMetricExtensional
    (g : Metric.Coordinate.Tensor2 n)
    (hg : Metric.Coordinate.IsPositiveDefinite g) :
    LeviCivita.MetricExtensional (coordinateMetricPairing g) := by
  intro U V h
  have hzero : ∀ W : Fin n → ℝ, coordinateMetricPairing g (U - V) W = 0 := by
    intro W
    rw [coordinateMetricPairing_sub_left]
    have := h W
    linarith
  exact sub_eq_zero.mp
    (Metric.Coordinate.IsPositiveDefinite.nondegenerate hg (U - V) (by
      intro W
      simpa [coordinateMetricPairing] using hzero W))

end LeviCivita.Coordinate
