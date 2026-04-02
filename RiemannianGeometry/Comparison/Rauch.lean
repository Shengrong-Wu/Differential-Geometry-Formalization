import Comparison.RauchReduction
import Curvature.SectionalRicci
import ParallelTransport.Frames
import Jacobi.VariationBridge
import Exponential.DifferentialAtZero
import Measure.ExpJacobian

/-! This public Rauch wrapper stays thin: it only re-exports the norm comparison consequences on
`modelPosDomain` from the repaired reduction interface. -/

namespace Comparison

universe u v

/-- Abstract sectional-curvature upper bound interface for Rauch comparison. -/
def SectionalUpperBound
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V] [Preorder S]
    (g : Curvature.Pairing V S) {C : LeviCivita.ConnectionContext V S}
    (R : Curvature.CurvatureTensor C) (k : S) : Prop :=
  ∀ X Y, Curvature.SectionalCurvature g R X Y ≤ k

/-- The norm of `dexp` applied to a fixed variation direction. -/
noncomputable def dexpNorm
    {n : ℕ} (exp : Exponential.Coordinate.LocalExponentialMap n)
    (v w : Exponential.Coordinate.Velocity n) : ℝ :=
  ‖(fderiv ℝ exp.toFun v) w‖

/-- A `dexp`-level comparison package exported from Rauch for later global applications. -/
def DexpNormComparison
    (k : ℝ)
    {n : ℕ} (exp : Exponential.Coordinate.LocalExponentialMap n)
    (radial direction : Exponential.Coordinate.Velocity n)
    (modelNorm : ℝ → ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → dexpNorm exp (t • radial) direction ≤ modelNorm t

theorem dexpNorm_zero_of_differentialAtZeroIsId
    {n : ℕ} {exp : Exponential.Coordinate.LocalExponentialMap n}
    (hdexp : Exponential.Coordinate.DifferentialAtZeroIsId exp)
    (w : Exponential.Coordinate.Velocity n) :
    dexpNorm exp 0 w = ‖w‖ := by
  rw [Exponential.Coordinate.DifferentialAtZeroIsId,
    Exponential.Coordinate.DifferentialAtZero] at hdexp
  rw [dexpNorm, hdexp.fderiv]
  simp

/-- Rauch comparison implies the corresponding norm comparison for `dexp` once the Jacobi-field
description of the differential is supplied. -/
theorem dexp_normComparison_of_rauch
    {k : ℝ}
    {n : ℕ} {exp : Exponential.Coordinate.LocalExponentialMap n}
    {data : JacobiNormData}
    {radial direction : Exponential.Coordinate.Velocity n}
    (hjacobi :
      data.jacobiNorm = fun t => dexpNorm exp (t • radial) direction)
    (hrauch : RauchNormComparison k data) :
    DexpNormComparison k exp radial direction data.modelNorm := by
  intro t ht
  simpa [DexpNormComparison, hjacobi, RauchNormComparison] using hrauch ht

/-- Direct `dexp` comparison from the owner-level scalar comparison theorem.
This is the active bridge-free export path; the older `RauchInputData` route remains only as a
compatibility wrapper. -/
theorem dexp_normComparison_of_scalarData
    {n : ℕ} {exp : Exponential.Coordinate.LocalExponentialMap n}
    {radial direction : Exponential.Coordinate.Velocity n}
    {data : ScalarJacobiComparisonData}
    (hjacobi :
      data.jacobiNorm = fun t => dexpNorm exp (t • radial) direction)
    (hscalar : HasScalarJacobiComparison data) :
    DexpNormComparison data.modelData.k exp radial direction data.modelNorm := by
  intro t ht
  simpa [DexpNormComparison, hjacobi, HasScalarJacobiComparison,
    ScalarJacobiComparisonData.modelNorm] using hscalar ht

/-- **LEGACY** — Compatibility wrapper routing through `RauchInputData`. Prefer
`dexp_normComparison_of_scalarData` on the active path. -/
theorem dexp_normComparison_of_scalarComparison
    {n : ℕ} {exp : Exponential.Coordinate.LocalExponentialMap n}
    {radial direction : Exponential.Coordinate.Velocity n}
    (input : RauchInputData)
    (hjacobi :
      input.data.jacobiNorm = fun t => dexpNorm exp (t • radial) direction) :
    DexpNormComparison input.modelData.k exp radial direction input.data.modelNorm := by
  simpa [RauchInputData.scalarComparisonData, ScalarJacobiComparisonData.modelNorm,
    canonicalModelJacobiData_model, canonicalModelJacobiData_k, input.matchesScalarModel] using
    (dexp_normComparison_of_scalarData
      (data := input.scalarComparisonData)
      (by
        simpa [RauchInputData.scalarComparisonData, ScalarJacobiComparisonData.modelNorm] using
          hjacobi)
      (hasScalarJacobiComparison_of_subsolution
        (by
          simp [RauchInputData.scalarComparisonData, ScalarJacobiComparisonData.modelNorm,
            canonicalModelJacobiData_model, canonicalModelJacobiData_k, input.matchesScalarModel])
        input.normODE.initialValue
        input.normODE.initialSlope
        input.normODE.hasFirstDeriv
        input.normODE.normSubsolution))

/-! ## Issue 4: Basiswise dexp Jacobian comparison -/

/-- **Basiswise `dexp` norm comparison.** Stores a `DexpNormComparison` for each standard basis
direction. This is the input needed for the Jacobian bound via Hadamard's inequality. -/
structure BasiswiseDexpNormComparison
    (k : ℝ) {n : ℕ} (exp : Exponential.Coordinate.LocalExponentialMap n)
    (radial : Exponential.Coordinate.Velocity n)
    (modelNorms : Fin n → ℝ → ℝ) : Prop where
  comparison : ∀ i : Fin n,
    DexpNormComparison k exp radial (Pi.basisFun ℝ (Fin n) i) (modelNorms i)

/-- From basiswise dexp norm comparison, derive a Jacobian bound with the honest
`√n` loss coming from converting the ambient sup norm to the Euclidean column norm
used by Hadamard's inequality. -/
theorem expJacobianFn_le_of_basiswise_dexpComparison
    {k : ℝ} {n : ℕ}
    {exp : Exponential.Coordinate.LocalExponentialMap n}
    {radial : Exponential.Coordinate.Velocity n}
    {modelNorms : Fin n → ℝ → ℝ}
    (hcomp : BasiswiseDexpNormComparison k exp radial modelNorms)
    {t : ℝ} (ht : t ∈ modelPosDomain k)
    (hv : t • radial ∈ exp.source) :
    Measure.Riemannian.expJacobianFn exp (t • radial) ≤
      ∏ i : Fin n, (Real.sqrt (Fintype.card (Fin n)) * modelNorms i t) := by
  refine Measure.Riemannian.expJacobianFn_le_of_basiswise_euclidean_bound
    exp (t • radial) hv
    (fun i => Real.sqrt (Fintype.card (Fin n)) * modelNorms i t) ?_ ?_
  · intro i
    have hi : 0 ≤ modelNorms i t := le_trans (norm_nonneg _) (hcomp.comparison i ht)
    positivity
  · intro i
    calc
      Measure.Riemannian.euclideanColumnNorm
          (Measure.Riemannian.coordinateExpDerivativeEndomorphism exp (t • radial)) i
          ≤ Real.sqrt (Fintype.card (Fin n)) *
              ‖(fderiv ℝ exp.toFun (t • radial)) (Pi.basisFun ℝ (Fin n) i)‖ := by
            simpa [Measure.Riemannian.euclideanColumnNorm,
              Measure.Riemannian.coordinateExpDerivativeEndomorphism] using
              piLp_norm_le_sqrt_card_mul_pi_norm
                ((fderiv ℝ exp.toFun (t • radial)) (Pi.basisFun ℝ (Fin n) i))
      _ ≤ Real.sqrt (Fintype.card (Fin n)) * modelNorms i t := by
            gcongr
            exact hcomp.comparison i ht

/-! ### Basiswise constructor from a family of scalar comparisons -/

/-- **Basiswise `dexp` norm comparison from a family of scalar comparisons.**
Given a `HasScalarJacobiComparison` for each standard basis direction and the identification of
each scalar comparison norm with the corresponding `dexpNorm`, this produces the full
`BasiswiseDexpNormComparison` package without routing through `RauchInputData`. -/
theorem basiswiseDexpNormComparison_of_scalarComparisonDataFamily
    {k : ℝ}
    {n : ℕ} {exp : Exponential.Coordinate.LocalExponentialMap n}
    {radial : Exponential.Coordinate.Velocity n}
    (inputs : Fin n → ScalarJacobiComparisonData)
    (hjacobi : ∀ i,
      (inputs i).jacobiNorm = fun t =>
        dexpNorm exp (t • radial) (Pi.basisFun ℝ (Fin n) i))
    (hk_eq : ∀ i, (inputs i).modelData.k = k)
    (hscalar : ∀ i, HasScalarJacobiComparison (inputs i)) :
    BasiswiseDexpNormComparison k exp radial
      (fun i => (inputs i).modelNorm) where
  comparison := fun i => by
    have hcomp := dexp_normComparison_of_scalarData
      (data := inputs i) (hjacobi i) (hscalar i)
    intro t ht
    have ht' : t ∈ modelPosDomain (inputs i).modelData.k := by
      rwa [hk_eq i]
    exact hcomp ht'

/-- **LEGACY** — Basiswise `dexp` norm comparison from a family of `RauchInputData`. Prefer
`basiswiseDexpNormComparison_of_scalarComparisonDataFamily` on the active path. -/
theorem basiswiseDexpNormComparison_of_scalarComparisonFamily
    {k : ℝ}
    {n : ℕ} {exp : Exponential.Coordinate.LocalExponentialMap n}
    {radial : Exponential.Coordinate.Velocity n}
    (inputs : Fin n → RauchInputData)
    (hjacobi : ∀ i,
      (inputs i).data.jacobiNorm = fun t =>
        dexpNorm exp (t • radial) (Pi.basisFun ℝ (Fin n) i))
    (hk_eq : ∀ i, (inputs i).modelData.k = k) :
    BasiswiseDexpNormComparison k exp radial
      (fun i => (inputs i).data.modelNorm) where
  comparison := fun i => by
    have hcomp := dexp_normComparison_of_scalarComparison (inputs i) (hjacobi i)
    intro t ht
    have hki : (inputs i).modelData.k = k := hk_eq i
    have ht' : t ∈ modelPosDomain (inputs i).modelData.k := by rwa [hki]
    exact hcomp ht'

end Comparison
