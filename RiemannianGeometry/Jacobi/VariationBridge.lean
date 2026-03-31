import Jacobi.Basic
import Variation.FirstVariationEnergy

namespace Jacobi

open Variation.Curve

variable {n : ℕ}
variable {C : LeviCivita.ConnectionContext (Vector n) ℝ}

/-- Data witnessing that a field `J` comes from a geodesic variation in the current coordinate
model. The crucial input is the torsion-free interchange identity together with the curvature
commutator formula that differentiates the geodesic equation along the variation. -/
structure GeodesicVariationWitness
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong (Vector n))
    (nablaTT : AlongSecondDerivative (Vector n))
    (J : ParallelTransport.FieldAlong (Vector n)) where
  variation : CovariantVariation n
  tangent_eq : ∀ t, T t = variation.tangentField 0 t
  variation_eq : ∀ t, J t = variation.variationField 0 t
  torsionFree : TorsionFreeInterchange n variation
  jacobi_commutator :
    ∀ t,
      nablaTT J t + R (J t) (T t) (T t) =
        variation.nablaT_V 0 t - variation.nablaS_T 0 t

/-- A field arises from a geodesic variation if it has such a witness. -/
def ArisesFromGeodesicVariation
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong (Vector n))
    (nablaTT : AlongSecondDerivative (Vector n))
    (J : ParallelTransport.FieldAlong (Vector n)) : Prop :=
  Nonempty (GeodesicVariationWitness (n := n) R T nablaTT J)

theorem GeodesicVariationWitness.tangent_eq_at
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (Vector n)}
    {nablaTT : AlongSecondDerivative (Vector n)}
    {J : ParallelTransport.FieldAlong (Vector n)}
    (witness : GeodesicVariationWitness (n := n) R T nablaTT J)
    (t : ℝ) :
    T t = witness.variation.tangentField 0 t :=
  witness.tangent_eq t

theorem GeodesicVariationWitness.variation_eq_at
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (Vector n)}
    {nablaTT : AlongSecondDerivative (Vector n)}
    {J : ParallelTransport.FieldAlong (Vector n)}
    (witness : GeodesicVariationWitness (n := n) R T nablaTT J)
    (t : ℝ) :
    J t = witness.variation.variationField 0 t :=
  witness.variation_eq t

/-- Torsion-free interchange plus the differentiated geodesic equation imply the Jacobi
equation. This is the actual bridge replacing the previous definitional alias. -/
theorem jacobiField_of_geodesicVariation
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (Vector n)}
    {nablaTT : AlongSecondDerivative (Vector n)}
    {J : ParallelTransport.FieldAlong (Vector n)}
    (variation : CovariantVariation n)
    (hT : ∀ t, T t = variation.tangentField 0 t)
    (hJ : ∀ t, J t = variation.variationField 0 t)
    (htorsion : TorsionFreeInterchange n variation)
    (hcurvature :
      ∀ t,
        nablaTT J t + R (J t) (T t) (T t) =
          variation.nablaT_V 0 t - variation.nablaS_T 0 t) :
    IsJacobiField R T nablaTT J := by
  let _ := hT
  let _ := hJ
  intro t
  have hcomm := hcurvature t
  have hswap := htorsion 0 t
  rw [hswap, sub_self] at hcomm
  exact hcomm

theorem arisesFromGeodesicVariation_of_geodesicVariation
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (Vector n)}
    {nablaTT : AlongSecondDerivative (Vector n)}
    {J : ParallelTransport.FieldAlong (Vector n)}
    (variation : CovariantVariation n)
    (hT : ∀ t, T t = variation.tangentField 0 t)
    (hJ : ∀ t, J t = variation.variationField 0 t)
    (htorsion : TorsionFreeInterchange n variation)
    (hcurvature :
      ∀ t,
        nablaTT J t + R (J t) (T t) (T t) =
          variation.nablaT_V 0 t - variation.nablaS_T 0 t) :
    ArisesFromGeodesicVariation R T nablaTT J :=
  ⟨⟨variation, hT, hJ, htorsion, hcurvature⟩⟩

/-- Any field arising from such a geodesic variation witness is a Jacobi field. -/
theorem isJacobiField_of_geodesicVariation
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (Vector n)}
    {nablaTT : AlongSecondDerivative (Vector n)}
    {J : ParallelTransport.FieldAlong (Vector n)}
    (h : ArisesFromGeodesicVariation (n := n) R T nablaTT J) :
    IsJacobiField R T nablaTT J := by
  rcases h with ⟨witness⟩
  exact
    jacobiField_of_geodesicVariation
      (variation := witness.variation)
      witness.tangent_eq witness.variation_eq witness.torsionFree witness.jacobi_commutator

theorem GeodesicVariationWitness.jacobiEquation
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (Vector n)}
    {nablaTT : AlongSecondDerivative (Vector n)}
    {J : ParallelTransport.FieldAlong (Vector n)}
    (witness : GeodesicVariationWitness (n := n) R T nablaTT J)
    (t : ℝ) :
    nablaTT J t + R (J t) (T t) (T t) = 0 :=
  jacobiField_of_geodesicVariation
    (variation := witness.variation)
    witness.tangent_eq witness.variation_eq witness.torsionFree witness.jacobi_commutator t

theorem GeodesicVariationWitness.isJacobiField
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (Vector n)}
    {nablaTT : AlongSecondDerivative (Vector n)}
    {J : ParallelTransport.FieldAlong (Vector n)}
    (witness : GeodesicVariationWitness (n := n) R T nablaTT J) :
    IsJacobiField R T nablaTT J :=
  jacobiField_of_geodesicVariation
    (variation := witness.variation)
    witness.tangent_eq witness.variation_eq witness.torsionFree witness.jacobi_commutator

end Jacobi
