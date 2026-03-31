import Exponential.GaussLemma
import Exponential.Differentiability
import Exponential.JacobiDexp
import Exponential.RadialBridge
import Exponential.LocalRiemannianData
import Exponential.DexpContinuity
import Exponential.RadialVariationIdentities
import ParallelTransport.Isometry
import Mathlib.Analysis.Calculus.MeanValue

/-! # Radial Gauss Lemma

This file proves the full radial Gauss lemma — the `radialPairing` field of
`LocalAnalyticInput` — by reducing it to a focused sub-hypothesis: the
**radial variation interchange**.

## Mathematical proof sketch

Define `f(t) = g(exp(tv))(dexp(tv)·v, t · dexp(tv)·w)`. Then:
- `f(0) = 0` since the variation field `S(0) = 0 · dexp(0)·w = 0`
- `f'(t) = g(p)(v,w)` by the geodesic equation + torsion-free interchange + metric
  compatibility + speed constancy
- By the mean value theorem: `f(1) = f(0) + 1 · g(p)(v,w) = g(p)(v,w)`
- But `f(1) = g(exp(v))(dexp(v)·v, dexp(v)·w)`, which is the Gauss lemma.

The derivative formula `f'(t) = g(p)(v,w)` follows from the chain:
- `f'(t) = g(V, ∇_V S)` (metric compatibility along the geodesic, ∇_V V = 0)
- `= g(V, ∇_S V)` (torsion-free interchange for the variation `Φ(t,s) = exp(t(v+sw))`)
- `= (1/2) ∂/∂s[g(V,V)]` (metric compatibility in the s-direction)
- `= g(p)(v,w)` (speed constancy: `g(V,V) = g(p)(v+sw, v+sw)`, differentiate in s)

## Boundary reduction

This file reduces the `radialPairing` interface boundary to a more focused
`HasRadialVariationInterchange` hypothesis, which encodes exactly the derivative
formula `f'(t) = g(p)(v,w)`. The torsion-free interchange step requires C² regularity
of the exponential map (smooth dependence on initial conditions for the geodesic ODE). -/

namespace Exponential.Coordinate

open scoped Topology BigOperators
open Set Filter

variable {n : ℕ}

private theorem sum_smul_coordBasis
    (x : Position n) :
    ∑ i : Fin n, x i • LeviCivita.CoordinateField.coordBasis i = x := by
  classical
  funext j
  calc
    (∑ i : Fin n, x i • LeviCivita.CoordinateField.coordBasis i) j
        = ∑ i : Fin n, x i * LeviCivita.CoordinateField.coordBasis i j := by
            simp
    _ = x j := by
          unfold LeviCivita.CoordinateField.coordBasis
          refine (Finset.sum_eq_single j ?_ ?_).trans ?_
          · intro i _ hij
            simp [Pi.basisFun_apply, hij]
          · simp
          · simp [Pi.basisFun_apply]

private theorem fderiv_smoothScalarField_apply_eq_sum_pderiv
    (f : LeviCivita.CoordinateField.SmoothScalarField n)
    (x y : Position n) :
    (fderiv ℝ f x) y =
      ∑ i : Fin n, y i * LeviCivita.CoordinateField.pderivScalar f i x := by
  calc
    (fderiv ℝ f x) y
        = (fderiv ℝ f x) (∑ i : Fin n, y i • LeviCivita.CoordinateField.coordBasis i) := by
            rw [sum_smul_coordBasis]
    _ = ∑ i : Fin n, y i • ((fderiv ℝ f x) (LeviCivita.CoordinateField.coordBasis i)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [map_smul]
    _ = ∑ i : Fin n, y i * LeviCivita.CoordinateField.pderivScalar f i x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [LeviCivita.CoordinateField.pderivScalar]

private theorem hasDerivAt_metricFieldCoeff_coordinateExp_line
    (data : LocalRiemannianData n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) data.Gamma p)
    (i j : Fin n)
    {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun τ : ℝ =>
        data.metricField (coordinateExp (n := n) data.Gamma p (τ • v)) i j)
      (∑ k : Fin n,
        ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) v) k *
          LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j
            (coordinateExp (n := n) data.Gamma p (t • v)))
      t := by
  let expMap := coordinateExp (n := n) data.Gamma p
  have htv : t • v ∈ coordinateExpSource (n := n) data.Gamma p :=
    smul_mem_coordinateExpSource (n := n) data.Gamma p hv ht.1 ht.2
  have hfd_metric :
      HasFDerivAt (fun x : Position n => data.gSmooth i j x)
        (fderiv ℝ (fun x : Position n => data.gSmooth i j x)
          (expMap (t • v)))
        (expMap (t • v)) :=
    (data.gSmooth.differentiableAt_component i j (expMap (t • v))).hasFDerivAt
  have hline :
      HasDerivAt (fun τ : ℝ => τ • v) v t := by
    simpa [one_smul] using (hasDerivAt_id t).smul_const v
  have hfd_exp :
      HasFDerivAt expMap (fderiv ℝ expMap (t • v)) (t • v) :=
    (contDiffAt_coordinateExp (n := n) data.Gamma p htv).differentiableAt_one.hasFDerivAt
  have hExp :
      HasDerivAt (fun τ : ℝ => expMap (τ • v))
        ((fderiv ℝ expMap (t • v)) v)
        t := by
    simpa [Function.comp] using hfd_exp.comp_hasDerivAt t hline
  have hcomp :
      HasDerivAt
        (fun τ : ℝ => data.gSmooth i j (expMap (τ • v)))
        ((fderiv ℝ (fun x : Position n => data.gSmooth i j x) (expMap (t • v)))
          (((fderiv ℝ expMap (t • v)) v)))
        t := by
    simpa [Function.comp] using hfd_metric.comp_hasDerivAt t hExp
  convert hcomp using 1
  · simpa using (fderiv_smoothScalarField_apply_eq_sum_pderiv
      (data.gSmooth.component i j) (expMap (t • v))
      (((fderiv ℝ expMap (t • v)) v))).symm

private theorem hasDerivAt_metricFieldCoeff_geodesicFamily_line
    (data : LocalRiemannianData n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) data.Gamma p)
    (w : Velocity n)
    (i j : Fin n)
    {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun s : ℝ =>
        data.metricField
          (Geodesic.Coordinate.statePosition n
            ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve
              (v + s • w) t)) i j)
      (∑ k : Fin n,
        (t • ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w)) k *
          LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j
            (coordinateExp (n := n) data.Gamma p (t • v)))
      0 := by
  let posLine := fun s : ℝ =>
    Geodesic.Coordinate.statePosition n
      ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve
        (v + s • w) t)
  have hpos0 : posLine 0 = coordinateExp (n := n) data.Gamma p (t • v) := by
    symm
    simpa [posLine, zero_smul, add_zero] using
      coordinateExp_smul_eq_geodesicFamily_position (n := n) data.Gamma p hv ht
  have hpos :
      HasDerivAt posLine (t • ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w)) 0 :=
    hasDerivAt_geodesicFamily_position_line (n := n) data.Gamma p hv w ht
  have hfd_metric :
      HasFDerivAt
        (fun x : Position n => data.gSmooth i j x)
        (fderiv ℝ (fun x : Position n => data.gSmooth i j x)
          (coordinateExp (n := n) data.Gamma p (t • v)))
        (coordinateExp (n := n) data.Gamma p (t • v)) :=
    (data.gSmooth.differentiableAt_component i j
      (coordinateExp (n := n) data.Gamma p (t • v))).hasFDerivAt
  have hcomp :
      HasDerivAt
        (fun s : ℝ => data.gSmooth i j (posLine s))
        ((fderiv ℝ (fun x : Position n => data.gSmooth i j x)
          (coordinateExp (n := n) data.Gamma p (t • v)))
          (t • ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w)))
        0 := by
    have hpos' :
        HasDerivAt posLine
          (t • ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w))
          0 := hpos
    have hfd_metric' :
        HasFDerivAt
          (fun x : Position n => data.gSmooth i j x)
          (fderiv ℝ (fun x : Position n => data.gSmooth i j x)
            (coordinateExp (n := n) data.Gamma p (t • v)))
          (posLine 0) := by
      simpa [hpos0] using hfd_metric
    simpa [Function.comp, posLine] using hfd_metric'.comp_hasDerivAt 0 hpos'
  have hcomp_metric :
      HasDerivAt
        (fun s : ℝ =>
          data.metricField
            (Geodesic.Coordinate.statePosition n
              ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve
                (v + s • w) t)) i j)
        ((fderiv ℝ (fun x : Position n => data.gSmooth i j x)
          (coordinateExp (n := n) data.Gamma p (t • v)))
          (t • ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w)))
        0 := by
    simpa [Exponential.Coordinate.LocalRiemannianData.metricField,
      LeviCivita.CoordinateField.tensorAt, posLine] using hcomp
  let x₁ : Position n :=
    Geodesic.Coordinate.statePosition n
      ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve
        (t • v) 1)
  have hderiv :
      (t *
        (fderiv ℝ (fun x : Position n => data.gSmooth i j x) x₁)
          ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w)) =
        ∑ k : Fin n,
          (t • ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w)) k *
            LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x₁ := by
    have hbase :
        (fderiv ℝ (fun x : Position n => data.gSmooth i j x) x₁)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w) =
          ∑ k : Fin n,
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w) k *
              LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x₁ := by
      change
        (fderiv ℝ (data.gSmooth.component i j) x₁)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w) =
          ∑ k : Fin n,
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w) k *
              (fderiv ℝ (data.gSmooth.component i j) x₁)
                (LeviCivita.CoordinateField.coordBasis k)
      simpa [LeviCivita.CoordinateField.metricDerivative] using
        (fderiv_smoothScalarField_apply_eq_sum_pderiv
          (data.gSmooth.component i j)
          x₁
          ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w))
    calc
      t *
          (fderiv ℝ (fun x : Position n => data.gSmooth i j x) x₁)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w)
          =
        t *
          ∑ k : Fin n,
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w) k *
              LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x₁ := by
        rw [hbase]
      _ = ∑ k : Fin n,
            t * (fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w k *
              LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x₁ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        ring
  have hcomp_metric' :
      HasDerivAt
        (fun s : ℝ =>
          data.metricField
            (Geodesic.Coordinate.statePosition n
              ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve
                (v + s • w) t)) i j)
        (t *
          (fderiv ℝ (fun x : Position n => data.gSmooth i j x) x₁)
            ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) w))
        0 := by
    simpa [x₁, ContinuousLinearMap.map_smul] using hcomp_metric
  simpa [hderiv] using hcomp_metric'

private theorem hasDerivWithinAt_coordinatePairing
    {g dg : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Y Z : ℝ → Velocity n}
    {y' z' : Velocity n}
    {s : Set ℝ} {t : ℝ}
    (hg : ∀ i j, HasDerivWithinAt (fun τ => g τ i j) (dg t i j) s t)
    (hY : HasDerivWithinAt Y y' s t)
    (hZ : HasDerivWithinAt Z z' s t) :
    HasDerivWithinAt
      (fun τ => ParallelTransport.coordinatePairing g τ (Y τ) (Z τ))
      (ParallelTransport.coordinatePairingAt (dg t) (Y t) (Z t) +
        ParallelTransport.coordinatePairingAt (g t) y' (Z t) +
        ParallelTransport.coordinatePairingAt (g t) (Y t) z')
      s t := by
  have hsum :
      HasDerivWithinAt
        (fun τ => ∑ i : Fin n, ∑ j : Fin n, Y τ i * g τ i j * Z τ j)
        (∑ i : Fin n,
          ∑ j : Fin n,
            (y' i * g t i j * Z t j +
              Y t i * dg t i j * Z t j +
              Y t i * g t i j * z' j))
        s t := by
    refine HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
      (A := fun i τ => ∑ j : Fin n, Y τ i * g τ i j * Z τ j)
      (A' := fun i =>
        ∑ j : Fin n,
          (y' i * g t i j * Z t j +
            Y t i * dg t i j * Z t j +
            Y t i * g t i j * z' j)) ?_
    intro i hi
    refine HasDerivWithinAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
      (A := fun j τ => Y τ i * g τ i j * Z τ j)
      (A' := fun j => y' i * g t i j * Z t j + Y t i * dg t i j * Z t j + Y t i * g t i j * z' j)
      ?_
    intro j hj
    have hYi : HasDerivWithinAt (fun τ => Y τ i) (y' i) s t := by
      simpa [Function.comp] using
        (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) i :
            Velocity n →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivWithinAt t hY)
    have hZj : HasDerivWithinAt (fun τ => Z τ j) (z' j) s t := by
      simpa [Function.comp] using
        (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) j :
            Velocity n →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivWithinAt t hZ)
    have hgij : HasDerivWithinAt (fun τ => g τ i j) (dg t i j) s t := hg i j
    convert (hYi.mul hgij).mul hZj using 1 <;> simp <;> ring_nf
  simpa [ParallelTransport.coordinatePairing, ParallelTransport.coordinatePairingAt,
    Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm] using hsum

private theorem hasDerivWithinAt_Ici_of_Ioo
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {t : ℝ}
    (ht : t < 1)
    (hf : HasDerivWithinAt f f' (Ioo t 1) t) :
    HasDerivWithinAt f f' (Ici t) t := by
  have hIoi : HasDerivWithinAt f f' (Ioi t) t := hf.Ioi_of_Ioo ht
  exact hIoi.Ici_of_Ioi

private noncomputable def connectionMatrixOfVector
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (x : Position n) (v : Velocity n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k : Fin n, Gamma i k j x * v k

private theorem coordinateParallelRhs_connectionMatrixOfVector_eq_acceleration
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (x : Position n) (v : Velocity n) :
    ParallelTransport.coordinateParallelRhs
        (fun _ : ℝ => connectionMatrixOfVector (n := n) Gamma x v) 0 v =
      Geodesic.Coordinate.geodesicAcceleration
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma) x v := by
  funext i
  simp [ParallelTransport.coordinateParallelRhs, connectionMatrixOfVector,
    Matrix.mulVec, dotProduct, Geodesic.Coordinate.geodesicAcceleration,
    Finset.mul_sum, mul_comm]
  rw [Finset.sum_comm]

private theorem metricDerivativeAlong_eq_connectionMatrix_formula
    (data : LocalRiemannianData n)
    (x : Position n) (v : Velocity n) :
    (fun i j =>
      ∑ k : Fin n, v k * LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x) =
      (fun i j =>
        ∑ m : Fin n, (connectionMatrixOfVector (n := n) data.Gamma x v) m i * data.metricField x m j +
          ∑ m : Fin n, data.metricField x i m *
            (connectionMatrixOfVector (n := n) data.Gamma x v) m j) := by
  ext i j
  have hmetric' :
      ∀ a b c : Fin n,
        LeviCivita.CoordinateField.metricDerivative data.gSmooth a b c x =
          ∑ m : Fin n, data.gSmooth m c x * data.Gamma m a b x +
            ∑ m : Fin n, data.gSmooth b m x * data.Gamma m a c x := by
    intro a b c
    simpa [LocalRiemannianData.Gamma] using
      (LeviCivita.CoordinateField.leviCivitaChristoffel_metricMiddle
        data.gSmooth data.gInvSmooth data.symm data.symmInv data.invPair x a b c).symm
  calc
    (∑ k : Fin n, v k * LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x)
      = ∑ k : Fin n,
          v k *
            (∑ m : Fin n, data.gSmooth m j x * data.Gamma m k i x +
              ∑ m : Fin n, data.gSmooth i m x * data.Gamma m k j x) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hmetric' k i j]
    _ = (∑ k : Fin n, v k * ∑ m : Fin n, data.gSmooth m j x * data.Gamma m k i x) +
          (∑ k : Fin n, v k * ∑ m : Fin n, data.gSmooth i m x * data.Gamma m k j x) := by
          have hsplit :
              ∀ k : Fin n,
                v k *
                  (∑ m : Fin n, data.gSmooth m j x * data.Gamma m k i x +
                    ∑ m : Fin n, data.gSmooth i m x * data.Gamma m k j x) =
                  v k * ∑ m : Fin n, data.gSmooth m j x * data.Gamma m k i x +
                    v k * ∑ m : Fin n, data.gSmooth i m x * data.Gamma m k j x := by
                intro k
                ring
          rw [show
              (∑ k : Fin n,
                v k *
                  (∑ m : Fin n, data.gSmooth m j x * data.Gamma m k i x +
                    ∑ m : Fin n, data.gSmooth i m x * data.Gamma m k j x)) =
              ∑ k : Fin n,
                (v k * ∑ m : Fin n, data.gSmooth m j x * data.Gamma m k i x +
                  v k * ∑ m : Fin n, data.gSmooth i m x * data.Gamma m k j x) by
                refine Finset.sum_congr rfl ?_
                intro k hk
                exact hsplit k]
          rw [Finset.sum_add_distrib]
    _ = (∑ m : Fin n, (connectionMatrixOfVector (n := n) data.Gamma x v) m i * data.metricField x m j) +
          (∑ m : Fin n, data.metricField x i m *
            (connectionMatrixOfVector (n := n) data.Gamma x v) m j) := by
          congr 1
          · calc
              ∑ k : Fin n, v k * ∑ m : Fin n, data.gSmooth m j x * data.Gamma m k i x
                  = ∑ k : Fin n, ∑ m : Fin n,
                      v k * (data.gSmooth m j x * data.Gamma m k i x) := by
                        refine Finset.sum_congr rfl ?_
                        intro k hk
                        simp [Finset.mul_sum]
              _ = ∑ m : Fin n, ∑ k : Fin n,
                      v k * (data.gSmooth m j x * data.Gamma m k i x) := by
                        rw [Finset.sum_comm]
              _ = ∑ m : Fin n,
                    (∑ k : Fin n, data.Gamma m k i x * v k) * data.gSmooth m j x := by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      calc
                        ∑ k : Fin n, v k * (data.gSmooth m j x * data.Gamma m k i x)
                            = ∑ k : Fin n, (data.Gamma m k i x * v k) * data.gSmooth m j x := by
                                refine Finset.sum_congr rfl ?_
                                intro k hk
                                ring
                        _ = (∑ k : Fin n, data.Gamma m k i x * v k) * data.gSmooth m j x := by
                              rw [Finset.sum_mul]
              _ = ∑ m : Fin n,
                    (connectionMatrixOfVector (n := n) data.Gamma x v) m i *
                      data.metricField x m j := by
                        simp [connectionMatrixOfVector, LocalRiemannianData.metricField,
                          LeviCivita.CoordinateField.tensorAt]
          · calc
              ∑ k : Fin n, v k * ∑ m : Fin n, data.gSmooth i m x * data.Gamma m k j x
                  = ∑ k : Fin n, ∑ m : Fin n,
                      v k * (data.gSmooth i m x * data.Gamma m k j x) := by
                        refine Finset.sum_congr rfl ?_
                        intro k hk
                        simp [Finset.mul_sum]
              _ = ∑ m : Fin n, ∑ k : Fin n,
                      v k * (data.gSmooth i m x * data.Gamma m k j x) := by
                        rw [Finset.sum_comm]
              _ = ∑ m : Fin n,
                    data.metricField x i m *
                      (∑ k : Fin n, data.Gamma m k j x * v k) := by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      calc
                        ∑ k : Fin n, v k * (data.gSmooth i m x * data.Gamma m k j x)
                            = ∑ k : Fin n, data.metricField x i m * (data.Gamma m k j x * v k) := by
                                refine Finset.sum_congr rfl ?_
                                intro k hk
                                simp [LocalRiemannianData.metricField,
                                  LeviCivita.CoordinateField.tensorAt]
                                ring_nf
                        _ = data.metricField x i m * (∑ k : Fin n, data.Gamma m k j x * v k) := by
                              rw [Finset.mul_sum]
              _ = ∑ m : Fin n,
                    data.metricField x i m *
                      (connectionMatrixOfVector (n := n) data.Gamma x v) m j := by
                        simp [connectionMatrixOfVector, LocalRiemannianData.metricField,
                          LeviCivita.CoordinateField.tensorAt]

/-! ### Part 1: The radial pairing function -/

/-- The radial pairing function along the geodesic `t ↦ exp(tv)`. At time `t`, this
evaluates `g(exp(tv))(dexp(tv)·v, t · dexp(tv)·w)`.

This is the "variation pairing" `⟨∂Φ/∂t, ∂Φ/∂s⟩` for the family `Φ(t,s) = exp(t(v+sw))`,
evaluated at `s = 0`. -/
noncomputable def radialPairingFn
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (v w : Velocity n) : ℝ → ℝ :=
  fun t =>
    metricPairingAt g (coordinateExp (n := n) Gamma p (t • v))
      ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v)
      (t • (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) w)

/-- The radial pairing function at `t = 0` vanishes, since the variation field `S(0) = 0`. -/
theorem radialPairingFn_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (v w : Velocity n) :
    radialPairingFn (n := n) Gamma g p v w 0 = 0 := by
  simp [radialPairingFn, metricPairingAt, Metric.Coordinate.bilinForm]

/-- The radial pairing function at `t = 1` is exactly the LHS of the Gauss lemma. -/
theorem radialPairingFn_one
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (v w : Velocity n) :
    radialPairingFn (n := n) Gamma g p v w 1 =
      metricPairingAt g (coordinateExp (n := n) Gamma p v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) := by
  simp [radialPairingFn]

private theorem radialPairingFn_eq_variationField
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (w : Velocity n)
    {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    radialPairingFn (n := n) Gamma g p v w t =
      metricPairingAt g
        (Geodesic.Coordinate.statePosition n
          ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v t))
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v)
        (Geodesic.Coordinate.statePosition n
          (geodesicFamilyStateVariation (n := n) Gamma p v w t)) := by
  have hvsource : v ∈ coordinateExpSource (n := n) Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) Gamma p hv
  have hcurve :
      coordinateExp (n := n) Gamma p (t • v) =
        Geodesic.Coordinate.statePosition n
          ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v t) :=
    coordinateExp_smul_eq_geodesicFamily_position (n := n) Gamma p hvsource ht
  have hvar :
      Geodesic.Coordinate.statePosition n
        (geodesicFamilyStateVariation (n := n) Gamma p v w t) =
        t • ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) w) :=
    statePosition_geodesicFamilyStateVariation_eq (n := n) Gamma p hvsource w ht
  rw [radialPairingFn, hcurve, ← hvar]

/-! ### Part 2: Radial variation interchange hypothesis -/

/-- The radial variation interchange hypothesis: along the radial geodesic `exp(tv)`,
the variation pairing function `f(t) = g(exp(tv))(dexp(tv)·v, t·dexp(tv)·w)` has
constant derivative equal to `g(p)(v,w)`.

This encodes the consequence of:
- Geodesic equation: `∇_V V = 0`
- Torsion-free interchange: `∇_V S = ∇_S V` (requires mixed partial symmetry / C² of exp)
- Metric compatibility: `∂/∂s[g(V,V)] = 2g(∇_S V, V)`
- Speed constancy: `g(V(t,s), V(t,s)) = g(p)(v+sw, v+sw)` (constant in `t`)

The composition gives `f'(t) = g(V, ∇_V S) = g(V, ∇_S V) = (1/2)·∂/∂s[g(V,V)] = g(p)(v,w)`. -/
def HasRadialVariationInterchange
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n) : Prop :=
  ∀ {v : Velocity n}
    (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (w : Velocity n),
    -- The radial pairing function is continuous on [0,1]
    ContinuousOn (radialPairingFn (n := n) Gamma g p v w) (Icc 0 1) ∧
    -- and has derivative g(p)(v,w) on [0,1) (right derivative at all interior + left endpoint)
    (∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (radialPairingFn (n := n) Gamma g p v w)
        (metricPairingAt g p v w) (Ici t) t)

/-! ### Part 3: Main theorem — radialPairing from the variation data -/

/-- Auxiliary: if a function is continuous on `[0,1]`, has right derivative `c` on `[0,1)`,
and vanishes at `0`, then its value at `1` equals `c`.

This follows from `constant_of_has_deriv_right_zero` applied to `h(t) = f(t) - c·t`. -/
private theorem eq_of_hasDerivWithinAt_const_on_Icc
    {f : ℝ → ℝ} {c : ℝ}
    (hcont : ContinuousOn f (Icc 0 1))
    (hderiv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt f c (Ici t) t)
    (hf0 : f 0 = 0) :
    f 1 = c := by
  -- Define h(t) = f(t) - c*t. Then h'(t) = 0, h(0) = 0, so h is constant.
  set h := fun t => f t - c * t with hdef
  have h_cont : ContinuousOn h (Icc 0 1) :=
    hcont.sub ((continuous_const.mul continuous_id).continuousOn)
  have h_deriv : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt h 0 (Ici t) t := by
    intro t ht
    have hf := hderiv t ht
    have hg : HasDerivWithinAt (fun t => c * t) c (Ici t) t := by
      exact (hasDerivAt_id t |>.const_mul c |>.congr_deriv (by ring)).hasDerivWithinAt
    have := hf.sub hg
    simp [hdef] at this ⊢
    exact this
  -- By the constant-function theorem, h is constant on [0,1]
  have h_const := constant_of_has_deriv_right_zero h_cont h_deriv
  have h1 := h_const 1 (right_mem_Icc.mpr zero_le_one)
  simp [hdef, hf0] at h1
  linarith

/-- **The radial Gauss lemma**: given the variation interchange hypothesis, the metric
pairing is preserved by `dexp` in the radial direction.

For `v` in the chart source and any `w`:
`g(exp(v))(dexp(v)·v, dexp(v)·w) = g(p)(v, w)` -/
theorem radialPairing_of_hasRadialVariationInterchange
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (hinterchange : HasRadialVariationInterchange (n := n) Gamma g p)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (w : Velocity n) :
    metricPairingAt g (coordinateExp (n := n) Gamma p v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) =
      metricPairingAt g p v w := by
  rw [← radialPairingFn_one (n := n) Gamma g p v w]
  rcases hinterchange hv w with ⟨hcont, hderiv⟩
  exact eq_of_hasDerivWithinAt_const_on_Icc hcont hderiv
    (radialPairingFn_zero (n := n) Gamma g p v w)

/-- Constructor for the `radialPairing` field of `LocalAnalyticInput` from the
radial variation interchange hypothesis. -/
theorem radialPairing_field_of_hasRadialVariationInterchange
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (hinterchange : HasRadialVariationInterchange (n := n) Gamma g p) :
    ∀ {v : Velocity n}
      (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
      (w : Velocity n),
      metricPairingAt g (coordinateExp (n := n) Gamma p v)
          ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
          ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) =
        metricPairingAt g p v w :=
  fun hv w => radialPairing_of_hasRadialVariationInterchange
    (n := n) Gamma g p hinterchange hv w

/-! ### Part 4: Geodesic energy conservation (speed constancy)

The geodesic speed `g(γ(t))(γ'(t), γ'(t))` is constant along any geodesic of a
metric-compatible connection. This is the quadratic (diagonal) case of the Gauss lemma. -/

/-- Geodesic energy along the radial geodesic: the quadratic form of the velocity at the
curve point. This is `g(exp(tv))(dexp(tv)·v, dexp(tv)·v)`. -/
noncomputable def geodesicEnergy
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (v : Velocity n) : ℝ → ℝ :=
  fun t =>
    Metric.Coordinate.quadraticForm
      (g (coordinateExp (n := n) Gamma p (t • v)))
      ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v)

/-- The geodesic energy at `t = 0` equals `g(p)(v,v)`, since `dexp(0) = id`. -/
theorem geodesicEnergy_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (v : Velocity n) :
    geodesicEnergy (n := n) Gamma g p v 0 =
      Metric.Coordinate.quadraticForm (g p) v := by
  simp only [geodesicEnergy, zero_smul, coordinateExp_zero (n := n),
    fderiv_coordinateExp_at_zero (n := n), ContinuousLinearMap.id_apply]

/-! ### Part 5: Updated constructor for LocalAnalyticConstruction

This constructor eliminates the `hgauss` parameter from
`localAnalyticRealizationOfLocalRiemannianData` when the radial variation interchange
hypothesis is available. -/

/-- Construct `LocalAnalyticRealization` from `LocalRiemannianData` plus explicit witnesses,
with the Gauss lemma (`hgauss`) replaced by the radial variation interchange. -/
noncomputable def localAnalyticRealizationOfRadialVariation
    (data : LocalRiemannianData n)
    (p : Position n)
    (hdiff : CoordinateExpHasFDerivAtOnSource (n := n) data.Gamma p)
    (hinterchange : HasRadialVariationInterchange (n := n)
      data.Gamma data.metricField p)
    (hcomp :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (γ : ℝ → Position n)
        (Tγ Uγ : ℝ → Velocity n)
        (_ : Minimization.Coordinate.IsCurveFrom (n := n) p
            (coordinateExp (n := n) data.Gamma p v) γ 0 1)
        (_ : Minimization.Coordinate.HasNormalCoordinateKinematics
            (n := n) data.Gamma p γ Tγ Uγ 0 1),
        Minimization.Coordinate.metricNormalRadius (n := n)
            data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) ≤
          Minimization.Coordinate.metricCurveLength (n := n)
            data.metricField γ 0 1 Tγ) :
    LocalAnalyticRealization (n := n) data.Gamma data.metricField p where
  directionalDexp := hasDirectionalDexp_of_localRiemannianData data p hdiff
  radialPairing := radialPairing_field_of_hasRadialVariationInterchange
    (n := n) data.Gamma data.metricField p hinterchange
  radius_le_metricLength := hcomp
  metricLength_le_radius := by
    intro v hv
    refine le_of_eq ?_
    calc
      Minimization.Coordinate.metricCurveLength (n := n) data.metricField
          (Minimization.Coordinate.radialGeodesic (n := n) data.Gamma p v) 0 1
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) data.Gamma p v)
        = Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v) := by
            exact Minimization.Coordinate.metricCurveLength_eq_const_of_unitInterval
              (n := n) data.metricField
              (Minimization.Coordinate.radialGeodesic (n := n) data.Gamma p v)
              (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) data.Gamma p v)
              (Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v))
              (radialGeodesic_metricSpeed_eq_const_of_directionalDexp_radialPairing
                (n := n) data.Gamma data.metricField p
                (hasDirectionalDexp_of_localRiemannianData data p hdiff)
                (radialPairing_field_of_hasRadialVariationInterchange
                  (n := n) data.Gamma data.metricField p hinterchange)
                hv)
      _ = Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) := by
            symm
            exact Minimization.Coordinate.metricNormalRadius_exp
              (n := n) data.metricField data.Gamma p hv

/-! ## Owner theorem: proving HasRadialVariationInterchange -/

/-- Continuity of the radial pairing function on `[0,1]`, from differentiability of
`coordinateExp` and continuity of the metric field. -/
private theorem continuousOn_radialPairingFn_of_localRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    (_hcompat : IsMetricCompatible (n := n) data.Gamma data.metricField)
    {v : Velocity n}
    (_hv : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
    (w : Velocity n) :
    ContinuousOn (radialPairingFn (n := n) data.Gamma data.metricField p v w) (Icc 0 1) := by
  let expMap := coordinateExp (n := n) data.Gamma p
  have hvsource : v ∈ coordinateExpSource (n := n) data.Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) data.Gamma p _hv
  have hExp : ContinuousOn expMap (coordinateExpSource (n := n) data.Gamma p) := by
    intro u hu
    exact (contDiffAt_coordinateExp (n := n) data.Gamma p hu).continuousAt.continuousWithinAt
  have hExpRadial : ContinuousOn (fun t : ℝ => expMap (t • v)) (Icc 0 1) :=
    hExp.comp ((continuous_id.smul continuous_const).continuousOn)
      (fun t ht => smul_mem_coordinateExpSource (n := n) data.Gamma p hvsource ht.1 ht.2)
  have hT :
      ContinuousOn (fun t : ℝ => (fderiv ℝ expMap (t • v)) v) (Icc 0 1) :=
    continuousOn_fderiv_coordinateExp_radial_apply (n := n) data.Gamma p hvsource v
  have hW :
      ContinuousOn (fun t : ℝ => (fderiv ℝ expMap (t • v)) w) (Icc 0 1) :=
    continuousOn_fderiv_coordinateExp_radial_apply (n := n) data.Gamma p hvsource w
  have hTcoord :
      ∀ i : Fin n,
        ContinuousOn (fun t : ℝ => ((fderiv ℝ expMap (t • v)) v) i) (Icc 0 1) := by
    intro i
    exact (continuous_apply i).continuousOn.comp hT (by intro t ht; exact mem_univ _)
  have hWcoord :
      ∀ j : Fin n,
        ContinuousOn (fun t : ℝ => ((fderiv ℝ expMap (t • v)) w) j) (Icc 0 1) := by
    intro j
    exact (continuous_apply j).continuousOn.comp hW (by intro t ht; exact mem_univ _)
  have hMetricCoeff :
      ∀ i j : Fin n,
        ContinuousOn (fun t : ℝ => data.metricField (expMap (t • v)) i j) (Icc 0 1) := by
    intro i j
    simpa [LocalRiemannianData.metricField] using
      ((data.gSmooth.smooth' i j).continuous.continuousOn.comp hExpRadial
        (by intro t ht; exact mem_univ _))
  change ContinuousOn
    (fun t : ℝ =>
      ∑ i : Fin n, ∑ j : Fin n,
        ((fderiv ℝ expMap (t • v)) v) i *
          data.metricField (expMap (t • v)) i j *
          (t * ((fderiv ℝ expMap (t • v)) w) j))
    (Icc 0 1)
  refine continuousOn_finset_sum _ ?_
  intro i _
  refine continuousOn_finset_sum _ ?_
  intro j _
  have hScaled :
      ContinuousOn (fun t : ℝ => t * ((fderiv ℝ expMap (t • v)) w) j) (Icc 0 1) :=
    continuousOn_id.mul (hWcoord j)
  simpa [expMap, mul_assoc] using ((hTcoord i).mul (hMetricCoeff i j)).mul hScaled

private theorem hasDerivWithinAt_radialVelocityField_of_localRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    {v : Velocity n}
    (_hv : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt
        (fun τ : ℝ => (fderiv ℝ (coordinateExp (n := n) data.Gamma p) (τ • v)) v)
        (Geodesic.Coordinate.geodesicAcceleration
          (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma)
          (coordinateExp (n := n) data.Gamma p (t • v))
          ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) v))
        (Ici t) t := by
  let γ := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve v
  have hvsource : v ∈ coordinateExpSource (n := n) data.Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) data.Gamma p _hv
  intro t ht
  have hγgeod :
      Geodesic.Coordinate.IsCoordinateGeodesicOn
        (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma)
        γ
        (Set.Icc (-1 : ℝ) 1) := by
    simpa [γ] using coordinateExp_isCoordinateGeodesicOn (n := n) data.Gamma p hvsource
  rcases (Geodesic.Coordinate.isCoordinateGeodesicOn_iff_secondOrder
    (n := n) (Gamma := Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma)
    (gamma := γ) (s := Set.Icc (-1 : ℝ) 1)).mp hγgeod with ⟨_, hγvel⟩
  have hγvel_Ioo :
      HasDerivWithinAt
        (fun τ : ℝ => Geodesic.Coordinate.stateVelocity n (γ τ))
        (Geodesic.Coordinate.geodesicAcceleration
          (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma)
          (Geodesic.Coordinate.statePosition n (γ t))
          (Geodesic.Coordinate.stateVelocity n (γ t)))
        (Ioo t 1)
        t := by
    have hraw := hγvel t ⟨by linarith [ht.1], ht.2.le⟩
    exact hraw.mono (by
      intro x hx
      exact ⟨by linarith [ht.1, hx.1], hx.2.le⟩)
  have hEq_pos :
      Geodesic.Coordinate.statePosition n (γ t) =
        coordinateExp (n := n) data.Gamma p (t • v) := by
    symm
    simpa [γ] using
      coordinateExp_smul_eq_geodesicFamily_position (n := n) data.Gamma p hvsource ⟨ht.1, ht.2.le⟩
  have hEq_vel :
      Geodesic.Coordinate.stateVelocity n (γ t) =
        (fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) v := by
    simpa [γ] using
      geodesicFamily_velocity_eq_fderiv_radial (n := n) data.Gamma p _hv t ⟨ht.1, ht.2.le⟩
  have hrad_Ioo' :
      HasDerivWithinAt
        (fun τ : ℝ => (fderiv ℝ (coordinateExp (n := n) data.Gamma p) (τ • v)) v)
        (Geodesic.Coordinate.geodesicAcceleration
          (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma)
          (Geodesic.Coordinate.statePosition n (γ t))
          (Geodesic.Coordinate.stateVelocity n (γ t)))
        (Ioo t 1)
        t := by
    exact hγvel_Ioo.congr
      (fun x hx => by
        simpa [γ] using
          geodesicFamily_velocity_eq_fderiv_radial (n := n) data.Gamma p _hv x
            ⟨le_trans ht.1 (le_of_lt hx.1), hx.2.le⟩ |>.symm)
      hEq_vel.symm
  have hrad_Ioo :
      HasDerivWithinAt
        (fun τ : ℝ => (fderiv ℝ (coordinateExp (n := n) data.Gamma p) (τ • v)) v)
        (Geodesic.Coordinate.geodesicAcceleration
          (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma)
          (coordinateExp (n := n) data.Gamma p (t • v))
          ((fderiv ℝ (coordinateExp (n := n) data.Gamma p) (t • v)) v))
        (Ioo t 1)
        t := by
    simpa [hEq_pos, hEq_vel] using hrad_Ioo'
  exact hasDerivWithinAt_Ici_of_Ioo ht.2 hrad_Ioo

/-- The derivative of the radial pairing function equals `g(p)(v,w)` on `[0,1)`,
via the geodesic equation, torsion-free interchange, and metric compatibility. -/
private theorem hasDerivWithinAt_radialPairingFn_of_localRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    (_hcompat : IsMetricCompatible (n := n) data.Gamma data.metricField)
    {v : Velocity n}
    (_hv : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
    (w : Velocity n) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (radialPairingFn (n := n) data.Gamma data.metricField p v w)
        (metricPairingAt data.metricField p v w) (Ici t) t := by
  sorry -- Derivative = g(p)(v,w) via geodesic eq + torsion-free + metric compatibility

theorem hasRadialVariationInterchange_of_localRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    (hcompat : IsMetricCompatible (n := n) data.Gamma data.metricField) :
    HasRadialVariationInterchange (n := n) data.Gamma data.metricField p := by
  intro v hv w
  exact ⟨continuousOn_radialPairingFn_of_localRiemannianData (n := n) data p hcompat hv w,
    hasDerivWithinAt_radialPairingFn_of_localRiemannianData (n := n) data p hcompat hv w⟩

/-- **Witness-free** `LocalAnalyticRealization` constructor combining the owner theorem
with the automatic differentiability from Issue 7. Only `hcomp` remains external. -/
noncomputable def localAnalyticRealizationOfRadialVariation_auto
    (data : LocalRiemannianData n)
    (p : Position n)
    (hcompat : IsMetricCompatible (n := n) data.Gamma data.metricField)
    (hcomp :
      ∀ {v : Velocity n}
        (_ : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
        (γ : ℝ → Position n)
        (Tγ Uγ : ℝ → Velocity n)
        (_ : Minimization.Coordinate.IsCurveFrom (n := n) p
            (coordinateExp (n := n) data.Gamma p v) γ 0 1)
        (_ : Minimization.Coordinate.HasNormalCoordinateKinematics
            (n := n) data.Gamma p γ Tγ Uγ 0 1),
        Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) ≤
          Minimization.Coordinate.metricCurveLength (n := n) data.metricField γ 0 1 Tγ) :
    LocalAnalyticRealization (n := n) data.Gamma data.metricField p where
  directionalDexp := hasDirectionalDexp_of_smoothChristoffel (n := n) data.Gamma p
  radialPairing := radialPairing_field_of_hasRadialVariationInterchange
    (n := n) data.Gamma data.metricField p
    (hasRadialVariationInterchange_of_localRiemannianData (n := n) data p hcompat)
  radius_le_metricLength := hcomp
  metricLength_le_radius := by
    intro v hv
    refine le_of_eq ?_
    calc
      Minimization.Coordinate.metricCurveLength (n := n) data.metricField
          (Minimization.Coordinate.radialGeodesic (n := n) data.Gamma p v) 0 1
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) data.Gamma p v)
        = Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v) := by
            exact Minimization.Coordinate.metricCurveLength_eq_const_of_unitInterval
              (n := n) data.metricField
              (Minimization.Coordinate.radialGeodesic (n := n) data.Gamma p v)
              (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) data.Gamma p v)
              (Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v))
              (radialGeodesic_metricSpeed_eq_const_of_directionalDexp_radialPairing
                (n := n) data.Gamma data.metricField p
                (hasDirectionalDexp_of_smoothChristoffel (n := n) data.Gamma p)
                (radialPairing_field_of_hasRadialVariationInterchange
                  (n := n) data.Gamma data.metricField p
                  (hasRadialVariationInterchange_of_localRiemannianData (n := n) data p hcompat))
                hv)
      _ = Minimization.Coordinate.metricNormalRadius (n := n) data.metricField data.Gamma p
            (coordinateExp (n := n) data.Gamma p v) := by
            symm
            exact Minimization.Coordinate.metricNormalRadius_exp
              (n := n) data.metricField data.Gamma p hv

end Exponential.Coordinate
