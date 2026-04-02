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

private theorem hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {a b t : ℝ}
    (h : HasDerivWithinAt f f' (Icc a b) t)
    (hat : a < t) (htb : t < b) :
    HasDerivWithinAt f f' (Ici t) t :=
  (h.hasDerivAt (Icc_mem_nhds hat htb)).hasDerivWithinAt

private theorem hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc_left
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {a b : ℝ}
    (h : HasDerivWithinAt f f' (Icc a b) a)
    (hab : a < b) :
    HasDerivWithinAt f f' (Ici a) a := by
  exact h.congr_set <|
    Eventually.set_eq <|
      Filter.eventually_of_mem (Iio_mem_nhds hab) (fun x hx => by
        simp only [mem_Icc, mem_Ici]
        exact ⟨fun hmem => hmem.1, fun hmem => ⟨hmem, le_of_lt hx⟩⟩)

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

/-- State-space geodesic energy `H(x,v) = g_x(v,v)` for local Riemannian data. -/
noncomputable def stateEnergy
    (data : LocalRiemannianData n)
    (z : Geodesic.Coordinate.State n) : ℝ :=
  Metric.Coordinate.quadraticForm
    (data.metricField (Geodesic.Coordinate.statePosition n z))
    (Geodesic.Coordinate.stateVelocity n z)

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

private theorem continuousOn_stateEnergy_of_isCoordinateGeodesicOn
    (data : LocalRiemannianData n)
    {gamma : ℝ → Geodesic.Coordinate.State n} {a b : ℝ}
    (hgamma : Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) gamma (Icc a b)) :
    ContinuousOn (fun t : ℝ => stateEnergy (n := n) data (gamma t)) (Icc a b) := by
  have hgamma_cont : ContinuousOn gamma (Icc a b) := HasDerivWithinAt.continuousOn hgamma
  have hpos :
      ContinuousOn (fun t : ℝ => Geodesic.Coordinate.statePosition n (gamma t)) (Icc a b) := by
    simpa [Function.comp, Geodesic.Coordinate.statePosition] using
      continuous_fst.continuousOn.comp hgamma_cont (by intro t ht; exact mem_univ _)
  have hvel :
      ContinuousOn (fun t : ℝ => Geodesic.Coordinate.stateVelocity n (gamma t)) (Icc a b) := by
    simpa [Function.comp, Geodesic.Coordinate.stateVelocity] using
      continuous_snd.continuousOn.comp hgamma_cont (by intro t ht; exact mem_univ _)
  have hvelcoord :
      ∀ i : Fin n,
        ContinuousOn (fun t : ℝ => Geodesic.Coordinate.stateVelocity n (gamma t) i) (Icc a b) := by
    intro i
    exact (continuous_apply i).continuousOn.comp hvel (by intro t ht; exact mem_univ _)
  have hMetricCoeff :
      ∀ i j : Fin n,
        ContinuousOn
          (fun t : ℝ => data.metricField (Geodesic.Coordinate.statePosition n (gamma t)) i j)
          (Icc a b) := by
    intro i j
    simpa [LocalRiemannianData.metricField, LeviCivita.CoordinateField.tensorAt] using
      ((data.gSmooth.smooth' i j).continuous.continuousOn.comp hpos
        (by intro t ht; exact mem_univ _))
  change ContinuousOn
    (fun t : ℝ =>
      ∑ i : Fin n, ∑ j : Fin n,
        Geodesic.Coordinate.stateVelocity n (gamma t) i *
          data.metricField (Geodesic.Coordinate.statePosition n (gamma t)) i j *
          Geodesic.Coordinate.stateVelocity n (gamma t) j)
    (Icc a b)
  refine continuousOn_finset_sum _ ?_
  intro i hi
  refine continuousOn_finset_sum _ ?_
  intro j hj
  simpa [mul_assoc] using ((hvelcoord i).mul (hMetricCoeff i j)).mul (hvelcoord j)

private theorem hasDerivWithinAt_stateEnergy_zero_of_isCoordinateGeodesicOn
    (data : LocalRiemannianData n)
    {gamma : ℝ → Geodesic.Coordinate.State n} {a b : ℝ}
    (hab : a < b)
    (hgamma : Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) gamma (Icc a b)) :
    ∀ t ∈ Ico a b,
      HasDerivWithinAt (fun τ : ℝ => stateEnergy (n := n) data (gamma τ)) 0 (Ici t) t := by
  rcases (Geodesic.Coordinate.isCoordinateGeodesicOn_iff_secondOrder
    (n := n)
    (Gamma := Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma)
    (gamma := gamma)
    (s := Icc a b)).mp hgamma with ⟨hpos, hvel⟩
  intro t ht
  let x : Position n := Geodesic.Coordinate.statePosition n (gamma t)
  let V : Velocity n := Geodesic.Coordinate.stateVelocity n (gamma t)
  let accel : Velocity n :=
    Geodesic.Coordinate.geodesicAcceleration
      (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V
  let dgV : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    ∑ k : Fin n, V k * LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x
  have hpos_Icc :
      HasDerivWithinAt
        (fun τ : ℝ => Geodesic.Coordinate.statePosition n (gamma τ))
        V
        (Icc a b)
        t := by
    simpa [x, V] using hpos t ⟨ht.1, ht.2.le⟩
  have hvel_Icc :
      HasDerivWithinAt
        (fun τ : ℝ => Geodesic.Coordinate.stateVelocity n (gamma τ))
        accel
        (Icc a b)
        t := by
    simpa [x, V, accel] using hvel t ⟨ht.1, ht.2.le⟩
  have hpos_Ici :
      HasDerivWithinAt
        (fun τ : ℝ => Geodesic.Coordinate.statePosition n (gamma τ))
        V
        (Ici t)
        t := by
    by_cases hta : t = a
    · subst hta
      exact hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc_left hpos_Icc hab
    · have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
      exact hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc hpos_Icc hat ht.2
  have hvel_Ici :
      HasDerivWithinAt
        (fun τ : ℝ => Geodesic.Coordinate.stateVelocity n (gamma τ))
        accel
        (Ici t)
        t := by
    by_cases hta : t = a
    · subst hta
      exact hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc_left hvel_Icc hab
    · have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
      exact hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc hvel_Icc hat ht.2
  have hg :
      ∀ i j,
        HasDerivWithinAt
          (fun τ => data.metricField (Geodesic.Coordinate.statePosition n (gamma τ)) i j)
          (dgV i j)
          (Ici t)
          t := by
    intro i j
    have hcoeff :
        HasDerivWithinAt
          (fun τ => data.gSmooth i j (Geodesic.Coordinate.statePosition n (gamma τ)))
          ((fderiv ℝ (fun y => data.gSmooth i j y) x) V)
          (Ici t)
          t := by
      exact (data.gSmooth.differentiableAt_component i j x).hasFDerivAt.comp_hasDerivWithinAt
        t hpos_Ici
    have hcoeff_val :
        (fderiv ℝ (fun y => data.gSmooth i j y) x) V = dgV i j := by
      have hsum :
          (fderiv ℝ (fun y => data.gSmooth i j y) x) V =
            ∑ k : Fin n, V k *
              (fderiv ℝ (fun y => data.gSmooth i j y) x)
                (LeviCivita.CoordinateField.coordBasis k) := by
        simpa using
          fderiv_smoothScalarField_apply_eq_sum_pderiv
            (n := n) (f := data.gSmooth.component i j) x V
      calc
        (fderiv ℝ (fun y => data.gSmooth i j y) x) V = ∑ k : Fin n, V k *
            (fderiv ℝ (fun y => data.gSmooth i j y) x)
              (LeviCivita.CoordinateField.coordBasis k) := hsum
        _ = dgV i j := by
          unfold dgV
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [LeviCivita.CoordinateField.metricDerivative_eq_fderiv]
    have hcoeff' :
        HasDerivWithinAt
          (fun τ => data.metricField (Geodesic.Coordinate.statePosition n (gamma τ)) i j)
          ((fderiv ℝ (fun y => data.gSmooth i j y) x) V)
          (Ici t)
          t := by
      simpa [LocalRiemannianData.metricField, LeviCivita.CoordinateField.tensorAt] using hcoeff
    exact hcoeff_val.symm ▸ hcoeff'
  have hpair :=
    hasDerivWithinAt_coordinatePairing
      (n := n)
      (g := fun τ => data.metricField (Geodesic.Coordinate.statePosition n (gamma τ)))
      (dg := fun _ => dgV)
      (Y := fun τ => Geodesic.Coordinate.stateVelocity n (gamma τ))
      (Z := fun τ => Geodesic.Coordinate.stateVelocity n (gamma τ))
      (y' := accel)
      (z' := accel)
      hg hvel_Ici hvel_Ici
  have hcancel :
      ParallelTransport.coordinatePairingAt dgV V V +
        ParallelTransport.coordinatePairingAt (data.metricField x) accel V +
        ParallelTransport.coordinatePairingAt (data.metricField x) V accel = 0 := by
    have hmetric :
        dgV =
          (fun i j =>
            ∑ m : Fin n, (connectionMatrixOfVector (n := n) data.Gamma x V) m i *
                data.metricField x m j +
              ∑ m : Fin n, data.metricField x i m *
                (connectionMatrixOfVector (n := n) data.Gamma x V) m j) := by
      simpa [dgV, x, V] using
        metricDerivativeAlong_eq_connectionMatrix_formula (n := n) data x V
    let A := connectionMatrixOfVector (n := n) data.Gamma x V
    let G : Matrix (Fin n) (Fin n) ℝ := data.metricField x
    have hDG :
        (fun i j =>
          ∑ m : Fin n, A m i * G m j +
            ∑ m : Fin n, G i m * A m j) =
        Matrix.transpose A * G + G * A := by
      ext i j
      simp [A, G, Matrix.mul_apply]
    have hzero :=
      ParallelTransport.coordinatePairingAt_parallel_deriv_eq_zero
        (A := fun _ : ℝ => A)
        (g := fun _ : ℝ => G)
        (dg := fun _ : ℝ => Matrix.transpose A * G + G * A)
        0 V V (by simp [hDG])
    simpa [hmetric, A, G, x, V, accel,
      coordinateParallelRhs_connectionMatrixOfVector_eq_acceleration (n := n) data.Gamma x V] using
      hzero
  have hpair' :
      HasDerivWithinAt
        (fun τ : ℝ => stateEnergy (n := n) data (gamma τ))
        (ParallelTransport.coordinatePairingAt dgV V V +
          ParallelTransport.coordinatePairingAt (data.metricField x) accel V +
          ParallelTransport.coordinatePairingAt (data.metricField x) V accel)
        (Ici t)
        t := by
    simpa [stateEnergy, Metric.Coordinate.quadraticForm, ParallelTransport.coordinatePairing] using
      hpair
  exact hcancel.symm ▸ hpair'

/-- Along any coordinate geodesic of the Levi-Civita spray for `LocalRiemannianData`, the
state-space energy `H(x,v) = g_x(v,v)` is constant. This is the owner theorem needed for the
smooth Hopf-Rinow compact-shell argument; the radial theorem is now just one special case. -/
theorem stateEnergy_eq_initial_of_isCoordinateGeodesicOn
    (data : LocalRiemannianData n)
    {gamma : ℝ → Geodesic.Coordinate.State n} {a b : ℝ}
    (hab : a ≤ b)
    (hgamma : Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) gamma (Icc a b)) :
    ∀ t ∈ Icc a b,
      stateEnergy (n := n) data (gamma t) = stateEnergy (n := n) data (gamma a) := by
  by_cases hdeg : a = b
  · intro t ht
    have ht0 : t = a := le_antisymm (by simpa [hdeg] using ht.2) ht.1
    simp [ht0]
  · have hlt : a < b := lt_of_le_of_ne hab hdeg
    exact constant_of_has_deriv_right_zero
      (continuousOn_stateEnergy_of_isCoordinateGeodesicOn (n := n) data hgamma)
      (hasDerivWithinAt_stateEnergy_zero_of_isCoordinateGeodesicOn (n := n) data hlt hgamma)

/-- A global lower metric bound turns conserved geodesic energy into a uniform Euclidean velocity
bound along the whole interval. -/
theorem stateVelocity_norm_le_of_metricLowerBound
    (data : LocalRiemannianData n)
    {m : ℝ}
    (hm_pos : 0 < m)
    (hmetric_lower :
      ∀ x : Position n, ∀ v : Velocity n,
        m * Metric.Coordinate.supNormSq v ≤
          Metric.Coordinate.quadraticForm (data.metricField x) v)
    {gamma : ℝ → Geodesic.Coordinate.State n} {a b : ℝ}
    (hab : a ≤ b)
    (hgamma : Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) gamma (Icc a b)) :
    ∀ t ∈ Icc a b,
      ‖Geodesic.Coordinate.stateVelocity n (gamma t)‖ ≤
        Real.sqrt (stateEnergy (n := n) data (gamma a) / m) := by
  let E : ℝ := stateEnergy (n := n) data (gamma a)
  have hE_nonneg : 0 ≤ E := by
    dsimp [E, stateEnergy]
    exact Metric.Coordinate.quadraticForm_nonneg
      (data.metricField_posDef (Geodesic.Coordinate.statePosition n (gamma a)))
      (Geodesic.Coordinate.stateVelocity n (gamma a))
  intro t ht
  let v := Geodesic.Coordinate.stateVelocity n (gamma t)
  have hmetric_lower_t :
      m * Metric.Coordinate.supNormSq v ≤
        Metric.Coordinate.quadraticForm
          (data.metricField (Geodesic.Coordinate.statePosition n (gamma t))) v :=
    hmetric_lower _ v
  have henergy :
      stateEnergy (n := n) data (gamma t) = E := by
    simpa [E] using
      stateEnergy_eq_initial_of_isCoordinateGeodesicOn (n := n) data hab hgamma t ht
  have hsq_le : Metric.Coordinate.supNormSq v ≤ E / m := by
    rw [le_div_iff₀ hm_pos]
    calc
      Metric.Coordinate.supNormSq v * m = m * Metric.Coordinate.supNormSq v := by ring
      _ ≤ Metric.Coordinate.quadraticForm
            (data.metricField (Geodesic.Coordinate.statePosition n (gamma t))) v :=
          hmetric_lower_t
      _ = stateEnergy (n := n) data (gamma t) := by
            rfl
      _ = E := henergy
  have hnorm_sq : ‖v‖ ^ 2 ≤ E / m := by
    simpa [Metric.Coordinate.supNormSq, pow_two] using hsq_le
  calc
    ‖v‖ = Real.sqrt (‖v‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (E / m) := by
      exact Real.sqrt_le_sqrt hnorm_sq
    _ = Real.sqrt (stateEnergy (n := n) data (gamma a) / m) := by
      rfl

/-- Under a global lower metric bound, a finite-horizon coordinate geodesic stays in a Euclidean
closed ball around its initial position. This is the corrected Layer B theorem: it replaces the
false generic compact-containment statement for arbitrary `LocalRiemannianData`. -/
theorem statePosition_mem_closedBall_of_metricLowerBound
    (data : LocalRiemannianData n)
    {m : ℝ}
    (hm_pos : 0 < m)
    (hmetric_lower :
      ∀ x : Position n, ∀ v : Velocity n,
        m * Metric.Coordinate.supNormSq v ≤
          Metric.Coordinate.quadraticForm (data.metricField x) v)
    {gamma : ℝ → Geodesic.Coordinate.State n} {a b : ℝ}
    (hab : a ≤ b)
    (hgamma : Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) gamma (Icc a b)) :
    ∀ t ∈ Icc a b,
      Geodesic.Coordinate.statePosition n (gamma t) ∈
        Metric.closedBall
          (Geodesic.Coordinate.statePosition n (gamma a))
          (Real.sqrt (stateEnergy (n := n) data (gamma a) / m) * (b - a)) := by
  rcases (Geodesic.Coordinate.isCoordinateGeodesicOn_iff_secondOrder
      (n := n)
      (Gamma := Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma)
      (gamma := gamma)
      (s := Icc a b)).mp hgamma with ⟨hpos, _⟩
  let C : ℝ := Real.sqrt (stateEnergy (n := n) data (gamma a) / m)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Real.sqrt_nonneg _
  have hdisp :
      ∀ t ∈ Icc a b,
        ‖Geodesic.Coordinate.statePosition n (gamma t) -
            Geodesic.Coordinate.statePosition n (gamma a)‖ ≤
          C * (t - a) := by
    simpa [C] using
      (norm_image_sub_le_of_norm_deriv_le_segment'
        (a := a) (b := b)
        (f := fun τ : ℝ => Geodesic.Coordinate.statePosition n (gamma τ))
        (f' := fun τ : ℝ => Geodesic.Coordinate.stateVelocity n (gamma τ))
        (C := C)
        (hf := by
          intro x hx
          exact hpos x hx)
        (bound := by
          intro x hx
          simpa [C] using
            stateVelocity_norm_le_of_metricLowerBound
              (n := n) data hm_pos hmetric_lower hab hgamma x (Ico_subset_Icc_self hx)))
  intro t ht
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsub : t - a ≤ b - a := sub_le_sub_right ht.2 a
  exact le_trans (hdisp t ht) (mul_le_mul_of_nonneg_left hsub hC_nonneg)

/-- If the base positions of a coordinate geodesic stay inside a compact position set `K`, then
the full state stays inside a compact shell `K × closedBall(0, R)`. This isolates the geometric
input needed by the smooth Hopf-Rinow compact-containment argument to compact base containment plus
the first integral `stateEnergy`. -/
theorem exists_stateCompactShell_of_isCoordinateGeodesicOn_of_position_isCompact
    (data : LocalRiemannianData n)
    {gamma : ℝ → Geodesic.Coordinate.State n} {a b : ℝ}
    (hab : a ≤ b)
    (hgamma : Geodesic.Coordinate.IsCoordinateGeodesicOn
      (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) gamma (Icc a b))
    {K : Set (Position n)}
    (hK : IsCompact K)
    (hbase : ∀ t ∈ Icc a b, Geodesic.Coordinate.statePosition n (gamma t) ∈ K) :
    ∃ R : ℝ, 0 ≤ R ∧
      IsCompact (K ×ˢ Metric.closedBall (0 : Velocity n) R) ∧
      ∀ t ∈ Icc a b, gamma t ∈ K ×ˢ Metric.closedBall (0 : Velocity n) R := by
  obtain ⟨m, M, hm_pos, hM_pos, hmetric⟩ :=
    data.exists_uniform_metric_normComparisonOn_isCompact hK
  let E : ℝ := stateEnergy (n := n) data (gamma a)
  have hE_nonneg : 0 ≤ E := by
    dsimp [E, stateEnergy]
    exact Metric.Coordinate.quadraticForm_nonneg
      (data.metricField_posDef (Geodesic.Coordinate.statePosition n (gamma a)))
      (Geodesic.Coordinate.stateVelocity n (gamma a))
  have henergy :
      ∀ t ∈ Icc a b,
        stateEnergy (n := n) data (gamma t) = E := by
    intro t ht
    simpa [E] using
      stateEnergy_eq_initial_of_isCoordinateGeodesicOn (n := n) data hab hgamma t ht
  let R : ℝ := Real.sqrt (E / m)
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact Real.sqrt_nonneg _
  refine ⟨R, hR_nonneg, ?_, ?_⟩
  · exact hK.prod (isCompact_closedBall (0 : Velocity n) R)
  · intro t ht
    constructor
    · exact hbase t ht
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      let v := Geodesic.Coordinate.stateVelocity n (gamma t)
      have hmetric_lower :
          m * Metric.Coordinate.supNormSq v ≤
            Metric.Coordinate.quadraticForm
              (data.metricField (Geodesic.Coordinate.statePosition n (gamma t))) v :=
        (hmetric _ (hbase t ht) v).1
      have hsq_le : Metric.Coordinate.supNormSq v ≤ E / m := by
        rw [le_div_iff₀ hm_pos]
        calc
          Metric.Coordinate.supNormSq v * m = m * Metric.Coordinate.supNormSq v := by ring
          _ ≤ Metric.Coordinate.quadraticForm
                (data.metricField (Geodesic.Coordinate.statePosition n (gamma t))) v :=
              hmetric_lower
          _ = stateEnergy (n := n) data (gamma t) := by
                rfl
          _ = E := henergy t ht
      have hnorm_sq :
          ‖v‖ ^ 2 ≤ E / m := by
        simpa [Metric.Coordinate.supNormSq, pow_two] using hsq_le
      calc
        ‖v‖ = Real.sqrt (‖v‖ ^ 2) := by
          rw [Real.sqrt_sq (norm_nonneg _)]
        _ ≤ Real.sqrt (E / m) := by
          exact Real.sqrt_le_sqrt hnorm_sq
        _ = R := by
          rfl

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

/-! ### Algebraic helpers for the energy cancellation -/

/-- Metric symmetry for the coordinate pairing: `g(X,Y) = g(Y,X)` when g is symmetric. -/
private theorem coordinatePairingAt_comm_of_symm
    {g : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ i j, g i j = g j i)
    (X Y : Velocity n) :
    ParallelTransport.coordinatePairingAt g X Y =
      ParallelTransport.coordinatePairingAt g Y X := by
  simp only [ParallelTransport.coordinatePairingAt]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [hsymm i j]; ring

private theorem metricField_symm
    (data : LocalRiemannianData n)
    (x : Position n) :
    ∀ i j : Fin n, data.metricField x i j = data.metricField x j i := by
  intro i j
  simpa [LocalRiemannianData.metricField, LeviCivita.CoordinateField.tensorAt] using
    data.symm x i j

/-- **Energy cancellation**: the three-term derivative of the geodesic energy is zero.
`dg(V)(V,V) + g(accel,V) + g(V,accel) = 0` where `dg(V) = ΓᵀG + GΓ` (metric compatibility)
and `accel = -ΓV·V` (geodesic equation). The four terms pair off: `g(ΓV,V) + g(V,ΓV) - g(ΓV,V) - g(V,ΓV) = 0`. -/
private theorem energy_deriv_cancellation
    (data : LocalRiemannianData n)
    (x : Position n) (V : Velocity n) :
    ParallelTransport.coordinatePairingAt
      (fun i j => ∑ m, (connectionMatrixOfVector (n := n) data.Gamma x V) m i *
          data.metricField x m j +
        ∑ m, data.metricField x i m *
          (connectionMatrixOfVector (n := n) data.Gamma x V) m j)
      V V +
    ParallelTransport.coordinatePairingAt (data.metricField x)
      (Geodesic.Coordinate.geodesicAcceleration
        (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V) V +
    ParallelTransport.coordinatePairingAt (data.metricField x) V
      (Geodesic.Coordinate.geodesicAcceleration
        (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V) = 0 := by
  let A := connectionMatrixOfVector (n := n) data.Gamma x V
  let G : Matrix (Fin n) (Fin n) ℝ := data.metricField x
  have hDG :
      (fun i j =>
        ∑ m : Fin n, A m i * G m j +
          ∑ m : Fin n, G i m * A m j) =
      Matrix.transpose A * G + G * A := by
    ext i j
    simp [A, G, Matrix.mul_apply]
  have hzero :=
    ParallelTransport.coordinatePairingAt_parallel_deriv_eq_zero
      (A := fun _ : ℝ => A)
      (g := fun _ : ℝ => G)
      (dg := fun _ : ℝ => Matrix.transpose A * G + G * A)
      0 V V (by simp)
  simpa [A, G, hDG, coordinateParallelRhs_connectionMatrixOfVector_eq_acceleration
    (n := n) data.Gamma x V] using hzero

private theorem continuousOn_geodesicEnergy_of_localRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source) :
    ContinuousOn (geodesicEnergy (n := n) data.Gamma data.metricField p v) (Icc 0 1) := by
  let expMap := coordinateExp (n := n) data.Gamma p
  have hvsource : v ∈ coordinateExpSource (n := n) data.Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) data.Gamma p hv
  have hExp : ContinuousOn expMap (coordinateExpSource (n := n) data.Gamma p) := by
    intro u hu
    exact (contDiffAt_coordinateExp (n := n) data.Gamma p hu).continuousAt.continuousWithinAt
  have hExpRadial : ContinuousOn (fun t : ℝ => expMap (t • v)) (Icc 0 1) :=
    hExp.comp ((continuous_id.smul continuous_const).continuousOn)
      (fun t ht => smul_mem_coordinateExpSource (n := n) data.Gamma p hvsource ht.1 ht.2)
  have hV :
      ContinuousOn (fun t : ℝ => (fderiv ℝ expMap (t • v)) v) (Icc 0 1) :=
    continuousOn_fderiv_coordinateExp_radial_apply (n := n) data.Gamma p hvsource v
  have hVcoord :
      ∀ i : Fin n,
        ContinuousOn (fun t : ℝ => ((fderiv ℝ expMap (t • v)) v) i) (Icc 0 1) := by
    intro i
    exact (continuous_apply i).continuousOn.comp hV (by intro t ht; exact mem_univ _)
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
          ((fderiv ℝ expMap (t • v)) v) j)
    (Icc 0 1)
  refine continuousOn_finset_sum _ ?_
  intro i _
  refine continuousOn_finset_sum _ ?_
  intro j _
  simpa [expMap, mul_assoc] using ((hVcoord i).mul (hMetricCoeff i j)).mul (hVcoord j)

private theorem hasDerivWithinAt_geodesicEnergy_zero_of_localRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt (geodesicEnergy (n := n) data.Gamma data.metricField p v) 0 (Ici t) t := by
  let expMap := coordinateExp (n := n) data.Gamma p
  have hvsource : v ∈ coordinateExpSource (n := n) data.Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) data.Gamma p hv
  intro t ht
  let x : Position n := expMap (t • v)
  let V : Velocity n := (fderiv ℝ expMap (t • v)) v
  let dgV : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    ∑ k : Fin n, V k *
      LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x
  have hg :
      ∀ i j, HasDerivWithinAt
        (fun τ => data.metricField (expMap (τ • v)) i j)
        (dgV i j) (Ici t) t := by
    intro i j
    have h :=
      hasDerivAt_metricFieldCoeff_coordinateExp_line
        (n := n) data p hvsource i j ⟨ht.1, ht.2.le⟩
    simpa [expMap, x, V, dgV] using h.hasDerivWithinAt
  have hV :
      HasDerivWithinAt
        (fun τ : ℝ => (fderiv ℝ expMap (τ • v)) v)
        (Geodesic.Coordinate.geodesicAcceleration
          (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V)
        (Ici t) t := by
    simpa [expMap, x, V] using
      hasDerivWithinAt_radialVelocityField_of_localRiemannianData
        (n := n) data p hv t ht
  have hpair :=
    hasDerivWithinAt_coordinatePairing
      (n := n) (g := fun τ => data.metricField (expMap (τ • v)))
      (dg := fun _ => dgV)
      (Y := fun τ => (fderiv ℝ expMap (τ • v)) v)
      (Z := fun τ => (fderiv ℝ expMap (τ • v)) v)
      (y' := Geodesic.Coordinate.geodesicAcceleration
        (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V)
      (z' := Geodesic.Coordinate.geodesicAcceleration
        (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V)
      hg hV hV
  have hcancel :
      ParallelTransport.coordinatePairingAt dgV V V +
        ParallelTransport.coordinatePairingAt (data.metricField x)
          (Geodesic.Coordinate.geodesicAcceleration
            (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V) V +
        ParallelTransport.coordinatePairingAt (data.metricField x) V
          (Geodesic.Coordinate.geodesicAcceleration
            (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V) = 0 := by
    have hmetric :
        dgV =
          (fun i j =>
            ∑ m : Fin n, (connectionMatrixOfVector (n := n) data.Gamma x V) m i *
                data.metricField x m j +
              ∑ m : Fin n, data.metricField x i m *
                (connectionMatrixOfVector (n := n) data.Gamma x V) m j) := by
      simpa [dgV, x, V] using
        metricDerivativeAlong_eq_connectionMatrix_formula (n := n) data x V
    rw [hmetric]
    simpa [x, V] using energy_deriv_cancellation (n := n) data x V
  have hpair' :
      HasDerivWithinAt
        (geodesicEnergy (n := n) data.Gamma data.metricField p v)
        (ParallelTransport.coordinatePairingAt dgV V V +
          ParallelTransport.coordinatePairingAt (data.metricField x)
            (Geodesic.Coordinate.geodesicAcceleration
              (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V) V +
          ParallelTransport.coordinatePairingAt (data.metricField x) V
            (Geodesic.Coordinate.geodesicAcceleration
              (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V))
        (Ici t) t := by
    simpa [geodesicEnergy, expMap, Metric.Coordinate.quadraticForm,
      ParallelTransport.coordinatePairing] using hpair
  exact hcancel.symm ▸ hpair'

/-- For concrete local Riemannian data, the radial geodesic energy is constant on `[0,1]`. This
packages the metric-compatibility argument in a reusable owner theorem rather than keeping it local
to the radial Gauss-lemma construction. -/
theorem geodesicEnergy_eq_initial_of_localRiemannianData
    (data : LocalRiemannianData n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      geodesicEnergy (n := n) data.Gamma data.metricField p v t =
        Metric.Coordinate.quadraticForm (data.metricField p) v := by
  have hcont :=
    continuousOn_geodesicEnergy_of_localRiemannianData (n := n) data p hv
  have hderiv :=
    hasDerivWithinAt_geodesicEnergy_zero_of_localRiemannianData (n := n) data p hv
  have hconst := constant_of_has_deriv_right_zero hcont hderiv
  intro t ht
  calc
    geodesicEnergy (n := n) data.Gamma data.metricField p v t
      = geodesicEnergy (n := n) data.Gamma data.metricField p v 0 := hconst t ht
    _ = Metric.Coordinate.quadraticForm (data.metricField p) v :=
      geodesicEnergy_zero (n := n) data.Gamma data.metricField p v

private theorem hasDerivAt_initialMetricQuadratic_line
    (data : LocalRiemannianData n)
    (p : Position n)
    (v w : Velocity n) :
    HasDerivAt
      (fun s : ℝ => Metric.Coordinate.quadraticForm (data.metricField p) (v + s • w))
      (2 * metricPairingAt data.metricField p v w)
      0 := by
  let G : Matrix (Fin n) (Fin n) ℝ := data.metricField p
  have hline :
      HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa [one_smul, Pi.add_apply] using
      (((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v)
  have hg :
      ∀ i j : Fin n, HasDerivAt (fun _ : ℝ => G i j) 0 0 := by
    intro i j
    simpa using (hasDerivAt_const (0 : ℝ) (G i j))
  have hpair :=
    ParallelTransport.hasDerivAt_coordinatePairing
      (n := n)
      (g := fun _ : ℝ => G)
      (dg := fun _ : ℝ => (0 : Matrix (Fin n) (Fin n) ℝ))
      (Y := fun s : ℝ => v + s • w)
      (Z := fun s : ℝ => v + s • w)
      (y' := w) (z' := w)
      hg hline hline
  have hcomm :
      ParallelTransport.coordinatePairingAt G w v =
        ParallelTransport.coordinatePairingAt G v w :=
    coordinatePairingAt_comm_of_symm (n := n) (metricField_symm (n := n) data p) w v
  have hpair' :
      HasDerivAt
        (fun s : ℝ => Metric.Coordinate.quadraticForm (data.metricField p) (v + s • w))
        (ParallelTransport.coordinatePairingAt G w v +
          ParallelTransport.coordinatePairingAt G v w)
        0 := by
    simpa [G, Metric.Coordinate.quadraticForm, ParallelTransport.coordinatePairing,
      ParallelTransport.coordinatePairingAt] using hpair
  simpa [G, metricPairingAt, hcomm, two_mul] using hpair'

/-- **The derivative of the radial pairing function equals `g(p)(v,w)` on `[0,1)`,
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
  have hvsource : v ∈ coordinateExpSource (n := n) data.Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) data.Gamma p _hv
  intro t ht
  let expMap := coordinateExp (n := n) data.Gamma p
  let ε :=
    (Geodesic.Coordinate.localCoordinateGeodesicFlowData
      (n := n) data.Gamma 0 (baseState n p)).ε
  let x : Position n := expMap (t • v)
  let V : Velocity n := (fderiv ℝ expMap (t • v)) v
  let S : Velocity n :=
    Geodesic.Coordinate.statePosition n
      (geodesicFamilyStateVariation (n := n) data.Gamma p v w t)
  let dS : Velocity n :=
    ε • Geodesic.Coordinate.stateVelocity n
      (geodesicFamilyStateVariation (n := n) data.Gamma p v w t)
  let G : Matrix (Fin n) (Fin n) ℝ := data.metricField x
  let A : Matrix (Fin n) (Fin n) ℝ := connectionMatrixOfVector (n := n) data.Gamma x V
  let B : Matrix (Fin n) (Fin n) ℝ := connectionMatrixOfVector (n := n) data.Gamma x S
  let c : ℝ := ParallelTransport.coordinatePairingAt G V (Matrix.mulVec B V + dS)
  let accel : Velocity n :=
    Geodesic.Coordinate.geodesicAcceleration
      (Geodesic.Coordinate.christoffelFieldOfSmooth data.Gamma) x V
  let variationLine : ℝ → ℝ := fun τ =>
    ParallelTransport.coordinatePairingAt
      (data.metricField (expMap (τ • v)))
      ((fderiv ℝ expMap (τ • v)) v)
      (Geodesic.Coordinate.statePosition n
        (geodesicFamilyStateVariation (n := n) data.Gamma p v w τ))
  let stateLine : ℝ → Geodesic.Coordinate.State n := fun s =>
    ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve (v + s • w) t)
  let energyLine : ℝ → ℝ := fun s =>
    ParallelTransport.coordinatePairingAt
      (data.metricField (Geodesic.Coordinate.statePosition n (stateLine s)))
      (Geodesic.Coordinate.stateVelocity n (stateLine s))
      (Geodesic.Coordinate.stateVelocity n (stateLine s))
  let quadLine : ℝ → ℝ := fun s =>
    Metric.Coordinate.quadraticForm (data.metricField p) (v + s • w)
  let dgV : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    ∑ k : Fin n, V k *
      LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x
  let dgS : Matrix (Fin n) (Fin n) ℝ := fun i j =>
    ∑ k : Fin n, S k *
      LeviCivita.CoordinateField.metricDerivative data.gSmooth k i j x
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have hS_eq :
      S = t • ((fderiv ℝ expMap (t • v)) w) := by
    simpa [S, expMap] using
      statePosition_geodesicFamilyStateVariation_eq
        (n := n) data.Gamma p hvsource w htIcc
  have hgV :
      ∀ i j, HasDerivWithinAt
        (fun τ => data.metricField (expMap (τ • v)) i j)
        (dgV i j) (Ici t) t := by
    intro i j
    have h :=
      hasDerivAt_metricFieldCoeff_coordinateExp_line
        (n := n) data p hvsource i j htIcc
    simpa [expMap, x, V, dgV] using h.hasDerivWithinAt
  have hV :
      HasDerivWithinAt
        (fun τ : ℝ => (fderiv ℝ expMap (τ • v)) v)
        accel
        (Ici t) t := by
    simpa [expMap, x, V, accel] using
      hasDerivWithinAt_radialVelocityField_of_localRiemannianData
        (n := n) data p _hv t ht
  have hS :
      HasDerivWithinAt
        (fun τ : ℝ =>
          Geodesic.Coordinate.statePosition n
            (geodesicFamilyStateVariation (n := n) data.Gamma p v w τ))
        dS
        (Ici t) t := by
    simpa [dS, ε] using
      hasDerivWithinAt_statePosition_geodesicFamilyStateVariation
        (n := n) data.Gamma p hvsource w ht
  have hpairRad_raw :=
    hasDerivWithinAt_coordinatePairing
      (n := n)
      (g := fun τ => data.metricField (expMap (τ • v)))
      (dg := fun _ => dgV)
      (Y := fun τ => (fderiv ℝ expMap (τ • v)) v)
      (Z := fun τ =>
        Geodesic.Coordinate.statePosition n
          (geodesicFamilyStateVariation (n := n) data.Gamma p v w τ))
      (y' := accel) (z' := dS)
      hgV hV hS
  have hpairRad :
      HasDerivWithinAt variationLine
        (ParallelTransport.coordinatePairingAt dgV V S +
          ParallelTransport.coordinatePairingAt G accel S +
          ParallelTransport.coordinatePairingAt G V dS)
        (Ici t) t := by
    simpa [variationLine, expMap, x, V, S, dS, G, accel, ParallelTransport.coordinatePairing]
      using hpairRad_raw
  have hmetricV :
      dgV =
        (fun i j =>
          ∑ m : Fin n, A m i * G m j +
            ∑ m : Fin n, G i m * A m j) := by
    simpa [dgV, A, G, x, V] using
      metricDerivativeAlong_eq_connectionMatrix_formula (n := n) data x V
  have hDG_V : dgV = Matrix.transpose A * G + G * A := by
    rw [hmetricV]
    ext i j
    simp [A, G, Matrix.mul_apply]
  have haccel :
      accel = -(Matrix.mulVec A V) := by
    calc
      accel
        = ParallelTransport.coordinateParallelRhs (fun _ : ℝ => A) 0 V := by
            symm
            simpa [A] using
              coordinateParallelRhs_connectionMatrixOfVector_eq_acceleration
                (n := n) data.Gamma x V
      _ = -(Matrix.mulVec A V) := by
            simp [ParallelTransport.coordinateParallelRhs]
  have hzeroVS :
      ParallelTransport.coordinatePairingAt dgV V S +
        ParallelTransport.coordinatePairingAt G accel S +
        ParallelTransport.coordinatePairingAt G V (-(Matrix.mulVec A S)) = 0 := by
    have hz :=
      ParallelTransport.coordinatePairingAt_parallel_deriv_eq_zero
        (A := fun _ : ℝ => A)
        (g := fun _ : ℝ => G)
        (dg := fun _ : ℝ => dgV)
        0 V S hDG_V
    rw [haccel]
    simpa [G, A, ParallelTransport.coordinateParallelRhs] using hz
  have hnegAS :
      ParallelTransport.coordinatePairingAt G V (-(Matrix.mulVec A S)) =
        -ParallelTransport.coordinatePairingAt G V (Matrix.mulVec A S) := by
    simp [ParallelTransport.coordinatePairingAt]
  have hVS :
      ParallelTransport.coordinatePairingAt dgV V S +
        ParallelTransport.coordinatePairingAt G accel S =
        ParallelTransport.coordinatePairingAt G V (Matrix.mulVec A S) := by
    rw [hnegAS] at hzeroVS
    linarith
  have hGamma_symm :
      Matrix.mulVec A S = Matrix.mulVec B V := by
    simpa [A, B, connectionMatrixOfVector] using
      (connectionMatrix_mulVec_symm (n := n) data x V S)
  have hrad_val :
      ParallelTransport.coordinatePairingAt dgV V S +
        ParallelTransport.coordinatePairingAt G accel S +
        ParallelTransport.coordinatePairingAt G V dS = c := by
    rw [hVS, hGamma_symm]
    simp [c, G, B, dS, ParallelTransport.coordinatePairingAt,
      Finset.sum_add_distrib, mul_add, add_mul, mul_assoc]
  have hvariation :
      HasDerivWithinAt variationLine c (Ici t) t := hrad_val ▸ hpairRad
  have heqRad :
      radialPairingFn (n := n) data.Gamma data.metricField p v w =ᶠ[𝓝[Set.Ici t] t]
        variationLine := by
    filter_upwards [inter_mem_nhdsWithin (Ici t) (Iio_mem_nhds ht.2)] with τ hτ
    have hτIcc : τ ∈ Icc (0 : ℝ) 1 := ⟨le_trans ht.1 hτ.1, hτ.2.le⟩
    have hcurve :
        Geodesic.Coordinate.statePosition n
          ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve v τ) =
          expMap (τ • v) := by
      simpa [expMap] using
        (coordinateExp_smul_eq_geodesicFamily_position
          (n := n) data.Gamma p hvsource hτIcc).symm
    simpa [variationLine, hcurve, expMap] using
      radialPairingFn_eq_variationField
        (n := n) data.Gamma data.metricField p _hv w hτIcc
  have hradial :
      HasDerivWithinAt
        (radialPairingFn (n := n) data.Gamma data.metricField p v w)
        c (Ici t) t := by
    refine hvariation.congr_of_eventuallyEq heqRad ?_
    have hcurve :
        Geodesic.Coordinate.statePosition n
          ((geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p data.Gamma).solve v t) =
          expMap (t • v) := by
      simpa [expMap] using
        (coordinateExp_smul_eq_geodesicFamily_position
          (n := n) data.Gamma p hvsource htIcc).symm
    simpa [variationLine, hcurve, expMap] using
      radialPairingFn_eq_variationField
        (n := n) data.Gamma data.metricField p _hv w htIcc
  have hgS :
      ∀ i j, HasDerivAt
        (fun s =>
          data.metricField (Geodesic.Coordinate.statePosition n (stateLine s)) i j)
        (dgS i j) 0 := by
    intro i j
    have h :=
      hasDerivAt_metricFieldCoeff_geodesicFamily_line
        (n := n) data p hvsource w i j htIcc
    simpa [stateLine, expMap, x, S, dgS, hS_eq] using h
  have hVel :
      HasDerivAt
        (fun s => Geodesic.Coordinate.stateVelocity n (stateLine s))
        dS 0 := by
    simpa [stateLine, dS, ε] using
      hasDerivAt_geodesicFamily_velocity_line
        (n := n) data.Gamma p hvsource w htIcc
  have hpairEnergy_raw :=
    ParallelTransport.hasDerivAt_coordinatePairing
      (n := n)
      (g := fun s =>
        data.metricField (Geodesic.Coordinate.statePosition n (stateLine s)))
      (dg := fun _ => dgS)
      (Y := fun s => Geodesic.Coordinate.stateVelocity n (stateLine s))
      (Z := fun s => Geodesic.Coordinate.stateVelocity n (stateLine s))
      (y' := dS) (z' := dS)
      hgS hVel hVel
  have hpairEnergy :
      HasDerivAt energyLine
        (ParallelTransport.coordinatePairingAt dgS V V +
          ParallelTransport.coordinatePairingAt G dS V +
          ParallelTransport.coordinatePairingAt G V dS)
        0 := by
    have hpos0 :
        Geodesic.Coordinate.statePosition n (stateLine 0) = x := by
      simpa [stateLine, x, expMap, zero_smul, add_zero] using
        (coordinateExp_smul_eq_geodesicFamily_position
          (n := n) data.Gamma p hvsource htIcc).symm
    have hvel0 :
        Geodesic.Coordinate.stateVelocity n (stateLine 0) = V := by
      simpa [stateLine, x, V, expMap, zero_smul, add_zero] using
        geodesicFamily_velocity_eq_fderiv_radial
          (n := n) data.Gamma p _hv t htIcc
    have hpairEnergy_raw' :
        HasDerivAt energyLine
          (ParallelTransport.coordinatePairingAt dgS
              (Geodesic.Coordinate.stateVelocity n (stateLine 0))
              (Geodesic.Coordinate.stateVelocity n (stateLine 0)) +
            ParallelTransport.coordinatePairingAt
              (data.metricField (Geodesic.Coordinate.statePosition n (stateLine 0)))
              dS
              (Geodesic.Coordinate.stateVelocity n (stateLine 0)) +
            ParallelTransport.coordinatePairingAt
              (data.metricField (Geodesic.Coordinate.statePosition n (stateLine 0)))
              (Geodesic.Coordinate.stateVelocity n (stateLine 0))
              dS)
          0 := by
      simpa [energyLine, stateLine, ParallelTransport.coordinatePairing] using hpairEnergy_raw
    have hval :
        ParallelTransport.coordinatePairingAt dgS
            (Geodesic.Coordinate.stateVelocity n (stateLine 0))
            (Geodesic.Coordinate.stateVelocity n (stateLine 0)) +
          ParallelTransport.coordinatePairingAt
            (data.metricField (Geodesic.Coordinate.statePosition n (stateLine 0)))
            dS
            (Geodesic.Coordinate.stateVelocity n (stateLine 0)) +
          ParallelTransport.coordinatePairingAt
            (data.metricField (Geodesic.Coordinate.statePosition n (stateLine 0)))
            (Geodesic.Coordinate.stateVelocity n (stateLine 0))
            dS =
          ParallelTransport.coordinatePairingAt dgS V V +
            ParallelTransport.coordinatePairingAt G dS V +
            ParallelTransport.coordinatePairingAt G V dS := by
      simpa [G, V, dS, hpos0, hvel0]
    exact hval ▸ hpairEnergy_raw'
  have hmetricS :
      dgS =
        (fun i j =>
          ∑ m : Fin n, B m i * G m j +
            ∑ m : Fin n, G i m * B m j) := by
    simpa [dgS, B, G, x, S] using
      metricDerivativeAlong_eq_connectionMatrix_formula (n := n) data x S
  have hDG_S : dgS = Matrix.transpose B * G + G * B := by
    rw [hmetricS]
    ext i j
    simp [B, G, Matrix.mul_apply]
  have hzeroVV :
      ParallelTransport.coordinatePairingAt dgS V V +
        ParallelTransport.coordinatePairingAt G (-(Matrix.mulVec B V)) V +
        ParallelTransport.coordinatePairingAt G V (-(Matrix.mulVec B V)) = 0 := by
    have hz :=
      ParallelTransport.coordinatePairingAt_parallel_deriv_eq_zero
        (A := fun _ : ℝ => B)
        (g := fun _ : ℝ => G)
        (dg := fun _ : ℝ => dgS)
        0 V V hDG_S
    simpa [G, B, ParallelTransport.coordinateParallelRhs] using hz
  have hnegLeft :
      ParallelTransport.coordinatePairingAt G (-(Matrix.mulVec B V)) V =
        -ParallelTransport.coordinatePairingAt G (Matrix.mulVec B V) V := by
    simp [ParallelTransport.coordinatePairingAt]
  have hnegRight :
      ParallelTransport.coordinatePairingAt G V (-(Matrix.mulVec B V)) =
        -ParallelTransport.coordinatePairingAt G V (Matrix.mulVec B V) := by
    simp [ParallelTransport.coordinatePairingAt]
  have hmetricTerm :
      ParallelTransport.coordinatePairingAt dgS V V =
        ParallelTransport.coordinatePairingAt G (Matrix.mulVec B V) V +
          ParallelTransport.coordinatePairingAt G V (Matrix.mulVec B V) := by
    rw [hnegLeft, hnegRight] at hzeroVV
    linarith
  have henergy_raw :
      ParallelTransport.coordinatePairingAt dgS V V +
        ParallelTransport.coordinatePairingAt G dS V +
        ParallelTransport.coordinatePairingAt G V dS =
        ParallelTransport.coordinatePairingAt G (Matrix.mulVec B V + dS) V +
          ParallelTransport.coordinatePairingAt G V (Matrix.mulVec B V + dS) := by
    rw [hmetricTerm]
    simp [ParallelTransport.coordinatePairingAt, Finset.sum_add_distrib,
      mul_add, add_mul, add_assoc]
    ring
  have hcommU :
      ParallelTransport.coordinatePairingAt G (Matrix.mulVec B V + dS) V =
        ParallelTransport.coordinatePairingAt G V (Matrix.mulVec B V + dS) :=
    coordinatePairingAt_comm_of_symm (n := n) (metricField_symm (n := n) data x)
      (Matrix.mulVec B V + dS) V
  have henergy_val :
      ParallelTransport.coordinatePairingAt dgS V V +
        ParallelTransport.coordinatePairingAt G dS V +
        ParallelTransport.coordinatePairingAt G V dS = 2 * c := by
    rw [henergy_raw, hcommU]
    simp [c, two_mul]
  have henergyFormula : HasDerivAt energyLine (2 * c) 0 := henergy_val ▸ hpairEnergy
  have hmem_eventually :
      ∀ᶠ s in 𝓝 (0 : ℝ),
        v + s • w ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source := by
    have hopen :
        IsOpen ((coordinateExpPartialHomeomorph (n := n) data.Gamma p).source) :=
      (coordinateExpPartialHomeomorph (n := n) data.Gamma p).open_source
    have hcont :
        ContinuousAt (fun s : ℝ => v + s • w) 0 :=
      ((continuous_const.add (continuous_id.smul continuous_const))).continuousAt
    have hbase : v + (0 : ℝ) • w ∈ (coordinateExpPartialHomeomorph (n := n) data.Gamma p).source := by
      simpa [zero_smul, add_zero] using _hv
    exact hcont.preimage_mem_nhds (hopen.mem_nhds hbase)
  have heqEnergy : energyLine =ᶠ[𝓝 (0 : ℝ)] quadLine := by
    filter_upwards [hmem_eventually] with s hs
    let u : Velocity n := v + s • w
    have hsSource : u ∈ coordinateExpSource (n := n) data.Gamma p :=
      coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) data.Gamma p hs
    have hpos :
        Geodesic.Coordinate.statePosition n (stateLine s) =
          expMap (t • u) := by
      simpa [stateLine, u, expMap] using
        (coordinateExp_smul_eq_geodesicFamily_position
          (n := n) data.Gamma p hsSource htIcc).symm
    have hvel :
        Geodesic.Coordinate.stateVelocity n (stateLine s) =
          (fderiv ℝ expMap (t • u)) u := by
      simpa [stateLine, u, expMap] using
        geodesicFamily_velocity_eq_fderiv_radial
          (n := n) data.Gamma p hs t htIcc
    have henergy :
        geodesicEnergy (n := n) data.Gamma data.metricField p u t =
          Metric.Coordinate.quadraticForm (data.metricField p) u := by
      exact geodesicEnergy_eq_initial_of_localRiemannianData
        (n := n) data p hs t htIcc
    simpa [energyLine, quadLine, stateLine, u, expMap, hpos, hvel,
      geodesicEnergy, Metric.Coordinate.quadraticForm,
      ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul] using henergy
  have henergyConst :
      HasDerivAt energyLine (2 * metricPairingAt data.metricField p v w) 0 := by
    exact (hasDerivAt_initialMetricQuadratic_line (n := n) data p v w).congr_of_eventuallyEq
      heqEnergy
  have hc_eq : 2 * c = 2 * metricPairingAt data.metricField p v w :=
    HasDerivAt.unique henergyFormula henergyConst
  have hc : c = metricPairingAt data.metricField p v w := by
    linarith
  exact hc ▸ hradial

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
