import ParallelTransport.Basic
import Exponential.LocalAnalyticRealization
import Exponential.Differentiability

/-! The Gauss-lemma layer exports radial pairing identities. The zero-slice version is fully
proved. The full radial version is projected from the `LocalAnalyticInput` / `LocalAnalyticRealization`
interface boundary. -/

namespace Exponential.Coordinate

open scoped Topology
open scoped BigOperators

variable {n : ℕ}

private theorem sum_coordBasis_mul (f : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, LeviCivita.CoordinateField.coordBasis i j * f j = f i := by
  classical
  unfold LeviCivita.CoordinateField.coordBasis
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hji
    convert zero_mul (f j)
    simp [Pi.basisFun_apply, hji]
  · simp
  · simp [Pi.basisFun_apply]

private theorem sum_mul_coordBasis (f : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, f j * LeviCivita.CoordinateField.coordBasis i j = f i := by
  classical
  calc
    ∑ j : Fin n, f j * LeviCivita.CoordinateField.coordBasis i j
      = ∑ j : Fin n, LeviCivita.CoordinateField.coordBasis i j * f j := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = f i := sum_coordBasis_mul f i

private theorem double_sum_coordBasis_mul_mul_coordBasis
    (f : Fin n → Fin n → ℝ) (i j : Fin n) :
    ∑ a : Fin n, ∑ b : Fin n,
      LeviCivita.CoordinateField.coordBasis i a * f a b *
        LeviCivita.CoordinateField.coordBasis j b = f i j := by
  classical
  calc
    ∑ a : Fin n, ∑ b : Fin n,
        LeviCivita.CoordinateField.coordBasis i a * f a b *
          LeviCivita.CoordinateField.coordBasis j b
      = ∑ a : Fin n, LeviCivita.CoordinateField.coordBasis i a *
          (∑ b : Fin n, f a b * LeviCivita.CoordinateField.coordBasis j b) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            ring
    _ = ∑ a : Fin n, LeviCivita.CoordinateField.coordBasis i a * f a j := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [sum_mul_coordBasis (fun b => f a b) j]
    _ = f i j := by
          exact sum_coordBasis_mul (fun a => f a j) i

private theorem coordinateMetricPairing_basisVectorField
    (gSmooth : LeviCivita.CoordinateField.SmoothTensor2Field n)
    (j k : Fin n) :
    LeviCivita.CoordinateField.coordinateMetricPairing gSmooth
      (LeviCivita.CoordinateField.basisVectorField j)
      (LeviCivita.CoordinateField.basisVectorField k) =
    gSmooth.component j k := by
  ext x
  simpa [LeviCivita.CoordinateField.coordinateMetricPairing,
    LeviCivita.CoordinateField.basisVectorField,
    LeviCivita.CoordinateField.constVectorField] using
      double_sum_coordBasis_mul_mul_coordBasis (fun a b => gSmooth a b x) j k

private theorem covariantDerivative_basisVectorField_apply
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (i j m : Fin n) (x : Position n) :
    LeviCivita.CoordinateField.covariantDerivative Gamma
      (LeviCivita.CoordinateField.basisVectorField i)
      (LeviCivita.CoordinateField.basisVectorField j) x m =
    Gamma m i j x := by
  calc
    LeviCivita.CoordinateField.covariantDerivative Gamma
        (LeviCivita.CoordinateField.basisVectorField i)
        (LeviCivita.CoordinateField.basisVectorField j) x m
      =
        (∑ a : Fin n,
          LeviCivita.CoordinateField.coordBasis i a *
            LeviCivita.CoordinateField.pderivVector
              (LeviCivita.CoordinateField.basisVectorField j) a x m) +
        ∑ a : Fin n, ∑ b : Fin n,
          LeviCivita.CoordinateField.coordBasis i a * Gamma m a b x *
            LeviCivita.CoordinateField.coordBasis j b := by
              simp [LeviCivita.CoordinateField.covariantDerivative_apply,
                LeviCivita.CoordinateField.basisVectorField,
                LeviCivita.CoordinateField.constVectorField]
    _ = 0 +
        ∑ a : Fin n, ∑ b : Fin n,
          LeviCivita.CoordinateField.coordBasis i a * Gamma m a b x *
            LeviCivita.CoordinateField.coordBasis j b := by
              congr 1
              apply Finset.sum_eq_zero
              intro a ha
              simp [LeviCivita.CoordinateField.pderivVector,
                LeviCivita.CoordinateField.basisVectorField,
                LeviCivita.CoordinateField.constVectorField]
    _ = Gamma m i j x := by
          rw [zero_add]
          exact double_sum_coordBasis_mul_mul_coordBasis (fun a b => Gamma m a b x) i j

private theorem coordinateMetricPairing_covariantDerivative_basis_left
    (gSmooth : LeviCivita.CoordinateField.SmoothTensor2Field n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (x : Position n) (i j k : Fin n) :
    (LeviCivita.CoordinateField.coordinateMetricPairing gSmooth
      (LeviCivita.CoordinateField.covariantDerivative Gamma
        (LeviCivita.CoordinateField.basisVectorField i)
        (LeviCivita.CoordinateField.basisVectorField j))
      (LeviCivita.CoordinateField.basisVectorField k)) x =
      ∑ m : Fin n, gSmooth m k x * Gamma m i j x := by
  calc
    (LeviCivita.CoordinateField.coordinateMetricPairing gSmooth
      (LeviCivita.CoordinateField.covariantDerivative Gamma
        (LeviCivita.CoordinateField.basisVectorField i)
        (LeviCivita.CoordinateField.basisVectorField j))
      (LeviCivita.CoordinateField.basisVectorField k)) x
      = ∑ m : Fin n,
          (LeviCivita.CoordinateField.covariantDerivative Gamma
            (LeviCivita.CoordinateField.basisVectorField i)
            (LeviCivita.CoordinateField.basisVectorField j) x m) * gSmooth m k x := by
              simp [LeviCivita.CoordinateField.coordinateMetricPairing,
                LeviCivita.CoordinateField.basisVectorField,
                LeviCivita.CoordinateField.constVectorField]
              apply Finset.sum_congr rfl
              intro m hm
              calc
                ∑ x_1,
                    (∑ x_2,
                          ∑ x_3,
                            LeviCivita.CoordinateField.coordBasis i x_2 * Gamma m x_2 x_3 x *
                              LeviCivita.CoordinateField.coordBasis j x_3) *
                      gSmooth m x_1 x *
                      LeviCivita.CoordinateField.coordBasis k x_1
                  = ∑ x_1,
                      (∑ x_2,
                            ∑ x_3,
                              LeviCivita.CoordinateField.coordBasis i x_2 * Gamma m x_2 x_3 x *
                                LeviCivita.CoordinateField.coordBasis j x_3) *
                        (gSmooth m x_1 x * LeviCivita.CoordinateField.coordBasis k x_1) := by
                            apply Finset.sum_congr rfl
                            intro x_1 hx_1
                            ring
                _ = (∑ x_2,
                        ∑ x_3,
                          LeviCivita.CoordinateField.coordBasis i x_2 * Gamma m x_2 x_3 x *
                            LeviCivita.CoordinateField.coordBasis j x_3) *
                      (∑ x_1, gSmooth m x_1 x * LeviCivita.CoordinateField.coordBasis k x_1) := by
                            rw [Finset.mul_sum]
                _ = (∑ x_2,
                        ∑ x_3,
                          LeviCivita.CoordinateField.coordBasis i x_2 * Gamma m x_2 x_3 x *
                            LeviCivita.CoordinateField.coordBasis j x_3) *
                      gSmooth m k x := by rw [sum_mul_coordBasis (fun a => gSmooth m a x) k]
    _ = ∑ m : Fin n, gSmooth m k x * Gamma m i j x := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [covariantDerivative_basisVectorField_apply]
          ring

private theorem coordinateMetricPairing_covariantDerivative_basis_right
    (gSmooth : LeviCivita.CoordinateField.SmoothTensor2Field n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (x : Position n) (i j k : Fin n) :
    (LeviCivita.CoordinateField.coordinateMetricPairing gSmooth
      (LeviCivita.CoordinateField.basisVectorField j)
      (LeviCivita.CoordinateField.covariantDerivative Gamma
        (LeviCivita.CoordinateField.basisVectorField i)
        (LeviCivita.CoordinateField.basisVectorField k))) x =
      ∑ m : Fin n, gSmooth j m x * Gamma m i k x := by
  calc
    (LeviCivita.CoordinateField.coordinateMetricPairing gSmooth
      (LeviCivita.CoordinateField.basisVectorField j)
      (LeviCivita.CoordinateField.covariantDerivative Gamma
        (LeviCivita.CoordinateField.basisVectorField i)
        (LeviCivita.CoordinateField.basisVectorField k))) x
      = ∑ m : Fin n,
          gSmooth j m x *
            (LeviCivita.CoordinateField.covariantDerivative Gamma
              (LeviCivita.CoordinateField.basisVectorField i)
              (LeviCivita.CoordinateField.basisVectorField k) x m) := by
              simp [LeviCivita.CoordinateField.coordinateMetricPairing,
                LeviCivita.CoordinateField.basisVectorField,
                LeviCivita.CoordinateField.constVectorField]
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro m hm
              calc
                ∑ x_1,
                    LeviCivita.CoordinateField.coordBasis j x_1 * gSmooth x_1 m x *
                      ∑ x_2,
                        ∑ x_3,
                          LeviCivita.CoordinateField.coordBasis i x_2 * Gamma m x_2 x_3 x *
                            LeviCivita.CoordinateField.coordBasis k x_3
                  = ∑ x_1,
                      (LeviCivita.CoordinateField.coordBasis j x_1 * gSmooth x_1 m x) *
                        (∑ x_2,
                          ∑ x_3,
                            LeviCivita.CoordinateField.coordBasis i x_2 * Gamma m x_2 x_3 x *
                              LeviCivita.CoordinateField.coordBasis k x_3) := by
                            apply Finset.sum_congr rfl
                            intro x_1 hx_1
                            ring
                _ = (∑ x_1, LeviCivita.CoordinateField.coordBasis j x_1 * gSmooth x_1 m x) *
                      (∑ x_2,
                        ∑ x_3,
                          LeviCivita.CoordinateField.coordBasis i x_2 * Gamma m x_2 x_3 x *
                            LeviCivita.CoordinateField.coordBasis k x_3) := by
                            rw [Finset.sum_mul]
                _ = gSmooth j m x *
                      (∑ x_2,
                        ∑ x_3,
                          LeviCivita.CoordinateField.coordBasis i x_2 * Gamma m x_2 x_3 x *
                            LeviCivita.CoordinateField.coordBasis k x_3) := by rw [sum_coordBasis_mul (fun a => gSmooth a m x) j]
    _ = ∑ m : Fin n, gSmooth j m x * Gamma m i k x := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [covariantDerivative_basisVectorField_apply]

private theorem deriv_coordinateMetricPairing_basisVectorField
    (gSmooth : LeviCivita.CoordinateField.SmoothTensor2Field n)
    (x : Position n) (i j k : Fin n) :
    ((LeviCivita.CoordinateField.coordinateConnectionContext n).deriv
      (LeviCivita.CoordinateField.basisVectorField i)
      (LeviCivita.CoordinateField.coordinateMetricPairing gSmooth
        (LeviCivita.CoordinateField.basisVectorField j)
        (LeviCivita.CoordinateField.basisVectorField k))) x =
      LeviCivita.CoordinateField.metricDerivative gSmooth i j k x := by
  rw [coordinateMetricPairing_basisVectorField]
  simpa [LeviCivita.CoordinateField.coordinateConnectionContext,
    LeviCivita.CoordinateField.directionalDerivative_apply,
    LeviCivita.CoordinateField.metricDerivative,
    LeviCivita.CoordinateField.basisVectorField,
    LeviCivita.CoordinateField.constVectorField] using
      sum_coordBasis_mul (fun dir => LeviCivita.CoordinateField.pderivScalar (gSmooth.component j k) dir x) i

theorem exists_metricCompatible_coordinate_middle_formula
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (hcompat : IsMetricCompatible (n := n) Gamma g) :
    ∃ gSmooth : LeviCivita.CoordinateField.SmoothTensor2Field n,
      (∀ x i j, g x i j = gSmooth i j x) ∧
      ∀ x i j k,
        LeviCivita.CoordinateField.metricDerivative gSmooth i j k x =
          ∑ m : Fin n, gSmooth m k x * Gamma m i j x +
            ∑ m : Fin n, gSmooth j m x * Gamma m i k x := by
  rcases hcompat with ⟨gSmooth, hg, hmetric⟩
  refine ⟨gSmooth, hg, ?_⟩
  intro x i j k
  have hx := congrArg (fun s : LeviCivita.CoordinateField.SmoothScalarField n => s x)
    (hmetric
      (LeviCivita.CoordinateField.basisVectorField i)
      (LeviCivita.CoordinateField.basisVectorField j)
      (LeviCivita.CoordinateField.basisVectorField k))
  simpa [deriv_coordinateMetricPairing_basisVectorField,
    coordinateMetricPairing_covariantDerivative_basis_left,
    coordinateMetricPairing_covariantDerivative_basis_right] using hx

/-- Zero-slice coordinate Gauss lemma: at the base point, the differential of the coordinate
exponential map is the identity, so the metric pairing is preserved. -/
theorem gaussLemma_coordinate
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (hcompat : IsMetricCompatible (n := n) Gamma g)
    (p : Position n) (v w : Velocity n) :
    metricPairingAt g p
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) 0) v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) 0) w) =
      metricPairingAt g p v w := by
  let _ := hcompat
  simp [metricPairingAt, fderiv_coordinateExp_at_zero]

/-- Exported radial Gauss-lemma pairing identity for the local exponential map, projected from
the `LocalAnalyticInput` interface boundary. -/
theorem gaussLemma_radial_pairing_of_input
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (input : LocalAnalyticInput (n := n) Gamma g p)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (w : Velocity n) :
    metricPairingAt g (coordinateExp (n := n) Gamma p v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) =
      metricPairingAt g p v w :=
  input.radialPairing hv w

/-- Realization-layer wrapper for the radial Gauss pairing theorem. -/
theorem gaussLemma_radial_pairing_of_realization
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (hcompat : IsMetricCompatible (n := n) Gamma g)
    (realization : LocalAnalyticRealization (n := n) Gamma g p)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (w : Velocity n) :
    metricPairingAt g (coordinateExp (n := n) Gamma p v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) =
      metricPairingAt g p v w :=
  (canonicalLocalAnalyticInput hcompat realization).radialPairing hv w

/-- Exported radial Gauss-lemma pairing identity for the local exponential map. -/
theorem gaussLemma_radial_pairing
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (input : LocalAnalyticInput (n := n) Gamma g p)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (w : Velocity n) :
    metricPairingAt g (coordinateExp (n := n) Gamma p v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) =
      metricPairingAt g p v w :=
  gaussLemma_radial_pairing_of_input (n := n) Gamma g p input hv w

/-- Along the radial direction, `dexp` preserves the metric norm. -/
theorem gaussLemma_radial_norm
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (input : LocalAnalyticInput (n := n) Gamma g p)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    Metric.Coordinate.quadraticForm
        (g (coordinateExp (n := n) Gamma p v))
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v) =
      Metric.Coordinate.quadraticForm (g p) v := by
  simpa [metricPairingAt_self] using
    gaussLemma_radial_pairing (n := n) Gamma g p input hv v

/-- Realization-layer wrapper for the radial norm form of Gauss lemma. -/
theorem gaussLemma_radial_norm_of_realization
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (hcompat : IsMetricCompatible (n := n) Gamma g)
    (realization : LocalAnalyticRealization (n := n) Gamma g p)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    Metric.Coordinate.quadraticForm
        (g (coordinateExp (n := n) Gamma p v))
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v) =
      Metric.Coordinate.quadraticForm (g p) v := by
  simpa [metricPairingAt_self] using
    gaussLemma_radial_pairing_of_realization (n := n) Gamma g p hcompat realization hv v

/-- Radial and angular directions remain orthogonal under `dexp`. -/
theorem gaussLemma_radial_orthogonal
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (input : LocalAnalyticInput (n := n) Gamma g p)
    {v w : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (horth : metricPairingAt g p v w = 0) :
    metricPairingAt g (coordinateExp (n := n) Gamma p v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) = 0 := by
  rw [gaussLemma_radial_pairing (n := n) Gamma g p input hv w, horth]

/-- Realization-layer wrapper for the radial-orthogonal Gauss lemma. -/
theorem gaussLemma_radial_orthogonal_of_realization
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (hcompat : IsMetricCompatible (n := n) Gamma g)
    (realization : LocalAnalyticRealization (n := n) Gamma g p)
    {v w : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (horth : metricPairingAt g p v w = 0) :
    metricPairingAt g (coordinateExp (n := n) Gamma p v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) = 0 := by
  simpa using
    gaussLemma_radial_orthogonal (n := n) Gamma g p
      (canonicalLocalAnalyticInput hcompat realization) hv horth

/-! ## Issue 2: Constant metric speed of the radial geodesic -/

private theorem radialGeodesicMetricVelocity_eq_fderiv_of_directionalDexp
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    (dexp : HasDirectionalDexp (n := n) Gamma p)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v t =
        (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v := by
  intro t ht
  let γ := (geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v
  have hvsource : v ∈ coordinateExpSource (n := n) Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) Gamma p hv
  have hcurveEq :
      Set.EqOn
        (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v))
        (fun τ : ℝ => Geodesic.Coordinate.statePosition n (γ τ))
        (Set.Icc (0 : ℝ) 1) := by
    intro τ hτ
    simpa [γ] using
      coordinateExp_smul_eq_geodesicFamily_position (n := n) Gamma p hvsource hτ
  have hγgeod :
      Geodesic.Coordinate.IsCoordinateGeodesicOn
        (Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
        γ
        (Set.Icc (-1 : ℝ) 1) := by
    simpa [γ] using coordinateExp_isCoordinateGeodesicOn (n := n) Gamma p hvsource
  rcases (Geodesic.Coordinate.isCoordinateGeodesicOn_iff_secondOrder
    (n := n) (Gamma := Geodesic.Coordinate.christoffelFieldOfSmooth Gamma)
    (gamma := γ) (s := Set.Icc (-1 : ℝ) 1)).mp hγgeod with ⟨hγpos, _⟩
  have hγpos' :
      HasDerivWithinAt
        (fun τ : ℝ => Geodesic.Coordinate.statePosition n (γ τ))
        (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v t)
        (Set.Icc (0 : ℝ) 1)
        t := by
    have hraw := hγpos t (by constructor <;> linarith [ht.1, ht.2])
    simpa [γ, Minimization.Coordinate.radialGeodesicMetricVelocity] using
      hraw.mono (by
        intro s hs
        exact ⟨by linarith [hs.1], hs.2⟩)
  have hline :
      HasDerivWithinAt
        (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v))
        (dexp.dexpDir (t • v) v)
        (Set.Icc (0 : ℝ) 1)
        t := by
    refine Exponential.Coordinate.hasDerivWithinAt_coordinateExp_comp
      (n := n) Gamma p dexp
      (α := fun τ : ℝ => τ • v)
      (U := fun _ : ℝ => v)
      (s := Set.Icc (0 : ℝ) 1)
      (t := t)
      ?_ ?_
    · simpa [one_smul] using
        (((hasDerivAt_id t).smul_const v).hasDerivWithinAt)
    · exact smul_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p hv ht
  have hline_fderiv :
      HasDerivWithinAt
        (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v))
        ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v)
        (Set.Icc (0 : ℝ) 1)
        t := by
    have hfd :
        HasFDerivAt (coordinateExp (n := n) Gamma p)
          (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v))
          (t • v) :=
      coordinateExpHasFDerivAtOnSource_of_smoothChristoffel (n := n) Gamma p
        (smul_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p hv ht)
    have hdexp_eq :
        dexp.dexpDir (t • v) v =
          (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v :=
      Exponential.Coordinate.dexpDir_eq_fderiv_of_hasFDerivAt
        (n := n) Gamma p dexp
        (smul_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p hv ht) hfd
    simpa [hdexp_eq] using hline
  have hradial :
      HasDerivWithinAt
        (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v))
        (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v t)
        (Set.Icc (0 : ℝ) 1)
        t := by
    exact hγpos'.congr_of_mem hcurveEq (by simpa using ht)
  have hUnique : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) 1) t :=
    (uniqueDiffOn_Icc (show (0 : ℝ) < 1 by norm_num)).uniqueDiffWithinAt (by simpa using ht)
  calc
    Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v t
      = derivWithin (fun τ : ℝ => coordinateExp (n := n) Gamma p (τ • v)) (Set.Icc (0 : ℝ) 1) t := by
          symm
          exact hradial.derivWithin hUnique
    _ = (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v := by
          exact hline_fderiv.derivWithin hUnique

/-- The radial geodesic has constant metric speed `sqrt(g(p)(v,v))` on `[0,1]`.
This is the diagonal case of the Gauss lemma: specializing `w = v` gives
the metric speed at each time `t` equals the initial speed. -/
theorem radialGeodesic_metricSpeed_eq_const_of_directionalDexp_radialPairing
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (dexp : HasDirectionalDexp (n := n) Gamma p)
    (hgauss :
      ∀ {v : Velocity n}
        (_hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
        (w : Velocity n),
        metricPairingAt g (coordinateExp (n := n) Gamma p v)
            ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) v)
            ((fderiv ℝ (coordinateExp (n := n) Gamma p) v) w) =
          metricPairingAt g p v w)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      Minimization.Coordinate.metricSpeed (n := n) g
          (Minimization.Coordinate.radialGeodesic (n := n) Gamma p v)
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v) t =
        Real.sqrt (Metric.Coordinate.quadraticForm (g p) v) := by
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
  have hvel_eq :=
    radialGeodesicMetricVelocity_eq_fderiv_of_directionalDexp
      (n := n) Gamma p dexp hv t ht'
  by_cases ht0 : t = 0
  · subst ht0
    calc
      Minimization.Coordinate.metricSpeed (n := n) g
          (Minimization.Coordinate.radialGeodesic (n := n) Gamma p v)
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v) 0
        = Real.sqrt (Metric.Coordinate.quadraticForm (g (coordinateExp (n := n) Gamma p 0)) v) := by
            simp [Minimization.Coordinate.metricSpeed, Minimization.Coordinate.radialGeodesic,
              hvel_eq, fderiv_coordinateExp_at_zero, coordinateExp_apply]
      _ = Real.sqrt (Metric.Coordinate.quadraticForm (g p) v) := by
            rw [coordinateExp_zero]
  · have ht_pos : 0 < t := lt_of_le_of_ne ht'.1 (Ne.symm ht0)
    have htv :
        t • v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source :=
      smul_mem_coordinateExpPartialHomeomorph_source (n := n) Gamma p hv ht'
    have hpair := hgauss (v := t • v) htv v
    have hquad :
        Metric.Coordinate.quadraticForm
            (g (coordinateExp (n := n) Gamma p (t • v)))
            ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v) =
          Metric.Coordinate.quadraticForm (g p) v := by
      let A :=
        Metric.Coordinate.quadraticForm
          (g (coordinateExp (n := n) Gamma p (t • v)))
          ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v)
      let B := Metric.Coordinate.quadraticForm (g p) v
      have hscaled : t * A = t * B := by
        change
          t *
              Metric.Coordinate.quadraticForm
                (g (coordinateExp (n := n) Gamma p (t • v)))
                ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v)
            =
          t * Metric.Coordinate.quadraticForm (g p) v
        have hpair' := hpair
        unfold metricPairingAt Metric.Coordinate.bilinForm at hpair'
        simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.map_smul, mul_assoc,
          mul_left_comm, mul_comm] at hpair'
        unfold Metric.Coordinate.quadraticForm
        ring_nf at hpair' ⊢
        simpa [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm] using hpair'
      have ht_nonzero : t ≠ 0 := ne_of_gt ht_pos
      have hscaled' : t⁻¹ * (t * A) = t⁻¹ * (t * B) := congrArg (fun x : ℝ => t⁻¹ * x) hscaled
      calc
        A = t⁻¹ * (t * A) := by
              field_simp [A, ht_nonzero]
        _ = t⁻¹ * (t * B) := hscaled'
        _ = B := by
              field_simp [B, ht_nonzero]
    calc
      Minimization.Coordinate.metricSpeed (n := n) g
          (Minimization.Coordinate.radialGeodesic (n := n) Gamma p v)
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v) t
        = Real.sqrt
            (Metric.Coordinate.quadraticForm
              (g (coordinateExp (n := n) Gamma p (t • v)))
              ((fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) v)) := by
                simp [Minimization.Coordinate.metricSpeed, Minimization.Coordinate.radialGeodesic,
                  hvel_eq]
      _ = Real.sqrt (Metric.Coordinate.quadraticForm (g p) v) := by rw [hquad]

/-- Input-packaged wrapper for the constant radial metric speed theorem. -/
theorem radialGeodesic_metricSpeed_eq_const_of_input
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : MetricField n)
    (p : Position n)
    (input : LocalAnalyticInput (n := n) Gamma g p)
    {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      Minimization.Coordinate.metricSpeed (n := n) g
          (Minimization.Coordinate.radialGeodesic (n := n) Gamma p v)
          (Minimization.Coordinate.radialGeodesicMetricVelocity (n := n) Gamma p v) t =
        Real.sqrt (Metric.Coordinate.quadraticForm (g p) v) := by
  exact radialGeodesic_metricSpeed_eq_const_of_directionalDexp_radialPairing
    (n := n) Gamma g p input.directionalDexp
    (fun {v} hv w => input.radialPairing hv w) hv

end Exponential.Coordinate
