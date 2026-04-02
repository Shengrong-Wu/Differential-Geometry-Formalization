import Exponential.LocalAnalyticRealization
import Exponential.GaussLemma
import Exponential.RadialGaussLemma
import Exponential.DexpContinuity
import ParallelTransport.Isometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The metric bridge isolates the Gauss/radial ingredients behind `_of_input` and
`_of_realization` wrappers used by the local minimization files. All theorems are fully proved
from their respective interface boundaries. -/

namespace Minimization.Coordinate

variable {n : ℕ}

private theorem coordinatePairingAt_comm_of_symm
    {g : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ i j, g i j = g j i)
    (X Y : Exponential.Coordinate.Velocity n) :
    ParallelTransport.coordinatePairingAt g X Y =
      ParallelTransport.coordinatePairingAt g Y X := by
  simp only [ParallelTransport.coordinatePairingAt]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsymm i j]
  ring

private theorem metricField_symm
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (x : Exponential.Coordinate.Position n) :
    ∀ i j : Fin n, data.metricField x i j = data.metricField x j i := by
  intro i j
  simpa [Exponential.Coordinate.LocalRiemannianData.metricField,
    LeviCivita.CoordinateField.tensorAt] using data.symm x i j

private theorem hasDerivWithinAt_coordinatePairing
    {g dg : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {Y Z : ℝ → Exponential.Coordinate.Velocity n}
    {y' z' : Exponential.Coordinate.Velocity n}
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
      (A' := fun j =>
        y' i * g t i j * Z t j + Y t i * dg t i j * Z t j + Y t i * g t i j * z' j) ?_
    intro j hj
    have hYi : HasDerivWithinAt (fun τ => Y τ i) (y' i) s t := by
      simpa [Function.comp] using
        (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) i :
            Exponential.Coordinate.Velocity n →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivWithinAt t hY)
    have hZj : HasDerivWithinAt (fun τ => Z τ j) (z' j) s t := by
      simpa [Function.comp] using
        (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) j :
            Exponential.Coordinate.Velocity n →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivWithinAt t hZ)
    have hgij : HasDerivWithinAt (fun τ => g τ i j) (dg t i j) s t := hg i j
    convert (hYi.mul hgij).mul hZj using 1 <;> simp <;> ring_nf
  simpa [ParallelTransport.coordinatePairing, ParallelTransport.coordinatePairingAt,
    Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm] using hsum

private theorem quadraticForm_add_smul
    {g : Metric.Coordinate.Tensor2 n}
    (hsymm : Metric.Coordinate.IsSymmetric g)
    (u w : Exponential.Coordinate.Velocity n) (c : ℝ) :
    Metric.Coordinate.quadraticForm g (u + c • w) =
      Metric.Coordinate.quadraticForm g u +
        2 * c * Metric.Coordinate.bilinForm g u w +
        c ^ 2 * Metric.Coordinate.quadraticForm g w := by
  calc
    Metric.Coordinate.quadraticForm g (u + c • w)
      = Metric.Coordinate.quadraticForm g u +
          c * Metric.Coordinate.bilinForm g u w +
          c * Metric.Coordinate.bilinForm g w u +
          c ^ 2 * Metric.Coordinate.quadraticForm g w := by
            simp [Metric.Coordinate.quadraticForm, Metric.Coordinate.bilinForm,
              Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, add_mul, mul_add,
              smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
            ring_nf
    _ = Metric.Coordinate.quadraticForm g u +
          2 * c * Metric.Coordinate.bilinForm g u w +
          c ^ 2 * Metric.Coordinate.quadraticForm g w := by
            rw [Metric.Coordinate.bilinForm_comm hsymm w u]
            ring

private theorem metric_bilin_sq_le
    {g : Metric.Coordinate.Tensor2 n}
    (hg : Metric.Coordinate.IsPositiveDefinite g)
    (u w : Exponential.Coordinate.Velocity n) :
    (Metric.Coordinate.bilinForm g u w) ^ 2 ≤
      Metric.Coordinate.quadraticForm g u * Metric.Coordinate.quadraticForm g w := by
  by_cases hw : w = 0
  · simp [hw, Metric.Coordinate.bilinForm, Metric.Coordinate.quadraticForm]
  have hwpos : 0 < Metric.Coordinate.quadraticForm g w := hg.2 w hw
  let c : ℝ := -(Metric.Coordinate.bilinForm g u w) / Metric.Coordinate.quadraticForm g w
  have hnonneg :
      0 ≤ Metric.Coordinate.quadraticForm g (u + c • w) :=
    Metric.Coordinate.quadraticForm_nonneg hg (u + c • w)
  have hmain :
      0 ≤ Metric.Coordinate.quadraticForm g u *
        Metric.Coordinate.quadraticForm g w -
          (Metric.Coordinate.bilinForm g u w) ^ 2 := by
    have htmp := hnonneg
    rw [quadraticForm_add_smul hg.1 u w c] at htmp
    have hwne : Metric.Coordinate.quadraticForm g w ≠ 0 := ne_of_gt hwpos
    dsimp [c] at htmp
    field_simp [hwne] at htmp
    nlinarith [htmp, hwpos]
  nlinarith [hmain]

private theorem metric_bilin_abs_le
    {g : Metric.Coordinate.Tensor2 n}
    (hg : Metric.Coordinate.IsPositiveDefinite g)
    (u w : Exponential.Coordinate.Velocity n) :
    |Metric.Coordinate.bilinForm g u w| ≤
      Real.sqrt (Metric.Coordinate.quadraticForm g u) *
        Real.sqrt (Metric.Coordinate.quadraticForm g w) := by
  have hu_nonneg : 0 ≤ Metric.Coordinate.quadraticForm g u :=
    Metric.Coordinate.quadraticForm_nonneg hg u
  have hw_nonneg : 0 ≤ Metric.Coordinate.quadraticForm g w :=
    Metric.Coordinate.quadraticForm_nonneg hg w
  have hsq :
      |Metric.Coordinate.bilinForm g u w| ^ 2 ≤
        (Real.sqrt (Metric.Coordinate.quadraticForm g u) *
          Real.sqrt (Metric.Coordinate.quadraticForm g w)) ^ 2 := by
    calc
      |Metric.Coordinate.bilinForm g u w| ^ 2
        = (Metric.Coordinate.bilinForm g u w) ^ 2 := by simp [sq_abs]
      _ ≤ Metric.Coordinate.quadraticForm g u * Metric.Coordinate.quadraticForm g w :=
          metric_bilin_sq_le hg u w
      _ = (Real.sqrt (Metric.Coordinate.quadraticForm g u) *
            Real.sqrt (Metric.Coordinate.quadraticForm g w)) ^ 2 := by
            calc
              Metric.Coordinate.quadraticForm g u * Metric.Coordinate.quadraticForm g w
                = (Real.sqrt (Metric.Coordinate.quadraticForm g u)) ^ 2 *
                    (Real.sqrt (Metric.Coordinate.quadraticForm g w)) ^ 2 := by
                      rw [Real.sq_sqrt hu_nonneg, Real.sq_sqrt hw_nonneg]
              _ = (Real.sqrt (Metric.Coordinate.quadraticForm g u) *
                    Real.sqrt (Metric.Coordinate.quadraticForm g w)) ^ 2 := by
                      ring
  have hright_nonneg :
      0 ≤ Real.sqrt (Metric.Coordinate.quadraticForm g u) *
        Real.sqrt (Metric.Coordinate.quadraticForm g w) := by
    positivity
  exact sq_le_sq₀ (abs_nonneg _) hright_nonneg |>.mp hsq

private theorem hasDerivAt_baseMetricQuadratic
    {g : Metric.Coordinate.Tensor2 n}
    (hsymm : Metric.Coordinate.IsSymmetric g)
    {u : ℝ → Exponential.Coordinate.Velocity n}
    {u' : Exponential.Coordinate.Velocity n}
    {t : ℝ}
    (hu : HasDerivAt u u' t) :
    HasDerivAt
      (fun s : ℝ => Metric.Coordinate.quadraticForm g (u s))
      (2 * Metric.Coordinate.bilinForm g (u t) u')
      t := by
  let G : ℝ → Matrix (Fin n) (Fin n) ℝ := fun _ => g
  have hG :
      ∀ i j, HasDerivWithinAt (fun τ => G τ i j) (0 : ℝ) Set.univ t := by
    intro i j
    have hconst : HasDerivWithinAt (fun τ : ℝ => g i j) (0 : ℝ) Set.univ t :=
      (hasDerivAt_const t (g i j)).hasDerivWithinAt
    simpa [G] using hconst
  have hpair_raw :
      HasDerivAt
        (fun s : ℝ => ParallelTransport.coordinatePairing G s (u s) (u s))
        (ParallelTransport.coordinatePairingAt (0 : Matrix (Fin n) (Fin n) ℝ) (u t) (u t) +
          ParallelTransport.coordinatePairingAt g u' (u t) +
          ParallelTransport.coordinatePairingAt g (u t) u')
        t := by
    simpa [G] using
      (hasDerivWithinAt_coordinatePairing (g := G) (dg := fun _ => 0)
        hG hu.hasDerivWithinAt hu.hasDerivWithinAt).hasDerivAt
  have hpair :
      HasDerivAt
        (fun s : ℝ => ParallelTransport.coordinatePairing G s (u s) (u s))
        (ParallelTransport.coordinatePairingAt g u' (u t) +
          ParallelTransport.coordinatePairingAt g (u t) u')
        t := by
    convert hpair_raw using 1
    simp [ParallelTransport.coordinatePairingAt]
  have hcomm :
      ParallelTransport.coordinatePairingAt g u' (u t) =
        ParallelTransport.coordinatePairingAt g (u t) u' := by
    exact coordinatePairingAt_comm_of_symm hsymm u' (u t)
  have hvalue :
      (ParallelTransport.coordinatePairingAt g u' (u t) +
        ParallelTransport.coordinatePairingAt g (u t) u') =
          2 * Metric.Coordinate.bilinForm g (u t) u' := by
    rw [hcomm]
    simp [ParallelTransport.coordinatePairingAt, Metric.Coordinate.bilinForm]
    ring
  have hquad :
      HasDerivAt
        (fun s : ℝ => Metric.Coordinate.quadraticForm g (u s))
        (ParallelTransport.coordinatePairingAt g u' (u t) +
          ParallelTransport.coordinatePairingAt g (u t) u')
        t := by
    exact hpair.congr_of_eventuallyEq <|
      Filter.Eventually.of_forall fun s => by
        change Metric.Coordinate.quadraticForm g (u s) =
          ParallelTransport.coordinatePairingAt g (u s) (u s)
        simp [Metric.Coordinate.quadraticForm, ParallelTransport.coordinatePairingAt]
  simpa [Metric.Coordinate.bilinForm] using hquad.congr_deriv hvalue

private theorem quadraticForm_le_card_mul_coordinateCoeffBound
    (g : Metric.Coordinate.Tensor2 n)
    (z : Exponential.Coordinate.Velocity n) :
    Metric.Coordinate.quadraticForm g z ≤
      ((Fintype.card (Fin n) : ℝ) * ParallelTransport.coordinateCoeffBound g) * ‖z‖ ^ 2 := by
  have hdot :
      |dotProduct z (Matrix.mulVec g z)| ≤
        (Fintype.card (Fin n) : ℝ) * (‖z‖ * ‖Matrix.mulVec g z‖) := by
    calc
      |dotProduct z (Matrix.mulVec g z)|
        = |∑ i : Fin n, z i * Matrix.mulVec g z i| := by
            simp [dotProduct]
      _ ≤ ∑ i : Fin n, |z i * Matrix.mulVec g z i| := by
            simpa using
              (Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun i : Fin n => z i * Matrix.mulVec g z i))
      _ = ∑ i : Fin n, |z i| * |Matrix.mulVec g z i| := by
            simp [abs_mul]
      _ ≤ ∑ i : Fin n, ‖z‖ * ‖Matrix.mulVec g z‖ := by
            refine Finset.sum_le_sum fun i _ => ?_
            gcongr
            · simpa [Pi.norm_def, Real.norm_eq_abs] using
                (show (‖z i‖₊ : ℝ) ≤ ‖z‖₊ from
                  Finset.le_sup (s := Finset.univ) (f := fun b : Fin n => ‖z b‖₊)
                    (Finset.mem_univ i))
            · simpa [Pi.norm_def, Real.norm_eq_abs] using
                (show (‖Matrix.mulVec g z i‖₊ : ℝ) ≤ ‖Matrix.mulVec g z‖₊ from
                  Finset.le_sup (s := Finset.univ) (f := fun b : Fin n => ‖Matrix.mulVec g z b‖₊)
                    (Finset.mem_univ i))
      _ = (Fintype.card (Fin n) : ℝ) * (‖z‖ * ‖Matrix.mulVec g z‖) := by
            simp [Finset.card_univ]
  calc
    Metric.Coordinate.quadraticForm g z
      = ParallelTransport.coordinatePairingAt g z z := by
          simp [Metric.Coordinate.quadraticForm, ParallelTransport.coordinatePairingAt]
    _ = dotProduct z (Matrix.mulVec g z) := by
          exact ParallelTransport.coordinatePairingAt_eq_dotProduct_mulVec g z z
    _ ≤ |dotProduct z (Matrix.mulVec g z)| := le_abs_self _
    _ ≤ (Fintype.card (Fin n) : ℝ) * (‖z‖ * ‖Matrix.mulVec g z‖) := hdot
    _ ≤ (Fintype.card (Fin n) : ℝ) * (‖z‖ *
          (ParallelTransport.coordinateCoeffBound g * ‖z‖)) := by
            gcongr
            exact ParallelTransport.norm_mulVec_le_coordinateCoeffBound g z
    _ = ((Fintype.card (Fin n) : ℝ) * ParallelTransport.coordinateCoeffBound g) * ‖z‖ ^ 2 := by
          ring

private theorem metricSpeed_intervalIntegrable_of_kinematics
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hkin : HasNormalCoordinateKinematics (n := n) data.Gamma p γ Tγ Uγ 0 1) :
    IntervalIntegrable
      (fun t => metricSpeed (n := n) data.metricField γ Tγ t)
      MeasureTheory.volume 0 1 := by
  let dexp := Exponential.Coordinate.hasDirectionalDexp_of_smoothChristoffel
    (n := n) data.Gamma p
  let u := normalCoordinateCurve (n := n) data.Gamma p γ
  let expMap := Exponential.Coordinate.coordinateExp (n := n) data.Gamma p
  let AField : ℝ → Exponential.Coordinate.Velocity n →L[ℝ] Exponential.Coordinate.Velocity n :=
    fun t => fderiv ℝ expMap (u t)
  let zField : ℝ → Exponential.Coordinate.Velocity n := fun t => AField t (Uγ t)
  have hab : (0 : ℝ) < 1 := by norm_num
  have hγ_cont :
      ContinuousOn γ (Set.Icc (0 : ℝ) 1) := by
    exact HasDerivWithinAt.continuousOn fun t ht => by
      simpa using hkin.curveVelocity t ht
  have hu_cont :
      ContinuousOn u (Set.Icc (0 : ℝ) 1) := by
    exact HasDerivWithinAt.continuousOn fun t ht => by
      simpa [u] using hkin.normalVelocity t ht
  have hu_source :
      Set.MapsTo u (Set.Icc (0 : ℝ) 1)
        (Exponential.Coordinate.coordinateExpSource (n := n) data.Gamma p) := by
    intro t ht
    exact Exponential.Coordinate.coordinateExpPartialHomeomorph_source_subset_coordinateExpSource
      (n := n) data.Gamma p
      (hkin.normalCoordinateCurve_mem_coordinateExpPartialHomeomorph_source ht)
  have hA_cont :
      ContinuousOn AField (Set.Icc (0 : ℝ) 1) := by
    exact (Exponential.Coordinate.continuousOn_fderiv_coordinateExp
      (n := n) data.Gamma p).comp hu_cont hu_source
  have hA_norm_cont :
      ContinuousOn (fun t : ℝ => ‖AField t‖) (Set.Icc (0 : ℝ) 1) := by
    exact continuous_norm.continuousOn.comp hA_cont (by
      intro t ht
      exact Set.mem_univ _)
  obtain ⟨CA0, hCA0⟩ := isCompact_Icc.exists_bound_of_continuousOn hA_norm_cont
  let CA : ℝ := max CA0 0
  have hCA_nonneg : 0 ≤ CA := by
    dsimp [CA]
    exact le_max_right _ _
  have hCA :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖AField t‖ ≤ CA := by
    intro t ht
    have ht0 : ‖AField t‖ ≤ CA0 := by
      simpa [abs_of_nonneg (norm_nonneg _)] using hCA0 t ht
    exact le_trans ht0 (le_max_left _ _)
  have hMetricCoeff_cont :
      ∀ i j : Fin n,
        ContinuousOn (fun t : ℝ => data.metricField (γ t) i j) (Set.Icc (0 : ℝ) 1) := by
    intro i j
    simpa [Exponential.Coordinate.LocalRiemannianData.metricField] using
      ((data.gSmooth.smooth' i j).continuous.continuousOn.comp hγ_cont
        (by
          intro t ht
          exact Set.mem_univ _))
  have hCoeff_cont :
      ContinuousOn
        (fun t : ℝ => ParallelTransport.coordinateCoeffBound (data.metricField (γ t)))
        (Set.Icc (0 : ℝ) 1) := by
    refine continuousOn_finset_sum _ ?_
    intro i hi
    refine continuousOn_finset_sum _ ?_
    intro j hj
    simpa [ParallelTransport.coordinateCoeffBound] using (hMetricCoeff_cont i j).abs
  obtain ⟨CG0, hCG0⟩ := isCompact_Icc.exists_bound_of_continuousOn hCoeff_cont
  let CG : ℝ := max CG0 0
  have hCG_nonneg : 0 ≤ CG := by
    dsimp [CG]
    exact le_max_right _ _
  have hCG :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ParallelTransport.coordinateCoeffBound (data.metricField (γ t)) ≤ CG := by
    intro t ht
    have ht0 :
        ParallelTransport.coordinateCoeffBound (data.metricField (γ t)) ≤ CG0 := by
      simpa [abs_of_nonneg
        (ParallelTransport.coordinateCoeffBound_nonneg (data.metricField (γ t)))] using hCG0 t ht
    exact le_trans ht0 (le_max_left _ _)
  have hz_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖zField t‖ ≤ CA * ‖Uγ t‖ := by
    intro t ht
    calc
      ‖zField t‖ = ‖AField t (Uγ t)‖ := rfl
      _ ≤ ‖AField t‖ * ‖Uγ t‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ CA * ‖Uγ t‖ := by
          gcongr
          exact hCA t ht
  have hspeed_bound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        metricSpeed (n := n) data.metricField γ Tγ t ≤
          (Real.sqrt (((Fintype.card (Fin n) : ℝ) * CG)) * CA) * ‖Uγ t‖ := by
    intro t ht
    have hu_mem :
        u t ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) data.Gamma p).source :=
      hkin.normalCoordinateCurve_mem_coordinateExpPartialHomeomorph_source ht
    have hu_mem_source :
        u t ∈ Exponential.Coordinate.coordinateExpSource (n := n) data.Gamma p :=
      Exponential.Coordinate.coordinateExpPartialHomeomorph_source_subset_coordinateExpSource
        (n := n) data.Gamma p hu_mem
    have hfd :
        HasFDerivAt expMap (AField t) (u t) := by
      change HasFDerivAt expMap (fderiv ℝ expMap (u t)) (u t)
      simpa [expMap] using
        Exponential.Coordinate.hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source
          (n := n) data.Gamma p hu_mem
    have hdexp :
        dexp.dexpDir (u t) (Uγ t) = zField t := by
      simpa [dexp, AField, zField] using
        Exponential.Coordinate.dexpDir_eq_fderiv_of_hasFDerivAt
          (n := n) data.Gamma p dexp hu_mem hfd (w := Uγ t)
    have hTγ :
        Tγ t = zField t := by
      simpa [zField, hdexp] using
        curveVelocity_eq_dexpDir_apply_normalVelocity
          (n := n) data.Gamma p dexp γ Tγ Uγ hab hkin t ht
    have hzsq :
        ‖zField t‖ ^ 2 ≤ (CA * ‖Uγ t‖) ^ 2 := by
      have hCAU_nonneg : 0 ≤ CA * ‖Uγ t‖ := by
        exact mul_nonneg hCA_nonneg (norm_nonneg _)
      exact (sq_le_sq₀ (norm_nonneg _) hCAU_nonneg).2 (hz_bound t ht)
    calc
      metricSpeed (n := n) data.metricField γ Tγ t
        = Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField (γ t)) (zField t)) := by
            rw [metricSpeed, hTγ]
      _ ≤ Real.sqrt
            (((Fintype.card (Fin n) : ℝ) *
                ParallelTransport.coordinateCoeffBound (data.metricField (γ t))) *
              ‖zField t‖ ^ 2) := by
            gcongr
            exact quadraticForm_le_card_mul_coordinateCoeffBound
              (data.metricField (γ t)) (zField t)
      _ ≤ Real.sqrt (((Fintype.card (Fin n) : ℝ) * CG) * (CA * ‖Uγ t‖) ^ 2) := by
            have hcard_nonneg : 0 ≤ (Fintype.card (Fin n) : ℝ) := by positivity
            have hcoeff_nonneg :
                0 ≤ ParallelTransport.coordinateCoeffBound (data.metricField (γ t)) :=
              ParallelTransport.coordinateCoeffBound_nonneg (data.metricField (γ t))
            have hmul₁ :
                (((Fintype.card (Fin n) : ℝ) *
                    ParallelTransport.coordinateCoeffBound (data.metricField (γ t))) *
                  ‖zField t‖ ^ 2) ≤
                  (((Fintype.card (Fin n) : ℝ) *
                      ParallelTransport.coordinateCoeffBound (data.metricField (γ t))) *
                    (CA * ‖Uγ t‖) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hzsq
                (mul_nonneg hcard_nonneg hcoeff_nonneg)
            have hmul₂ :
                (((Fintype.card (Fin n) : ℝ) *
                    ParallelTransport.coordinateCoeffBound (data.metricField (γ t))) *
                  (CA * ‖Uγ t‖) ^ 2) ≤
                  (((Fintype.card (Fin n) : ℝ) * CG) * (CA * ‖Uγ t‖) ^ 2) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hCG t ht) hcard_nonneg)
                (sq_nonneg _)
            exact Real.sqrt_le_sqrt (le_trans hmul₁ hmul₂)
      _ = (Real.sqrt (((Fintype.card (Fin n) : ℝ) * CG)) * CA) * ‖Uγ t‖ := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
              abs_of_nonneg (mul_nonneg hCA_nonneg (norm_nonneg _))]
            ring
  have hU_norm_int :
      IntervalIntegrable (fun t : ℝ => ‖Uγ t‖) MeasureTheory.volume 0 1 :=
    hkin.displacement.integrable.norm
  have hdom_int :
      IntervalIntegrable
        (fun t : ℝ => (Real.sqrt (((Fintype.card (Fin n) : ℝ) * CG)) * CA) * ‖Uγ t‖)
        MeasureTheory.volume 0 1 := by
    simpa [mul_assoc] using hU_norm_int.const_mul
      (Real.sqrt (((Fintype.card (Fin n) : ℝ) * CG)) * CA)
  have hA_meas :
      MeasureTheory.AEStronglyMeasurable AField
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact (hA_cont.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hU_meas :
      MeasureTheory.AEStronglyMeasurable Uγ
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hkin.displacement.integrable.aestronglyMeasurable
  let evalCLM :
      (Exponential.Coordinate.Velocity n →L[ℝ] Exponential.Coordinate.Velocity n) →L[ℝ]
        Exponential.Coordinate.Velocity n →L[ℝ] Exponential.Coordinate.Velocity n :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ (Exponential.Coordinate.Velocity n))
  have hz_meas :
      MeasureTheory.AEStronglyMeasurable zField
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    simpa [zField, evalCLM] using evalCLM.aestronglyMeasurable_comp₂ hA_meas hU_meas
  have hzcoord_meas :
      ∀ i : Fin n,
        MeasureTheory.AEStronglyMeasurable (fun t : ℝ => zField t i)
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro i
    simpa [Function.comp] using
      (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) i :
          Exponential.Coordinate.Velocity n →L[ℝ] ℝ)).continuous.comp_aestronglyMeasurable hz_meas)
  have hgij_meas :
      ∀ i j : Fin n,
        MeasureTheory.AEStronglyMeasurable (fun t : ℝ => data.metricField (γ t) i j)
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro i j
    exact (hMetricCoeff_cont i j).mono Set.Ioc_subset_Icc_self |>.aestronglyMeasurable
      measurableSet_Ioc
  have hspeed'_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ =>
          Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField (γ t)) (zField t)))
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hsq_meas_raw :
        MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ =>
            ∑ i : Fin n, ∑ j : Fin n, zField t i * data.metricField (γ t) i j * zField t j)
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      have hinner :
          ∀ i : Fin n,
            MeasureTheory.AEStronglyMeasurable
              (fun t : ℝ => ∑ j : Fin n, zField t i * data.metricField (γ t) i j * zField t j)
              (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        intro i
        have hinner' :
            MeasureTheory.AEStronglyMeasurable
              (∑ j : Fin n, fun t : ℝ => zField t i * data.metricField (γ t) i j * zField t j)
              (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
          exact
            (Finset.aestronglyMeasurable_sum
              (s := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n => fun t : ℝ =>
                zField t i * data.metricField (γ t) i j * zField t j)
              (fun j _ => ((hzcoord_meas i).mul (hgij_meas i j)).mul (hzcoord_meas j)))
        refine hinner'.congr <| Filter.Eventually.of_forall fun t => ?_
        change
          (∑ j : Fin n, fun t : ℝ => zField t i * data.metricField (γ t) i j * zField t j) t =
            ∑ j : Fin n, zField t i * data.metricField (γ t) i j * zField t j
        simp
      have houter' :
          MeasureTheory.AEStronglyMeasurable
            (∑ i : Fin n, fun t : ℝ =>
              ∑ j : Fin n, zField t i * data.metricField (γ t) i j * zField t j)
            (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
        exact
          (Finset.aestronglyMeasurable_sum
            (s := (Finset.univ : Finset (Fin n)))
            (f := fun i : Fin n => fun t : ℝ =>
              ∑ j : Fin n, zField t i * data.metricField (γ t) i j * zField t j)
            (fun i _ => hinner i))
      refine houter'.congr <| Filter.Eventually.of_forall fun t => ?_
      change
        (∑ i : Fin n, fun t : ℝ =>
          ∑ j : Fin n, zField t i * data.metricField (γ t) i j * zField t j) t =
          ∑ i : Fin n, ∑ j : Fin n, zField t i * data.metricField (γ t) i j * zField t j
      simp
    have hsq_meas :
        MeasureTheory.AEStronglyMeasurable
          (fun t : ℝ => Metric.Coordinate.quadraticForm (data.metricField (γ t)) (zField t))
          (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      simpa [Metric.Coordinate.quadraticForm] using hsq_meas_raw
    simpa using Real.continuous_sqrt.comp_aestronglyMeasurable hsq_meas
  have hspeed_eq :
      (fun t : ℝ =>
        metricSpeed (n := n) data.metricField γ Tγ t) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun t : ℝ =>
          Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField (γ t)) (zField t))) := by
    change
      ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1),
        metricSpeed (n := n) data.metricField γ Tγ t =
          Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField (γ t)) (zField t))
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 <|
      Filter.Eventually.of_forall fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hu_mem :
          u t ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) data.Gamma p).source :=
        hkin.normalCoordinateCurve_mem_coordinateExpPartialHomeomorph_source ht'
      have hfd :
          HasFDerivAt expMap (AField t) (u t) := by
        change HasFDerivAt expMap (fderiv ℝ expMap (u t)) (u t)
        simpa [expMap] using
          Exponential.Coordinate.hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source
            (n := n) data.Gamma p hu_mem
      have hdexp :
          dexp.dexpDir (u t) (Uγ t) = zField t := by
        simpa [dexp, AField, zField] using
          Exponential.Coordinate.dexpDir_eq_fderiv_of_hasFDerivAt
            (n := n) data.Gamma p dexp hu_mem hfd (w := Uγ t)
      have hTγ :
          Tγ t = zField t := by
        simpa [zField, hdexp] using
          curveVelocity_eq_dexpDir_apply_normalVelocity
            (n := n) data.Gamma p dexp γ Tγ Uγ hab hkin t ht'
      simp [metricSpeed, hTγ]
  have hspeed_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => metricSpeed (n := n) data.metricField γ Tγ t)
        (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hspeed'_meas.congr hspeed_eq.symm
  have hspeed_meas_uIoc :
      MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => metricSpeed (n := n) data.metricField γ Tγ t)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hspeed_meas
  refine IntervalIntegrable.mono_fun' hdom_int hspeed_meas_uIoc ?_
  change
    ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1),
      ‖metricSpeed (n := n) data.metricField γ Tγ t‖ ≤
        (Real.sqrt (((Fintype.card (Fin n) : ℝ) * CG)) * CA) * ‖Uγ t‖
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2 <|
    Filter.Eventually.of_forall fun t ht => by
    have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hs : metricSpeed (n := n) data.metricField γ Tγ t ≤
        (Real.sqrt (((Fintype.card (Fin n) : ℝ) * CG)) * CA) * ‖Uγ t‖ :=
      hspeed_bound t ht'
    rw [Real.norm_eq_abs, abs_of_nonneg (metricSpeed_nonneg (n := n) data.metricField γ Tγ t)]
    exact hs

/-- Exported metric bridge for comparison curves via input package. -/
theorem metricNormalRadius_le_metricCurveLength_of_kinematics_of_input
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      metricCurveLength (n := n) g γ 0 1 Tγ :=
  input.radius_le_metricLength hv γ Tγ Uγ hγ hkin

/-- Realization-layer wrapper for the metric bridge on comparison curves. -/
theorem metricNormalRadius_le_metricCurveLength_of_kinematics_of_realization
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) Gamma g)
    (realization : Exponential.Coordinate.LocalAnalyticRealization (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      metricCurveLength (n := n) g γ 0 1 Tγ :=
  metricNormalRadius_le_metricCurveLength_of_kinematics_of_input
    (n := n) Gamma g p
    (Exponential.Coordinate.canonicalLocalAnalyticInput hcompat realization)
    hv γ Tγ Uγ hγ hkin

/-- Exported metric bridge for comparison curves. -/
theorem metricNormalRadius_le_metricCurveLength_of_kinematics
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      metricCurveLength (n := n) g γ 0 1 Tγ :=
  metricNormalRadius_le_metricCurveLength_of_kinematics_of_input
    (n := n) Gamma g p input hv γ Tγ Uγ hγ hkin

theorem radialGeodesic_metricLength_eq_metricNormalRadius_of_metricSpeed_eq
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (hspeed :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        metricSpeed (n := n) g
            (radialGeodesic (n := n) Gamma p v)
            (radialGeodesicMetricVelocity (n := n) Gamma p v) t =
          Real.sqrt (Metric.Coordinate.quadraticForm (g p) v)) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) =
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
  calc
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v)
      = Real.sqrt (Metric.Coordinate.quadraticForm (g p) v) := by
          exact metricCurveLength_eq_const_of_unitInterval (n := n) g
            (radialGeodesic (n := n) Gamma p v)
            (radialGeodesicMetricVelocity (n := n) Gamma p v)
            (Real.sqrt (Metric.Coordinate.quadraticForm (g p) v)) hspeed
    _ = metricNormalRadius (n := n) g Gamma p
          (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
          symm
          exact metricNormalRadius_exp (n := n) g Gamma p hv

theorem radialGeodesic_metricLength_le_metricNormalRadius_of_metricSpeed_eq
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (hspeed :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        metricSpeed (n := n) g
            (radialGeodesic (n := n) Gamma p v)
            (radialGeodesicMetricVelocity (n := n) Gamma p v) t =
          Real.sqrt (Metric.Coordinate.quadraticForm (g p) v)) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
  le_of_eq <|
    radialGeodesic_metricLength_eq_metricNormalRadius_of_metricSpeed_eq
      (n := n) g Gamma p hv hspeed

/-- Metric radial-length identity exported for the minimization layer. -/
theorem radialGeodesic_metricLength_le_metricNormalRadius_of_input
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
  radialGeodesic_metricLength_le_metricNormalRadius_of_metricSpeed_eq
    (n := n) g Gamma p hv
    (Exponential.Coordinate.radialGeodesic_metricSpeed_eq_const_of_input
      (n := n) Gamma g p input hv)

/-- Realization-layer wrapper for the radial metric-length comparison. -/
theorem radialGeodesic_metricLength_le_metricNormalRadius_of_realization
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) Gamma g)
    (realization : Exponential.Coordinate.LocalAnalyticRealization (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
  radialGeodesic_metricLength_le_metricNormalRadius_of_input
    (n := n) g Gamma p
    (Exponential.Coordinate.canonicalLocalAnalyticInput hcompat realization) hv

/-- Metric radial-length identity exported for the minimization layer. -/
theorem radialGeodesic_metricLength_le_metricNormalRadius
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (input : Exponential.Coordinate.LocalAnalyticInput (n := n) Gamma g p)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    metricCurveLength (n := n) g
        (radialGeodesic (n := n) Gamma p v) 0 1
        (radialGeodesicMetricVelocity (n := n) Gamma p v) ≤
      metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) :=
  radialGeodesic_metricLength_le_metricNormalRadius_of_input
    (n := n) g Gamma p input hv

/-! ## Issue 3: Owner theorem for radius ≤ metric curve length -/

private theorem metricNormalRadiusEps_sub_le_metricCurveLength_of_kinematics
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) data.Gamma data.metricField)
    (ε : ℝ) (hε : 0 < ε)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hkin : HasNormalCoordinateKinematics (n := n) data.Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ 1) -
        metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ 0) ≤
      metricCurveLength (n := n) data.metricField γ 0 1 Tγ := by
  let dexp := Exponential.Coordinate.hasDirectionalDexp_of_smoothChristoffel
    (n := n) data.Gamma p
  let u := normalCoordinateCurve (n := n) data.Gamma p γ
  let expMap := Exponential.Coordinate.coordinateExp (n := n) data.Gamma p
  let rε : ℝ → ℝ := fun t =>
    metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ t)
  have hab : (0 : ℝ) < 1 := by norm_num
  have hu_cont :
      ContinuousOn u (Set.Icc (0 : ℝ) 1) := by
    exact HasDerivWithinAt.continuousOn fun t ht => by
      simpa [u] using hkin.normalVelocity t ht
  have hu_coord_cont :
      ∀ i : Fin n, ContinuousOn (fun t : ℝ => u t i) (Set.Icc (0 : ℝ) 1) := by
    intro i
    exact
      (((ContinuousLinearMap.proj (R := ℝ) (ι := Fin n) (φ := fun _ : Fin n => ℝ) i :
          Exponential.Coordinate.Velocity n →L[ℝ] ℝ)).continuous.continuousOn.comp hu_cont
        (by
          intro t ht
          exact Set.mem_univ _))
  have hquad_cont :
      ContinuousOn
        (fun t : ℝ => Metric.Coordinate.quadraticForm (data.metricField p) (u t))
        (Set.Icc (0 : ℝ) 1) := by
    unfold Metric.Coordinate.quadraticForm
    refine continuousOn_finset_sum _ ?_
    intro i hi
    refine continuousOn_finset_sum _ ?_
    intro j hj
    exact ((hu_coord_cont i).mul continuousOn_const).mul (hu_coord_cont j)
  have hr_cont :
      ContinuousOn rε (Set.Icc (0 : ℝ) 1) := by
    have harg_cont :
        ContinuousOn
          (fun t : ℝ => ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u t))
          (Set.Icc (0 : ℝ) 1) := by
      exact continuousOn_const.add hquad_cont
    simpa [rε, metricNormalRadiusEps, u] using
      (Real.continuous_sqrt.continuousOn.comp harg_cont (by
        intro t ht
        exact Set.mem_univ _))
  have hspeed_int :
      IntervalIntegrable
        (fun t => metricSpeed (n := n) data.metricField γ Tγ t)
        MeasureTheory.volume 0 1 :=
    metricSpeed_intervalIntegrable_of_kinematics (n := n) data p γ Tγ Uγ hkin
  have hspeed_integrableOn :
      MeasureTheory.IntegrableOn
        (fun t => metricSpeed (n := n) data.metricField γ Tγ t)
        (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        (μ := MeasureTheory.volume)
        (f := fun t => metricSpeed (n := n) data.metricField γ Tγ t)
        (by norm_num)).1 hspeed_int
  have hradialPairing :
      ∀ {w : Exponential.Coordinate.Velocity n}
        (hw : w ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph
          (n := n) data.Gamma p).source)
        (z : Exponential.Coordinate.Velocity n),
        Exponential.Coordinate.metricPairingAt data.metricField
            (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p w)
            ((fderiv ℝ (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p) w) w)
            ((fderiv ℝ (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p) w) z) =
          Exponential.Coordinate.metricPairingAt data.metricField p w z :=
    Exponential.Coordinate.radialPairing_field_of_hasRadialVariationInterchange
      (n := n) data.Gamma data.metricField p
      (Exponential.Coordinate.hasRadialVariationInterchange_of_localRiemannianData
        (n := n) data p hcompat)
  have hderiv :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt rε
          (Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x) /
            Real.sqrt
              (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)))
          (Set.Ioi x) x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hu_at : HasDerivAt u (Uγ x) x := by
      exact (hkin.normalVelocity x hxIcc).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
    have hquad_at :
        HasDerivAt
          (fun s : ℝ => Metric.Coordinate.quadraticForm (data.metricField p) (u s))
          (2 * Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x))
          x :=
      hasDerivAt_baseMetricQuadratic
        (n := n) (metricField_symm (n := n) data p) hu_at
    have hq_nonneg :
        0 ≤ Metric.Coordinate.quadraticForm (data.metricField p) (u x) :=
      Metric.Coordinate.quadraticForm_nonneg (data.metricField_posDef p) (u x)
    have harg_pos :
        0 < ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x) := by
      nlinarith [sq_pos_of_pos hε, hq_nonneg]
    have hsqrt :
        HasDerivAt
          (fun s : ℝ =>
            Real.sqrt (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u s)))
          ((2 * Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x)) /
            (2 * Real.sqrt
              (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x))))
          x := by
      simpa using ((hasDerivAt_const x (ε ^ 2)).add hquad_at).sqrt (ne_of_gt harg_pos)
    have hsqrt' :
        HasDerivAt
          (fun s : ℝ =>
            Real.sqrt (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u s)))
          (Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x) /
            Real.sqrt
              (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)))
          x := by
      have hsqrt_ne :
          Real.sqrt (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)) ≠ 0 :=
        (Real.sqrt_pos.2 harg_pos).ne'
      have hvalue :
          (2 * Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x)) /
              (2 * Real.sqrt
                (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x))) =
            Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x) /
              Real.sqrt
                (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)) := by
        field_simp [hsqrt_ne]
      exact hsqrt.congr_deriv hvalue
    simpa [rε, metricNormalRadiusEps, u] using hsqrt'.hasDerivWithinAt
  have hderiv_le :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x) /
            Real.sqrt
              (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)) ≤
          metricSpeed (n := n) data.metricField γ Tγ x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
    have hu_mem :
        u x ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) data.Gamma p).source :=
      hkin.normalCoordinateCurve_mem_coordinateExpPartialHomeomorph_source hxIcc
    have hfd :
        HasFDerivAt expMap (fderiv ℝ expMap (u x)) (u x) := by
      change HasFDerivAt expMap (fderiv ℝ expMap (u x)) (u x)
      simpa [expMap] using
        Exponential.Coordinate.hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source
          (n := n) data.Gamma p hu_mem
    have hdexp :
        dexp.dexpDir (u x) (Uγ x) = (fderiv ℝ expMap (u x)) (Uγ x) := by
      simpa [expMap] using
        Exponential.Coordinate.dexpDir_eq_fderiv_of_hasFDerivAt
          (n := n) data.Gamma p dexp hu_mem hfd (w := Uγ x)
    have hTγ :
        Tγ x = (fderiv ℝ expMap (u x)) (Uγ x) := by
      calc
        Tγ x = dexp.dexpDir (u x) (Uγ x) := by
          exact curveVelocity_eq_dexpDir_apply_normalVelocity
            (n := n) data.Gamma p dexp γ Tγ Uγ hab hkin x hxIcc
        _ = (fderiv ℝ expMap (u x)) (Uγ x) := hdexp
    have hpair :
        Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x) =
          Metric.Coordinate.bilinForm
            (data.metricField (γ x))
            ((fderiv ℝ expMap (u x)) (u x))
            (Tγ x) := by
      have hpair0 := (hradialPairing hu_mem (Uγ x)).symm
      unfold Exponential.Coordinate.metricPairingAt at hpair0
      rw [hkin.coordinateExp_normalCoordinateCurve hxIcc, ← hTγ] at hpair0
      simpa [expMap] using hpair0
    have hradial_norm :
        Metric.Coordinate.quadraticForm (data.metricField p) (u x) =
          Metric.Coordinate.quadraticForm
            (data.metricField (γ x))
            ((fderiv ℝ expMap (u x)) (u x)) := by
      have hnorm0 := hradialPairing hu_mem (u x)
      unfold Exponential.Coordinate.metricPairingAt at hnorm0
      rw [hkin.coordinateExp_normalCoordinateCurve hxIcc] at hnorm0
      simpa [expMap] using hnorm0.symm
    have hpair_abs :
        |Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x)| ≤
          Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) (u x)) *
            metricSpeed (n := n) data.metricField γ Tγ x := by
      calc
        |Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x)|
          = |Metric.Coordinate.bilinForm
              (data.metricField (γ x))
              ((fderiv ℝ expMap (u x)) (u x))
              (Tγ x)| := by rw [hpair]
        _ ≤ Real.sqrt
              (Metric.Coordinate.quadraticForm
                (data.metricField (γ x))
                ((fderiv ℝ expMap (u x)) (u x))) *
            Real.sqrt
              (Metric.Coordinate.quadraticForm (data.metricField (γ x)) (Tγ x)) := by
              exact metric_bilin_abs_le (n := n) (data.metricField_posDef (γ x))
                ((fderiv ℝ expMap (u x)) (u x)) (Tγ x)
        _ = Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) (u x)) *
            metricSpeed (n := n) data.metricField γ Tγ x := by
              rw [← hradial_norm, metricSpeed]
    have hq_nonneg :
        0 ≤ Metric.Coordinate.quadraticForm (data.metricField p) (u x) :=
      Metric.Coordinate.quadraticForm_nonneg (data.metricField_posDef p) (u x)
    have hsqrt_le :
        Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) (u x)) ≤
          Real.sqrt
            (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)) := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg ε, hq_nonneg]
    have harg_pos :
        0 < ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x) := by
      nlinarith [sq_pos_of_pos hε, hq_nonneg]
    have hnum_le :
        Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x) ≤
          metricSpeed (n := n) data.metricField γ Tγ x *
            Real.sqrt
              (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)) := by
      have habs_le :
          |Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x)| ≤
            metricSpeed (n := n) data.metricField γ Tγ x *
              Real.sqrt
                (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)) := by
        calc
          |Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x)|
            ≤ Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) (u x)) *
                metricSpeed (n := n) data.metricField γ Tγ x := hpair_abs
          _ = metricSpeed (n := n) data.metricField γ Tγ x *
                Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) (u x)) := by
                ring
          _ ≤ metricSpeed (n := n) data.metricField γ Tγ x *
                Real.sqrt
                  (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)) := by
                exact mul_le_mul_of_nonneg_left hsqrt_le
                  (metricSpeed_nonneg (n := n) data.metricField γ Tγ x)
      exact le_trans (le_abs_self _) habs_le
    exact (div_le_iff₀ (Real.sqrt_pos.2 harg_pos)).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hnum_le
  have hsub :
      rε 1 - rε 0 ≤
        ∫ y in 0..1, metricSpeed (n := n) data.metricField γ Tγ y := by
    exact intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (g := rε)
      (g' := fun x =>
        Metric.Coordinate.bilinForm (data.metricField p) (u x) (Uγ x) /
          Real.sqrt
            (ε ^ 2 + Metric.Coordinate.quadraticForm (data.metricField p) (u x)))
      (φ := fun y => metricSpeed (n := n) data.metricField γ Tγ y)
      (by norm_num) hr_cont hderiv hspeed_integrableOn hderiv_le

  simpa [rε, metricCurveLength_eq] using hsub

private theorem metricNormalRadiusEps_le_eps_add_metricCurveLength_of_kinematics
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) data.Gamma data.metricField)
    (ε : ℝ) (hε : 0 < ε)
    {v : Exponential.Coordinate.Velocity n}
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) data.Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) ≤
      ε + metricCurveLength (n := n) data.metricField γ 0 1 Tγ := by
  have hsub :=
    metricNormalRadiusEps_sub_le_metricCurveLength_of_kinematics
      (n := n) data p hcompat ε hε γ Tγ Uγ hkin
  have hr0 : metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ 0) = ε := by
    simpa [hγ.1] using
      metricNormalRadiusEps_base (n := n) hε.le data.metricField data.Gamma p
  have hr1 :
      metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ 1) =
        metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p
          (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) := by
    simp [hγ.2]
  linarith

/-- **Owner theorem for Issue 3.** For any curve `γ` from `p` to `exp(v)` with normal coordinate
kinematics, the metric normal radius is ≤ the metric curve length of `γ`.

This follows from:
1. `hkin.displacement.integral_eq` writes the endpoint displacement as `∫ Uγ`
2. `normalCoordinates_exp_roundtrip` identifies the displacement with `v`
3. `norm_integral_le_integral_norm` bounds the integral
4. `metricSpeed_eq_dexpDir_normalVelocity` rewrites the integrand via dexp
5. Gauss lemma (Issue 1) bounds the normal-coordinate speed by the metric speed -/
theorem metricNormalRadius_le_metricCurveLength_of_kinematics_owner
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) data.Gamma data.metricField)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) data.Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) data.Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) data.metricField data.Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) ≤
      metricCurveLength (n := n) data.metricField γ 0 1 Tγ := by
  rw [metricNormalRadius_exp (n := n) data.metricField data.Gamma p hv]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hq_nonneg :
      0 ≤ Metric.Coordinate.quadraticForm (data.metricField p) v :=
    Metric.Coordinate.quadraticForm_nonneg (data.metricField_posDef p) v
  have hmono :
      Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v) ≤
        metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p
          (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) := by
    rw [metricNormalRadiusEps_exp (n := n) ε data.metricField data.Gamma p hv]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg ε, hq_nonneg]
  calc
    Real.sqrt (Metric.Coordinate.quadraticForm (data.metricField p) v)
      ≤ metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p
          (Exponential.Coordinate.coordinateExp (n := n) data.Gamma p v) := hmono
    _ ≤ ε + metricCurveLength (n := n) data.metricField γ 0 1 Tγ :=
      metricNormalRadiusEps_le_eps_add_metricCurveLength_of_kinematics
        (n := n) data p hcompat ε hε γ Tγ Uγ hγ hkin
    _ = metricCurveLength (n := n) data.metricField γ 0 1 Tγ + ε := by ring

/-- Local calibration along any normal-coordinate kinematic curve: the base-point metric radius
can increase by at most the metric length accumulated along the curve. -/
theorem metricNormalRadius_sub_le_metricCurveLength_of_kinematics_owner
    (data : Exponential.Coordinate.LocalRiemannianData n)
    (p : Exponential.Coordinate.Position n)
    (hcompat : Exponential.Coordinate.IsMetricCompatible (n := n) data.Gamma data.metricField)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hkin : HasNormalCoordinateKinematics (n := n) data.Gamma p γ Tγ Uγ 0 1) :
    metricNormalRadius (n := n) data.metricField data.Gamma p (γ 1) -
        metricNormalRadius (n := n) data.metricField data.Gamma p (γ 0) ≤
      metricCurveLength (n := n) data.metricField γ 0 1 Tγ := by
  have hmain :
      metricNormalRadius (n := n) data.metricField data.Gamma p (γ 1) ≤
        metricNormalRadius (n := n) data.metricField data.Gamma p (γ 0) +
          metricCurveLength (n := n) data.metricField γ 0 1 Tγ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hq0_nonneg :
        0 ≤ Metric.Coordinate.quadraticForm (data.metricField p)
          (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 0)) :=
      Metric.Coordinate.quadraticForm_nonneg (data.metricField_posDef p) _
    have hq1_nonneg :
        0 ≤ Metric.Coordinate.quadraticForm (data.metricField p)
          (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 1)) :=
      Metric.Coordinate.quadraticForm_nonneg (data.metricField_posDef p) _
    have hmono1 :
        metricNormalRadius (n := n) data.metricField data.Gamma p (γ 1) ≤
          metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ 1) := by
      rw [metricNormalRadius_eq, metricNormalRadiusEps_eq]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg ε, hq1_nonneg]
    have hmono0 :
        metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ 0) ≤
          metricNormalRadius (n := n) data.metricField data.Gamma p (γ 0) + ε := by
      rw [metricNormalRadiusEps_eq, metricNormalRadius_eq]
      have hsq :
          ε ^ 2 +
              Metric.Coordinate.quadraticForm (data.metricField p)
                (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 0)) ≤
            (Real.sqrt
                (Metric.Coordinate.quadraticForm (data.metricField p)
                  (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 0))) +
              ε) ^ 2 := by
        have hcross :
            0 ≤
              2 * ε *
                Real.sqrt
                  (Metric.Coordinate.quadraticForm (data.metricField p)
                    (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 0))) := by
          positivity
        nlinarith [Real.sq_sqrt hq0_nonneg, hcross]
      have hsum_nonneg :
          0 ≤
            Real.sqrt
                (Metric.Coordinate.quadraticForm (data.metricField p)
                  (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 0))) +
              ε := by
        positivity
      calc
        Real.sqrt
            (ε ^ 2 +
              Metric.Coordinate.quadraticForm (data.metricField p)
                (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 0)))
          ≤ Real.sqrt
              ((Real.sqrt
                    (Metric.Coordinate.quadraticForm (data.metricField p)
                      (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 0))) +
                  ε) ^ 2) := Real.sqrt_le_sqrt hsq
        _ =
            Real.sqrt
                (Metric.Coordinate.quadraticForm (data.metricField p)
                  (Exponential.Coordinate.normalCoordinates (n := n) data.Gamma p (γ 0))) +
              ε := by
              rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hsum_nonneg]
    have hsub :
        metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ 1) ≤
          metricNormalRadiusEps (n := n) ε data.metricField data.Gamma p (γ 0) +
            metricCurveLength (n := n) data.metricField γ 0 1 Tγ := by
      have :=
        metricNormalRadiusEps_sub_le_metricCurveLength_of_kinematics
          (n := n) data p hcompat ε hε γ Tγ Uγ hkin
      linarith
    linarith
  linarith

end Minimization.Coordinate
