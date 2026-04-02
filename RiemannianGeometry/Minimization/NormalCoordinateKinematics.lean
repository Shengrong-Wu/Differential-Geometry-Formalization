import Minimization.NormalNeighborhoods
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Metric.CoordinateMetric
import Variation.CurveLength
import Exponential.VariationDexp

/-! Normal-coordinate kinematics live here: this file records the curve, velocity, and
normal-coordinate displacement data used by the metric bridge and short-geodesic wrappers. -/

namespace Exponential.Coordinate

/-- A coordinate metric field over the fixed coordinate model `Fin n → ℝ`. -/
abbrev MetricField (n : ℕ) :=
  Position n → Metric.Coordinate.Tensor2 n

end Exponential.Coordinate

namespace Minimization.Coordinate

open scoped Topology

variable {n : ℕ}

/-- A curve lies in the normal neighborhood on the interval if every point stays in the carrier. -/
def LiesInOn
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n) (s : Set ℝ) : Prop :=
  Set.MapsTo γ s (normalNeighborhood (n := n) Gamma p)

/-- Endpoint condition for a comparison curve. -/
def IsCurveFrom
    (p q : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n) (a b : ℝ) : Prop :=
  γ a = p ∧ γ b = q

/-- A coordinate velocity witness for a curve on a set. -/
def HasCoordinateVelocityOn
    (γ : ℝ → Fin n → ℝ)
    (T : ℝ → Fin n → ℝ)
    (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt γ (T t) s t

/-- The normal-coordinate image of a curve based at `p`. -/
noncomputable def normalCoordinateCurve
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n) :
    ℝ → Exponential.Coordinate.Velocity n :=
  fun t => Exponential.Coordinate.normalCoordinates (n := n) Gamma p (γ t)

theorem normalCoordinateCurve_mapsTo_coordinateExpPartialHomeomorph_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    {s : Set ℝ}
    (hlies : LiesInOn (n := n) Gamma p γ s) :
    Set.MapsTo
      (normalCoordinateCurve (n := n) Gamma p γ)
      s
      (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source := by
  intro t ht
  exact Exponential.Coordinate.normalCoordinates_mem_coordinateExpPartialHomeomorph_source
    (n := n) Gamma p (by simpa [LiesInOn, normalNeighborhood] using hlies ht)

theorem coordinateExp_normalCoordinateCurve_eqOn
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    {s : Set ℝ}
    (hlies : LiesInOn (n := n) Gamma p γ s) :
    Set.EqOn
      (fun t =>
        Exponential.Coordinate.coordinateExp (n := n) Gamma p
          (normalCoordinateCurve (n := n) Gamma p γ t))
      γ s := by
  intro t ht
  exact Exponential.Coordinate.coordinateExp_normalCoordinates
    (n := n) Gamma p (by simpa [LiesInOn, normalNeighborhood] using hlies ht)

/-- A chosen Euclidean velocity witness in normal coordinates. This is the strongest genuine
comparison statement available before the Gauss-lemma/Jacobi layer identifies it with
Riemannian curve length. -/
structure HasNormalCoordinateDisplacement
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (T : ℝ → Exponential.Coordinate.Velocity n)
    (a b : ℝ) : Prop where
  integrable : IntervalIntegrable T MeasureTheory.volume a b
  integral_eq :
    ∫ t in a..b, T t =
      Exponential.Coordinate.normalCoordinates (n := n) Gamma p (γ b) -
        Exponential.Coordinate.normalCoordinates (n := n) Gamma p (γ a)

/-- Comparison-curve kinematics in normal coordinates: an actual coordinate velocity witness for
the curve together with a velocity witness for its normal-coordinate image. The displacement field
remains explicit because the current API still lacks an away-from-zero chain rule for
`normalCoordinates`. -/
structure HasNormalCoordinateKinematics
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ : ℝ → Exponential.Coordinate.Velocity n)
    (Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (a b : ℝ) : Prop where
  liesInOn : LiesInOn (n := n) Gamma p γ (Set.Icc a b)
  curveVelocity :
    HasCoordinateVelocityOn (n := n) γ Tγ (Set.Icc a b)
  normalVelocity :
    HasCoordinateVelocityOn (n := n)
      (normalCoordinateCurve (n := n) Gamma p γ) Uγ (Set.Icc a b)
  displacement :
    HasNormalCoordinateDisplacement (n := n) Gamma p γ Uγ a b

theorem HasNormalCoordinateKinematics.normalCoordinateCurve_mem_coordinateExpPartialHomeomorph_source
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {p : Exponential.Coordinate.Position n}
    {γ : ℝ → Exponential.Coordinate.Position n}
    {Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n}
    {a b : ℝ}
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ a b)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    normalCoordinateCurve (n := n) Gamma p γ t ∈
      (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source :=
  normalCoordinateCurve_mapsTo_coordinateExpPartialHomeomorph_source
    (n := n) Gamma p γ hkin.liesInOn ht

theorem HasNormalCoordinateKinematics.coordinateExp_normalCoordinateCurve
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {p : Exponential.Coordinate.Position n}
    {γ : ℝ → Exponential.Coordinate.Position n}
    {Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n}
    {a b : ℝ}
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ a b)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    Exponential.Coordinate.coordinateExp (n := n) Gamma p
        (normalCoordinateCurve (n := n) Gamma p γ t) = γ t :=
  coordinateExp_normalCoordinateCurve_eqOn (n := n) Gamma p γ hkin.liesInOn ht

theorem HasNormalCoordinateKinematics.restrict
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {p : Exponential.Coordinate.Position n}
    {γ : ℝ → Exponential.Coordinate.Position n}
    {Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n}
    {a b : ℝ}
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ a b)
    {c d : ℝ}
    (hac : a ≤ c)
    (hcd : c ≤ d)
    (hdb : d ≤ b) :
    HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ c d := by
  have hab : a ≤ b := le_trans hac (le_trans hcd hdb)
  have hsub_Icc : Set.Icc c d ⊆ Set.Icc a b := by
    intro t ht
    constructor
    · exact le_trans hac ht.1
    · exact le_trans ht.2 hdb
  have hsub_uIcc : Set.uIcc c d ⊆ Set.uIcc a b := by
    simpa [Set.uIcc_of_le hcd, Set.uIcc_of_le hab] using hsub_Icc
  have hcurve_restrict :
      HasCoordinateVelocityOn (n := n) γ Tγ (Set.Icc c d) := by
    intro t ht
    exact (hkin.curveVelocity t (hsub_Icc ht)).mono hsub_Icc
  have hnormal_restrict :
      HasCoordinateVelocityOn (n := n)
        (normalCoordinateCurve (n := n) Gamma p γ) Uγ (Set.Icc c d) := by
    intro t ht
    exact (hkin.normalVelocity t (hsub_Icc ht)).mono hsub_Icc
  have hnormal_cont :
      ContinuousOn (normalCoordinateCurve (n := n) Gamma p γ) (Set.Icc c d) :=
    HasDerivWithinAt.continuousOn hnormal_restrict
  have hderiv_at :
      ∀ t ∈ Set.Ioo c d,
        HasDerivAt (normalCoordinateCurve (n := n) Gamma p γ) (Uγ t) t := by
    intro t ht
    exact (hnormal_restrict t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  refine
    { liesInOn := ?_
      curveVelocity := hcurve_restrict
      normalVelocity := hnormal_restrict
      displacement := ?_ }
  · intro t ht
    exact hkin.liesInOn (hsub_Icc ht)
  · refine
      { integrable := hkin.displacement.integrable.mono_set hsub_uIcc
        integral_eq := ?_ }
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcd hnormal_cont hderiv_at
      (hkin.displacement.integrable.mono_set hsub_uIcc)

theorem HasNormalCoordinateKinematics.rescaleToUnitInterval
    {Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n}
    {p : Exponential.Coordinate.Position n}
    {γ : ℝ → Exponential.Coordinate.Position n}
    {Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n}
    {b : ℝ}
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 b)
    (hb : 0 ≤ b) :
    HasNormalCoordinateKinematics (n := n) Gamma p
      (fun s => γ (b * s))
      (fun s => b • Tγ (b * s))
      (fun s => b • Uγ (b * s))
      0 1 := by
  have hmaps : Set.MapsTo (fun s : ℝ => b * s) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) b) := by
    intro s hs
    constructor
    · exact mul_nonneg hb hs.1
    · have hmul : b * s ≤ b * 1 := mul_le_mul_of_nonneg_left hs.2 hb
      simpa using hmul
  have hcurve_reparam :
      HasCoordinateVelocityOn (n := n)
        (fun s => γ (b * s))
        (fun s => b • Tγ (b * s))
        (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hinner :
        HasDerivWithinAt (fun τ : ℝ => b * τ) b (Set.Icc (0 : ℝ) 1) s := by
      simpa [smul_eq_mul, mul_comm] using (((hasDerivAt_id s).smul_const b).hasDerivWithinAt)
    have houter :
        HasDerivWithinAt γ (Tγ (b * s)) (Set.Icc (0 : ℝ) b) (b * s) :=
      hkin.curveVelocity (b * s) (hmaps hs)
    simpa [Function.comp] using
      (houter.hasFDerivWithinAt.comp_hasDerivWithinAt (x := s) hinner hmaps)
  have hnormal_reparam :
      HasCoordinateVelocityOn (n := n)
        (normalCoordinateCurve (n := n) Gamma p (fun s => γ (b * s)))
        (fun s => b • Uγ (b * s))
        (Set.Icc (0 : ℝ) 1) := by
    intro s hs
    have hinner :
        HasDerivWithinAt (fun τ : ℝ => b * τ) b (Set.Icc (0 : ℝ) 1) s := by
      simpa [smul_eq_mul, mul_comm] using (((hasDerivAt_id s).smul_const b).hasDerivWithinAt)
    have houter :
        HasDerivWithinAt (normalCoordinateCurve (n := n) Gamma p γ)
          (Uγ (b * s)) (Set.Icc (0 : ℝ) b) (b * s) :=
      hkin.normalVelocity (b * s) (hmaps hs)
    simpa [normalCoordinateCurve, Function.comp] using
      (houter.hasFDerivWithinAt.comp_hasDerivWithinAt (x := s) hinner hmaps)
  have hdisp_int :
      IntervalIntegrable (fun s => b • Uγ (b * s)) MeasureTheory.volume 0 1 := by
    by_cases hb0 : b = 0
    · simpa [hb0] using
        (intervalIntegrable_zero : IntervalIntegrable
          (fun _ : ℝ => (0 : Exponential.Coordinate.Velocity n))
          MeasureTheory.volume 0 1)
    · have hcomp :
          IntervalIntegrable (fun s => Uγ (b * s)) MeasureTheory.volume (0 / b) (b / b) :=
        hkin.displacement.integrable.comp_mul_left
      simpa [hb0, zero_div, div_self, zero_mul, one_mul] using hcomp.smul b
  refine
    { liesInOn := ?_
      curveVelocity := hcurve_reparam
      normalVelocity := hnormal_reparam
      displacement := ?_ }
  · intro s hs
    exact hkin.liesInOn (hmaps hs)
  · refine
      { integrable := hdisp_int
        integral_eq := ?_ }
    calc
      ∫ s in (0 : ℝ)..1, b • Uγ (b * s)
        = b • ∫ s in (0 : ℝ)..1, Uγ (b * s) := by
            rw [intervalIntegral.integral_smul]
      _ = ∫ s in (0 : ℝ)..b, Uγ s := by
            simpa [zero_mul, one_mul] using
              (intervalIntegral.smul_integral_comp_mul_left
                (f := fun s : ℝ => Uγ s)
                (a := (0 : ℝ)) (b := (1 : ℝ)) (c := b))
      _ = Exponential.Coordinate.normalCoordinates (n := n) Gamma p (γ b) -
            Exponential.Coordinate.normalCoordinates (n := n) Gamma p (γ 0) :=
          by simpa [zero_mul, one_mul] using hkin.displacement.integral_eq
      _ = Exponential.Coordinate.normalCoordinates (n := n) Gamma p (γ (b * 1)) -
            Exponential.Coordinate.normalCoordinates (n := n) Gamma p (γ (b * 0)) := by
          simp [zero_mul, one_mul]

theorem curveVelocity_eq_dexpDir_apply_normalVelocity
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (dexp : Exponential.Coordinate.HasDirectionalDexp (n := n) Gamma p)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    {a b : ℝ}
    (hab : a < b)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ a b) :
    ∀ t ∈ Set.Icc a b,
      Tγ t =
        dexp.dexpDir
          (normalCoordinateCurve (n := n) Gamma p γ t)
          (Uγ t) := by
  intro t ht
  let s : Set ℝ := Set.Icc a b
  let u := normalCoordinateCurve (n := n) Gamma p γ
  have hu : HasDerivWithinAt u (Uγ t) s t := by
    simpa [s, u] using hkin.normalVelocity t ht
  have hu_mem :
      u t ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source := by
    simpa [u] using hkin.normalCoordinateCurve_mem_coordinateExpPartialHomeomorph_source ht
  have hcomp :
      HasDerivWithinAt
        (fun τ => Exponential.Coordinate.coordinateExp (n := n) Gamma p (u τ))
        (dexp.dexpDir (u t) (Uγ t))
        s t := by
    exact Exponential.Coordinate.hasDerivWithinAt_coordinateExp_comp
      (n := n) Gamma p dexp hu hu_mem
  have hcompγ :
      HasDerivWithinAt
        γ
        (dexp.dexpDir (u t) (Uγ t))
        s t := by
    exact hcomp.congr_of_mem
      (fun x hx =>
        (coordinateExp_normalCoordinateCurve_eqOn (n := n) Gamma p γ hkin.liesInOn hx).symm)
      (by simpa [s] using ht)
  have hγ : HasDerivWithinAt γ (Tγ t) s t := by
    simpa [s] using hkin.curveVelocity t ht
  have hUnique : UniqueDiffWithinAt ℝ s t := (uniqueDiffOn_Icc hab).uniqueDiffWithinAt (by simpa [s] using ht)
  calc
    Tγ t = derivWithin γ s t := by
      symm
      exact hγ.derivWithin hUnique
    _ = dexp.dexpDir (u t) (Uγ t) := by
      exact hcompγ.derivWithin hUnique

/-- A radial geodesic is one whose normal coordinates scale linearly in time. -/
noncomputable def radialGeodesic
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (v : Exponential.Coordinate.Velocity n) :
    ℝ → Exponential.Coordinate.Position n :=
  fun t => Exponential.Coordinate.coordinateExp (n := n) Gamma p (t • v)

/-- The constant Euclidean velocity field associated to the radial normal-coordinate segment. -/
def radialVelocityField
    (v : Exponential.Coordinate.Velocity n) :
    ℝ → Exponential.Coordinate.Velocity n :=
  fun _ => v

/-- Convert a coordinate velocity into the genuine Euclidean `L²` norm used by
`Variation.Curve.speed`. -/
noncomputable def toEuclideanL2
    : Exponential.Coordinate.Velocity n →L[ℝ] PiLp 2 (fun _ : Fin n => ℝ) :=
  (PiLp.continuousLinearEquiv (p := 2) ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap

@[simp] theorem toEuclideanL2_apply
    (v : Exponential.Coordinate.Velocity n) :
    toEuclideanL2 (n := n) v = WithLp.toLp 2 v :=
  rfl

theorem speed_eq_norm_toEuclideanL2
    (T : ℝ → Exponential.Coordinate.Velocity n) (t : ℝ) :
    Variation.Curve.speed (n := n) T t =
      ‖toEuclideanL2 (n := n) (T t)‖ := by
  rw [toEuclideanL2_apply, Variation.Curve.speed, PiLp.norm_eq_of_L2]
  congr 1
  unfold Variation.Curve.pairing
  apply Finset.sum_congr rfl
  intro i hi
  rw [PiLp.toLp_apply]
  rw [Real.norm_eq_abs, sq_abs, pow_two]

theorem curveLength_eq_integral_norm_toEuclideanL2
    (T : ℝ → Exponential.Coordinate.Velocity n) (a b : ℝ) :
    Variation.Curve.curveLength (n := n) a b T =
      ∫ t in a..b, ‖toEuclideanL2 (n := n) (T t)‖ := by
  rw [Variation.Curve.curveLength]
  apply intervalIntegral.integral_congr
  intro t ht
  simp [speed_eq_norm_toEuclideanL2]

/-- Coordinate metric speed along a curve for a chosen coordinate velocity field. -/
noncomputable def metricSpeed
    (g : Exponential.Coordinate.MetricField n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (T : ℝ → Exponential.Coordinate.Velocity n) (t : ℝ) : ℝ :=
  Real.sqrt (Metric.Coordinate.quadraticForm (g (γ t)) (T t))

theorem metricSpeed_nonneg
    (g : Exponential.Coordinate.MetricField n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (T : ℝ → Exponential.Coordinate.Velocity n) (t : ℝ) :
    0 ≤ metricSpeed (n := n) g γ T t :=
  Real.sqrt_nonneg _

/-- Coordinate metric length along a curve for a chosen coordinate velocity field. -/
noncomputable def metricCurveLength
    (g : Exponential.Coordinate.MetricField n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (a b : ℝ)
    (T : ℝ → Exponential.Coordinate.Velocity n) : ℝ :=
  ∫ t in a..b, metricSpeed (n := n) g γ T t

@[simp] theorem metricCurveLength_eq
    (g : Exponential.Coordinate.MetricField n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (a b : ℝ)
    (T : ℝ → Exponential.Coordinate.Velocity n) :
    metricCurveLength (n := n) g γ a b T =
      ∫ t in a..b, metricSpeed (n := n) g γ T t :=
  rfl

theorem metricCurveLength_eq_const_of_unitInterval
    (g : Exponential.Coordinate.MetricField n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (T : ℝ → Exponential.Coordinate.Velocity n)
    (c : ℝ)
    (hspeed :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        metricSpeed (n := n) g γ T t = c) :
    metricCurveLength (n := n) g γ 0 1 T = c := by
  rw [metricCurveLength_eq]
  calc
    ∫ t in 0..1, metricSpeed (n := n) g γ T t
      = ∫ t in 0..1, c := by
          apply intervalIntegral.integral_congr
          intro t ht
          exact hspeed t ht
    _ = c := by simpa using intervalIntegral.integral_const c

theorem metricSpeed_eq_dexpDir_normalVelocity
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n)
    (dexp : Exponential.Coordinate.HasDirectionalDexp (n := n) Gamma p)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    {a b : ℝ}
    (hab : a < b)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ a b)
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    metricSpeed (n := n) g γ Tγ t =
      Real.sqrt
        (Metric.Coordinate.quadraticForm
          (g (γ t))
          (dexp.dexpDir
            (normalCoordinateCurve (n := n) Gamma p γ t)
            (Uγ t))) := by
  rw [metricSpeed]
  congr 1
  exact congrArg (Metric.Coordinate.quadraticForm (g (γ t)))
    (curveVelocity_eq_dexpDir_apply_normalVelocity
      (n := n) Gamma p dexp γ Tγ Uγ hab hkin t ht)

/-- The coordinate velocity field carried by the spray-built radial geodesic. -/
noncomputable def radialGeodesicMetricVelocity
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (v : Exponential.Coordinate.Velocity n) :
    ℝ → Exponential.Coordinate.Velocity n :=
  fun t =>
    Geodesic.Coordinate.stateVelocity n
      ((Exponential.Coordinate.geodesicFamilyAtBaseOfLocalCoordinateFlow (n := n) p Gamma).solve v t)

/-- Base-point metric norm of normal coordinates. This is the radial quantity matched by the
genuine Gauss-lemma length identity, unlike the Euclidean `normalRadius`. -/
noncomputable def metricNormalRadius
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) : ℝ :=
  Real.sqrt
    (Metric.Coordinate.quadraticForm (g p)
      (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x))

@[simp] theorem metricNormalRadius_eq
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) :
    metricNormalRadius (n := n) g Gamma p x =
      Real.sqrt
        (Metric.Coordinate.quadraticForm (g p)
          (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x)) :=
  rfl

@[simp] theorem metricNormalRadius_base
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    metricNormalRadius (n := n) g Gamma p p = 0 := by
  rw [metricNormalRadius, Exponential.Coordinate.normalCoordinates_base (n := n) Gamma p]
  simp [Metric.Coordinate.quadraticForm]

theorem metricNormalRadius_exp
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    metricNormalRadius (n := n) g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) =
      Real.sqrt (Metric.Coordinate.quadraticForm (g p) v) := by
  rw [metricNormalRadius,
    Exponential.Coordinate.normalCoordinates_exp_roundtrip (n := n) Gamma p v hv]

/-- Regularized base-point metric radius used to avoid the singularity at the base point. -/
noncomputable def metricNormalRadiusEps
    (ε : ℝ)
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) : ℝ :=
  Real.sqrt
    (ε ^ 2 + Metric.Coordinate.quadraticForm (g p)
      (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x))

@[simp] theorem metricNormalRadiusEps_eq
    (ε : ℝ)
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) :
    metricNormalRadiusEps (n := n) ε g Gamma p x =
      Real.sqrt
        (ε ^ 2 + Metric.Coordinate.quadraticForm (g p)
          (Exponential.Coordinate.normalCoordinates (n := n) Gamma p x)) :=
  rfl

@[simp] theorem metricNormalRadiusEps_zero
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) :
    metricNormalRadiusEps (n := n) 0 g Gamma p x =
      metricNormalRadius (n := n) g Gamma p x := by
  simp [metricNormalRadiusEps, metricNormalRadius]

theorem metricNormalRadiusEps_nonneg
    (ε : ℝ)
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (x : Exponential.Coordinate.Position n) :
    0 ≤ metricNormalRadiusEps (n := n) ε g Gamma p x :=
  Real.sqrt_nonneg _

@[simp] theorem metricNormalRadiusEps_base
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n) :
    metricNormalRadiusEps (n := n) ε g Gamma p p = ε := by
  rw [metricNormalRadiusEps, Exponential.Coordinate.normalCoordinates_base (n := n) Gamma p]
  simp [Metric.Coordinate.quadraticForm, hε, sq]

theorem metricNormalRadiusEps_exp
    (ε : ℝ)
    (g : Exponential.Coordinate.MetricField n)
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    metricNormalRadiusEps (n := n) ε g Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) =
      Real.sqrt (ε ^ 2 + Metric.Coordinate.quadraticForm (g p) v) := by
  rw [metricNormalRadiusEps,
    Exponential.Coordinate.normalCoordinates_exp_roundtrip (n := n) Gamma p v hv]

@[simp] theorem radialGeodesic_zero
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (v : Exponential.Coordinate.Velocity n) :
    radialGeodesic (n := n) Gamma p v 0 = p := by
  simpa [radialGeodesic] using Exponential.Coordinate.coordinateExp_zero (n := n) Gamma p

@[simp] theorem radialGeodesic_one
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (v : Exponential.Coordinate.Velocity n) :
    radialGeodesic (n := n) Gamma p v 1 =
      Exponential.Coordinate.coordinateExp (n := n) Gamma p v := by
  simp [radialGeodesic]

theorem radialGeodesic_curveFrom
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    (v : Exponential.Coordinate.Velocity n) :
    IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v)
      (radialGeodesic (n := n) Gamma p v) 0 1 := by
  constructor
  · simpa using radialGeodesic_zero (n := n) Gamma p v
  · simpa using radialGeodesic_one (n := n) Gamma p v

theorem radialGeodesic_liesInOn
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    {s : Set ℝ}
    (hsegment :
      ∀ t ∈ s,
        t • v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    LiesInOn (n := n) Gamma p (radialGeodesic (n := n) Gamma p v) s := by
  intro t ht
  exact
    (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).map_source
      (hsegment t ht)

theorem radialGeodesic_hasNormalCoordinateDisplacement
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    HasNormalCoordinateDisplacement (n := n) Gamma p
      (radialGeodesic (n := n) Gamma p v) (radialVelocityField (n := n) v) 0 1 := by
  refine ⟨intervalIntegrable_const, ?_⟩
  calc
    ∫ t in 0..1, radialVelocityField (n := n) v t = ∫ t in 0..1, v := by rfl
    _ = v := by simpa using intervalIntegral.integral_const v
    _ =
        Exponential.Coordinate.normalCoordinates (n := n) Gamma p
            (radialGeodesic (n := n) Gamma p v 1) -
          Exponential.Coordinate.normalCoordinates (n := n) Gamma p
            (radialGeodesic (n := n) Gamma p v 0) := by
          rw [radialGeodesic_one, radialGeodesic_zero,
            Exponential.Coordinate.normalCoordinates_exp_roundtrip (n := n) Gamma p v hv,
            Exponential.Coordinate.normalCoordinates_base (n := n) Gamma p]
          simp

/-- The basic kinematic comparison presently available from the normal-coordinate displacement
witness: endpoint radius is bounded by the Euclidean length of the chosen normal-coordinate
velocity field. -/
theorem normalRadius_le_curveLength_of_kinematics
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (Tγ Uγ : ℝ → Exponential.Coordinate.Velocity n)
    (hγ :
      IsCurveFrom (n := n) p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) γ 0 1)
    (hkin : HasNormalCoordinateKinematics (n := n) Gamma p γ Tγ Uγ 0 1) :
    normalRadius (n := n) Gamma p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) ≤
      Variation.Curve.curveLength (n := n) 0 1 Uγ := by
  let _ := hv
  let _ := hkin.liesInOn
  let _ := hkin.curveVelocity
  let _ := hkin.normalVelocity
  have hcoords :
      ∫ t in 0..1, Uγ t =
        Exponential.Coordinate.normalCoordinates (n := n) Gamma p
          (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
    rcases hγ with ⟨ha, hb⟩
    rw [hkin.displacement.integral_eq, ha, hb,
      Exponential.Coordinate.normalCoordinates_base (n := n) Gamma p]
    simp
  have hmap :
      ∫ t in 0..1, toEuclideanL2 (n := n) (Uγ t) =
        toEuclideanL2 (n := n) (∫ t in 0..1, Uγ t) := by
    exact (toEuclideanL2 (n := n)).intervalIntegral_comp_comm hkin.displacement.integrable
  calc
    normalRadius (n := n) Gamma p (Exponential.Coordinate.coordinateExp (n := n) Gamma p v)
      = ‖toEuclideanL2 (n := n) (∫ t in 0..1, Uγ t)‖ := by
          rw [normalRadius, hcoords, toEuclideanL2_apply]
    _ = ‖∫ t in 0..1, toEuclideanL2 (n := n) (Uγ t)‖ := by
          rw [hmap]
    _ ≤ ∫ t in 0..1, ‖toEuclideanL2 (n := n) (Uγ t)‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ = Variation.Curve.curveLength (n := n) 0 1 Uγ := by
          symm
          exact curveLength_eq_integral_norm_toEuclideanL2 (n := n) Uγ 0 1

/-- The Euclidean normal-coordinate length of the radial segment equals the Euclidean radial norm.
The genuine metric-length analogue is expected to use `metricCurveLength` and `metricNormalRadius`
once the radial Gauss-lemma bridge is available. -/
theorem radialGeodesic_length_le_radius
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Exponential.Coordinate.Position n)
    {v : Exponential.Coordinate.Velocity n}
    (hv :
      v ∈ (Exponential.Coordinate.coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    Variation.Curve.curveLength (n := n) 0 1
      (radialVelocityField (n := n) v) ≤
      normalRadius (n := n) Gamma p
        (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
  have hEq :
      Variation.Curve.curveLength (n := n) 0 1 (radialVelocityField (n := n) v) =
        normalRadius (n := n) Gamma p
          (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
    calc
      Variation.Curve.curveLength (n := n) 0 1 (radialVelocityField (n := n) v)
        = ∫ t in 0..1, ‖toEuclideanL2 (n := n) (radialVelocityField (n := n) v t)‖ := by
            exact curveLength_eq_integral_norm_toEuclideanL2
              (n := n) (radialVelocityField (n := n) v) 0 1
      _ = ∫ t in 0..1, ‖toEuclideanL2 (n := n) v‖ := by
            apply intervalIntegral.integral_congr
            intro t ht
            simp [radialVelocityField]
      _ = ‖toEuclideanL2 (n := n) v‖ := by
            simpa using intervalIntegral.integral_const ‖toEuclideanL2 (n := n) v‖
      _ = normalRadius (n := n) Gamma p
            (Exponential.Coordinate.coordinateExp (n := n) Gamma p v) := by
            rw [normalRadius, toEuclideanL2_apply,
              Exponential.Coordinate.normalCoordinates_exp_roundtrip (n := n) Gamma p v hv]
  exact le_of_eq hEq

end Minimization.Coordinate
