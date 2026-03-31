import Exponential.Differentiability
import ODE.FlowContDiff

/-! # Continuity of the radial dexp field

This file proves that the directional derivative of the coordinate exponential map
is continuous along radial lines. The key input is `contDiffAt_coordinateExp`,
which gives `C¹` regularity of the exponential map on its source. -/

namespace Exponential.Coordinate

open Set

variable {n : ℕ}

/-- The coordinate exponential map is `C¹` on its source. -/
theorem contDiffAt_coordinateExp
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p) :
    ContDiffAt ℝ 1 (coordinateExp (n := n) Gamma p) v := by
  classical
  let z₀ := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let ε := data.ε
  set ins : Velocity n → Geodesic.Coordinate.State n := fun w => (p, ε⁻¹ • w) with hins_def
  have hins_mem : ins v ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource (n := n) Gamma 0 z₀ := by
    simp only [Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource, Metric.mem_ball]
    have hvnorm : ‖v‖ < data.ε * data.r := by
      have hbal : v ∈ Metric.ball (0 : Velocity n) (data.ε * data.r) := by
        simpa [coordinateExpSource, localCoordinateExponentialSource, z₀, data] using hv
      rwa [Metric.mem_ball, dist_zero_right] at hbal
    have hscaled : ‖ε⁻¹ • v‖ < data.r := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos data.hε, inv_mul_eq_div]
      exact (div_lt_iff₀ (show (0 : ℝ) < data.ε from data.hε)).mpr
        (by linarith [mul_comm (data.r : ℝ) (data.ε : ℝ)])
    calc
      dist (ins v) z₀ = dist (ε⁻¹ • v) (0 : Geodesic.Coordinate.Velocity n) := by
        simp [ins, z₀, baseState, dist_prod_same_left]
      _ = ‖ε⁻¹ • v‖ := by rw [dist_eq_norm, sub_zero]
      _ < data.r := hscaled
  have hε_mem : ε ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
    show ε ∈ Set.Icc (0 - data.ε) (0 + data.ε)
    simp only [zero_sub, zero_add]
    exact ⟨le_of_lt (neg_lt_of_neg_lt (by linarith [data.hε])), le_refl _⟩
  have hflow_cont :
      ContDiffAt ℝ 1
        (fun z' : Geodesic.Coordinate.State n =>
          Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z', ε))
        (ins v) :=
    Geodesic.Coordinate.contDiffAt_localCoordinateGeodesicFlow_initialState
      (n := n) Gamma 0 z₀ hins_mem hε_mem
  have hins_cont : ContDiffAt ℝ 1 ins v := by
    exact contDiffAt_const.prodMk ((contDiffAt_id : ContDiffAt ℝ 1 (fun w : Velocity n => w) v).const_smul ε⁻¹)
  have hcomp_cont :
      ContDiffAt ℝ 1
        (fun w : Velocity n =>
          Geodesic.Coordinate.statePosition n
            (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (ins w, ε)))
        v := by
    have hproj_cont :
        ContDiffAt ℝ 1
          (fun z' : Geodesic.Coordinate.State n =>
            Geodesic.Coordinate.statePosition n
              (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (z', ε)))
          (ins v) := by
      simpa [Geodesic.Coordinate.statePosition] using
        hflow_cont.continuousLinearMap_comp
          (ContinuousLinearMap.fst ℝ (Geodesic.Coordinate.Position n)
            (Geodesic.Coordinate.Velocity n))
    exact hproj_cont.comp v hins_cont
  convert hcomp_cont using 1
  funext w
  simp only [coordinateExp_apply, Geodesic.Coordinate.statePosition]
  simp only [geodesicFamilyAtBaseOfLocalCoordinateFlow, rescaledLocalCoordinateGeodesic,
    Geodesic.Coordinate.timeRescaleStateCurve, Geodesic.Coordinate.statePosition,
    ins, z₀, data, baseState, Geodesic.Coordinate.localCoordinateGeodesicFlow, mul_one]
  rfl

/-- Star-shapedness: `t • v ∈ coordinateExpSource` for `t ∈ [0,1]` and `v ∈ coordinateExpSource`.
The source is a ball around 0, hence star-shaped. -/
theorem smul_mem_coordinateExpSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • v ∈ coordinateExpSource (n := n) Gamma p := by
  simp only [coordinateExpSource, localCoordinateExponentialSource, Metric.mem_ball,
    dist_zero_right] at hv ⊢
  calc ‖t • v‖ = ‖t‖ * ‖v‖ := norm_smul t v
    _ ≤ 1 * ‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith, ht1⟩
    _ = ‖v‖ := one_mul _
    _ < _ := hv

/-- Continuity of the Fréchet derivative of `coordinateExp` on its source. -/
theorem continuousOn_fderiv_coordinateExp
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    ContinuousOn (fderiv ℝ (coordinateExp (n := n) Gamma p))
      (coordinateExpSource (n := n) Gamma p) :=
  fun _u hu => (contDiffAt_coordinateExp (n := n) Gamma p hu).continuousAt_fderiv
    (by simp) |>.continuousWithinAt

/-- Continuity of `t ↦ fderiv(coordinateExp)(t·v)` on `[0,1]`. -/
theorem continuousOn_fderiv_coordinateExp_radial
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p) :
    ContinuousOn (fun (t : ℝ) => fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v))
      (Set.Icc (0 : ℝ) 1) :=
  (continuousOn_fderiv_coordinateExp (n := n) Gamma p).comp
    ((continuous_id.smul continuous_const).continuousOn)
    (fun _t ht => smul_mem_coordinateExpSource (n := n) Gamma p hv ht.1 ht.2)

/-- Continuity of `t ↦ (fderiv(coordinateExp)(t·v)) w` on `[0,1]`. -/
theorem continuousOn_fderiv_coordinateExp_radial_apply
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n)
    {v : Velocity n}
    (hv : v ∈ coordinateExpSource (n := n) Gamma p)
    (w : Velocity n) :
    ContinuousOn (fun (t : ℝ) => (fderiv ℝ (coordinateExp (n := n) Gamma p) (t • v)) w)
      (Set.Icc (0 : ℝ) 1) :=
  (continuousOn_fderiv_coordinateExp_radial (n := n) Gamma p hv).clm_apply continuousOn_const

end Exponential.Coordinate
