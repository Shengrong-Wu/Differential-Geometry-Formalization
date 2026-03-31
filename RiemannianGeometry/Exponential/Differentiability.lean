import Exponential.NormalCoordinates
import Geodesic.FlowDifferentiability

/-! # Differentiability of the coordinate exponential map

This file proves `CoordinateExpHasFDerivAtOnSource` from the geodesic flow differentiability
established in `Geodesic/FlowDifferentiability.lean`. The proof composes:

1. insertion of `v` into the phase-space initial state `(p, v/ε)`,
2. the local geodesic flow at time `ε`,
3. position projection,
4. time rescaling.
-/

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

/-- Differentiability of `coordinateExp` on the chart source. -/
def CoordinateExpHasFDerivAtOnSource
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) : Prop :=
  ∀ {v : Velocity n},
    v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source →
      HasFDerivAt (coordinateExp (n := n) Gamma p)
        (fderiv ℝ (coordinateExp (n := n) Gamma p) v) v

/-- The coordinate exponential map is Fréchet differentiable on the chart source. -/
theorem coordinateExpHasFDerivAtOnSource_of_smoothChristoffel
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    CoordinateExpHasFDerivAtOnSource (n := n) Gamma p := by
  intro v hv
  classical
  let z₀ := baseState n p
  let data := Geodesic.Coordinate.localCoordinateGeodesicFlowData (n := n) Gamma 0 z₀
  let ε := data.ε
  set ins : Velocity n → Geodesic.Coordinate.State n := fun w => (p, ε⁻¹ • w) with hins_def

  -- Step 1: Source membership via source-transport
  have hvsource : v ∈ coordinateExpSource (n := n) Gamma p :=
    coordinateExpPartialHomeomorph_source_subset_coordinateExpSource (n := n) Gamma p hv

  -- Step 2: ins v is in the open flow source (strictly interior)
  -- hvsource gives ‖v‖ < data.ε * data.r; dividing by ε gives ‖ε⁻¹•v‖ < data.r strictly.
  have hins_mem : ins v ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource (n := n) Gamma 0 z₀ := by
    simp only [Geodesic.Coordinate.localCoordinateGeodesicFlowOpenSource, Metric.mem_ball]
    have hvnorm : ‖v‖ < data.ε * data.r := by
      have hbal : v ∈ Metric.ball (0 : Velocity n) (data.ε * data.r) :=
        (by simpa [coordinateExpSource, localCoordinateExponentialSource, z₀, data]
          using hvsource)
      rwa [Metric.mem_ball, dist_zero_right] at hbal
    have hscaled : ‖ε⁻¹ • v‖ < data.r := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos data.hε, inv_mul_eq_div]
      exact (div_lt_iff₀ (show (0 : ℝ) < data.ε from data.hε)).mpr
        (by linarith [mul_comm (data.r : ℝ) (data.ε : ℝ)])
    calc dist (ins v) z₀
        = dist (ε⁻¹ • v) (0 : Geodesic.Coordinate.Velocity n) := by
            simp [ins, z₀, baseState, dist_prod_same_left]
      _ = ‖ε⁻¹ • v‖ := by rw [dist_eq_norm, sub_zero]
      _ < data.r := hscaled

  -- Step 3: ε is in the time domain
  have hε_mem : ε ∈ Geodesic.Coordinate.localCoordinateGeodesicFlowTimeDomain (n := n) Gamma 0 z₀ := by
    show ε ∈ Set.Icc (0 - data.ε) (0 + data.ε)
    simp only [zero_sub, zero_add]
    exact ⟨le_of_lt (neg_lt_of_neg_lt (by linarith [data.hε])), le_refl _⟩

  -- Step 4: Flow differentiability at ins v (Issue 6)
  have hflow_diff :=
    Geodesic.Coordinate.hasFDerivAt_localCoordinateGeodesicFlow_initialState
      (n := n) Gamma 0 z₀ hins_mem hε_mem

  -- Step 5: coordinateExp is differentiable as a composition
  suffices hda : DifferentiableAt ℝ (coordinateExp (n := n) Gamma p) v from hda.hasFDerivAt

  -- The insertion map is affine, hence differentiable
  have hins_diff : DifferentiableAt ℝ ins v := by
    dsimp [ins]
    exact (differentiableAt_const p).prodMk (differentiableAt_id.const_smul ε⁻¹)

  -- statePosition is a CLM, hence differentiable
  have hpos_diff : ∀ z, DifferentiableAt ℝ (Geodesic.Coordinate.statePosition n) z :=
    fun z => (ContinuousLinearMap.fst ℝ (Geodesic.Coordinate.Position n)
      (Geodesic.Coordinate.Velocity n)).differentiableAt

  -- The composition statePosition ∘ (fun z' => flow(z', ε)) ∘ ins is differentiable
  have hcomp_diff : DifferentiableAt ℝ
      (fun w => Geodesic.Coordinate.statePosition n
        (Geodesic.Coordinate.localCoordinateGeodesicFlow (n := n) Gamma 0 z₀ (ins w, ε))) v := by
    apply DifferentiableAt.comp v (hpos_diff _)
    exact hflow_diff.differentiableAt.comp v hins_diff

  -- coordinateExp agrees with this composition
  convert hcomp_diff using 1
  funext w
  simp only [Function.comp_def, coordinateExp_apply, Geodesic.Coordinate.statePosition]
  simp only [geodesicFamilyAtBaseOfLocalCoordinateFlow, rescaledLocalCoordinateGeodesic,
    Geodesic.Coordinate.timeRescaleStateCurve, Geodesic.Coordinate.statePosition,
    ins, z₀, data, baseState,
    Geodesic.Coordinate.localCoordinateGeodesicFlow, mul_one]
  rfl

/-- Exported: Fréchet differentiability of `coordinateExp` on the chart source. -/
theorem hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    HasFDerivAt (coordinateExp (n := n) Gamma p)
      (fderiv ℝ (coordinateExp (n := n) Gamma p) v) v :=
  (coordinateExpHasFDerivAtOnSource_of_smoothChristoffel (n := n) Gamma p) hv

/-- Backward-compatible wrapper accepting an explicit witness (now redundant). -/
theorem hasFDerivAt_coordinateExp_of_witness
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source)
    (_hdiff : CoordinateExpHasFDerivAtOnSource (n := n) Gamma p) :
    HasFDerivAt (coordinateExp (n := n) Gamma p)
      (fderiv ℝ (coordinateExp (n := n) Gamma p) v) v :=
  hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source (n := n) Gamma p hv

/-- Thin `DifferentiableAt` corollary. -/
theorem differentiableAt_coordinateExp_of_mem_partialHomeomorph_source
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) {v : Velocity n}
    (hv : v ∈ (coordinateExpPartialHomeomorph (n := n) Gamma p).source) :
    DifferentiableAt ℝ (coordinateExp (n := n) Gamma p) v :=
  (hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source (n := n) Gamma p hv).differentiableAt

/-- Pointwise-on-source differentiability of `coordinateExp`. -/
theorem differentiableOn_coordinateExp_of_witness
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (p : Position n) :
    DifferentiableOn ℝ (coordinateExp (n := n) Gamma p)
      (coordinateExpPartialHomeomorph (n := n) Gamma p).source := by
  intro v hv
  exact (hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source
    (n := n) Gamma p hv).differentiableAt.differentiableWithinAt

end Exponential.Coordinate
