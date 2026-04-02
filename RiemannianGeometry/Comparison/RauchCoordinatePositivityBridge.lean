import Comparison.RauchPositivitySet
import ParallelTransport.Frames

namespace Comparison

open ParallelTransport

variable {n : ℕ}

/-- Coefficients of a field in the canonical coordinate parallel frame, extracted using the
time-dependent metric pairing. -/
noncomputable def coordinateParallelCoeffs
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (Y : FieldAlong (CoordinateVector n)) :
    ℝ → CoordinateVector n :=
  fun t i => coordinatePairingAt (g t) (Y t) ((coordinateParallelFrame A hAcont).vec i t)

/-- Coefficients of the covariant derivative field in the canonical coordinate parallel frame. -/
noncomputable def coordinateParallelCovDerivCoeffs
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (V : FieldAlong (CoordinateVector n)) :
    ℝ → CoordinateVector n :=
  fun t i => coordinatePairingAt (g t) (V t) ((coordinateParallelFrame A hAcont).vec i t)

/-- The remaining geometric comparison gap, reformulated honestly at the owner layer:
an actual field `Y` together with its covariant derivative `V` and second covariant derivative
`W`, expressed against the canonical coordinate parallel frame, yields the positivity-set
coordinate package consumed by `RauchPositivitySet`. This keeps the missing input geometric
instead of scalar-ODE shaped. -/
structure CoordinateParallelJacobiPositivityBridgeData
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ) where
  connectionA : ℝ → Matrix (Fin n) (Fin n) ℝ
  connectionA_cont : ∀ i j, Continuous fun t => connectionA t i j
  metric : ℝ → Matrix (Fin n) (Fin n) ℝ
  metricDeriv : ℝ → Matrix (Fin n) (Fin n) ℝ
  metricDeriv_hasDeriv : ∀ t i j, HasDerivAt (fun s => metric s i j) (metricDeriv t i j) t
  pairingCompat :
    ∀ t ∈ modelPosDomain k,
      metricDeriv t =
        Matrix.transpose (connectionA t) * metric t + metric t * connectionA t
  field : FieldAlong (CoordinateVector n)
  covDeriv : FieldAlong (CoordinateVector n)
  covSecondDeriv : FieldAlong (CoordinateVector n)
  fieldZero : field 0 = 0
  initialSlope :
    deriv (coordinateJacobiNorm
      (coordinateParallelCoeffs metric connectionA connectionA_cont field)) 0 = 1
  fieldDeriv :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
      HasDerivAt field (covDeriv t + coordinateParallelRhs connectionA t (field t)) t
  covDerivDeriv :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
      HasDerivAt covDeriv
        (covSecondDeriv t + coordinateParallelRhs connectionA t (covDeriv t)) t
  frameDeriv :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i : Fin n,
      HasDerivAt ((coordinateParallelFrame connectionA connectionA_cont).vec i)
        (coordinateParallelRhs connectionA t
          (((coordinateParallelFrame connectionA connectionA_cont).vec i) t)) t
  curvatureCoords :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i : Fin n,
      coordinatePairingAt (metric t) (covSecondDeriv t)
        (((coordinateParallelFrame connectionA connectionA_cont).vec i) t) =
          (-(Matrix.mulVec (sys.A t)
              ((coordinateParallelCoeffs metric connectionA connectionA_cont field) t))) i
  positive :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
      0 < jacobi_normSq (coordinateParallelCoeffs metric connectionA connectionA_cont field) t

private theorem coordinatePairingAt_add_left
    (g : Matrix (Fin n) (Fin n) ℝ)
    (v w z : CoordinateVector n) :
    coordinatePairingAt g (v + w) z =
      coordinatePairingAt g v z + coordinatePairingAt g w z := by
  simp [coordinatePairingAt, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul, mul_add, add_assoc, add_left_comm, add_comm]

theorem hasDerivAt_coordinateParallelCoeff
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (bridge : CoordinateParallelJacobiPositivityBridgeData (n := n) sys k)
    {t : ℝ} (ht : t ∈ modelPosDomain k) (i : Fin n) :
    HasDerivAt
      (fun s =>
        (coordinateParallelCoeffs bridge.metric bridge.connectionA bridge.connectionA_cont
          bridge.field) s i)
      ((coordinateParallelCovDerivCoeffs bridge.metric bridge.connectionA bridge.connectionA_cont
          bridge.covDeriv) t i) t := by
  let E := coordinateParallelFrame bridge.connectionA bridge.connectionA_cont
  have hpair :=
    hasDerivAt_coordinatePairing
      (g := bridge.metric) (dg := bridge.metricDeriv)
      (Y := bridge.field) (Z := E.vec i) (t := t)
      (fun a b => bridge.metricDeriv_hasDeriv t a b)
      (bridge.fieldDeriv ht) (bridge.frameDeriv ht i)
  have hzero :=
    coordinatePairingAt_parallel_deriv_eq_zero
      bridge.connectionA bridge.metric bridge.metricDeriv t (bridge.field t) (E.vec i t)
      (bridge.pairingCompat t ht)
  have hsplit :
      coordinatePairingAt (bridge.metric t)
          (bridge.covDeriv t + coordinateParallelRhs bridge.connectionA t (bridge.field t))
          (E.vec i t) =
        coordinatePairingAt (bridge.metric t) (bridge.covDeriv t) (E.vec i t) +
          coordinatePairingAt (bridge.metric t)
            (coordinateParallelRhs bridge.connectionA t (bridge.field t)) (E.vec i t) := by
    simp [coordinatePairingAt_add_left]
  have hsum :
      coordinatePairingAt (bridge.metricDeriv t) (bridge.field t) (E.vec i t) +
          coordinatePairingAt (bridge.metric t)
            (bridge.covDeriv t + coordinateParallelRhs bridge.connectionA t (bridge.field t))
            (E.vec i t) +
          coordinatePairingAt (bridge.metric t) (bridge.field t)
            (coordinateParallelRhs bridge.connectionA t (E.vec i t)) =
        coordinatePairingAt (bridge.metric t) (bridge.covDeriv t) (E.vec i t) := by
    rw [hsplit]
    linarith
  have hpair' :
      HasDerivAt
        (fun s =>
          (coordinateParallelCoeffs bridge.metric bridge.connectionA bridge.connectionA_cont
            bridge.field) s i)
        (coordinatePairingAt (bridge.metricDeriv t) (bridge.field t) (E.vec i t) +
            coordinatePairingAt (bridge.metric t)
              (bridge.covDeriv t + coordinateParallelRhs bridge.connectionA t (bridge.field t))
              (E.vec i t) +
            coordinatePairingAt (bridge.metric t) (bridge.field t)
              (coordinateParallelRhs bridge.connectionA t (E.vec i t))) t := by
    simpa [coordinateParallelCoeffs, E] using hpair
  convert hpair' using 1
  simpa [coordinateParallelCovDerivCoeffs, E] using hsum.symm

theorem hasDerivAt_coordinateParallelCovDerivCoeff
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (bridge : CoordinateParallelJacobiPositivityBridgeData (n := n) sys k)
    {t : ℝ} (ht : t ∈ modelPosDomain k) (i : Fin n) :
    HasDerivAt
      (fun s =>
        (coordinateParallelCovDerivCoeffs bridge.metric bridge.connectionA bridge.connectionA_cont
          bridge.covDeriv) s i)
      (-(Matrix.mulVec (sys.A t)
          ((coordinateParallelCoeffs bridge.metric bridge.connectionA bridge.connectionA_cont
            bridge.field) t)) i) t := by
  let E := coordinateParallelFrame bridge.connectionA bridge.connectionA_cont
  have hpair :=
    hasDerivAt_coordinatePairing
      (g := bridge.metric) (dg := bridge.metricDeriv)
      (Y := bridge.covDeriv) (Z := E.vec i) (t := t)
      (fun a b => bridge.metricDeriv_hasDeriv t a b)
      (bridge.covDerivDeriv ht) (bridge.frameDeriv ht i)
  have hzero :=
    coordinatePairingAt_parallel_deriv_eq_zero
      bridge.connectionA bridge.metric bridge.metricDeriv t (bridge.covDeriv t) (E.vec i t)
      (bridge.pairingCompat t ht)
  have hsplit :
      coordinatePairingAt (bridge.metric t)
          (bridge.covSecondDeriv t + coordinateParallelRhs bridge.connectionA t (bridge.covDeriv t))
          (E.vec i t) =
        coordinatePairingAt (bridge.metric t) (bridge.covSecondDeriv t) (E.vec i t) +
          coordinatePairingAt (bridge.metric t)
            (coordinateParallelRhs bridge.connectionA t (bridge.covDeriv t)) (E.vec i t) := by
    simp [coordinatePairingAt_add_left]
  have hsum :
      coordinatePairingAt (bridge.metricDeriv t) (bridge.covDeriv t) (E.vec i t) +
          coordinatePairingAt (bridge.metric t)
            (bridge.covSecondDeriv t + coordinateParallelRhs bridge.connectionA t (bridge.covDeriv t))
            (E.vec i t) +
          coordinatePairingAt (bridge.metric t) (bridge.covDeriv t)
            (coordinateParallelRhs bridge.connectionA t (E.vec i t)) =
        coordinatePairingAt (bridge.metric t) (bridge.covSecondDeriv t) (E.vec i t) := by
    rw [hsplit]
    linarith
  have hcurv := bridge.curvatureCoords ht i
  have hpair' :
      HasDerivAt
        (fun s =>
          (coordinateParallelCovDerivCoeffs bridge.metric bridge.connectionA bridge.connectionA_cont
            bridge.covDeriv) s i)
        (coordinatePairingAt (bridge.metricDeriv t) (bridge.covDeriv t) (E.vec i t) +
            coordinatePairingAt (bridge.metric t)
              (bridge.covSecondDeriv t +
                coordinateParallelRhs bridge.connectionA t (bridge.covDeriv t))
              (E.vec i t) +
            coordinatePairingAt (bridge.metric t) (bridge.covDeriv t)
              (coordinateParallelRhs bridge.connectionA t (E.vec i t))) t := by
    simpa [coordinateParallelCovDerivCoeffs, E] using hpair
  convert hpair' using 1
  simpa [coordinateParallelCoeffs, E] using hcurv.symm.trans hsum.symm

/-- The geometric frame/covariant-derivative bridge canonically produces the positivity-set
coordinate package used by the repaired Rauch lower-comparison route. -/
noncomputable def coordinateJacobiPositivityData_of_coordinateParallelBridge
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (bridge : CoordinateParallelJacobiPositivityBridgeData (n := n) sys k) :
    CoordinateJacobiPositivityData n sys k where
  J := coordinateParallelCoeffs bridge.metric bridge.connectionA bridge.connectionA_cont bridge.field
  J' := coordinateParallelCovDerivCoeffs
    bridge.metric bridge.connectionA bridge.connectionA_cont bridge.covDeriv
  initialValue := by
    funext i
    rw [coordinateParallelCoeffs, bridge.fieldZero, coordinateParallelFrame_initial]
    simp [coordinatePairingAt]
  initialSlope := bridge.initialSlope
  componentDeriv := by
    intro t ht i
    exact hasDerivAt_coordinateParallelCoeff (sys := sys) (k := k) bridge ht i
  componentSecondDeriv := by
    intro t ht i
    exact hasDerivAt_coordinateParallelCovDerivCoeff (sys := sys) (k := k) bridge ht i
  positive := bridge.positive

/-- Direct lower Rauch comparison from the geometric coordinate-frame bridge, without storing a
scalar `normODE` witness. -/
theorem rauch_lowerComparison_of_coordinateParallelBridge
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (bridge : CoordinateParallelJacobiPositivityBridgeData (n := n) sys k)
    (hbound : HasRayleighUpperBound sys.A k) :
    RauchNormLowerComparison k
      (let hpos :=
        coordinateJacobiPositivityData_of_coordinateParallelBridge (sys := sys) (k := k) bridge
       (rauchSupersolutionInputData_of_coordinateJacobi (sys := sys) hbound hpos).data) := by
  let hpos :
      CoordinateJacobiPositivityData n sys k :=
    coordinateJacobiPositivityData_of_coordinateParallelBridge (sys := sys) (k := k) bridge
  exact rauch_lowerComparison_of_coordinateJacobi
    (sys := sys) hbound hpos

end Comparison
