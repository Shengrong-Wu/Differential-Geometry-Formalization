import Comparison.RauchCoordinateCurvatureBridge
import Comparison.RauchCoordinatePositivityBridge

namespace Comparison

open ParallelTransport

variable {n : ℕ}

/-- A single owner-local geometric package for the lower Rauch route in canonical
coordinate-parallel form.

This combines the two previously separate ingredients:

* curvature control in the canonical coordinate-parallel frame, giving the Rayleigh upper bound;
* positivity-set Jacobi norm data in the same frame, giving the repaired scalar lower comparison.

The result is a direct lower-Rauch theorem with no scalar `normODE` witness in the API. -/
structure CoordinateParallelRauchLowerBridgeData
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
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
  tangent : FieldAlong (CoordinateVector n)
  curvature : Curvature.CurvatureTensor C
  sectionalUpper :
    NormalizedSectionalUpperBoundAlongCoordinate metric curvature tangent k
  tangent_unit :
    ∀ t, coordinatePairingAt (metric t) (tangent t) (tangent t) = 1
  frame_orthonormal :
    ∀ t i j,
      coordinatePairingAt (metric t)
        ((coordinateParallelFrame connectionA connectionA_cont).vec i t)
        ((coordinateParallelFrame connectionA connectionA_cont).vec j t) =
          if i = j then 1 else 0
  frame_normal :
    ∀ t i,
      coordinatePairingAt (metric t)
        ((coordinateParallelFrame connectionA connectionA_cont).vec i t) (tangent t) = 0
  matrixCurvatureCoords :
    ∀ t ξ i,
      (Matrix.mulVec (sys.A t) ξ) i =
        coordinatePairingAt (metric t)
          (curvature
            (frameLift (coordinateParallelFrame connectionA connectionA_cont) t ξ)
            (tangent t) (tangent t))
          (((coordinateParallelFrame connectionA connectionA_cont).vec i t))
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
  jacobiCoords :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i : Fin n,
      coordinatePairingAt (metric t) (covSecondDeriv t)
        (((coordinateParallelFrame connectionA connectionA_cont).vec i) t) =
          (-(Matrix.mulVec (sys.A t)
              ((coordinateParallelCoeffs metric connectionA connectionA_cont field) t))) i
  positive :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k →
      0 < jacobi_normSq (coordinateParallelCoeffs metric connectionA connectionA_cont field) t

/-- Forget the combined lower-Rauch bridge down to the curvature/Rayleigh bridge. -/
noncomputable def CoordinateParallelRauchLowerBridgeData.toCurvatureBridge
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (bridge : CoordinateParallelRauchLowerBridgeData (n := n) (C := C) sys k) :
    CoordinateFrameCurvatureBridgeData bridge.metric bridge.curvature bridge.tangent sys where
  frame := coordinateParallelFrame bridge.connectionA bridge.connectionA_cont
  tangent_unit := bridge.tangent_unit
  frame_orthonormal := bridge.frame_orthonormal
  frame_normal := bridge.frame_normal
  curvatureCoords := bridge.matrixCurvatureCoords

/-- Forget the combined lower-Rauch bridge down to the positivity-set bridge. -/
noncomputable def CoordinateParallelRauchLowerBridgeData.toPositivityBridge
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (bridge : CoordinateParallelRauchLowerBridgeData (n := n) (C := C) sys k) :
    CoordinateParallelJacobiPositivityBridgeData sys k where
  connectionA := bridge.connectionA
  connectionA_cont := bridge.connectionA_cont
  metric := bridge.metric
  metricDeriv := bridge.metricDeriv
  metricDeriv_hasDeriv := bridge.metricDeriv_hasDeriv
  pairingCompat := bridge.pairingCompat
  field := bridge.field
  covDeriv := bridge.covDeriv
  covSecondDeriv := bridge.covSecondDeriv
  fieldZero := bridge.fieldZero
  initialSlope := bridge.initialSlope
  fieldDeriv := bridge.fieldDeriv
  covDerivDeriv := bridge.covDerivDeriv
  frameDeriv := bridge.frameDeriv
  curvatureCoords := bridge.jacobiCoords
  positive := bridge.positive

/-- The combined geometric bridge canonically yields the Rayleigh upper bound required by the
norm-squared comparison core. -/
theorem hasRayleighUpperBound_of_coordinateParallelLowerBridge
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (bridge : CoordinateParallelRauchLowerBridgeData (n := n) (C := C) sys k) :
    HasRayleighUpperBound sys.A k := by
  exact hasRayleighUpperBound_of_coordinateFrameCurvatureBridge
    bridge.sectionalUpper bridge.toCurvatureBridge

/-- Direct lower Rauch comparison from the single geometric canonical-frame bridge. -/
theorem rauch_lowerComparison_of_coordinateParallelLowerBridge
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (bridge : CoordinateParallelRauchLowerBridgeData (n := n) (C := C) sys k) :
    RauchNormLowerComparison k
      (let hpos := coordinateJacobiPositivityData_of_coordinateParallelBridge
        (sys := sys) (k := k) bridge.toPositivityBridge
       (rauchSupersolutionInputData_of_coordinateJacobi
          (sys := sys)
          (hasRayleighUpperBound_of_coordinateParallelLowerBridge bridge)
          hpos).data) := by
  let hbound : HasRayleighUpperBound sys.A k :=
    hasRayleighUpperBound_of_coordinateParallelLowerBridge bridge
  exact rauch_lowerComparison_of_coordinateParallelBridge
    (sys := sys) (k := k) bridge.toPositivityBridge hbound

end Comparison
