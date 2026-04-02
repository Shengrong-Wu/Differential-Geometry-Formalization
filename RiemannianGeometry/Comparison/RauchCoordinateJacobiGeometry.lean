import Comparison.RauchCoordinateLowerBridge

namespace Comparison

open ParallelTransport

variable {n : ℕ}

/-- Actual Jacobi/geodesic data in the canonical coordinate-parallel frame.

This is closer to the genuine geometry than `CoordinateParallelJacobiPositivityBridgeData`:
instead of postulating the coefficient-level second-order identity directly, it stores the
pointwise Jacobi equation for a field `Y` with covariant derivatives `V`, `W`. The coefficient
Jacobi package is then derived from those geometric ingredients together with the orthonormal
parallel-frame reconstruction lemma and the remaining matrix curvature-coordinate bridge. -/
structure CoordinateParallelJacobiGeometryData
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
  jacobiEq :
    ∀ t,
      covSecondDeriv t + curvature (field t) (tangent t) (tangent t) = 0
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

/-- In the orthonormal canonical parallel frame, the geometric field equals the frame lift of its
coordinate coefficient function. -/
private theorem field_eq_frameLift_coordinateParallelCoeffs_of_pointwise_orthonormal
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hframe_orthonormal :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i j,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t) =
            if i = j then 1 else 0)
    {t : ℝ} (ht : t ∈ modelPosDomain k) :
    frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t
      ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont geom.field) t) =
        geom.field t := by
  simpa [coordinateParallelCoeffs] using
    frameLift_pairingCoeffs_eq_self_of_pointwise_orthonormal
      (g := geom.metric)
      (frame := coordinateParallelFrame geom.connectionA geom.connectionA_cont)
      t (geom.field t) (hframe_orthonormal ht)

/-- The field-specific curvature coordinates are derived from the matrix-coordinate bridge by
reconstructing the field from its coefficients in the orthonormal canonical parallel frame. -/
private theorem curvatureFieldCoords_of_matrixCurvatureCoords
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hframe_orthonormal :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i j,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t) =
            if i = j then 1 else 0)
    (hmatrixCurvatureCoords :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ ξ i,
        (Matrix.mulVec (sys.A t) ξ) i =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              (frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t ξ)
              (geom.tangent t) (geom.tangent t))
            (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)))
    {t : ℝ} (ht : t ∈ modelPosDomain k) (i : Fin n) :
    coordinatePairingAt (geom.metric t)
      (geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t))
      (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)) =
        (Matrix.mulVec (sys.A t)
          ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
            geom.field) t)) i := by
  let E := coordinateParallelFrame geom.connectionA geom.connectionA_cont
  let ξ :=
    (coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont geom.field) t
  have hfield :
      frameLift E t ξ = geom.field t := by
    simpa [E, ξ] using
      field_eq_frameLift_coordinateParallelCoeffs_of_pointwise_orthonormal
        (geom := geom) hframe_orthonormal ht
  calc
    coordinatePairingAt (geom.metric t)
        (geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t))
        (E.vec i t)
        =
          coordinatePairingAt (geom.metric t)
            (geom.curvature (frameLift E t ξ) (geom.tangent t) (geom.tangent t))
            (E.vec i t) := by
              rw [hfield]
    _ = (Matrix.mulVec (sys.A t) ξ) i := by
          symm
          exact hmatrixCurvatureCoords ht ξ i

/-- The Jacobi equation together with the field-level curvature coordinates yields the coefficient
equation required by the positivity-set bridge. -/
theorem jacobiCoords_of_coordinateParallelJacobiGeometry
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hframe_orthonormal :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i j,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t) =
            if i = j then 1 else 0)
    (hmatrixCurvatureCoords :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ ξ i,
        (Matrix.mulVec (sys.A t) ξ) i =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              (frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t ξ)
              (geom.tangent t) (geom.tangent t))
            (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)))
    {t : ℝ} (ht : t ∈ modelPosDomain k) (i : Fin n) :
    coordinatePairingAt (geom.metric t) (geom.covSecondDeriv t)
      (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i) t) =
        (-(Matrix.mulVec (sys.A t)
          ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
            geom.field) t))) i := by
  let E := coordinateParallelFrame geom.connectionA geom.connectionA_cont
  have hpair_raw :
      coordinatePairingAt (geom.metric t)
        (geom.covSecondDeriv t + geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t))
        (E.vec i t) =
      coordinatePairingAt (geom.metric t) 0 (E.vec i t) := by
    simpa [coordinatePairingAt_add_left, E] using
      congrArg (fun v => coordinatePairingAt (geom.metric t) v (E.vec i t)) (geom.jacobiEq t)
  have hzero :
      coordinatePairingAt (geom.metric t) 0 (E.vec i t) = 0 := by
    simp [coordinatePairingAt]
  have hpair :
      coordinatePairingAt (geom.metric t) (geom.covSecondDeriv t) (E.vec i t) +
        coordinatePairingAt (geom.metric t)
          (geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t)) (E.vec i t) = 0 := by
    rw [hzero] at hpair_raw
    simpa [coordinatePairingAt_add_left] using hpair_raw
  have hcurv :=
    curvatureFieldCoords_of_matrixCurvatureCoords
      (sys := sys) (k := k) geom hframe_orthonormal hmatrixCurvatureCoords ht i
  calc
    coordinatePairingAt (geom.metric t) (geom.covSecondDeriv t) (E.vec i t)
        = -coordinatePairingAt (geom.metric t)
            (geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t)) (E.vec i t) := by
            linarith
    _ = (-(Matrix.mulVec (sys.A t)
          ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
            geom.field) t))) i := by
          simpa using congrArg Neg.neg hcurv

/-- A genuine Jacobi/geodesic package yields the coefficient-level positivity-set bridge. -/
noncomputable def CoordinateParallelJacobiGeometryData.toPositivityBridge
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hframe_orthonormal :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i j,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t) =
            if i = j then 1 else 0)
    (hmatrixCurvatureCoords :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ ξ i,
        (Matrix.mulVec (sys.A t) ξ) i =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              (frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t ξ)
              (geom.tangent t) (geom.tangent t))
            (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t))) :
    CoordinateParallelJacobiPositivityBridgeData sys k where
  connectionA := geom.connectionA
  connectionA_cont := geom.connectionA_cont
  metric := geom.metric
  metricDeriv := geom.metricDeriv
  metricDeriv_hasDeriv := geom.metricDeriv_hasDeriv
  pairingCompat := geom.pairingCompat
  field := geom.field
  covDeriv := geom.covDeriv
  covSecondDeriv := geom.covSecondDeriv
  fieldZero := geom.fieldZero
  initialSlope := geom.initialSlope
  fieldDeriv := geom.fieldDeriv
  covDerivDeriv := geom.covDerivDeriv
  frameDeriv := geom.frameDeriv
  curvatureCoords := by
    intro t ht i
    exact jacobiCoords_of_coordinateParallelJacobiGeometry
      (sys := sys) (k := k) geom hframe_orthonormal hmatrixCurvatureCoords ht i
  positive := geom.positive

/-- Build the combined lower-Rauch bridge from genuine Jacobi/geodesic data plus the curvature
control of the canonical parallel frame. This is the direct owner-local constructor reducing the
remaining gap to a single actual geometric package. -/
noncomputable def coordinateParallelRauchLowerBridgeData_of_jacobiGeometry
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hsec :
      NormalizedSectionalUpperBoundAlongCoordinate geom.metric geom.curvature geom.tangent k)
    (htangent_unit :
      ∀ t, coordinatePairingAt (geom.metric t) (geom.tangent t) (geom.tangent t) = 1)
    (hframe_orthonormal :
      ∀ t i j,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t) =
            if i = j then 1 else 0)
    (hframe_normal :
      ∀ t i,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          (geom.tangent t) = 0)
    (hmatrixCurvatureCoords :
      ∀ t ξ i,
        (Matrix.mulVec (sys.A t) ξ) i =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              (frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t ξ)
              (geom.tangent t) (geom.tangent t))
            (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t))) :
    CoordinateParallelRauchLowerBridgeData (n := n) (C := C) sys k where
  connectionA := geom.connectionA
  connectionA_cont := geom.connectionA_cont
  metric := geom.metric
  metricDeriv := geom.metricDeriv
  metricDeriv_hasDeriv := geom.metricDeriv_hasDeriv
  pairingCompat := geom.pairingCompat
  tangent := geom.tangent
  curvature := geom.curvature
  sectionalUpper := hsec
  tangent_unit := htangent_unit
  frame_orthonormal := hframe_orthonormal
  frame_normal := hframe_normal
  matrixCurvatureCoords := hmatrixCurvatureCoords
  field := geom.field
  covDeriv := geom.covDeriv
  covSecondDeriv := geom.covSecondDeriv
  fieldZero := geom.fieldZero
  initialSlope := geom.initialSlope
  fieldDeriv := geom.fieldDeriv
  covDerivDeriv := geom.covDerivDeriv
  frameDeriv := geom.frameDeriv
  jacobiCoords := by
    intro t ht i
    exact jacobiCoords_of_coordinateParallelJacobiGeometry
      (sys := sys) (k := k) geom
      (fun _ _ i j => hframe_orthonormal _ i j)
      (fun _ _ ξ i => hmatrixCurvatureCoords _ ξ i)
      ht i
  positive := geom.positive

/-- Direct lower Rauch comparison from genuine Jacobi/geodesic data in the canonical
coordinate-parallel frame. -/
theorem rauch_lowerComparison_of_coordinateParallelJacobiGeometry_onModel
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hsec :
      NormalizedSectionalUpperBoundAlongCoordinate geom.metric geom.curvature geom.tangent k)
    (htangent_unit :
      ∀ t, coordinatePairingAt (geom.metric t) (geom.tangent t) (geom.tangent t) = 1)
    (hframe_orthonormal :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i j,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t) =
            if i = j then 1 else 0)
    (hframe_normal :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          (geom.tangent t) = 0)
    (hmatrixCurvatureCoords :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ ξ i,
        (Matrix.mulVec (sys.A t) ξ) i =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              (frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t ξ)
              (geom.tangent t) (geom.tangent t))
            (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t))) :
    RauchNormLowerComparison k
      (let hpos :=
        coordinateJacobiPositivityData_of_coordinateParallelBridge
          (sys := sys) (k := k)
          (geom.toPositivityBridge hframe_orthonormal hmatrixCurvatureCoords)
       (rauchSupersolutionInputData_of_coordinateJacobi_onModel
          (sys := sys)
          (hasRayleighUpperBoundOn_of_coordinateFrame
            (frame := coordinateParallelFrame geom.connectionA geom.connectionA_cont)
            (s := modelPosDomain k)
            hsec
            (fun t _ => htangent_unit t)
            (fun t ht => hframe_orthonormal ht)
            (fun t ht => hframe_normal ht)
            (fun t ht => hmatrixCurvatureCoords ht))
          hpos).data) := by
  let hpos :
      CoordinateJacobiPositivityData n sys k :=
    coordinateJacobiPositivityData_of_coordinateParallelBridge
      (sys := sys) (k := k)
      (geom.toPositivityBridge hframe_orthonormal hmatrixCurvatureCoords)
  let hbound :
      HasRayleighUpperBoundOn sys.A (modelPosDomain k) k :=
    hasRayleighUpperBoundOn_of_coordinateFrame
      (frame := coordinateParallelFrame geom.connectionA geom.connectionA_cont)
      (s := modelPosDomain k)
      hsec
      (fun t _ => htangent_unit t)
      (fun t ht => hframe_orthonormal ht)
      (fun t ht => hframe_normal ht)
      (fun t ht => hmatrixCurvatureCoords ht)
  exact rauch_lowerComparison_of_coordinateJacobi_onModel
    (sys := sys) (k := k) hbound hpos

/-- Direct lower Rauch comparison from genuine Jacobi/geodesic data in the canonical
coordinate-parallel frame. -/
theorem rauch_lowerComparison_of_coordinateParallelJacobiGeometry
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hsec :
      NormalizedSectionalUpperBoundAlongCoordinate geom.metric geom.curvature geom.tangent k)
    (htangent_unit :
      ∀ t, coordinatePairingAt (geom.metric t) (geom.tangent t) (geom.tangent t) = 1)
    (hframe_orthonormal :
      ∀ t i j,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t) =
            if i = j then 1 else 0)
    (hframe_normal :
      ∀ t i,
        coordinatePairingAt (geom.metric t)
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)
          (geom.tangent t) = 0)
    (hmatrixCurvatureCoords :
      ∀ t ξ i,
        (Matrix.mulVec (sys.A t) ξ) i =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              (frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t ξ)
              (geom.tangent t) (geom.tangent t))
            (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t))) :
    RauchNormLowerComparison k
      (let bridge :=
        coordinateParallelRauchLowerBridgeData_of_jacobiGeometry
          (sys := sys) (k := k) geom hsec htangent_unit hframe_orthonormal hframe_normal
          hmatrixCurvatureCoords
       let hpos :=
        coordinateJacobiPositivityData_of_coordinateParallelBridge
          (sys := sys) (k := k) bridge.toPositivityBridge
       (rauchSupersolutionInputData_of_coordinateJacobi
          (sys := sys)
          (hasRayleighUpperBound_of_coordinateParallelLowerBridge bridge)
          hpos).data) := by
  exact rauch_lowerComparison_of_coordinateParallelJacobiGeometry_onModel
    (sys := sys) (k := k) geom hsec htangent_unit
    (fun _ _ i j => hframe_orthonormal _ i j)
    (fun _ _ i => hframe_normal _ i)
    (fun _ _ ξ i => hmatrixCurvatureCoords _ ξ i)

end Comparison
