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
  /-- Field derivative at `t = 0` (boundary of `modelPosDomain`). -/
  fieldDeriv_zero :
    HasDerivAt field (covDeriv 0 + coordinateParallelRhs connectionA 0 (field 0)) 0
  /-- Covariant derivative of the covariant derivative at `t = 0`. -/
  covDerivDeriv_zero :
    HasDerivAt covDeriv
      (covSecondDeriv 0 + coordinateParallelRhs connectionA 0 (covDeriv 0)) 0
  /-- Frame derivative at `t = 0`. -/
  frameDeriv_zero : ∀ i : Fin n,
    HasDerivAt ((coordinateParallelFrame connectionA connectionA_cont).vec i)
      (coordinateParallelRhs connectionA 0
        (((coordinateParallelFrame connectionA connectionA_cont).vec i) 0)) 0
  /-- Metric compatibility at `t = 0`. -/
  pairingCompat_zero :
    metricDeriv 0 =
      Matrix.transpose (connectionA 0) * metric 0 + metric 0 * connectionA 0
  /-- Nontrivial initial velocity in the parallel frame at `t = 0`. -/
  initialVelocityPos :
    0 < vecNormSq
      (coordinateParallelCovDerivCoeffs metric connectionA connectionA_cont covDeriv 0)

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
theorem jacobiCoords_of_coordinateParallelJacobiGeometry_of_fieldCurvatureCoords
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hfieldCurvatureCoords :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i : Fin n,
        coordinatePairingAt (geom.metric t)
          (geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t))
          (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)) =
            (Matrix.mulVec (sys.A t)
              ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
                geom.field) t)) i)
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
  have hcurv := hfieldCurvatureCoords ht i
  calc
    coordinatePairingAt (geom.metric t) (geom.covSecondDeriv t) (E.vec i t)
        = -coordinatePairingAt (geom.metric t)
            (geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t)) (E.vec i t) := by
            linarith
    _ = (-(Matrix.mulVec (sys.A t)
          ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
            geom.field) t))) i := by
          simpa using congrArg Neg.neg hcurv

/-- The Jacobi equation together with the matrix curvature-coordinate bridge yields the
field-specific coefficient equation required by the positivity-set bridge. -/
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
  exact jacobiCoords_of_coordinateParallelJacobiGeometry_of_fieldCurvatureCoords
    (sys := sys) (k := k) geom
    (fun t ht i =>
      curvatureFieldCoords_of_matrixCurvatureCoords
        (sys := sys) (k := k) geom hframe_orthonormal hmatrixCurvatureCoords ht i)
    ht i

/-- A genuine Jacobi/geodesic package yields the coefficient-level positivity-set bridge from the
field-specific curvature identity alone. -/
noncomputable def CoordinateParallelJacobiGeometryData.toPositivityBridge_of_fieldCurvatureCoords
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hfieldCurvatureCoords :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i : Fin n,
        coordinatePairingAt (geom.metric t)
          (geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t))
          (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)) =
            (Matrix.mulVec (sys.A t)
              ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
                geom.field) t)) i) :
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
    exact jacobiCoords_of_coordinateParallelJacobiGeometry_of_fieldCurvatureCoords
      (sys := sys) (k := k) geom hfieldCurvatureCoords ht i
  positive := geom.positive

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
    CoordinateParallelJacobiPositivityBridgeData sys k :=
  geom.toPositivityBridge_of_fieldCurvatureCoords
    (fun t ht i =>
      curvatureFieldCoords_of_matrixCurvatureCoords
        (sys := sys) (k := k) geom hframe_orthonormal hmatrixCurvatureCoords ht i)

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
coordinate-parallel frame, using only the two weaker curvature bridges actually consumed
downstream:

* a Rayleigh-side quadratic-form bridge for arbitrary `ξ`,
* a field-specific curvature-coordinate bridge for the chosen Jacobi field. -/
theorem rauch_lowerComparison_of_coordinateParallelJacobiGeometry_split
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
    (hcurvatureQuad :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ ξ,
        matrixQuadForm (sys.A t) ξ =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              (frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t ξ)
              (geom.tangent t) (geom.tangent t))
            (frameLift (coordinateParallelFrame geom.connectionA geom.connectionA_cont) t ξ))
    (hfieldCurvatureCoords :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i : Fin n,
        coordinatePairingAt (geom.metric t)
          (geom.curvature (geom.field t) (geom.tangent t) (geom.tangent t))
          (((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)) =
            (Matrix.mulVec (sys.A t)
              ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
                geom.field) t)) i) :
    RauchNormLowerComparison k
      (let hpos :=
        coordinateJacobiPositivityData_of_coordinateParallelBridge
          (sys := sys) (k := k)
          (geom.toPositivityBridge_of_fieldCurvatureCoords hfieldCurvatureCoords)
       (rauchSupersolutionInputData_of_coordinateJacobi_onModel
          (sys := sys)
          (hasRayleighUpperBoundOn_of_coordinateFrameQuadratic
            (frame := coordinateParallelFrame geom.connectionA geom.connectionA_cont)
            (s := modelPosDomain k)
            hsec
            (fun t _ => htangent_unit t)
            (fun t ht => hframe_orthonormal ht)
            (fun t ht => hframe_normal ht)
            (fun t ht => hcurvatureQuad ht))
          hpos).data) := by
  let hpos :
      CoordinateJacobiPositivityData n sys k :=
    coordinateJacobiPositivityData_of_coordinateParallelBridge
      (sys := sys) (k := k)
      (geom.toPositivityBridge_of_fieldCurvatureCoords hfieldCurvatureCoords)
  let hbound :
      HasRayleighUpperBoundOn sys.A (modelPosDomain k) k :=
    hasRayleighUpperBoundOn_of_coordinateFrameQuadratic
      (frame := coordinateParallelFrame geom.connectionA geom.connectionA_cont)
      (s := modelPosDomain k)
      hsec
      (fun t _ => htangent_unit t)
      (fun t ht => hframe_orthonormal ht)
      (fun t ht => hframe_normal ht)
      (fun t ht => hcurvatureQuad ht)
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

/-! ### Zero-point derivative theorems

The parallel coefficient derivatives at `t = 0` (excluded from `modelPosDomain k`),
derived from the `_zero` fields of `CoordinateParallelJacobiGeometryData`. -/

/-- First derivative of the parallel coefficient at `t = 0`. -/
theorem hasDerivAt_coordinateParallelCoeff_atZero
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (i : Fin n) :
    HasDerivAt
      (fun s =>
        (coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
          geom.field) s i)
      ((coordinateParallelCovDerivCoeffs geom.metric geom.connectionA geom.connectionA_cont
          geom.covDeriv) 0 i) 0 := by
  let E := coordinateParallelFrame geom.connectionA geom.connectionA_cont
  have hpair :=
    hasDerivAt_coordinatePairing
      (g := geom.metric) (dg := geom.metricDeriv)
      (Y := geom.field) (Z := E.vec i) (t := 0)
      (fun a b => geom.metricDeriv_hasDeriv 0 a b)
      geom.fieldDeriv_zero (geom.frameDeriv_zero i)
  have hzero :=
    coordinatePairingAt_parallel_deriv_eq_zero
      geom.connectionA geom.metric geom.metricDeriv 0 (geom.field 0) (E.vec i 0)
      geom.pairingCompat_zero
  have hsplit :
      coordinatePairingAt (geom.metric 0)
          (geom.covDeriv 0 + coordinateParallelRhs geom.connectionA 0 (geom.field 0))
          (E.vec i 0) =
        coordinatePairingAt (geom.metric 0) (geom.covDeriv 0) (E.vec i 0) +
          coordinatePairingAt (geom.metric 0)
            (coordinateParallelRhs geom.connectionA 0 (geom.field 0)) (E.vec i 0) := by
    simp [coordinatePairingAt_add_left]
  have hsum :
      coordinatePairingAt (geom.metricDeriv 0) (geom.field 0) (E.vec i 0) +
          coordinatePairingAt (geom.metric 0)
            (geom.covDeriv 0 + coordinateParallelRhs geom.connectionA 0 (geom.field 0))
            (E.vec i 0) +
          coordinatePairingAt (geom.metric 0) (geom.field 0)
            (coordinateParallelRhs geom.connectionA 0 (E.vec i 0)) =
        coordinatePairingAt (geom.metric 0) (geom.covDeriv 0) (E.vec i 0) := by
    rw [hsplit]
    linarith
  have hpair' :
      HasDerivAt
        (fun s =>
          (coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
            geom.field) s i)
        (coordinatePairingAt (geom.metricDeriv 0) (geom.field 0) (E.vec i 0) +
            coordinatePairingAt (geom.metric 0)
              (geom.covDeriv 0 + coordinateParallelRhs geom.connectionA 0 (geom.field 0))
              (E.vec i 0) +
            coordinatePairingAt (geom.metric 0) (geom.field 0)
              (coordinateParallelRhs geom.connectionA 0 (E.vec i 0))) 0 := by
    simpa [coordinateParallelCoeffs, E] using hpair
  convert hpair' using 1
  simpa [coordinateParallelCovDerivCoeffs, E] using hsum.symm

/-- Second derivative of the parallel coefficient at `t = 0`.

At `t = 0` the curvature-coordinate identity `⟨W, Eᵢ⟩ = -(A · J)ᵢ` simplifies to
`0 = 0` because `J(0) = 0` (from `fieldZero`). -/
theorem hasDerivAt_coordinateParallelCovDerivCoeff_atZero
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (i : Fin n) :
    HasDerivAt
      (fun s =>
        (coordinateParallelCovDerivCoeffs geom.metric geom.connectionA geom.connectionA_cont
          geom.covDeriv) s i)
      (-(Matrix.mulVec (sys.A 0)
          ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
            geom.field) 0)) i) 0 := by
  let E := coordinateParallelFrame geom.connectionA geom.connectionA_cont
  have hpair :=
    hasDerivAt_coordinatePairing
      (g := geom.metric) (dg := geom.metricDeriv)
      (Y := geom.covDeriv) (Z := E.vec i) (t := 0)
      (fun a b => geom.metricDeriv_hasDeriv 0 a b)
      geom.covDerivDeriv_zero (geom.frameDeriv_zero i)
  have hzero :=
    coordinatePairingAt_parallel_deriv_eq_zero
      geom.connectionA geom.metric geom.metricDeriv 0 (geom.covDeriv 0) (E.vec i 0)
      geom.pairingCompat_zero
  have hsplit :
      coordinatePairingAt (geom.metric 0)
          (geom.covSecondDeriv 0 + coordinateParallelRhs geom.connectionA 0 (geom.covDeriv 0))
          (E.vec i 0) =
        coordinatePairingAt (geom.metric 0) (geom.covSecondDeriv 0) (E.vec i 0) +
          coordinatePairingAt (geom.metric 0)
            (coordinateParallelRhs geom.connectionA 0 (geom.covDeriv 0)) (E.vec i 0) := by
    simp [coordinatePairingAt_add_left]
  have hsum :
      coordinatePairingAt (geom.metricDeriv 0) (geom.covDeriv 0) (E.vec i 0) +
          coordinatePairingAt (geom.metric 0)
            (geom.covSecondDeriv 0 + coordinateParallelRhs geom.connectionA 0 (geom.covDeriv 0))
            (E.vec i 0) +
          coordinatePairingAt (geom.metric 0) (geom.covDeriv 0)
            (coordinateParallelRhs geom.connectionA 0 (E.vec i 0)) =
        coordinatePairingAt (geom.metric 0) (geom.covSecondDeriv 0) (E.vec i 0) := by
    rw [hsplit]
    linarith
  -- At t = 0: J(0) = 0 so -(A(0)·J(0))ᵢ = 0, and ⟨W(0), Eᵢ(0)⟩ = 0 by jacobiEq + fieldZero.
  have hJ_zero :
      (coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
        geom.field) 0 = 0 := by
    funext j
    rw [coordinateParallelCoeffs, geom.fieldZero, coordinateParallelFrame_initial]
    simp [coordinatePairingAt]
  have hcurv_zero :
      coordinatePairingAt (geom.metric 0) (geom.covSecondDeriv 0) (E.vec i 0) =
        (-(Matrix.mulVec (sys.A 0)
          ((coordinateParallelCoeffs geom.metric geom.connectionA geom.connectionA_cont
            geom.field) 0)) i) := by
    rw [hJ_zero]
    simp [Matrix.mulVec, dotProduct, coordinatePairingAt]
    -- covSecondDeriv 0 = -R(field 0, T 0)T 0 = -R(0, T 0)T 0 = 0 by jacobiEq + fieldZero
    have hjacobi := geom.jacobiEq 0
    have hfield0 := geom.fieldZero
    -- jacobiEq: covSecondDeriv 0 + curvature (field 0) (tangent 0) (tangent 0) = 0
    -- field 0 = 0, so curvature 0 T T = 0 by smul_left: R (0 • x) y z = 0 • R x y z = 0
    -- Actually R(0, Y)Z = 0: from add_left, R(0+0)YZ = R(0)YZ + R(0)YZ, so R(0)YZ = 0
    have hR_zero : geom.curvature (0 : CoordinateVector n) (geom.tangent 0) (geom.tangent 0) = 0 := by
      have h := geom.curvature.smul_left (0 : ℝ) (0 : CoordinateVector n) (geom.tangent 0) (geom.tangent 0)
      simp at h
      exact h
    rw [hfield0] at hjacobi
    rw [hR_zero, add_zero] at hjacobi
    -- Now covSecondDeriv 0 = 0
    rw [hjacobi]
    simp
  have hpair' :
      HasDerivAt
        (fun s =>
          (coordinateParallelCovDerivCoeffs geom.metric geom.connectionA geom.connectionA_cont
            geom.covDeriv) s i)
        (coordinatePairingAt (geom.metricDeriv 0) (geom.covDeriv 0) (E.vec i 0) +
            coordinatePairingAt (geom.metric 0)
              (geom.covSecondDeriv 0 +
                coordinateParallelRhs geom.connectionA 0 (geom.covDeriv 0))
              (E.vec i 0) +
            coordinatePairingAt (geom.metric 0) (geom.covDeriv 0)
              (coordinateParallelRhs geom.connectionA 0 (E.vec i 0))) 0 := by
    simpa [coordinateParallelCovDerivCoeffs, E] using hpair
  convert hpair' using 1
  simpa [coordinateParallelCoeffs, E] using hcurv_zero.symm.trans hsum.symm

end Comparison
