import Comparison.RauchCoordinateJacobiGeometry

/-! # Geometric Realization for Comparison Theorems

This file provides the entry point from natural Riemannian geometry data (metric, connection,
curvature, geodesic, Jacobi field) to the full Rauch/Bishop-Gromov comparison chain.

## The geometric realization gap

The active comparison chain is:

```
ScalarJacobiComparisonData + HasScalarJacobiComparison
  → DexpNormComparison (per direction)
  → BasiswiseDexpNormComparison (all n directions)
  → Jacobian majorant (via Hadamard)
  → HasLocalVolumeDensityComparison (via LocalVolumeComparisonConstructionFromJacobianBound)
  → HasBishopGromovMonotonicity (via BishopGromovConstructionFromDensity)
```

This chain is fully proved. The remaining "geometric realization gap" is:

**How does one construct `HasScalarJacobiComparison` from the actual Riemannian data?**

The answer goes through the following reduction:

1. Riemannian data → `CoordinateFrameCurvatureBridgeData` (frame + curvature representation)
2. Bridge → `HasRayleighUpperBound` (via `hasRayleighUpperBound_of_coordinateFrameCurvatureBridge`)
3. Rayleigh bound → norm-squared supersolution (via `RauchNormCore`)
4. Square root → `HasScalarJacobiLowerComparison` (via `RauchNormSqrt` + `RauchPositivitySet`)

Steps 2–4 are fully proved. Step 1 requires:

* `frame_orthonormal` — parallel frame preserves orthonormality (derivable from metric
  compatibility + initial conditions via `coordinateParallelFrame_isOrthonormal`, but only on the
  local transport domain; global extension needs completeness)
* `frame_normal` — frame vectors stay perpendicular to the tangent (derivable from metric
  compatibility + tangent being parallel, but requires the tangent field to be in the same
  transport family)
* `curvatureCoords` — the Jacobi coefficient matrix `A(t)` equals the projection of
  `R(·, T)T` onto the normal frame. **This is the genuine hard geometric content.**

This file provides:

* `RiemannianGeodesicComparisonSetup`: the natural geometric primitives from which
  `CoordinateFrameCurvatureBridgeData` is constructed.
* `coordinateFrameCurvatureBridge_of_setup`: the construction.
* `FullRauchComparisonSetup`: combines geodesic setup with Jacobi field data for the
  complete lower comparison.
* `coordinateParallelRauchLowerBridgeData_of_fullSetup`: builds the full lower bridge.
* `rauch_lowerComparison_of_fullSetup`: the end-to-end lower Rauch comparison.
-/

namespace Comparison

open ParallelTransport

variable {n : ℕ}

/-! ## Geodesic curvature setup

The natural geometric input for constructing `CoordinateFrameCurvatureBridgeData`.
This captures what a geometer naturally has when studying comparison along a geodesic:
a metric, connection, curvature tensor, unit-speed tangent, and the key bridge
relating the Jacobi coefficient matrix to curvature. -/

/-- Geometric data for a unit-speed geodesic in coordinate form, together with the
curvature-to-matrix bridge needed for Rauch comparison.

**Mathematical content of each field:**

* `connectionA` — the connection matrix `Γ(t)` along the geodesic; governs parallel transport
  via `dE/dt = -Γ(t) E(t)`
* `metric` — the Riemannian metric tensor `g(t)` along the geodesic in coordinate form
* `tangent` — the velocity field `T(t) = γ'(t)` of the reference geodesic
* `curvature` — the Riemannian curvature tensor `R` along the geodesic
* `sys` — the Jacobi coefficient system `Y'' + A(t)Y = 0`
* `tangent_unit` — `⟨T(t), T(t)⟩_g = 1`: the geodesic has unit speed
* `frame_orthonormal` — the parallel frame stays orthonormal for all time
  (follows from metric compatibility for complete manifolds; needs global transport existence)
* `frame_normal` — frame vectors are perpendicular to the tangent for all time
  (follows from metric compatibility + tangent being autoparallel)
* `curvatureCoords` — `(A(t) ξ)_i = ⟨R(∑ⱼ ξⱼ eⱼ(t), T(t)) T(t), eᵢ(t)⟩_g`:
  **the core geometric bridge** relating the abstract matrix `A(t)` to the actual curvature
  tensor. This is the projection of the curvature endomorphism `R(·,T)T` onto the
  parallel normal frame. -/
structure RiemannianGeodesicComparisonSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) where
  connectionA : ℝ → Matrix (Fin n) (Fin n) ℝ
  connectionA_cont : ∀ i j, Continuous fun t => connectionA t i j
  metric : ℝ → Matrix (Fin n) (Fin n) ℝ
  tangent : FieldAlong (CoordinateVector n)
  curvature : Curvature.CurvatureTensor C
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
  curvatureCoords :
    ∀ t ξ i,
      (Matrix.mulVec (sys.A t) ξ) i =
        coordinatePairingAt (metric t)
          (curvature
            (frameLift (coordinateParallelFrame connectionA connectionA_cont) t ξ)
            (tangent t) (tangent t))
          ((coordinateParallelFrame connectionA connectionA_cont).vec i t)

/-- Construct `CoordinateFrameCurvatureBridgeData` from the natural geodesic comparison setup. -/
noncomputable def coordinateFrameCurvatureBridge_of_setup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n}
    (setup : RiemannianGeodesicComparisonSetup (n := n) (C := C) sys) :
    CoordinateFrameCurvatureBridgeData setup.metric setup.curvature setup.tangent sys where
  frame := coordinateParallelFrame setup.connectionA setup.connectionA_cont
  tangent_unit := setup.tangent_unit
  frame_orthonormal := setup.frame_orthonormal
  frame_normal := setup.frame_normal
  curvatureCoords := setup.curvatureCoords

/-- From the geodesic setup and a sectional curvature upper bound, derive the Rayleigh
inequality needed by the norm-squared comparison core. -/
theorem hasRayleighUpperBound_of_setup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (setup : RiemannianGeodesicComparisonSetup (n := n) (C := C) sys)
    (hsec : NormalizedSectionalUpperBoundAlongCoordinate setup.metric setup.curvature setup.tangent k) :
    HasRayleighUpperBound sys.A k :=
  hasRayleighUpperBound_of_coordinateFrameCurvatureBridge hsec
    (coordinateFrameCurvatureBridge_of_setup setup)

/-! ## Full Rauch comparison setup

Combines the geodesic curvature setup with Jacobi field data for the complete lower
comparison theorem. -/

/-- Full geometric setup for lower Rauch comparison: a unit-speed geodesic with curvature
bound, plus a Jacobi field along it with the required regularity.

**Mathematical content of the Jacobi field assumptions:**

* `field` — the Jacobi field `Y(t)` with `Y(0) = 0`
* `covDeriv` — the covariant derivative `∇_T Y(t)` along the geodesic
* `covSecondDeriv` — the second covariant derivative `∇²_T Y(t)`
* `fieldDeriv` — `Y'(t) = ∇_T Y(t) + Γ(t)·Y(t)`: the coordinate ODE for the Jacobi field
* `covDerivDeriv` — `V'(t) = ∇²_T Y(t) + Γ(t)·V(t)`: the coordinate ODE for ∇_T Y
* `jacobiCoords` — `⟨∇²_T Y, eᵢ⟩_g = -(A(t)·ξ(t))_i`: the Jacobi equation projected
  onto the parallel frame, where `ξ(t)_i = ⟨Y(t), eᵢ(t)⟩_g`
* `positive` — `‖ξ(t)‖² > 0` on the model positivity domain: the Jacobi field doesn't vanish -/
structure FullRauchComparisonSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ) extends
    RiemannianGeodesicComparisonSetup (n := n) (C := C) sys where
  metricDeriv : ℝ → Matrix (Fin n) (Fin n) ℝ
  metricDeriv_hasDeriv : ∀ t i j, HasDerivAt (fun s => metric s i j) (metricDeriv t i j) t
  pairingCompat :
    ∀ t ∈ modelPosDomain k,
      metricDeriv t =
        Matrix.transpose (connectionA t) * metric t + metric t * connectionA t
  sectionalUpper :
    NormalizedSectionalUpperBoundAlongCoordinate metric curvature tangent k
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

/-- Construct `CoordinateParallelRauchLowerBridgeData` from the full geometric setup. -/
noncomputable def coordinateParallelRauchLowerBridgeData_of_fullSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (setup : FullRauchComparisonSetup (n := n) (C := C) sys k) :
    CoordinateParallelRauchLowerBridgeData (n := n) (C := C) sys k where
  connectionA := setup.connectionA
  connectionA_cont := setup.connectionA_cont
  metric := setup.metric
  metricDeriv := setup.metricDeriv
  metricDeriv_hasDeriv := setup.metricDeriv_hasDeriv
  pairingCompat := setup.pairingCompat
  tangent := setup.tangent
  curvature := setup.curvature
  sectionalUpper := setup.sectionalUpper
  tangent_unit := setup.tangent_unit
  frame_orthonormal := setup.frame_orthonormal
  frame_normal := setup.frame_normal
  matrixCurvatureCoords := setup.curvatureCoords
  field := setup.field
  covDeriv := setup.covDeriv
  covSecondDeriv := setup.covSecondDeriv
  fieldZero := setup.fieldZero
  initialSlope := setup.initialSlope
  fieldDeriv := setup.fieldDeriv
  covDerivDeriv := setup.covDerivDeriv
  frameDeriv := setup.frameDeriv
  jacobiCoords := setup.jacobiCoords
  positive := setup.positive

/-- End-to-end lower Rauch comparison from the full Riemannian geodesic setup. -/
theorem rauch_lowerComparison_of_fullSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (setup : FullRauchComparisonSetup (n := n) (C := C) sys k) :
    RauchNormLowerComparison k
      (let bridge := coordinateParallelRauchLowerBridgeData_of_fullSetup setup
       let hpos := coordinateJacobiPositivityData_of_coordinateParallelBridge
         (sys := sys) (k := k) bridge.toPositivityBridge
       (rauchSupersolutionInputData_of_coordinateJacobi
         (sys := sys)
         (hasRayleighUpperBound_of_coordinateParallelLowerBridge bridge)
         hpos).data) :=
  rauch_lowerComparison_of_coordinateParallelLowerBridge sys k
    (coordinateParallelRauchLowerBridgeData_of_fullSetup setup)

/-! ## Local active full setup

This is the owner-facing route that avoids the false global burden on frame orthonormality and
frame normality. The actual active comparison chain only uses those facts on `modelPosDomain k`,
so they should be derived from transport-domain hypotheses rather than postulated on all of `ℝ`. -/

/-- Local/full geometric setup for the active lower-Rauch route.

This extends the genuine Jacobi/geodesic package by the transport-domain hypotheses needed to
derive frame orthonormality and frame normality on `modelPosDomain k`, plus the remaining hard
matrix-curvature coordinate bridge on that same domain. -/
structure FullRauchComparisonLocalSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ) extends
    CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k where
  hgcont : ∀ i j, Continuous fun t => metric t i j
  pairingCompat_transport :
    ∀ t ∈ Set.Ioo (-(coordinateTransportData connectionA connectionA_cont).ε)
        (coordinateTransportData connectionA connectionA_cont).ε,
      metricDeriv t =
        Matrix.transpose (connectionA t) * metric t + metric t * connectionA t
  transport_contains_modelPosDomain :
    modelPosDomain k ⊆ transportDomain (coordinateParallelTransport connectionA connectionA_cont)
  sectionalUpper :
    NormalizedSectionalUpperBoundAlongCoordinate metric curvature tangent k
  tangent_unit :
    ∀ t, coordinatePairingAt (metric t) (tangent t) (tangent t) = 1
  tangent_parallel :
    IsParallelAlong (coordinateParallelAlongDerivative connectionA connectionA_cont) tangent
  initialFrameOrthonormal :
    ∀ i j,
      coordinatePairingAt (metric 0) (coordinateBasisVector i) (coordinateBasisVector j) =
        if i = j then 1 else 0
  initialFrameNormal :
    ∀ i,
      coordinatePairingAt (metric 0) (coordinateBasisVector i) (tangent 0) = 0
  matrixCurvatureCoords :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ ξ i,
      (Matrix.mulVec (sys.A t) ξ) i =
        coordinatePairingAt (metric t)
          (curvature
            (frameLift (coordinateParallelFrame connectionA connectionA_cont) t ξ)
            (tangent t) (tangent t))
          (((coordinateParallelFrame connectionA connectionA_cont).vec i t))

/-! ## Helper: frame orthonormality from metric compatibility

When the metric compatibility condition `dg = Aᵀg + gA` holds on the transport domain and the
initial metric makes the standard basis orthonormal, the parallel frame is automatically
orthonormal on the entire transport domain.

For a **complete** manifold the transport domain is all of `ℝ`, so `frame_orthonormal` follows.
For a local setup, this lemma shows orthonormality on the transport domain, and the user must
extend to the full domain required by `RiemannianGeodesicComparisonSetup`. -/

/-- Metric compatibility makes the pairing of any two parallel fields constant on the transport
domain. This is the owner-level invariant behind both frame orthonormality and frame normality. -/
theorem coordinatePairingAt_eq_initial_of_parallel_on_transportDomain
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (g dg : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hgcont : ∀ i j, Continuous fun t => g t i j)
    (hdg : ∀ t i j, HasDerivAt (fun s => g s i j) (dg t i j) t)
    (hcompat :
      ∀ t ∈ Set.Ioo (-(coordinateTransportData A hAcont).ε)
          (coordinateTransportData A hAcont).ε,
        dg t = Matrix.transpose (A t) * g t + g t * A t)
    {Y Z : FieldAlong (CoordinateVector n)}
    (hY : IsParallelAlong (coordinateParallelAlongDerivative A hAcont) Y)
    (hZ : IsParallelAlong (coordinateParallelAlongDerivative A hAcont) Z) :
    ∀ t ∈ transportDomain (coordinateParallelTransport A hAcont),
      coordinatePairingAt (g t) (Y t) (Z t) =
        coordinatePairingAt (g 0) (Y 0) (Z 0) := by
  let T := coordinateParallelTransport A hAcont
  have hpres :=
    coordinateParallelTransport_preservesPairing A hAcont g dg hgcont hdg hcompat
  have hYeq : Set.EqOn Y (T (Y 0)) (transportDomain T) := by
    simpa [T] using coordinateParallelTransport_unique A hAcont rfl hY
  have hZeq : Set.EqOn Z (T (Z 0)) (transportDomain T) := by
    simpa [T] using coordinateParallelTransport_unique A hAcont rfl hZ
  intro t ht
  have hYt : Y t = T (Y 0) t := hYeq ht
  have hZt : Z t = T (Z 0) t := hZeq ht
  calc
    coordinatePairingAt (g t) (Y t) (Z t)
        = coordinatePairingAt (g t) (T (Y 0) t) (T (Z 0) t) := by rw [hYt, hZt]
    _ = coordinatePairingAt (g 0) (Y 0) (Z 0) := by
        simpa [T, coordinatePairing] using hpres.2 (Y 0) (Z 0) t ht

/-- If a field is parallel for the same connection and starts orthogonal to the transported basis,
then it stays orthogonal to that basis on the transport domain. This is the honest local form of
the `frame_normal` input. -/
theorem coordinateParallelFrame_normal_on_transportDomain
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (g dg : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hgcont : ∀ i j, Continuous fun t => g t i j)
    (hdg : ∀ t i j, HasDerivAt (fun s => g s i j) (dg t i j) t)
    (hcompat :
      ∀ t ∈ Set.Ioo (-(coordinateTransportData A hAcont).ε)
          (coordinateTransportData A hAcont).ε,
        dg t = Matrix.transpose (A t) * g t + g t * A t)
    {Y : FieldAlong (CoordinateVector n)}
    (hY : IsParallelAlong (coordinateParallelAlongDerivative A hAcont) Y)
    (h₀ : ∀ i,
      coordinatePairingAt (g 0) (coordinateBasisVector i) (Y 0) = 0) :
    ∀ t ∈ transportDomain (coordinateParallelTransport A hAcont),
      ∀ i,
        coordinatePairingAt (g t)
          ((coordinateParallelFrame A hAcont).vec i t) (Y t) = 0 := by
  intro t ht i
  have hconst :=
    coordinatePairingAt_eq_initial_of_parallel_on_transportDomain
      A hAcont g dg hgcont hdg hcompat
      (Y := (coordinateParallelFrame A hAcont).vec i)
      (Z := Y)
      (coordinateParallelFrame_isParallel A hAcont i)
      hY t ht
  calc
    coordinatePairingAt (g t)
        ((coordinateParallelFrame A hAcont).vec i t) (Y t)
        = coordinatePairingAt (g 0)
            ((coordinateParallelFrame A hAcont).vec i 0) (Y 0) := hconst
    _ = coordinatePairingAt (g 0) (coordinateBasisVector i) (Y 0) := by
          rw [coordinateParallelFrame_initial A hAcont i]
    _ = 0 := h₀ i

theorem coordinateParallelFrame_orthonormal_on_transportDomain
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (g dg : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hgcont : ∀ i j, Continuous fun t => g t i j)
    (hdg : ∀ t i j, HasDerivAt (fun s => g s i j) (dg t i j) t)
    (hcompat :
      ∀ t ∈ Set.Ioo (-(coordinateTransportData A hAcont).ε)
          (coordinateTransportData A hAcont).ε,
        dg t = Matrix.transpose (A t) * g t + g t * A t)
    (h₀ : ∀ i j,
      coordinatePairingAt (g 0) (coordinateBasisVector i) (coordinateBasisVector j) =
        if i = j then (1 : ℝ) else 0) :
    ∀ t ∈ transportDomain (coordinateParallelTransport A hAcont),
      ∀ i j,
        coordinatePairingAt (g t)
          ((coordinateParallelFrame A hAcont).vec i t)
          ((coordinateParallelFrame A hAcont).vec j t) =
            if i = j then 1 else 0 := by
  intro t ht i j
  have hortho :=
    coordinateParallelFrame_isOrthonormal A hAcont g dg hgcont hdg hcompat
      (fun a b => if a = b then (1 : ℝ) else 0) h₀
  exact hortho i j t ht

/-- When the metric compatibility holds globally (not just on the transport domain), and the
initial metric makes the standard basis orthonormal, the parallel frame is orthonormal on the
transport domain. This is the typical case for complete manifolds. -/
theorem coordinateParallelFrame_orthonormal_of_globalCompat
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (g dg : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hgcont : ∀ i j, Continuous fun t => g t i j)
    (hdg : ∀ t i j, HasDerivAt (fun s => g s i j) (dg t i j) t)
    (hcompat : ∀ t, dg t = Matrix.transpose (A t) * g t + g t * A t)
    (h₀ : ∀ i j,
      coordinatePairingAt (g 0) (coordinateBasisVector i) (coordinateBasisVector j) =
        if i = j then (1 : ℝ) else 0) :
    ∀ t ∈ transportDomain (coordinateParallelTransport A hAcont),
      ∀ i j,
        coordinatePairingAt (g t)
          ((coordinateParallelFrame A hAcont).vec i t)
          ((coordinateParallelFrame A hAcont).vec j t) =
            if i = j then 1 else 0 :=
  coordinateParallelFrame_orthonormal_on_transportDomain A hAcont g dg hgcont hdg
    (fun t _ => hcompat t) h₀

/-- In the local/full setup, the canonical parallel frame is orthonormal on `modelPosDomain k`. -/
theorem frame_orthonormal_on_modelPosDomain_of_fullLocalSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (setup : FullRauchComparisonLocalSetup (n := n) (C := C) sys k) :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i j,
      coordinatePairingAt (setup.metric t)
        ((coordinateParallelFrame setup.connectionA setup.connectionA_cont).vec i t)
        ((coordinateParallelFrame setup.connectionA setup.connectionA_cont).vec j t) =
          if i = j then 1 else 0 := by
  intro t ht i j
  exact coordinateParallelFrame_orthonormal_on_transportDomain
    setup.connectionA setup.connectionA_cont setup.metric setup.metricDeriv
    setup.hgcont setup.metricDeriv_hasDeriv setup.pairingCompat_transport
    setup.initialFrameOrthonormal t (setup.transport_contains_modelPosDomain ht) i j

/-- In the local/full setup, the canonical parallel frame stays normal to the tangent on
`modelPosDomain k`. -/
theorem frame_normal_on_modelPosDomain_of_fullLocalSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (setup : FullRauchComparisonLocalSetup (n := n) (C := C) sys k) :
    ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i,
      coordinatePairingAt (setup.metric t)
        ((coordinateParallelFrame setup.connectionA setup.connectionA_cont).vec i t)
        (setup.tangent t) = 0 := by
  intro t ht i
  exact coordinateParallelFrame_normal_on_transportDomain
    setup.connectionA setup.connectionA_cont setup.metric setup.metricDeriv
    setup.hgcont setup.metricDeriv_hasDeriv setup.pairingCompat_transport
    setup.tangent_parallel setup.initialFrameNormal t
    (setup.transport_contains_modelPosDomain ht) i

/-- The local/full setup yields the Rayleigh upper bound on `modelPosDomain k`, which is the
actual domain used by the repaired lower-Rauch comparison chain. -/
theorem hasRayleighUpperBoundOn_modelPosDomain_of_fullLocalSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (setup : FullRauchComparisonLocalSetup (n := n) (C := C) sys k) :
    HasRayleighUpperBoundOn sys.A (modelPosDomain k) k := by
  exact hasRayleighUpperBoundOn_of_coordinateFrame
    (frame := coordinateParallelFrame setup.connectionA setup.connectionA_cont)
    (s := modelPosDomain k)
    setup.sectionalUpper
    (fun t _ => setup.tangent_unit t)
    (frame_orthonormal_on_modelPosDomain_of_fullLocalSetup setup)
    (frame_normal_on_modelPosDomain_of_fullLocalSetup setup)
    (fun t ht => setup.matrixCurvatureCoords ht)

/-- The active lower-Rauch theorem from the local/full setup. Frame orthonormality and frame
normality are derived internally on `modelPosDomain k` from transport-domain metric compatibility
and tangent parallelness; only the genuine hard curvature-coordinate bridge remains explicit. -/
theorem rauch_lowerComparison_of_fullLocalSetup
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (sys : Jacobi.CoordinateJacobiSystem n) (k : ℝ)
    (setup : FullRauchComparisonLocalSetup (n := n) (C := C) sys k) :
    RauchNormLowerComparison k
      (let hpos :=
        coordinateJacobiPositivityData_of_coordinateParallelBridge
          (sys := sys) (k := k)
          (setup.toCoordinateParallelJacobiGeometryData.toPositivityBridge
            (frame_orthonormal_on_modelPosDomain_of_fullLocalSetup setup)
            setup.matrixCurvatureCoords)
       (rauchSupersolutionInputData_of_coordinateJacobi_onModel
          (sys := sys)
          (hasRayleighUpperBoundOn_modelPosDomain_of_fullLocalSetup setup)
          hpos).data) := by
  exact rauch_lowerComparison_of_coordinateParallelJacobiGeometry_onModel
    (sys := sys) (k := k) setup.toCoordinateParallelJacobiGeometryData
    setup.sectionalUpper
    setup.tangent_unit
    (frame_orthonormal_on_modelPosDomain_of_fullLocalSetup setup)
    (frame_normal_on_modelPosDomain_of_fullLocalSetup setup)
    setup.matrixCurvatureCoords

/-! ## Curvature linearity constructor

When the curvature tensor is linear in its first argument and the basis-column identity holds,
the full `matrixCurvatureCoords` field can be derived internally. This is the preferred end state
described in the agent memo: the coefficient matrix is obtained from transported curvature, not
from a hand-filled hypothesis. -/

/-- Construct `FullRauchComparisonLocalSetup` from curvature linearity and the basis-column
identity `A(t)_ij = ⟨R(eⱼ(t), T(t)) T(t), eᵢ(t)⟩_g`, without postulating the full
componentwise `matrixCurvatureCoords` directly.

In actual Riemannian geometry the curvature tensor is always multilinear, and the basis identity
is the *definition* of the Jacobi coefficient matrix. So this constructor captures the genuine
geometric content with no artificial inflation. -/
noncomputable def FullRauchComparisonLocalSetup.ofCurvatureLinearity
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (hgcont : ∀ i j, Continuous fun t => geom.metric t i j)
    (pairingCompat_transport :
      ∀ t ∈ Set.Ioo (-(coordinateTransportData geom.connectionA geom.connectionA_cont).ε)
          (coordinateTransportData geom.connectionA geom.connectionA_cont).ε,
        geom.metricDeriv t =
          Matrix.transpose (geom.connectionA t) * geom.metric t +
            geom.metric t * geom.connectionA t)
    (transport_contains_modelPosDomain :
      modelPosDomain k ⊆
        transportDomain (coordinateParallelTransport geom.connectionA geom.connectionA_cont))
    (sectionalUpper :
      NormalizedSectionalUpperBoundAlongCoordinate geom.metric geom.curvature geom.tangent k)
    (tangent_unit :
      ∀ t, coordinatePairingAt (geom.metric t) (geom.tangent t) (geom.tangent t) = 1)
    (tangent_parallel :
      IsParallelAlong
        (coordinateParallelAlongDerivative geom.connectionA geom.connectionA_cont) geom.tangent)
    (initialFrameOrthonormal :
      ∀ i j,
        coordinatePairingAt (geom.metric 0) (coordinateBasisVector i) (coordinateBasisVector j) =
          if i = j then 1 else 0)
    (initialFrameNormal :
      ∀ i,
        coordinatePairingAt (geom.metric 0) (coordinateBasisVector i) (geom.tangent 0) = 0)
    (basisCurvatureCoords :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i j,
        sys.A t i j =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t)
              (geom.tangent t) (geom.tangent t))
            ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t)) :
    FullRauchComparisonLocalSetup (n := n) (C := C) sys k where
  __ := geom
  hgcont := hgcont
  pairingCompat_transport := pairingCompat_transport
  transport_contains_modelPosDomain := transport_contains_modelPosDomain
  sectionalUpper := sectionalUpper
  tangent_unit := tangent_unit
  tangent_parallel := tangent_parallel
  initialFrameOrthonormal := initialFrameOrthonormal
  initialFrameNormal := initialFrameNormal
  matrixCurvatureCoords := by
    intro t ht ξ i
    exact matrixCurvatureCoords_of_basisAndLinearity
      (coordinateParallelFrame geom.connectionA geom.connectionA_cont)
      geom.curvature.add_left geom.curvature.smul_left (basisCurvatureCoords ht) ξ i

/-- Canonical-system convenience wrapper over `ofCurvatureLinearity`.

When the coefficient system `sys` is definitionally identified with the transported-curvature
matrix `canonicalJacobiSystemOfCurvature`, the basis-column identity is automatic and callers do
not need to pass it separately. -/
noncomputable def FullRauchComparisonLocalSetup.ofCanonicalCurvatureSystem
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n} {k : ℝ}
    (geom : CoordinateParallelJacobiGeometryData (n := n) (C := C) sys k)
    (Acont : ∀ i j, Continuous fun t =>
      coordinatePairingAt (geom.metric t)
        (geom.curvature
          ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t)
          (geom.tangent t) (geom.tangent t))
        ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t))
    (hsys :
      sys =
        canonicalJacobiSystemOfCurvature
          geom.metric geom.curvature geom.tangent
          (coordinateParallelFrame geom.connectionA geom.connectionA_cont) Acont)
    (hgcont : ∀ i j, Continuous fun t => geom.metric t i j)
    (pairingCompat_transport :
      ∀ t ∈ Set.Ioo (-(coordinateTransportData geom.connectionA geom.connectionA_cont).ε)
          (coordinateTransportData geom.connectionA geom.connectionA_cont).ε,
        geom.metricDeriv t =
          Matrix.transpose (geom.connectionA t) * geom.metric t +
            geom.metric t * geom.connectionA t)
    (transport_contains_modelPosDomain :
      modelPosDomain k ⊆
        transportDomain (coordinateParallelTransport geom.connectionA geom.connectionA_cont))
    (sectionalUpper :
      NormalizedSectionalUpperBoundAlongCoordinate geom.metric geom.curvature geom.tangent k)
    (tangent_unit :
      ∀ t, coordinatePairingAt (geom.metric t) (geom.tangent t) (geom.tangent t) = 1)
    (tangent_parallel :
      IsParallelAlong
        (coordinateParallelAlongDerivative geom.connectionA geom.connectionA_cont) geom.tangent)
    (initialFrameOrthonormal :
      ∀ i j,
        coordinatePairingAt (geom.metric 0) (coordinateBasisVector i) (coordinateBasisVector j) =
          if i = j then 1 else 0)
    (initialFrameNormal :
      ∀ i,
        coordinatePairingAt (geom.metric 0) (coordinateBasisVector i) (geom.tangent 0) = 0) :
    FullRauchComparisonLocalSetup (n := n) (C := C) sys k := by
  have hbasis :
      ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → ∀ i j,
        sys.A t i j =
          coordinatePairingAt (geom.metric t)
            (geom.curvature
              ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec j t)
              (geom.tangent t) (geom.tangent t))
            ((coordinateParallelFrame geom.connectionA geom.connectionA_cont).vec i t) := by
    intro t _ i j
    have hA :
        sys.A t i j =
          (canonicalJacobiSystemOfCurvature
            geom.metric geom.curvature geom.tangent
            (coordinateParallelFrame geom.connectionA geom.connectionA_cont) Acont).A t i j := by
      exact congrArg (fun S : Jacobi.CoordinateJacobiSystem n => S.A t i j) hsys
    simpa [canonicalJacobiSystemOfCurvature_A] using hA
  exact FullRauchComparisonLocalSetup.ofCurvatureLinearity
    (geom := geom)
    hgcont pairingCompat_transport transport_contains_modelPosDomain
    sectionalUpper tangent_unit tangent_parallel
    initialFrameOrthonormal initialFrameNormal
    hbasis

end Comparison
