# Riemannian Geometry — Lean 4 Workspace

## What this project is

This repository is a Lean 4 / Mathlib formalization of Riemannian geometry, built as an AI-assisted proof engineering project. The goal is to construct a rigorous, machine-checkable library covering local and global Riemannian geometry — from metric infrastructure and Levi-Civita connections through geodesics, exponential maps, Jacobi fields, and ultimately global theorems such as Hopf–Rinow and comparison geometry.

The architecture deliberately separates two presentation styles that coexist in the codebase:

- **Abstract / type-class layer**: theorems stated over abstract `AddGroup`, `SMul`, and custom `ConnectionContext` types, giving results that are independent of any particular coordinate system.
- **Coordinate / `Fin n` layer**: theorems stated in explicit `Fin n → ℝ` coordinates, giving concrete computational content and enabling direct connection to Mathlib's ODE and measure theory libraries.

Both layers are present for most areas of the library and are linked by bridge lemmas.

---

## Toolchain and build

- **Lean**: `leanprover/lean4:v4.28.0`
- **Mathlib**: `leanprover-community/mathlib v4.28.0`
- **Lake workspace file**: `lakefile.toml`

**Important build rule**: use module names like `Exponential.Basic` and `Minimization.LocalMinimizers` directly — do not prepend `RiemannianGeometry.`.

```bash
lake build          # full project (~2977 jobs, green as of 2026-04-02)
lake build Exponential
lake build Minimization
```

**Proof policy (as of 2026-04-02)**:
The tree currently has `0` literal `sorry`, `0` literal `admit`, and `0` literal `axiom`
occurrences under `RiemannianGeometry/`, and full `lake build` is green. The remaining work is no
longer placeholder cleanup. The hard comparison bridge is now closed: `matrixCurvatureCoords` is
derived from basis coordinates plus structural curvature linearity, the canonical curvature-built
Jacobi system is available, and both the comparison realization layer and the Cartan-Hadamard
squared-norm layer now have canonical-system convenience constructors. The remaining active work is:
- direct end-to-end packaging theorems from the canonical local setup to positivity /
  no-conjugate-point conclusions, if desired by downstream users
- possible owner construction of the continuity witness `Acont` for the canonical coefficient
  matrix (acceptable witness debt for now)
- `HopfRinow/SmoothGeodesicComplete.lean` and `HopfRinow/MetricGeodesicBridge.lean` remain honest
  dormant interface packages for a smooth-to-metric route. They are not active blockers for the
  finished coordinate-level Hopf-Rinow theorem.



---

## Repository layout

```
RiemannianGeometry/
├── Bochner.lean                                    # root re-export
├── Bochner/
│   ├── Basic.lean                                  # BundleConnectionAlgebra, ConnectionForm, curvature
│   ├── Bochner.lean                                # covariant_square_eq_curvature_action
│   ├── ClassicalCoordinateBochner.lean             # Gradient, Hessian, scalarLaplacian, ricciAction
│   ├── ComponentBridge.lean                        # covariant_square_in_components
│   ├── ConcreteCoordinateBochner.lean              # concrete_coordinate_bochner
│   └── CoordinateBochner.lean                      # coordinate algebra, wedge products
├── Comparison.lean                                 # root re-export
├── Comparison/
│   ├── BishopGromov.lean                           # BishopGromovInput; active density-based route + legacy wrapper [cond]
│   ├── BishopGromovMonotonicity.lean               # bishopGromov_monotonicity_of_local_inequality
│   ├── GeometricRealization.lean                   # local active comparison setup; canonical-system constructors
│   ├── LocalVolumeFromRauch.lean                   # LocalVolumeFromRauchData, bridge Rauch→density (new)
│   ├── RauchCoordinateCurvatureBridge.lean         # frame/curvature Rayleigh bridge + canonical curvature-built Jacobi system
│   ├── RauchCoordinateJacobiGeometry.lean          # Jacobi geometry package with zero-time coefficient data
│   ├── RauchCoordinateLowerBridge.lean             # unified local Rauch bridge; compatibility layer
│   ├── RauchCoordinatePositivityBridge.lean        # Jacobi positivity bridge in the parallel frame
│   ├── VolumeGrowthFromDensity.lean                # bridge-free density→BG monotonicity
│   ├── CartanHadamard.lean                         # squared-norm reduction core + local/canonical geometric constructors [cond]
│   ├── Myers.lean                                  # MyersHypotheses, compactSpace_of_myers                   [cond]
│   ├── ODEModels.lean                              # sn(k,t), SatisfiesModelNormBound, modelPosDomain
│   ├── Rauch.lean                                  # SectionalUpperBound, dexp_normComparison_of_rauch        [cond]
│   ├── RauchReduction.lean                         # legacy scalar/norm reduction packaging [boundary]
│   ├── ScalarConvexity.lean                        # positivity from nonnegative second derivative
│   ├── ScalarJacobiComparison.lean                 # hasScalarJacobiComparison_of_subsolution
│   ├── SturmComparison.lean                        # scalarComparison_of_subsolution (complete)
│   ├── VolumeComparisonLocal.lean                  # thin local density wrapper [boundary]
│   └── VolumeConstruction.lean                     # Jacobian/density constructors + legacy wrappers [boundary]
├── Curvature.lean                                  # root re-export
├── Curvature/
│   ├── Basic.lean                                  # curvatureOperator R(X,Y)Z, CurvatureTensor
│   ├── SectionalRicci.lean                         # SectionalCurvature, RicciCurvature, RicciLowerBound
│   └── Symmetries.lean                             # FirstPairSkew, FirstBianchi, algebraic symmetries
├── ODE.lean                                        # root re-export
├── ODE/
│   ├── Core.lean                                   # autonomous flow adapter, Gronwall comparison, fixed-time Lipschitz dependence
│   ├── UniformRemainder.lean                       # compact-tube uniform first-order remainder estimate
│   ├── Linearized.lean                             # short-time linearized equation and evaluation operator
│   ├── LinearizedGlobal.lean                       # global linearized CLM via overlap uniqueness and piecewise assembly
│   ├── FlowFDeriv.lean                             # hasFlowFDerivAtFixedTime_of_contDiff (C¹ flow diff'ability)
│   └── FlowContDiff.lean                           # contDiffAt_flow_of_contDiff (C¹ flow regularity)
├── Exponential.lean                                # root re-export                                           [cond]
├── Exponential/
│   ├── Basic.lean                                  # LocalExponentialMap, coordinateExp, coordinateExp_zero
│   ├── DexpContinuity.lean                         # contDiffAt_coordinateExp, radial continuity of fderiv
│   ├── Differentiability.lean                      # coordinateExpHasFDerivAtOnSource_of_smoothChristoffel [CLOSED]
│   ├── DifferentialAtZero.lean                     # fderiv (coordinateExp p) 0 = id
│   ├── GaussLemma.lean                             # gaussLemma_coordinate (proved), gaussLemma_radial_pairing [cond]
│   ├── JacobiDexp.lean                             # hasDirectionalDexp_of_smoothChristoffel (witness-free)
│   ├── LocalAnalyticConstruction.lean              # `_auto` constructors; active local analytic route closed, compatibility package retained
│   ├── LocalAnalyticInput.lean                     # compatibility boundary package for local analytic data
│   ├── LocalAnalyticRealization.lean               # compatibility realization wrapper
│   ├── LocalInverse.lean                           # localExpInverse, PartialHomeomorph via IFT
│   ├── LocalRiemannianData.lean                    # LocalRiemannianData, isMetricCompatible
│   ├── NormalCoordinates.lean                      # normalCoordinates, roundtrip lemmas
│   ├── RadialBridge.lean                           # radialSource, smul_mem_radialSource_of_mem
│   ├── RadialGaussLemma.lean                       # owner radial-pairing theorem and `_auto` realization constructor
│   ├── RadialVariationIdentities.lean              # owner-local radial variation derivative helpers
│   └── VariationDexp.lean                          # HasDirectionalDexp [boundary], chain-rule wrappers
├── Geodesic.lean                                   # root re-export
├── Geodesic/
│   ├── Basic.lean                                  # Position, Velocity, State, InitialConditions
│   ├── CoordinateEquation.lean                     # geodesicAcceleration (ẍⁱ = -Γⁱⱼₖẋʲẋᵏ)
│   ├── FlowDifferentiability.lean                  # hasFlowFDerivAtInitialState_of_smoothChristoffel
│   ├── LocalExistence.lean                         # exists_isCoordinateGeodesicOn_Icc, LocalCoordinateGeodesicFlowData
│   ├── LocalUniqueness.lean                        # eqOn_Icc_of_isCoordinateGeodesicOn_lipschitzOn
│   └── Spray.lean                                  # geodesicSpray, IsCoordinateGeodesicOn, timeRescaleStateCurve
├── HopfRinow.lean                                  # root re-export                                           [cond]
├── HopfRinow/
│   ├── CompleteProper.lean                         # local-compactness reduction + coordinate complete→proper
│   ├── DistanceRealizer.lean                       # metric geodesic ↔ distance-realizer layer
│   ├── GeodesicExtension.lean                      # GeodesicExtensionData [boundary]: complete_geodesic
│   ├── HopfRinow.lean                              # corrected Hopf-Rinow public theorem spine                 [cond]
│   ├── InputConstruction.lean                      # CompleteProperData, HopfRinowData, CompleteToHopfRinowData [boundary]
│   ├── LengthCompactness.lean                      # hasLengthCompactness_of_proper (Arzela-Ascoli)
│   ├── LocalCompactness.lean                       # exists_compact_small_closedBall
│   ├── MetricGeodesicBridge.lean                   # dormant smooth→metric geodesic-extension bridge interface
│   ├── MetricLength.lean                           # prefix-length / reparametrization metric layer
│   ├── MinExistence.lean                           # MinExistenceData [boundary]: complete_minimizers
│   ├── MinimizerExistence.lean                     # coordinate complete→minimizers via straight lines
│   ├── SmoothGeodesicComplete.lean                 # smooth completeness interface via uniform-step data
│   ├── StronglyConvex.lean                         # strongly convex small-ball wrapper
│   └── Properness.lean                             # RiemannianProper, RiemannianComplete, riemannianComplete_of_proper
├── Jacobi.lean                                     # root re-export
├── Jacobi/
│   ├── Basic.lean                                  # IsJacobiField (∇_T∇_TJ + R(J,T)T = 0), InitialData
│   ├── ConjugatePoints.lean                        # AreConjugate, HasConjugateEndpointValueProblem
│   ├── ExistenceUniqueness.lean                    # JacobiOperator, Picard-Lindelof + Gronwall
│   └── VariationBridge.lean                        # GeodesicVariationWitness, jacobiField_of_geodesicVariation
├── LeviCivita.lean                                 # root re-export
├── LeviCivita/
│   ├── Basic.lean                                  # ConnectionContext, CovariantDerivative, MetricCompatible, TorsionFree, IsLeviCivita
│   ├── CoordinateChristoffel.lean                  # christoffelToCovariantDerivative, leviCivitaChristoffel_eq_variation
│   ├── CoordinateFields.lean                       # SmoothVectorField, SmoothTensor2Field, SmoothChristoffelField
│   ├── Globalization.lean                          # existsUnique_isLeviCivita, existsUnique_isLeviCivita_real
│   ├── Koszul.lean                                 # koszulRHS, KoszulFormula, isLeviCivita_koszulFormula_real
│   ├── LeviCivita.lean                             # isLeviCivita_leviCivita, leviCivita_unique
│   └── LocalExistence.lean                         # coordinateMetricPairing, existsUnique_localLeviCivitaConnection
├── Measure.lean                                    # root re-export
├── Measure/
│   ├── ExpJacobian.lean                            # ExpJacobian, Hadamard det bound, basiswise Jacobian bound
│   ├── HadamardBound.lean                          # Hadamard determinant bound on Euclidean linear maps
│   ├── NormComparison.lean                         # sup/L² norm comparison on `Fin n → ℝ`
│   ├── PolarCoordinates.lean                       # HasPolarDecomposition, hasPolarDecomposition_coordinateExpLocalExponentialMap
│   ├── PullbackDensity.lean                        # pullbackDensity, pullbackDensityENNReal, pullbackMeasure
│   └── RiemannianVolume.lean                       # MetricField, densityOfTensor, IsDensity
├── Metric.lean                                     # root re-export
├── Metric/
│   ├── Basic.lean                                  # tangentInner, Cauchy-Schwarz, OrthogonalAt
│   ├── CoordinateMetric.lean                       # quadraticForm, IsPositiveDefinite, IsInversePair, bilinForm
│   ├── Musical.lean                                # flat, sharp, flat_injective
│   └── SmoothMetric.lean                           # SmoothMetric, ContMDiffMetric, smoothMetric_inner_symm
├── Minimization.lean                               # root re-export
├── Minimization/
│   ├── LocalMinimizers.lean                        # radialComparison_metric_of_input                          [cond]
│   ├── MetricBridge.lean                           # metricNormalRadius_le_metricCurveLength_of_kinematics     [cond]
│   ├── NormalCoordinateKinematics.lean             # HasNormalCoordinateDisplacement, HasNormalCoordinateKinematics [boundary]
│   ├── NormalCoordinateKinematicsConstructor.lean  # witness-free constructor from lies-in / C¹ curve data
│   ├── NormalNeighborhoods.lean                    # normalNeighborhood_open, base_mem_normalNeighborhood
│   └── ShortGeodesicsMinimize.lean                 # shortGeodesicsMinimize_of_input                           [cond]
├── ParallelTransport.lean                          # root re-export
├── ParallelTransport/
│   ├── Basic.lean                                  # FieldAlong, IsParallelAlong, TransportOperator
│   ├── Frames.lean                                 # ParallelFrame, IsOrthonormalFrame, frameOfTransport
│   └── Isometry.lean                               # IsometryAlong, isometryAlong_of_preservesPairing
├── SecondBianchi.lean                              # root re-export
├── SecondBianchi/
│   ├── Basic.lean                                  # LocalConnectionAlgebra, covariantExterior
│   ├── ClassicalCoordinateBianchi.lean             # classical_second_bianchi_cyclic (∇R cyclic sum = 0)
│   ├── ComponentBridge.lean                        # second_bianchi_in_components, indexed_second_bianchi
│   ├── ConcreteCoordinateBianchi.lean              # classical_second_bianchi_cyclic_concrete
│   ├── CoordinateBianchi.lean                      # CoordDiffData, coordAlgebra, wedge forms
│   ├── SecondBianchi.lean                          # second_bianchi_identity (d_∇Ω = 0)
│   ├── SecondBianchi/
│   │   └── ClassicalCoordinateBianchi.lean         # classical_second_bianchi_cyclic_of_bridge
│   ├── SmoothCoordinateBianchi.lean                # smoothCurvature_antisym, smooth second Bianchi
│   └── SmoothCoordinateScaffold.lean               # SmoothForm1/2/3, CoordSpace, coordBasis
├── Variation.lean                                  # root re-export
├── Variation/
│   ├── Basic.lean                                  # LocalConnectionVariationAlgebra, curvatureVariation
│   ├── ComponentBridge.lean                        # curvature_variation_in_components
│   ├── CoordinateVariation.lean                    # CoordVariationData, classical_curvature_variation
│   ├── CurveEnergy.lean                            # speedSq, speedSq_nonneg
│   ├── CurveLength.lean                            # speed_eq_sqrt_speedSq, UnitSpeedAt
│   ├── CurveVariation.lean                         # TwoParameterFamily, CurveVariation, FieldAlongVariation
│   ├── FirstVariationEnergy.lean                   # firstVariationOfEnergy, energyCritical_of_geodesic
│   ├── FirstVariationLength.lean                   # firstVariationOfLength_unitSpeed, geodesic_of_lengthCritical
│   ├── IndexForm.lean                              # indexFormIntegrand, curvaturePairing, kineticPairing
│   ├── LeviCivitaVariationBridge.lean              # leviCivitaVariation, curvature_variation_of_leviCivita_bridge
│   ├── RicciScalarVariation.lean                   # ricci_variation_formula, scalar_variation_formula
│   ├── SecondVariation.lean                        # secondVariationOfEnergy_eq_indexForm
│   └── Variation.lean                              # curvature_variation_identity (F' = d_∇A)
├── Weitzenbock.lean                                # root re-export
└── Weitzenbock/
    ├── Basic.lean                                  # OneFormHodgeAlgebra, hodgeLaplacian
    ├── ClassicalCoordinateWeitzenbock.lean         # deltaD_from_second_eq_rough_plus_ricci_minus_dDelta
    ├── ComponentBridge.lean                        # weitzenbock_in_components, indexed_weitzenbock
    ├── ConcreteCoordinateWeitzenbock.lean          # concrete_weitzenbock_one_form
    ├── CoordinateWeitzenbock.lean                  # HodgeData, classical_weitzenbock
    └── Weitzenbock.lean                            # weitzenbock_identity (Δ_H α = ∇*∇α + ℛα)

Legend: [boundary] = defines interface boundary  [cond] = conditionally proved
```

---

## Module descriptions

### Metric

Provides the basic Riemannian metric infrastructure at two levels.

The abstract layer (`Metric/Basic.lean`) works over a `RiemannianBundle` with Mathlib's tangent space infrastructure. It defines `tangentInner` (the Riemannian inner product at a point), proves symmetry, Cauchy–Schwarz, positivity, and the standard `‖v‖²` identity.

The coordinate layer (`Metric/CoordinateMetric.lean`, `Metric/SmoothMetric.lean`) works with `Fin n → Fin n → ℝ` metric tensors. It defines positive definiteness, the inverse tensor `g^{ij}`, the musical isomorphisms (index raising/lowering), and the smooth Christoffel-compatible field type `SmoothTensor2Field`.

### LeviCivita

Proves existence and uniqueness of the Levi-Civita connection in several complementary forms.

The abstract layer (`LeviCivita/Basic.lean`) defines a `ConnectionContext` (a bracket on vector fields plus a derivation on scalars), an abstract `CovariantDerivative` satisfying the Leibniz rule, metric compatibility (`MetricCompatible`), torsion-freeness (`TorsionFree`), and the combined `IsLeviCivita` predicate. The uniqueness theorem is proved from the Koszul formula at this abstract level.

The coordinate layer (`LeviCivita/CoordinateFields.lean`, `LeviCivita/LocalExistence.lean`, `LeviCivita/Globalization.lean`) gives explicit `Fin n`-index Christoffel symbols
```
Γᵏᵢⱼ = ½ gᵏˡ (∂ᵢgⱼˡ + ∂ⱼgᵢˡ − ∂ˡgᵢⱼ)
```
together with the smooth field versions needed by the geodesic and exponential map layers.

### ODE

Provides the compact finite-dimensional autonomous ODE layer used by the geodesic-flow and
exponential-map pipeline.

`ODE/Core.lean` normalizes the closed-interval local-flow API and proves the fixed-time Lipschitz
dependence estimate used in later comparison arguments. `ODE/UniformRemainder.lean` isolates the
uniform first-order Taylor remainder estimate on compact tubes. `ODE/Linearized.lean` packages the
short-time linearized equation and its fixed-time evaluation operator. `ODE/LinearizedGlobal.lean`
extends this to the full chosen interval by overlap uniqueness and piecewise assembly, and is now
clean. `ODE/FlowFDeriv.lean` proves fixed-time Fréchet differentiability of a C^1 autonomous flow via the
Gronwall linearisation-error bound (`flow_linearisation_error_bound`) and the isLittleO
characterisation of `HasFDerivAt` (`hasFlowFDerivAtFixedTime_of_contDiff`). The backward-compatibility
interface `HasFlowFDerivAtFixedTime` and its projection corollaries are preserved. `ODE/FlowContDiff.lean`
upgrades this to fixed-time `ContDiffAt` regularity of the flow in the initial state; the ODE-side
pipeline is now fully clean.

### Geodesic

Encodes the geodesic ODE as a first-order system in phase space `Position n × Velocity n`.

`Geodesic/Basic.lean` defines positions, velocities, states, and initial conditions. `Geodesic/CoordinateEquation.lean` builds the geodesic acceleration from Christoffel fields (`ẍⁱ = −Γⁱⱼₖ ẋʲ ẋᵏ`). `Geodesic/LocalExistence.lean` invokes Mathlib's Picard–Lindelöf theorem to obtain a local solution. `Geodesic/LocalUniqueness.lean` proves local uniqueness from prescribed initial conditions.

`Geodesic/FlowDifferentiability.lean` proves `hasFlowFDerivAtInitialState_of_smoothChristoffel` — the geodesic flow is Fréchet differentiable in the initial state, without requiring an explicit witness. The proof instantiates the generic C^1 ODE theorem from `ODE/FlowFDeriv.lean` for the geodesic spray. Witness-free corollaries `hasFDerivAt_localCoordinateGeodesicFlow_initialState`, `differentiableAt_localCoordinateGeodesicFlow_initialState`, and `contDiffAt_localCoordinateGeodesicFlow_initialState` are exported; the old witness-consuming signature is retained as `hasFDerivAt_localCoordinateGeodesicFlow_initialState_of_witness`. The file also exports `flow_fderiv_at_initial_of_smoothChristoffel` — a variational corollary giving the derivative of the flow along radial initial-velocity lines, needed by the Gauss lemma proof. The geodesic-flow differentiability path is now clean.

### ParallelTransport

Defines parallel transport as the solution of a first-order linear ODE along a curve in a trivialized fiber `V = ℝⁿ`.

`ParallelTransport/Basic.lean` defines `FieldAlong V`, `AlongDerivative`, `IsParallelAlong`, and `TransportOperator`. It proves that parallel fields are continuous.

`ParallelTransport/Isometry.lean` proves that the transport operator is an isometry under metric-compatible connections. `ParallelTransport/Frames.lean` transports entire orthonormal frames.

### Curvature

Defines the curvature tensor at the abstract level.

`Curvature/Basic.lean` defines `R(X, Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` as `curvatureOperator`, packages it as `CurvatureTensor`, and proves extensionality lemmas.

`Curvature/SectionalRicci.lean` defines sectional curvature (`SectionalCurvature`) and Ricci curvature (`RicciCurvature`) from the abstract tensor. `Curvature/Symmetries.lean` proves the algebraic symmetries of the curvature tensor.

### Exponential

Constructs the local exponential map and owns the active local analytic branch.

`Exponential/Basic.lean` defines `LocalExponentialMap`, `GeodesicFamilyAtBase`, `coordinateExp`, and proves `coordinateExp_zero`. All proofs are genuine.

`Exponential/DifferentialAtZero.lean` proves `fderiv exp 0 = id` — **fully proved, no external input**.

`Exponential/Differentiability.lean` exports `coordinateExpHasFDerivAtOnSource_of_smoothChristoffel` — the witness-free Fréchet differentiability theorem for `coordinateExp` on the chart source. The proof composes flow differentiability (from `Geodesic/FlowDifferentiability.lean`) with the time-rescaling and linear maps that define `coordinateExp`. Witness-free corollaries `hasFDerivAt_coordinateExp_of_mem_partialHomeomorph_source`, `differentiableAt_coordinateExp_of_mem_partialHomeomorph_source`, and `differentiableOn_coordinateExp_of_witness` are exported. The file is now clean; the compatibility `def` `CoordinateExpHasFDerivAtOnSource` is retained for downstream code.

`Exponential/DexpContinuity.lean` upgrades differentiability to `ContDiffAt ℝ 1` for `coordinateExp` on its source and proves continuity of the radial `fderiv` field. This closes the old continuity side of the local analytic branch.

`Exponential/LocalRiemannianData.lean` defines `LocalRiemannianData n` — smooth metric data with symmetry, inverse-pair, and positive-definiteness fields. No stored proof fields.

`Exponential/JacobiDexp.lean` constructs `HasDirectionalDexp` both from an explicit witness (`hasDirectionalDexp_of_localRiemannianData`) and witness-free (`hasDirectionalDexp_of_smoothChristoffel`).

`Exponential/VariationDexp.lean` defines the `HasDirectionalDexp` structure and proves `hasDerivWithinAt_coordinateExp_comp` and `hasDerivAt_coordinateExp_line` — all proofs are genuine.

`Exponential/GaussLemma.lean` provides `gaussLemma_coordinate` (zero-slice metric pairing at the
origin), `exists_metricCompatible_coordinate_middle_formula`, and the radial Gauss-lemma
consequences consumed by the local minimization route.

`Exponential/LocalAnalyticInput.lean` and `Exponential/LocalAnalyticRealization.lean` remain in
the tree as compatibility packages. They are acceptable Lean interfaces, but they are no longer
the active owner bottleneck.

`Exponential/LocalAnalyticConstruction.lean` now exports `_auto` constructors such as
`localAnalyticRealizationOfLocalRiemannianData_auto` and
`canonicalLocalAnalyticInputOfLocalRiemannianData_auto`, so the active local analytic route is
closed at the owner layer.

`Exponential/RadialVariationIdentities.lean` is the owner-local derivative toolbox for the radial
variation argument.

`Exponential/RadialGaussLemma.lean` now contains the owner radial-pairing theorem and the `_auto`
realization constructor.

### Variation

Provides the curve-length / energy calculus and variational formulas.

The abstract layer (`Variation/Basic.lean`, `Variation/Variation.lean`) encodes the structural curvature-variation identity `Ḟ = d_∇ Ā` in a `LocalConnectionVariationAlgebra`, and proves it purely algebraically.

The coordinate layer provides `curveLength`, `curveEnergy`, first and second variation formulas, and the index form `I(J, J')` — **fully proved**.

### Jacobi

Defines Jacobi fields and proves local existence/uniqueness via the coordinate ODE.

`Jacobi/Basic.lean` defines `IsJacobiField R T nablaTT J` as `∀ t, ∇_T ∇_T J(t) + R(J(t), T(t))T(t) = 0`.

`Jacobi/ExistenceUniqueness.lean` writes the Jacobi equation as a concrete `2n`-dimensional first-order ODE in coordinates, invokes Picard–Lindelöf for existence, and Gronwall's inequality for uniqueness — **genuine local existence and uniqueness proved**.

`Jacobi/VariationBridge.lean` provides bridge lemmas connecting variational geodesic families to Jacobi fields. `Jacobi/ConjugatePoints.lean` defines conjugate points.

### Minimization

Assembles the local minimization theory. The public wrapper theorems still consume
`LocalAnalyticInput` and `HasNormalCoordinateKinematics`, but the active route now has owner-level
auto constructors for both ingredients.

`Minimization/NormalCoordinateKinematics.lean` defines `HasNormalCoordinateDisplacement` and
`HasNormalCoordinateKinematics` — explicit `Prop`-valued interface structures for the displacement
chain rule of `normalCoordinates`. This is acceptable witness packaging in Lean. The companion file
`Minimization/NormalCoordinateKinematicsConstructor.lean` proves the witness-free constructor
`hasNormalCoordinateKinematics_of_liesIn`.

`Minimization/MetricBridge.lean` now owns the metric comparison inequality on the active route.
The exported wrapper theorems remain conditional only because the compatibility packages are still
part of the public API.

### SecondBianchi

Proves the second Bianchi identity `d_∇ Ω = 0` at three levels of generality: abstract algebra, coordinate `Fin n`, and smooth coordinate. **Entire directory is complete — no external input**.

### Bochner

Proves the Bochner–Weitzenböck identity for bundle-valued 1-forms. **Entire directory is complete — no external input**.

### Weitzenbock

Proves the Hodge–Weitzenböck identity for 1-forms `Δ_H α = ∇*∇ α + ℛ α`. **Entire directory is complete — no external input**.

### Measure

Provides Riemannian volume and polar-coordinate infrastructure. `Measure/PolarCoordinates.lean` — `hasPolarDecomposition_coordinateExpLocalExponentialMap` — **fully proved**. `Measure/ExpJacobian.lean` now exports `expJacobianFn_le_prod_column_norms` (Hadamard determinant bound) and `expJacobianFn_le_of_basiswise_bound` (Jacobian bound from basiswise dexp norm comparison).

### Comparison

Encodes scalar comparison, Rauch comparison, Cartan-Hadamard, and volume comparison geometry.

**Scalar and volume comparison**: `Comparison/SturmComparison.lean` owns the scalar Sturm theorem;
`Comparison/Rauch.lean`, `Measure/ExpJacobian.lean`, `Comparison/VolumeConstruction.lean`,
`Comparison/VolumeGrowthFromDensity.lean`, and `Comparison/BishopGromovMonotonicity.lean` now
provide a clean active chain from scalar Jacobi comparison to Jacobian majorants, local density
comparison, and Bishop-Gromov monotonicity. The files `RauchReduction.lean`,
`LocalVolumeFromRauch.lean`, `VolumeComparisonLocal.lean`, `VolumeConstruction.lean`, and
`BishopGromov.lean` still retain compatibility wrappers, but those are no longer the active owner
path.

**Current comparison status**: the old geometric-realization blocker is closed on the active route.
`Comparison/RauchCoordinateCurvatureBridge.lean` now provides the canonical curvature-built Jacobi
system, `Comparison/GeometricRealization.lean` has local and canonical-system constructors, and
`Comparison/CartanHadamard.lean` builds `SquaredNormJacobiReduction` both from a full local setup
and directly from canonical curvature data. The remaining comparison-side work is mostly user-facing
packaging and possible owner construction of the continuity witness `Acont`.

### HopfRinow

Encodes the corrected Hopf–Rinow theorem spine from explicit interface-boundary structures.

`HopfRinow/DistanceRealizer.lean` is now a real metric owner file: it proves the restriction
lemmas for metric geodesics, minimizing-geodesic ⇒ distance-realizer, and the corrected reverse
direction under the sharp Lipschitz hypothesis. `HopfRinow/LengthCompactness.lean` proves
`hasLengthCompactness_of_proper` genuinely via Arzelà-Ascoli. `HopfRinow/LocalCompactness.lean`
and `HopfRinow/StronglyConvex.lean` now provide the small-ball wrapper layer.

`HopfRinow/GeodesicExtension.lean` defines `GeodesicExtensionData` with field
`complete_geodesic : RiemannianComplete M → HasGeodesicExtension M`. `HopfRinow/MinExistence.lean`
defines `MinExistenceData` with field `complete_minimizers : RiemannianComplete M →
MinimizingGeodesicsExist M`. `HopfRinow/InputConstruction.lean` defines the corrected assembly
layer: `CompleteProperData`, `HopfRinowData`, and `CompleteToHopfRinowData`. The false bridge
`MinimizersProperInput` is intentionally not part of the public spine.

The coordinate-level route is now assembled: `HopfRinow/CompleteProper.lean` proves coordinate
complete→proper, `HopfRinow/MinimizerExistence.lean` proves coordinate complete→minimizers, and
`HopfRinow/HopfRinow.lean` exports both `coordinate_hopfRinowData` and
`coordinate_hopfRinowTheorem`.

`HopfRinow/SmoothGeodesicComplete.lean` and `HopfRinow/MetricGeodesicBridge.lean` remain honest
interface packages for an alternative smooth-to-metric route. They are dormant design-stage
boundaries, not active blockers for the coordinate theorem. No `sorry` anywhere under
`HopfRinow/`.

---

## Current proof status (2026-04-02)

### Build and scans

```
lake build
  → Build completed successfully (2977 jobs)

Keyword / placeholder scan under `RiemannianGeometry/`
  `sorry` : 0
  `admit` : 0
  `axiom` : 0

`audit_allinone_keywords.py --json`
  flagged_files          : 40
  material_flagged_files : 25
```

The keyword audit is useful, but it over-approximates. Most flagged files are either acceptable
Lean witness packages or legacy compatibility wrappers kept for API stability.

### Real remaining owner tasks

- `Comparison/CartanHadamard.lean`: add thin end-to-end theorems from canonical local setup data
  to positivity / no-conjugate-point conclusions if downstream files want to avoid mentioning the
  reduction structure explicitly.
- `Comparison/RauchCoordinateCurvatureBridge.lean`: `Acont` for
  `canonicalJacobiSystemOfCurvature` is still an explicit continuity witness. This is acceptable
  Lean packaging, but it is the main remaining owner-side regularity boundary if further cleanup is
  desired.

### Acceptable witness packages flagged by audit

- `Exponential/VariationDexp.lean`: `HasDirectionalDexp` is acceptable API packaging, and the
  witness-free constructor `hasDirectionalDexp_of_smoothChristoffel` already exists.
- `Minimization/NormalCoordinateKinematics.lean`: `HasNormalCoordinateDisplacement` and
  `HasNormalCoordinateKinematics` are acceptable analytic witnesses; the constructor
  `hasNormalCoordinateKinematics_of_liesIn` lives in
  `Minimization/NormalCoordinateKinematicsConstructor.lean`.
- `Comparison/CartanHadamard.lean`: the `HasDerivAt` fields inside `SquaredNormJacobiReduction`
  and `ScalarJacobiReduction` are acceptable analysis packaging, not separate geometric gaps.
- `HopfRinow/GeodesicExtension.lean`, `HopfRinow/MinExistence.lean`, and
  `HopfRinow/InputConstruction.lean`: public theorem-assembly packages.

### Legacy compatibility wrappers flagged by audit

- `Comparison/RauchReduction.lean`
- `Comparison/LocalVolumeFromRauch.lean`
- `Comparison/VolumeComparisonLocal.lean`
- `Comparison/VolumeConstruction.lean`
- `Comparison/BishopGromov.lean`

These remain in the tree for compatibility, but the active comparison route is already the direct
Jacobian-majorant → local-density → Bishop-Gromov chain.

---

## The remaining mathematical handoff

What remains is no longer the comparison geometry itself. It is downstream packaging and interface
cleanup.

1. Add thin user-facing Cartan-Hadamard theorems that compose the canonical local setup with the
   existing reduction / positivity results.
2. Decide whether `Acont` for the canonical coefficient matrix should remain explicit witness data
   or be constructed at the owner layer.
3. Decide whether the dormant smooth Hopf-Rinow bridge packages
   (`SmoothGeodesicComplete.lean`, `MetricGeodesicBridge.lean`) should remain as explicit public
   interfaces or be replaced by final owner realizations.


---

# Documents

`Partially Proved` below means the file contains honest owner-local lemmas and no `sorry`, but its
advertised top-level theorem inventory is still incomplete.

| Section | File name | Features | Status |
|---------|-----------|----------|--------|
| `Bochner` | `Bochner.lean` | Root re-export module | Fully Proved |
| `Bochner` | `Bochner/Basic.lean` | `BundleConnectionAlgebra`, `ConnectionForm`, `curvature`, `covariantDeriv0/1`, `curvatureAction` | Fully Proved |
| `Bochner` | `Bochner/Bochner.lean` | `covariant_square_eq_curvature_action` — abstract Bochner–Weitzenböck identity | Fully Proved |
| `Bochner` | `Bochner/ClassicalCoordinateBochner.lean` | `Gradient`, `Hessian`, `scalarLaplacian`, `roughLaplacianGradient`, `ricciAction` — classical coordinate Bochner formula | Fully Proved |
| `Bochner` | `Bochner/ComponentBridge.lean` | `covariant_square_through`, `covariant_square_in_components`, `covector_commutator_from_bridge` — component bridge | Fully Proved |
| `Bochner` | `Bochner/ConcreteCoordinateBochner.lean` | `concrete_coordinate_bochner` — `(1/2)Δ‖∇f‖² = ‖Hess f‖² + ⟨∇f,∇Δf⟩ + Ric(∇f,∇f)` | Fully Proved |
| `Bochner` | `Bochner/CoordinateBochner.lean` | `CoordConnectionData`, coordinate algebra for Bochner, wedge products | Fully Proved |
| `Comparison` | `Comparison.lean` | Root re-export module | Fully Proved |
| `Comparison` | `Comparison/BishopGromov.lean` | `BishopGromovInput`, `bishopGromov_of_localVolumeComparison` — global volume ratio monotonicity | Conditionally Proved |
| `Comparison` | `Comparison/BishopGromovMonotonicity.lean` | `bishopGromov_monotonicity_of_local_inequality` — monotonicity of volume ratio from per-ray differential inequality | Fully Proved |
| `Comparison` | `Comparison/CartanHadamard.lean` | `SquaredNormJacobiReduction`, `ScalarJacobiReduction`, `squaredNormJacobi_pos_of_reduction`, no-conjugate-point wrappers, Cartan-Hadamard packaging; local and canonical geometric constructors are now present | Conditionally Proved |
| `Comparison` | `Comparison/GeometricRealization.lean` | `RiemannianGeodesicComparisonSetup`, `FullRauchComparisonLocalSetup`, `rauch_lowerComparison_of_fullLocalSetup`, canonical local constructors — active owner-facing realization layer | Conditionally Proved |
| `Comparison` | `Comparison/LocalVolumeFromRauch.lean` | `LocalVolumeFromRauchData`, `localVolumeDensityComparison_of_rauchBridge`, `logJacobianDifferentialInequality_of_rauchBridge` — bridge from Rauch-side construction to local density comparison | Boundary-Defining |
| `Comparison` | `Comparison/Myers.lean` | `MyersHypotheses`, `MyersDiameterBound`, `compactSpace_of_myers`, `compactness_of_complete_connected_of_myers` — compactness from Ricci lower bound, depends on HopfRinow interfaces | Conditionally Proved |
| `Comparison` | `Comparison/ODEModels.lean` | `SolvesModelJacobiODE`, `HasModelInitialConditions`, `SatisfiesModelNormBound`, `sn`-model utilities | Fully Proved |
| `Comparison` | `Comparison/Rauch.lean` | `SectionalUpperBound`, `DexpNormComparison`, `dexp_normComparison_of_rauch`, `dexp_normComparison_of_scalarComparison` — Rauch dexp norm bound, requires `RauchInputData` witness | Conditionally Proved |
| `Comparison` | `Comparison/RauchCoordinateCurvatureBridge.lean` | `frameLift`, `NormalizedSectionalUpperBoundAlongCoordinate`, `CoordinateFrameCurvatureBridgeData`, `hasRayleighUpperBound_of_coordinateFrameCurvatureBridge`, `canonicalJacobiSystemOfCurvature`, `matrixCurvatureCoords_of_basisAndLinearity` | Fully Proved |
| `Comparison` | `Comparison/RauchCoordinateJacobiGeometry.lean` | `CoordinateParallelJacobiGeometryData`, zero-time coefficient derivative lemmas, `rauch_lowerComparison_of_coordinateParallelJacobiGeometry` — owner Jacobi package for the active route | Conditionally Proved |
| `Comparison` | `Comparison/RauchCoordinateLowerBridge.lean` | `CoordinateParallelRauchLowerBridgeData`, `rauch_lowerComparison_of_coordinateParallelLowerBridge` — unified lower-Rauch package retained as compatibility / interface layer | Boundary-Defining |
| `Comparison` | `Comparison/RauchCoordinatePositivityBridge.lean` | `CoordinateParallelJacobiPositivityBridgeData`, `coordinateJacobiPositivityData_of_coordinateParallelBridge`, `rauch_lowerComparison_of_coordinateParallelBridge` — coordinate-parallel field to positivity-set scalar package | Fully Proved |
| `Comparison` | `Comparison/RauchCurvatureBridge.lean` | `NormalizedSectionalUpperBound`, `CurvatureMatrixBridgeData`, `hasRayleighUpperBound_of_curvatureBridge` — coordinate Jacobi matrix to curvature Rayleigh inequality | Fully Proved |
| `Comparison` | `Comparison/RauchNormCore.lean` | `jacobi_normSq`, `HasRayleighUpperBound`, `jacobi_normSq_secondDeriv_lower_bound`, `jacobi_normSq_convex_of_nonpositive_curvature` — squared-norm infrastructure for Jacobi comparison | Fully Proved |
| `Comparison` | `Comparison/RauchNormSqrt.lean` | `sqrt_route_algebraic_criterion`, `jacobi_normSq_sqrt_supersolution_criterion_of_upperRayleigh` — square-root reduction algebraic machinery for Rauch | Fully Proved |
| `Comparison` | `Comparison/RauchPositivitySet.lean` | `coordinateJacobiNorm`, `CoordinateJacobiPositivityData`, `rauch_lowerComparison_of_coordinateJacobi` — positivity-set reduction from coordinate Jacobi to scalar ODE | Fully Proved |
| `Comparison` | `Comparison/RauchReduction.lean` | `RauchNormODEData` (interface boundary: subsolution/initial-condition witness), `RauchInputData`, `HasRauchReduction`, `hasRauchReduction_of_scalarComparison` — vector-to-scalar Jacobi reduction; `hasRauchReduction_of_scalarComparison` proved once `RauchInputData` witness is supplied | Boundary-Defining |
| `Comparison` | `Comparison/ScalarJacobiComparison.lean` | `ScalarJacobiComparisonData`, `HasScalarJacobiComparison`, `hasScalarJacobiComparison_of_subsolution` — converts scalar Sturm theorem to package interface | Fully Proved |
| `Comparison` | `Comparison/ScalarConvexity.lean` | `positive_of_nonneg_second_deriv` — 1D analytical core of Cartan-Hadamard; positivity from nonnegative second derivative via MVT | Fully Proved |
| `Comparison` | `Comparison/SturmComparison.lean` | `scalarWronskian`, `deriv_scalarWronskian_nonpos_of_subsolution`, `antitoneOn_scalarWronskian_of_subsolution`, `scalarComparison_of_subsolution` — complete scalar Sturm comparison theorem | Fully Proved |
| `Comparison` | `Comparison/VolumeComparisonLocal.lean` | `LocalVolumeComparisonInput`, `localVolumeDensityComparison_of_input`, `logJacobianDifferentialInequality_of_input` — thin wrapper over `LocalVolumeComparisonConstruction` | Boundary-Defining |
| `Comparison` | `Comparison/VolumeConstruction.lean` | `LocalVolumeComparisonConstruction` (boundary: `comparisonFromRauch` field), `BishopGromovConstruction` (boundary: `monotonicityFromLocal` field), `localVolumeDensityComparison_of_construction`, `bishopGromov_of_logJacobianDifferentialInequality` | Boundary-Defining |
| `Comparison` | `Comparison/VolumeGrowthFromDensity.lean` | `VolumeGrowthFromDensityData`, `bishopGromov_monotonicity_of_density_growth` — one-dimensional integral step from density-ratio monotonicity to Bishop–Gromov ratio monotonicity | Conditionally Proved |
| `Curvature` | `Curvature.lean` | Root re-export module | Fully Proved |
| `Curvature` | `Curvature/Basic.lean` | `curvatureOperator` (`R(X,Y)Z`), `CurvatureTensor`, extensionality lemmas | Fully Proved |
| `Curvature` | `Curvature/SectionalRicci.lean` | `SectionalCurvature`, `RicciCurvature`, `RicciLowerBound` | Fully Proved |
| `Curvature` | `Curvature/Symmetries.lean` | `FirstPairSkew`, `FirstBianchi`, algebraic curvature symmetry identities | Fully Proved |
| `Exponential` | `Exponential.lean` | Root re-export module; re-exports conditional files | Conditionally Proved |
| `Exponential` | `Exponential/Basic.lean` | `LocalExponentialMap`, `coordinateExp`, `coordinateExp_zero`, `RealizedByGeodesicFamily`, spray-built geodesic family | Fully Proved |
| `Exponential` | `Exponential/Differentiability.lean` | `coordinateExpHasFDerivAtOnSource_of_smoothChristoffel` (owner theorem), `CoordinateExpHasFDerivAtOnSource` (compat def), witness-free corollaries | Fully Proved |
| `Exponential` | `Exponential/DifferentialAtZero.lean` | `hasFDerivAt_coordinateExp_at_zero`, `fderiv_coordinateExp_at_zero` (`= id`), `strictDifferentialAtZeroIsId` | Fully Proved |
| `Exponential` | `Exponential/GaussLemma.lean` | `gaussLemma_coordinate` (zero-slice, proved), `exists_metricCompatible_coordinate_middle_formula` (proved), `gaussLemma_radial_pairing_of_input` / `_of_realization` (conditional on `LocalAnalyticInput`), `gaussLemma_radial_norm`, `gaussLemma_radial_orthogonal` | Conditionally Proved |
| `Exponential` | `Exponential/JacobiDexp.lean` | `hasDirectionalDexp_of_smoothChristoffel` (witness-free), `hasDirectionalDexp_of_localRiemannianData` (compat) | Fully Proved |
| `Exponential` | `Exponential/LocalAnalyticConstruction.lean` | original constructors + `_auto` variants; the active owner route is closed via `localAnalyticRealizationOfLocalRiemannianData_auto` and `canonicalLocalAnalyticInputOfLocalRiemannianData_auto`, while compatibility constructors remain available | Boundary-Defining |
| `Exponential` | `Exponential/LocalAnalyticInput.lean` | `LocalAnalyticInput` (boundary: `radialPairing`, `radius_le_metricLength`, `metricLength_le_radius` fields), `IsMetricCompatible`, `metricPairingAt` | Boundary-Defining |
| `Exponential` | `Exponential/LocalAnalyticRealization.lean` | `LocalAnalyticRealization` — intermediate package (directional dexp + bridge data, before metric compatibility attached), `canonicalLocalAnalyticInput` | Boundary-Defining |
| `Exponential` | `Exponential/LocalInverse.lean` | `zero_mem_localExp_source`, `localExpInverse_base`, `localExp_leftInverse` — strict-IFT `PartialHomeomorph` chart | Fully Proved |
| `Exponential` | `Exponential/LocalRiemannianData.lean` | `LocalRiemannianData` (metric + inverse + symmetry + posDef), `isMetricCompatible` — purely metric data, no proof fields | Fully Proved |
| `Exponential` | `Exponential/NormalCoordinates.lean` | `normalCoordinates`, `coordinateExp_normalCoordinates_roundtrip`, `normalCoordinates_exp_roundtrip`, `normalCoordinates_zero_image` — chart/source API | Fully Proved |
| `Exponential` | `Exponential/RadialBridge.lean` | `radialSource`, `smul_mem_radialSource_of_mem`, `mapsTo_line_radialSource` — star-shaped radial source | Fully Proved |
| `Exponential` | `Exponential/VariationDexp.lean` | `HasDirectionalDexp` (interface boundary: directional chain rule for `coordinateExp`), `hasDerivWithinAt_coordinateExp_comp`, `hasDerivAt_coordinateExp_line` | Boundary-Defining |
| `Geodesic` | `Geodesic.lean` | Root re-export module | Fully Proved |
| `Geodesic` | `Geodesic/Basic.lean` | `Position`, `Velocity`, `State`, `InitialConditions`, `mkState`, `statePosition`, `stateVelocity` | Fully Proved |
| `Geodesic` | `Geodesic/CoordinateEquation.lean` | `geodesicAcceleration` (`ẍⁱ = −Γⁱⱼₖẋʲẋᵏ`), `ChristoffelField`, `constantChristoffelField` | Fully Proved |
| `Geodesic` | `Geodesic/FlowDifferentiability.lean` | `hasFlowFDerivAtInitialState_of_smoothChristoffel` (owner theorem), witness-free corollaries, `flow_fderiv_at_initial_of_smoothChristoffel` (variational corollary) | Fully Proved |
| `Geodesic` | `Geodesic/LocalExistence.lean` | `exists_isCoordinateGeodesicOn_Icc_of_isPicardLindelof`, `LocalCoordinateGeodesicFlowData`, `localTimePoint`, `contDiff_geodesicSpray` — Picard–Lindelöf local solution | Fully Proved |
| `Geodesic` | `Geodesic/LocalUniqueness.lean` | `eqOn_Icc_of_isCoordinateGeodesicOn_lipschitzOn`, `eqOn_Ioo_of_same_initial` — local uniqueness from matching initial data | Fully Proved |
| `Geodesic` | `Geodesic/Spray.lean` | `geodesicSpray`, `IsCoordinateGeodesicOn`, `timeRescaleStateCurve`, `isCoordinateGeodesicOn_iff_secondOrder` — spray/scaling ODE lemmas | Fully Proved |
| `HopfRinow` | `HopfRinow.lean` | Root re-export module; re-exports conditional files | Conditionally Proved |
| `HopfRinow` | `HopfRinow/CompleteProper.lean` | `exists_compact_mem_nhds_of_exists_isCompact_closedBall`, `weaklyLocallyCompactSpace_of_exists_isCompact_closedBall`, `locallyCompactSpace_of_exists_isCompact_closedBall`, `coordinate_properSpace`, `coordinate_complete_implies_proper`, `coordinate_completeProperData` — local compactness reduction + coordinate-level complete→proper | Fully Proved |
| `HopfRinow` | `HopfRinow/DistanceRealizer.lean` | `IsGeodesicOnWithSpeed.restrict_Icc`, `IsMinimizingGeodesicBetween.toIsDistanceRealizerBetween`, corrected reverse implication `IsDistanceRealizerBetween.toIsMinimizingGeodesicBetween_of_lipschitz` | Fully Proved |
| `HopfRinow` | `HopfRinow/GeodesicExtension.lean` | `GeodesicExtensionData` (interface boundary: `complete_geodesic` field, completeness→extension), `HasGeodesicExtension`, `someGeodesicExtension`, `hasGeodesicExtension_of_complete` (projection) | Boundary-Defining |
| `HopfRinow` | `HopfRinow/HopfRinow.lean` | `HopfRinowTheorem`, `hopfRinowTheorem_of_input`, `hopfRinowTheorem_of_bridge`, `hopfRinowTheoremOfGeometricDirections`, `coordinate_hopfRinowData`, `coordinate_hopfRinowTheorem` — corrected four-way spine + coordinate-level assembly | Conditionally Proved |
| `HopfRinow` | `HopfRinow/InputConstruction.lean` | `CompleteProperData`, `HopfRinowData` (bundles extension+existence+proper), `CompleteToHopfRinowData`, bridge constructors | Boundary-Defining |
| `HopfRinow` | `HopfRinow/LengthCompactness.lean` | `HasLengthCompactness`, `hasLengthCompactness_of_proper` (proved via Arzelà-Ascoli), `hasLengthCompactness_iff`, `isCompact_lengthCompactContainer` | Fully Proved |
| `HopfRinow` | `HopfRinow/LocalCompactness.lean` | `exists_compact_small_closedBall` — compact small closed balls inside the normal-neighborhood package | Fully Proved |
| `HopfRinow` | `HopfRinow/MetricGeodesicBridge.lean` | `SmoothMetricBridgeData`, `coordinate_hasGeodesicExtension_of_smooth_and_bridge`, `coordinate_geodesicExtensionData_of_smooth_bridge` — smooth-to-metric bridge interface with structure fields | Boundary-Defining |
| `HopfRinow` | `HopfRinow/MetricLength.lean` | `sameEndpoints`, `MetricPathLength.length/prefixLength`, limit-of-Lipschitz lemmas, `exists_reparam_lipschitz_of_lipschitz`, `endpoint_lipschitz_eq_distance_implies_minimizingGeodesic` — metric-length / reparametrization infrastructure | Fully Proved |
| `HopfRinow` | `HopfRinow/MinExistence.lean` | `MinExistenceData` (interface boundary: `complete_minimizers` field, completeness→minimizers), `MinimizingGeodesicsExist`, `minimizingGeodesicsExist_of_complete` (projection) | Boundary-Defining |
| `HopfRinow` | `HopfRinow/MinimizerExistence.lean` | `compactSuperset_of_commonSource_uniformLipschitz`, `coordinateStraightLine`, `coordinateStraightLine_dist`, `coordinateStraightLine_isMinimizingGeodesicBetween`, `coordinate_minimizingGeodesicsExist`, `coordinate_minExistenceData` — coordinate-level complete→minimizers via straight-line geodesics | Fully Proved |
| `HopfRinow` | `HopfRinow/Properness.lean` | `RiemannianProper`, `RiemannianComplete`, `riemannianComplete_of_proper`, `riemannianProper_of_properSpace` | Fully Proved |
| `HopfRinow` | `HopfRinow/SmoothGeodesicComplete.lean` | `CoordinateGeodesicOnInterval`, `HasCoordinateGeodesicCompleteness`, `geodesic_exists_forward`, `SmoothGeodesicCompletenessData` — smooth geodesic completeness interface with ODE continuation carried as structure field | Boundary-Defining |
| `HopfRinow` | `HopfRinow/StronglyConvex.lean` | `StronglyConvexBall`, `exists_stronglyConvexBall`, `StronglyConvexBall.mem_normalNeighborhood`; minimizing/uniqueness layer still pending | Partially Proved |
| `Jacobi` | `Jacobi.lean` | Root re-export module | Fully Proved |
| `Jacobi` | `Jacobi/Basic.lean` | `IsJacobiField` (`∇_T∇_TJ + R(J,T)T = 0`), `InitialData`, `isJacobiField_zero_iff` | Fully Proved |
| `Jacobi` | `Jacobi/ConjugatePoints.lean` | `VanishesAt`, `AreConjugate`, `HasConjugateEndpointValueProblem`, `hasConjugatePointAtZero_iff` | Fully Proved |
| `Jacobi` | `Jacobi/ExistenceUniqueness.lean` | `JacobiOperator`, `isJacobiOperator_iff`, Picard–Lindelöf + Gronwall → local existence and uniqueness of Jacobi fields | Fully Proved |
| `Jacobi` | `Jacobi/VariationBridge.lean` | `GeodesicVariationWitness`, `jacobiField_of_geodesicVariation`, `isJacobiField_of_geodesicVariation` — bridges geodesic variation families to Jacobi fields | Fully Proved |
| `LeviCivita` | `LeviCivita.lean` | Root re-export module | Fully Proved |
| `LeviCivita` | `LeviCivita/Basic.lean` | `ConnectionContext`, `CovariantDerivative`, `MetricCompatible`, `TorsionFree`, `IsLeviCivita` | Fully Proved |
| `LeviCivita` | `LeviCivita/CoordinateChristoffel.lean` | `leviCivitaChristoffel_eq_variation`, `christoffelToCovariantDerivative_torsionFree`, `christoffelToCovariantDerivative_metricCompatible` — Γᵏᵢⱼ lifts to abstract covariant derivative | Fully Proved |
| `LeviCivita` | `LeviCivita/CoordinateFields.lean` | `SmoothVectorField`, `SmoothTensor2Field`, `SmoothChristoffelField`, coordinate field types | Fully Proved |
| `LeviCivita` | `LeviCivita/Globalization.lean` | `existsUnique_isLeviCivita`, `existsUnique_isLeviCivita_real`, `existsUnique_isLeviCivita_real_symm` — global existence and uniqueness | Fully Proved |
| `LeviCivita` | `LeviCivita/Koszul.lean` | `koszulRHS`, `KoszulFormula`, `isLeviCivita_koszulFormula_real` — Koszul formula from `IsLeviCivita` | Fully Proved |
| `LeviCivita` | `LeviCivita/LeviCivita.lean` | `isLeviCivita_leviCivita`, `leviCivita_unique`, `leviCivitaRealSymm_unique` — main existence/uniqueness assembly | Fully Proved |
| `LeviCivita` | `LeviCivita/LocalExistence.lean` | `SatisfiesMetricContraction`, `coordinateMetricPairing`, `existsUnique_localLeviCivitaConnection` — abstract metric pairing from coordinate data | Fully Proved |
| `ODE` | `ODE.lean` | Root re-export module; autonomous ODE support plus the fixed-time differentiability interface | Fully Proved |
| `ODE` | `ODE/Core.lean` | `hasDerivWithinAt_Ici_of_hasDerivWithinAt_Icc`, `flow_dist_le_forward`, `flow_approx_dist_le_forward`, `flow_fixedTime_dist_le` — derivative conversion and Gronwall flow estimates | Fully Proved |
| `ODE` | `ODE/FlowContDiff.lean` | `contDiffAt_flow_of_contDiff` — `C¹` regularity of the fixed-time flow in the initial condition | Fully Proved |
| `ODE` | `ODE/FlowFDeriv.lean` | `HasFlowFDerivAtFixedTime`, `hasFDerivAt_flowFixedTime_of_contDiff_of_linearized`, `hasFlowFDerivAtFixedTime_of_contDiff` — fixed-time Fréchet differentiability of the flow | Fully Proved |
| `ODE` | `ODE/Linearized.lean` | `LinearizedSolutionData`, `exists_linearizedSolutionData`, `exists_linearizedSolution_clm`, `linearizedSolution_norm_le` — short-time linearized ODE solution operator | Fully Proved |
| `ODE` | `ODE/LinearizedGlobal.lean` | `linearizedSolutionData_extend`, `exists_linearizedSolution_clm_on_Icc` — global linearized CLM on the full interval | Fully Proved |
| `ODE` | `ODE/UniformRemainder.lean` | `uniform_firstOrder_remainder`, `uniform_firstOrder_remainder_of_contDiff`, `tube_remainder_estimate` — uniform Taylor remainder control on compact sets and along trajectories | Fully Proved |
| `Measure` | `Measure.lean` | Root re-export module | Fully Proved |
| `Measure` | `Measure/ExpJacobian.lean` | `ExpJacobian`, `expJacobianFn_le_prod_column_norms` (Hadamard), `expJacobianFn_le_of_basiswise_bound` | Fully Proved |
| `Measure` | `Measure/HadamardBound.lean` | `abs_gramSchmidt_det_le_prod_norm`, `abs_linearMap_det_le_prod_norm` — Hadamard determinant bound on Euclidean linear maps | Fully Proved |
| `Measure` | `Measure/NormComparison.lean` | `pi_norm_le_l2_norm`, `pi_norm_le_piLp_norm`, `piLp_norm_le_sqrt_card_mul_pi_norm` — sup/L² norm comparison on `Fin n → ℝ` | Fully Proved |
| `Measure` | `Measure/PolarCoordinates.lean` | `HasPolarDecomposition`, `hasPolarDecomposition_coordinateExpLocalExponentialMap` (proved unconditionally), `canonicalPolarJacobian_eq_of_compatible` | Fully Proved |
| `Measure` | `Measure/PullbackDensity.lean` | `pullbackDensity`, `pullbackDensityENNReal`, `pullbackMeasure`, `pullbackDensity_nonneg` — Jacobian-weighted pullback density | Fully Proved |
| `Measure` | `Measure/RiemannianVolume.lean` | `MetricField`, `densityOfTensor`, `IsDensity`, `densityFromMetricField` — Riemannian volume data and density construction | Fully Proved |
| `Metric` | `Metric.lean` | Root re-export module | Fully Proved |
| `Metric` | `Metric/Basic.lean` | `tangentInner`, `tangentInner_symm`, `tangentInner_cauchy_schwarz`, `tangentInner_pos_of_ne_zero` — abstract inner product on tangent bundle | Fully Proved |
| `Metric` | `Metric/CoordinateMetric.lean` | `quadraticForm`, `IsSymmetric`, `IsPositiveDefinite`, `IsInversePair`, `basisVector`, `bilinForm` — coordinate metric tensor algebra | Fully Proved |
| `Metric` | `Metric/Musical.lean` | `flat`, `sharp`, `flat_injective`, `flat_eq_iff` — musical isomorphisms (index raising/lowering) | Fully Proved |
| `Metric` | `Metric/SmoothMetric.lean` | `SmoothMetric`, `ContMDiffMetric`, `smoothMetric_inner_symm`, `smoothMetric_inner_pos` — smooth Riemannian metric on manifolds | Fully Proved |
| `Minimization` | `Minimization.lean` | Root re-export module | Fully Proved |
| `Minimization` | `Minimization/LocalMinimizers.lean` | `radialComparison_euclidean`, `radialComparison_metric_of_input` / `_of_realization`, `radialComparison_metric` — local minimizer metric comparison; all conditional on `LocalAnalyticInput` + `HasNormalCoordinateKinematics` | Conditionally Proved |
| `Minimization` | `Minimization/MetricBridge.lean` | `metricNormalRadius_le_metricCurveLength_of_kinematics_of_input`, `radialGeodesic_metricLength_le_metricNormalRadius_of_input` — metric bridge inequalities, conditional on `LocalAnalyticInput` + `HasNormalCoordinateKinematics` | Conditionally Proved |
| `Minimization` | `Minimization/NormalCoordinateKinematics.lean` | `HasNormalCoordinateDisplacement` (boundary: displacement integral identity), `HasNormalCoordinateKinematics` (boundary: displacement chain rule witness for `normalCoordinates`), `LiesInOn`, `IsCurveFrom`, `HasCoordinateVelocityOn` | Boundary-Defining |
| `Minimization` | `Minimization/NormalCoordinateKinematicsConstructor.lean` | `hasNormalCoordinateKinematics_of_liesIn` — witness-free constructor for the normal-coordinate kinematics package | Fully Proved |
| `Minimization` | `Minimization/NormalNeighborhoods.lean` | `normalNeighborhood_open`, `base_mem_normalNeighborhood`, `normalCoordinates_coordinateExp_eq` — normal neighborhood API | Fully Proved |
| `Minimization` | `Minimization/ShortGeodesicsMinimize.lean` | `shortGeodesicsMinimize_of_input` / `_of_realization`, `shortGeodesicsMinimize`, `NormalDistanceFormula`, `normalDistance_eq_radius` — short geodesics are local minimizers, conditional on `LocalAnalyticInput` + `HasNormalCoordinateKinematics` | Conditionally Proved |
| `ParallelTransport` | `ParallelTransport.lean` | Root re-export module | Fully Proved |
| `ParallelTransport` | `ParallelTransport/Basic.lean` | `FieldAlong`, `IsParallelAlong`, `TransportOperator`, `continuousOn_of_isParallelAlong` — parallel transport ODE | Fully Proved |
| `ParallelTransport` | `ParallelTransport/Frames.lean` | `ParallelFrame`, `frameOfTransport`, `IsOrthonormalFrame`, `frameOfTransport_isParallel` — parallel frame transport | Fully Proved |
| `ParallelTransport` | `ParallelTransport/Isometry.lean` | `PreservesPairing`, `IsometryAlong`, `isometryAlong_of_preservesPairing`, `isometryAlong_iff` — transport operator is an isometry under metric-compatible connections | Fully Proved |
| `SecondBianchi` | `SecondBianchi.lean` | Root re-export module | Fully Proved |
| `SecondBianchi` | `SecondBianchi/Basic.lean` | `LocalConnectionAlgebra`, `covariantExterior` — abstract algebra for second Bianchi | Fully Proved |
| `SecondBianchi` | `SecondBianchi/ClassicalCoordinateBianchi.lean` | `cyclicCovariantDerivative`, `classical_second_bianchi_cyclic` — `∇_e R^i_{jkl} + ∇_k R^i_{jle} + ∇_l R^i_{jek} = 0` | Fully Proved |
| `SecondBianchi` | `SecondBianchi/ComponentBridge.lean` | `second_bianchi_through`, `second_bianchi_in_components`, `indexed_second_bianchi` — component bridge | Fully Proved |
| `SecondBianchi` | `SecondBianchi/ConcreteCoordinateBianchi.lean` | `ConcreteCoordDiffData`, `curvature_antisym`, `classical_second_bianchi_cyclic_concrete` — concrete coordinate level | Fully Proved |
| `SecondBianchi` | `SecondBianchi/CoordinateBianchi.lean` | `CoordDiffData`, `coordAlgebra`, `wedge11/12/21` — coordinate bridge algebra | Fully Proved |
| `SecondBianchi` | `SecondBianchi/SecondBianchi.lean` | `second_bianchi_identity` — `d_∇Ω = 0` at abstract level | Fully Proved |
| `SecondBianchi` | `SecondBianchi/SecondBianchi/ClassicalCoordinateBianchi.lean` | `classical_second_bianchi_cyclic_of_bridge` — bridge helper | Fully Proved |
| `SecondBianchi` | `SecondBianchi/SmoothCoordinateBianchi.lean` | `smoothD2_wedge11`, `smoothCurvature_antisym`, `smooth_proj_eq_explicit` — smooth coordinate second Bianchi | Fully Proved |
| `SecondBianchi` | `SecondBianchi/SmoothCoordinateScaffold.lean` | `SmoothForm1/2/3`, `CoordSpace`, `coordBasis` — smooth coordinate scaffold | Fully Proved |
| `Variation` | `Variation.lean` | Root re-export module | Fully Proved |
| `Variation` | `Variation/Basic.lean` | `LocalConnectionVariationAlgebra`, `curvatureVariation`, `covariantVariation` — abstract curvature variation algebra | Fully Proved |
| `Variation` | `Variation/ComponentBridge.lean` | `curvature_variation_through`, `curvature_variation_in_components`, `indexed_curvature_variation` — component bridge | Fully Proved |
| `Variation` | `Variation/CoordinateVariation.lean` | `CoordVariationData`, `classical_curvature_variation`, `proj_curvature_variation_eq_explicit` — coordinate curvature variation identity | Fully Proved |
| `Variation` | `Variation/CurveEnergy.lean` | `speedSq`, `speedSq_nonneg` — curve energy integrand | Fully Proved |
| `Variation` | `Variation/CurveLength.lean` | `speed_eq_sqrt_speedSq`, `UnitSpeedAt`, `unitSpeedAt_iff` — curve length/speed | Fully Proved |
| `Variation` | `Variation/CurveVariation.lean` | `TwoParameterFamily`, `CurveVariation`, `FieldAlongVariation` — variational setup structures | Fully Proved |
| `Variation` | `Variation/FirstVariationEnergy.lean` | `firstVariationOfEnergy`, `energyCritical_of_geodesic`, `firstVariationEnergyValue_of_fixedEndpoints` — first variation of energy | Fully Proved |
| `Variation` | `Variation/FirstVariationLength.lean` | `firstVariationOfLength_unitSpeed`, `lengthCritical_of_geodesic`, `geodesic_of_lengthCritical` — first variation of arc length | Fully Proved |
| `Variation` | `Variation/IndexForm.lean` | `indexFormIntegrand`, `curvaturePairing`, `kineticPairing`, index form bilinearity and symmetry | Fully Proved |
| `Variation` | `Variation/LeviCivitaVariationBridge.lean` | `leviCivitaVariation`, `curvature_variation_of_leviCivita_bridge` — bridge to Levi-Civita context | Fully Proved |
| `Variation` | `Variation/RicciScalarVariation.lean` | `ricciVariationFromCurvature`, `ricci_variation_formula`, `scalar_variation_formula` — Ricci and scalar curvature variation | Fully Proved |
| `Variation` | `Variation/SecondVariation.lean` | `secondVariationOfEnergy_eq_indexForm`, `secondVariationOfLength_eq_indexForm` — second variation = index form | Fully Proved |
| `Variation` | `Variation/Variation.lean` | `curvature_variation_identity` — `Ḟ = d_∇Ā` abstract algebraic identity | Fully Proved |
| `Weitzenbock` | `Weitzenbock.lean` | Root re-export module | Fully Proved |
| `Weitzenbock` | `Weitzenbock/Basic.lean` | `OneFormHodgeAlgebra`, `hodgeLaplacian` — abstract Hodge–Weitzenböck algebra | Fully Proved |
| `Weitzenbock` | `Weitzenbock/ClassicalCoordinateWeitzenbock.lean` | `deltaD_from_second_eq_rough_plus_ricci_minus_dDelta`, `trace_covector_commutator` — `Δ_H α = ∇*∇α + ℛα` in coordinates | Fully Proved |
| `Weitzenbock` | `Weitzenbock/ComponentBridge.lean` | `weitzenbock_through`, `weitzenbock_in_components`, `indexed_weitzenbock` — component bridge | Fully Proved |
| `Weitzenbock` | `Weitzenbock/ConcreteCoordinateWeitzenbock.lean` | `concrete_weitzenbock_one_form`, `concrete_weitzenbock_pairing` — concrete coordinate Weitzenböck | Fully Proved |
| `Weitzenbock` | `Weitzenbock/CoordinateWeitzenbock.lean` | `HodgeData`, `classical_weitzenbock` — `HodgeData`-parameterized Weitzenböck identity | Fully Proved |
| `Weitzenbock` | `Weitzenbock/Weitzenbock.lean` | `weitzenbock_identity` — `Δ_H α = ∇*∇α + ℛα` at abstract level | Fully Proved |
| `Exponential` | `Exponential/DexpContinuity.lean` | `contDiffAt_coordinateExp`, `continuousOn_fderiv_coordinateExp`, radial continuity of the `fderiv` field | Fully Proved |
| `Exponential` | `Exponential/RadialVariationIdentities.lean` | `hasDerivAt_geodesicFamily_position_line` and related owner-local radial variation helpers | Fully Proved |
