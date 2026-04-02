# Riemannian Geometry — Lean 4 Formalization

A Lean 4 / Mathlib formalization of Riemannian geometry, built as an AI-assisted proof engineering project. The goal is a rigorous, machine-checkable library covering local and global Riemannian geometry — from metric infrastructure and Levi-Civita connections through geodesics, exponential maps, Jacobi fields, and global theorems such as Hopf–Rinow and comparison geometry.

---

## Architecture

The library maintains two complementary presentation styles throughout:

- **Abstract / type-class layer** — theorems stated over abstract `AddGroup`, `SMul`, and custom `ConnectionContext` types, coordinate-independent and directly reusable across Mathlib's differential-geometry infrastructure.
- **Coordinate / `Fin n` layer** — theorems stated in explicit `Fin n → ℝ` component form, enabling direct connection to Mathlib's ODE and measure-theory libraries.

Both layers coexist for most modules and are linked by bridge lemmas.

---

## Toolchain and build

| | |
|---|---|
| **Lean** | `leanprover/lean4:v4.28.0` |
| **Mathlib** | `leanprover-community/mathlib v4.28.0` |
| **Build file** | `RiemannianGeometry/lakefile.toml` |

```bash
cd RiemannianGeometry
lake build                  # full project (~2949 jobs, 0 sorry, green as of 2026-04-02)
lake build Exponential
lake build Minimization
```

> **Build rule**: use module names like `Exponential.Basic` directly — do not prepend `RiemannianGeometry.`.

**Proof status (2026-04-02):** The project is **complete** with **0 remaining `sorry` placeholders**. The two previously open goals (`Exponential/RadialGaussLemma.lean` and `Minimization/MetricBridge.lean`) have been closed, and thirteen new supporting files have been added.

---

## Repository layout

```
Differential-Geometry-Formalization/
├── README.md
├── .gitignore
├── docs/
│   └── Formalized Differential Geometry.pdf   # natural-language proof companion
└── RiemannianGeometry/
    ├── lakefile.toml
    ├── lean-toolchain
    ├── lake-manifest.json
    ├── Bochner.lean          (+ Bochner/)
    ├── Comparison.lean       (+ Comparison/)
    ├── Curvature.lean        (+ Curvature/)
    ├── Exponential.lean      (+ Exponential/)
    ├── Geodesic.lean         (+ Geodesic/)
    ├── HopfRinow.lean        (+ HopfRinow/)
    ├── Jacobi.lean           (+ Jacobi/)
    ├── LeviCivita.lean       (+ LeviCivita/)
    ├── Measure.lean          (+ Measure/)
    ├── Metric.lean           (+ Metric/)
    ├── Minimization.lean     (+ Minimization/)
    ├── ODE.lean              (+ ODE/)
    ├── ParallelTransport.lean (+ ParallelTransport/)
    ├── SecondBianchi.lean    (+ SecondBianchi/)
    ├── Variation.lean        (+ Variation/)
    └── Weitzenbock.lean      (+ Weitzenbock/)
```

---

## Module descriptions

### Metric

Provides the foundational Riemannian metric infrastructure at two levels.

The abstract layer (`Metric/Basic.lean`) defines `tangentInner` and proves symmetry, Cauchy–Schwarz, positivity, and the `‖v‖²` identity. The coordinate layer (`Metric/CoordinateMetric.lean`, `Metric/SmoothMetric.lean`) works with `Fin n → Fin n → ℝ` metric tensors, defining positive definiteness, the inverse tensor `g^{ij}`, the musical isomorphisms (index raising/lowering), and the smooth `SmoothTensor2Field` type.

### LeviCivita

Proves existence and uniqueness of the Levi-Civita connection.

The abstract layer (`LeviCivita/Basic.lean`) defines `ConnectionContext`, `CovariantDerivative`, `MetricCompatible`, `TorsionFree`, and `IsLeviCivita`, with uniqueness derived from the Koszul formula. The coordinate layer gives explicit Christoffel symbols
```
Γᵏᵢⱼ = ½ gᵏˡ (∂ᵢgⱼˡ + ∂ⱼgᵢˡ − ∂ˡgᵢⱼ)
```
with global existence verified in `Globalization.lean`.

### ODE

The compact autonomous ODE infrastructure used throughout the geodesic and exponential-map pipeline. Provides fixed-time Lipschitz dependence, uniform first-order Taylor remainder estimates on compact tubes, a short-time linearized solution operator with global extension (`LinearizedGlobal.lean`), fixed-time Fréchet differentiability (`FlowFDeriv.lean`), and `ContDiffAt` regularity (`FlowContDiff.lean`). The entire ODE pipeline is clean.

### Geodesic

Encodes the geodesic ODE as a first-order system in phase space `Position n × Velocity n`. Defines the geodesic acceleration `ẍⁱ = −Γⁱⱼₖ ẋʲ ẋᵏ`, proves local existence via Picard–Lindelöf (`LocalExistence.lean`), local uniqueness (`LocalUniqueness.lean`), and Fréchet differentiability of the geodesic flow in the initial state (`FlowDifferentiability.lean`). The variational corollary `flow_fderiv_at_initial_of_smoothChristoffel` is exported for the Gauss lemma.

### ParallelTransport

Defines parallel transport as the solution of a linear ODE along a curve in a trivialized fiber `ℝⁿ`. Proves the transport operator is a linear isometry under metric-compatible connections (`Isometry.lean`) and transports orthonormal frames to orthonormal frames (`Frames.lean`).

### Curvature

Defines the Riemann curvature tensor `R(X,Y)Z = ∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` as `curvatureOperator`, with sectional curvature (`SectionalCurvature`), Ricci curvature (`RicciCurvature`), and all algebraic symmetries (first-pair skew, first Bianchi identity, pair-swap symmetry).

### Exponential

Constructs the local exponential map `exp_p : T_pM → M` in coordinates (`coordinateExp`). Proves differentiability (`Differentiability.lean`), `fderiv exp 0 = id` (`DifferentialAtZero.lean`), `ContDiffAt` regularity (`DexpContinuity.lean`), the Gauss lemma in algebraic form (`GaussLemma.lean`), and constructs normal coordinates and the local inverse chart via the inverse function theorem (`LocalInverse.lean`, `NormalCoordinates.lean`).

### Minimization

Proves that normal neighborhoods are open (`NormalNeighborhoods.lean`), that short geodesics are length-minimizing (`ShortGeodesicsMinimize.lean`), and establishes the radial metric distance comparison (`LocalMinimizers.lean`).

### Measure

Defines the Riemannian volume form via the metric tensor (`RiemannianVolume.lean`), the pullback measure under the exponential map (`PullbackDensity.lean`), the Jacobian bound of the exponential map via Hadamard's determinant inequality (`ExpJacobian.lean`, `HadamardBound.lean`), and polar coordinate decomposition (`PolarCoordinates.lean`).

### Variation

Develops curve energy and length functionals, first and second variation formulas (`FirstVariationEnergy.lean`, `FirstVariationLength.lean`, `SecondVariation.lean`), the energy-criticality characterization of geodesics, the index form `I(J, J')`, and Ricci/scalar curvature variation formulas. The abstract curvature-variation identity `Ḟ = d_∇Ā` is proved algebraically in `Variation.lean`.

### Jacobi

Defines Jacobi fields as solutions of `∇_T∇_T J + R(J,T)T = 0`, proves existence and uniqueness from prescribed initial data via Picard–Lindelöf and Gronwall (`ExistenceUniqueness.lean`), defines conjugate points (`ConjugatePoints.lean`), and bridges geodesic variations to Jacobi fields (`VariationBridge.lean`).

### SecondBianchi

Proves the second Bianchi identity `d_∇Ω = 0` at three levels: abstract algebra, coordinate `Fin n`, and smooth coordinate. The classical cyclic sum `∇R = 0` is derived via bridge lemmas. **Entire module is complete — no external input.**

### Bochner

Proves the Bochner–Weitzenböck identity `∇*∇ = Δ_H − ℛ` with abstract, classical coordinate, and concrete coordinate versions. **Entire module is complete — no external input.**

### Weitzenbock

Proves the Hodge–Weitzenböck identity `Δ_H α = ∇*∇ α + ℛ α` for one-forms at abstract, coordinate, and concrete levels. **Entire module is complete — no external input.**

### Comparison

Scalar comparison (`SturmComparison.lean` — `scalarComparison_of_subsolution`, complete), Rauch comparison theorem (`Rauch.lean`), local volume comparison from Rauch bounds (`LocalVolumeFromRauch.lean`), Bishop–Gromov monotonicity (`BishopGromovMonotonicity.lean`), Cartan–Hadamard theorem (`CartanHadamard.lean`), Myers's theorem (`Myers.lean`), and the Bishop–Gromov volume comparison inequality (`BishopGromov.lean`).

### HopfRinow

Proves local compactness of Riemannian manifolds (`LocalCompactness.lean`), the Arzelà-Ascoli length-compactness lemma (`LengthCompactness.lean`), the equivalence of metric and smooth geodesic distance-realizers (`DistanceRealizer.lean`), and packages the four-way Hopf–Rinow spine: Complete → GeodesicallyComplete, Complete → Minimizers, Complete → Proper, Proper → Complete (`HopfRinow.lean`).

---

## Proof status (2026-04-02)

**Build**: ✅ green, ~2949 jobs, 0 errors, **0 `sorry` warnings** (as of 2026-04-02).

### All proved modules

| Module | Key results |
|--------|-------------|
| `SecondBianchi/*` | Abstract + coordinate second Bianchi identity |
| `Bochner/*` | Abstract + classical Bochner formula |
| `Weitzenbock/*` | Hodge–Weitzenböck identity |
| `Metric/*` | Coordinate/smooth metric infrastructure, `CoordinateMetricBounds` |
| `LeviCivita/*` | Existence, uniqueness, Christoffel fields, globalization |
| `ODE/*` | Flow Lipschitz, linearization, Fréchet differentiability, `ContDiffAt` |
| `Geodesic/*` | Geodesic ODE, Picard–Lindelöf solution, flow differentiability |
| `ParallelTransport/*` | Transport operator, isometry, frame transport |
| `Curvature/*` | Curvature tensor, sectional/Ricci curvature, symmetries |
| `Jacobi/*` | Jacobi ODE, Picard–Lindelöf + Gronwall existence/uniqueness |
| `Variation/*` | First/second variation of energy and length, index form |
| `Measure/*` | Riemannian volume, pullback density, Hadamard Jacobian bound |
| `Exponential/*` | `coordinateExp`, differential at zero, Fréchet differentiability, `ContDiffAt`, local inverse, Gauss lemma (zero-slice + full radial form), normal coordinates, `NormalCoordinateDifferentiability` |
| `Minimization/*` | Normal neighborhoods, metric bridge, short geodesics minimize, radial comparison, witness-free kinematics constructor |
| `Comparison/*` | Sturm comparison, Rauch norm core, scalar convexity, Bishop–Gromov monotonicity, full Rauch coordinate chain (8 new bridge files), geometric realization entry point |
| `HopfRinow/*` | Length compactness (Arzelà-Ascoli), local compactness, distance realizer, properness, coordinate metric distance, local minimizer, geodesic extension, `coordinate_hopfRinowTheorem` |

---

## Documentation

A natural-language proof companion is included in `docs/Formalized Differential Geometry.pdf`. It provides human-readable proofs of all formalized results, organized by module in the same order as the Lean source.
