import HopfRinow.CompleteProper
import HopfRinow.DistanceRealizer
import HopfRinow.LengthCompactness
import HopfRinow.MetricLength
import HopfRinow.MinExistence

/-! Design-stage skeleton for the corrected complete→minimizers direction. -/

namespace HopfRinow

universe u

/-!
Target theorem inventory:

```lean
theorem complete_implies_minimizers
    (hcomplete : RiemannianComplete M) :
    MinimizingGeodesicsExist M
```

Expected proof ingredients:

- `complete_implies_proper`,
- `hasLengthCompactness_of_proper`,
- almost-minimizing curves,
- Lipschitz limit lemmas,
- `distanceRealizer_implies_minimizingGeodesic`.
-/

theorem compactSuperset_of_commonSource_uniformLipschitz
    {X : Type u} [PseudoMetricSpace X]
    (hcompact : HasLengthCompactness X)
    {S : Set (UnitIntervalCurve X)} {p : X} {L : NNReal}
    (h0 : ∀ ⦃γ⦄, γ ∈ S → γ ⟨0, by simp⟩ = p)
    (hlip : ∀ ⦃γ⦄, γ ∈ S → UniformLipschitzBound X L γ) :
    ∃ K : Set (UnitIntervalCurve X), IsCompact K ∧ S ⊆ K :=
  hcompact S (isLengthCompactFamily_of_commonSource_uniformLipschitz h0 hlip)

/-- Export the intended owner theorem name from the minimizing-geodesic input package. -/
theorem complete_implies_minimizers
    {M : Type u} [PseudoMetricSpace M]
    (input : MinExistenceData M) :
    RiemannianComplete M → MinimizingGeodesicsExist M :=
  input.complete_minimizers

/-- Package a proved complete-to-minimizers theorem back into the input layer. -/
def minExistenceData_of_complete_implies_minimizers
    {M : Type u} [PseudoMetricSpace M]
    (h : RiemannianComplete M → MinimizingGeodesicsExist M) :
    MinExistenceData M where
  complete_minimizers := h

end HopfRinow
