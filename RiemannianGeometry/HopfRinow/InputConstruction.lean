import HopfRinow.GeodesicExtension
import HopfRinow.MinExistence
import HopfRinow.Properness

/-! # Hopf-Rinow bridge layer

This file packages the corrected public theorem spine used by the live Hopf-Rinow assembly:

- `Complete → HasGeodesicExtension`
- `Complete → MinimizingGeodesicsExist`
- `Complete → RiemannianProper`

The false bridge `MinimizingGeodesicsExist → RiemannianProper` is intentionally absent. -/

namespace HopfRinow

universe u

/-- Correct bridge for the complete→proper direction. -/
structure CompleteProperData (M : Type u) [PseudoMetricSpace M] : Prop where
  complete_proper : RiemannianComplete M → RiemannianProper M

/- Legacy note: the old `MinimizersProperInput` implication is intentionally omitted from the
design-stage copy because the corrected theorem spine uses `Complete → Proper` directly. -/

/-- Package the three nonstandard Hopf-Rinow directions as explicit inputs. -/
structure HopfRinowData (M : Type u) [PseudoMetricSpace M] : Prop where
  geodesicExtension : GeodesicExtensionData M
  minimizers : MinExistenceData M
  completeProper : CompleteProperData M

/-- Corrected local-to-global bridge layer for Hopf-Rinow. -/
structure CompleteToHopfRinowData (M : Type u) [PseudoMetricSpace M] : Prop where
  complete_geodesic : RiemannianComplete M → HasGeodesicExtension M
  complete_minimizers : RiemannianComplete M → MinimizingGeodesicsExist M
  complete_proper : RiemannianComplete M → RiemannianProper M

def geodesicExtensionDataOfBridge
    {M : Type u} [PseudoMetricSpace M]
    (bridge : CompleteToHopfRinowData M) :
    GeodesicExtensionData M where
  complete_geodesic := bridge.complete_geodesic

def minExistenceDataOfBridge
    {M : Type u} [PseudoMetricSpace M]
    (bridge : CompleteToHopfRinowData M) :
    MinExistenceData M where
  complete_minimizers := bridge.complete_minimizers

def completeProperDataOfBridge
    {M : Type u} [PseudoMetricSpace M]
    (bridge : CompleteToHopfRinowData M) :
    CompleteProperData M where
  complete_proper := bridge.complete_proper

def hopfRinowDataOfBridge
    {M : Type u} [PseudoMetricSpace M]
    (bridge : CompleteToHopfRinowData M) :
    HopfRinowData M where
  geodesicExtension := geodesicExtensionDataOfBridge bridge
  minimizers := minExistenceDataOfBridge bridge
  completeProper := completeProperDataOfBridge bridge

end HopfRinow
