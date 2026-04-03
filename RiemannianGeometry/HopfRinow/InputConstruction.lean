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

end HopfRinow
