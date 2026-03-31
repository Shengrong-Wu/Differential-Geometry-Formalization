import Geodesic
import HopfRinow.CompleteProper

/-! Design-stage skeleton for smooth geodesic completeness.

The future live file should prove the ODE continuation theorem in the smooth category before the
metric-geodesic bridge is applied. -/

namespace HopfRinow

/-!
Planned internal interface:

```lean
structure HasSmoothGeodesicExtension ...
```

Target theorem inventory:

```lean
theorem geodesic_extend_past_endpoint_of_compact_stateTube

theorem complete_implies_smoothGeodesicComplete
```

This file should stay ODE/smooth-facing and should not itself export the final metric geodesic
extension statement.
-/

end HopfRinow
