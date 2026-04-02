import HopfRinow.GeodesicExtension
import HopfRinow.SmoothGeodesicComplete
import Exponential.LocalAnalyticInput

/-! # Smooth-to-metric geodesic bridge

This file defines the interface for bridging smooth (coordinate) geodesic completeness
to the metric geodesic extension property used by the public Hopf-Rinow theorem.

## Architecture

The active Hopf-Rinow assembly currently consumes only one bridge step:

1. **Extension**: a smooth coordinate-geodesic line produced by smooth completeness yields a
   metric geodesic extension object.

Earlier design notes also tracked a stronger local-recognition step inside strongly convex balls,
but that field is not used by the live assembled theorem path and is intentionally omitted from the
active bridge surface here.

The coordinate metric field `g` is carried explicitly in the bridge interface so the active
coordinate-level assembly does not hide its dependence on the Riemannian metric data. -/

namespace HopfRinow

open Geodesic.Coordinate

variable {n : ℕ}

/-- Data package for the smooth-to-metric bridge on the active Hopf-Rinow path. -/
structure SmoothMetricBridgeData
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n) where
  /-- A smooth geodesic line produces a metric geodesic line. -/
  smooth_line_is_metric_line :
    HasCoordinateGeodesicCompleteness Gamma →
      HasGeodesicExtension (Exponential.Coordinate.Position n)

/-- From smooth completeness + bridge data, derive the metric geodesic extension. -/
theorem coordinate_hasGeodesicExtension_of_smooth_and_bridge
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (hsmooth : SmoothGeodesicCompletenessData Gamma)
    (hbridge : SmoothMetricBridgeData Gamma g) :
    HasGeodesicExtension (Exponential.Coordinate.Position n) :=
  hbridge.smooth_line_is_metric_line (hsmooth.completeness)

/-- Package the smooth completeness + bridge into `GeodesicExtensionData`. -/
def coordinate_geodesicExtensionData_of_smooth_bridge
    (Gamma : LeviCivita.CoordinateField.SmoothChristoffelField n)
    (g : Exponential.Coordinate.MetricField n)
    (hsmooth : SmoothGeodesicCompletenessData Gamma)
    (hbridge : SmoothMetricBridgeData Gamma g) :
    GeodesicExtensionData (Exponential.Coordinate.Position n) where
  complete_geodesic := fun _ =>
    coordinate_hasGeodesicExtension_of_smooth_and_bridge Gamma g hsmooth hbridge

end HopfRinow
