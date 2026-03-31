import Comparison.VolumeConstruction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Volume growth monotonicity from local density comparison

This file bridges from local radial density comparison to the Bishop-Gromov monotonicity
of the volume ratio `volume(r) / modelVolume(r)`.

The key relation: if the density ratio `ρ(s) / ρ_model(s)` is nonincreasing, and both
volume functions are obtained by integrating their respective radial densities, then
the volume ratio `V(r) / V_model(r) = ∫₀ʳ ρ / ∫₀ʳ ρ_model` is also nonincreasing.

This is the one-dimensional "Chebyshev integral inequality" step. -/

namespace Comparison

open MeasureTheory Set

variable {n : ℕ}

/-- Package stating that the two global volume functions are obtained by integrating
the local density and model density, and that the density ratio is nonincreasing. -/
structure VolumeGrowthFromDensityData where
  localData : VolumeDensityComparisonData (n := n)
  growthData : VolumeGrowthData
  /-- The radial density function entering the volume integral. -/
  radialDensity : ℝ → ℝ
  /-- The radial model density function entering the model volume integral. -/
  radialModelDensity : ℝ → ℝ
  /-- The actual volume is the integral of the radial density. -/
  volume_eq_integral : ∀ r : ℝ, 0 ≤ r →
    growthData.volume r = ∫ s in (0)..r, radialDensity s
  /-- The model volume is the integral of the model density. -/
  modelVolume_eq_integral : ∀ r : ℝ, 0 ≤ r →
    growthData.modelVolume r = ∫ s in (0)..r, radialModelDensity s
  /-- The radial density is nonneg. -/
  radialDensity_nonneg : ∀ s : ℝ, 0 ≤ s → 0 ≤ radialDensity s
  /-- The model density is positive where relevant. -/
  radialModelDensity_pos : ∀ s : ℝ, 0 < s → 0 < radialModelDensity s
  /-- The density ratio is nonincreasing on `(0, ∞)`. This is the genuine differential
  inequality content: it says `d/dr [log(ρ/ρ_model)] ≤ 0`. -/
  densityRatio_antitone : AntitoneOn
    (fun s => radialDensity s / radialModelDensity s) (Ioi 0)
  /-- Both densities are integrable on `[0, r]`. -/
  density_integrable : ∀ r : ℝ, 0 ≤ r →
    IntervalIntegrable radialDensity MeasureTheory.volume 0 r
  modelDensity_integrable : ∀ r : ℝ, 0 ≤ r →
    IntervalIntegrable radialModelDensity MeasureTheory.volume 0 r

/-- **Owner theorem for Issue 5.** Under the volume-from-density representation and the
density-ratio monotonicity, the Bishop-Gromov antitonicity holds: `V(r)/V_model(r)` is
monotone nonincreasing on `[0, ∞)`.

The proof is the 1D "weighted Chebyshev integral inequality": if `f(s)/g(s)` is nonincreasing
and `g > 0`, then `∫₀ʳ f / ∫₀ʳ g` is nonincreasing. -/
theorem bishopGromov_monotonicity_of_density_growth
    (data : VolumeGrowthFromDensityData (n := n))
    (_hineq : HasLogJacobianDifferentialInequality data.localData) :
    HasBishopGromovMonotonicity data.growthData := by
  let q : ℝ → ℝ := fun s => data.radialDensity s / data.radialModelDensity s
  have hmodelVolume_pos : ∀ {r : ℝ}, 0 < r → 0 < data.growthData.modelVolume r := by
    intro r hr
    rw [data.modelVolume_eq_integral r hr.le]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      (data.modelDensity_integrable r hr.le)
      (fun x hx => data.radialModelDensity_pos x hx.1)
      hr
  have hratio_le_average : ∀ {r : ℝ}, 0 < r →
      q r ≤ data.growthData.volume r / data.growthData.modelVolume r := by
    intro r hr
    have hmodel_pos_r : 0 < data.radialModelDensity r := data.radialModelDensity_pos r hr
    have hmodelVolume_pos_r : 0 < data.growthData.modelVolume r := hmodelVolume_pos hr
    have hconst_int :
        IntervalIntegrable (fun s => q r * data.radialModelDensity s) MeasureTheory.volume 0 r :=
      (data.modelDensity_integrable r hr.le).const_mul (q r)
    have hmono_int :
        ∫ s in 0..r, q r * data.radialModelDensity s
          ≤ ∫ s in 0..r, data.radialDensity s := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hr.le hconst_int
        (data.density_integrable r hr.le) ?_
      intro s hs
      have hs_pos : 0 < s := hs.1
      have hmodel_pos_s : 0 < data.radialModelDensity s := data.radialModelDensity_pos s hs_pos
      have hratio :
          q r ≤ q s := data.densityRatio_antitone hs_pos hr hs.2.le
      calc
        q r * data.radialModelDensity s
          ≤ q s * data.radialModelDensity s := by
              exact mul_le_mul_of_nonneg_right hratio (le_of_lt hmodel_pos_s)
        _ = data.radialDensity s := by
              simp [q, div_mul_cancel₀ _ hmodel_pos_s.ne']
    have hmul :
        q r * data.growthData.modelVolume r ≤ data.growthData.volume r := by
      simpa [intervalIntegral.integral_const_mul, q,
        data.volume_eq_integral r hr.le, data.modelVolume_eq_integral r hr.le] using hmono_int
    exact (le_div_iff₀ hmodelVolume_pos_r).2 <| by
      simpa [q, mul_comm, mul_left_comm, mul_assoc] using hmul
  intro r hr R hR hrR
  by_cases hEq : r = R
  · subst hEq
    exact le_rfl
  · have hr_lt_R : r < R := lt_of_le_of_ne hrR hEq
    let avg_r : ℝ := data.growthData.volume r / data.growthData.modelVolume r
    have hmodelVolume_pos_r : 0 < data.growthData.modelVolume r := hmodelVolume_pos hr
    have hmodelVolume_pos_R : 0 < data.growthData.modelVolume R := hmodelVolume_pos hR
    have htailDensity_int :
        IntervalIntegrable data.radialDensity MeasureTheory.volume r R :=
      (data.density_integrable R hR.le).mono_set <|
        Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le hr.le hrR) Set.right_mem_uIcc
    have htailModel_int :
        IntervalIntegrable data.radialModelDensity MeasureTheory.volume r R :=
      (data.modelDensity_integrable R hR.le).mono_set <|
        Set.uIcc_subset_uIcc (Set.mem_uIcc_of_le hr.le hrR) Set.right_mem_uIcc
    have htail_bound :
        ∫ s in r..R, data.radialDensity s
          ≤ ∫ s in r..R, avg_r * data.radialModelDensity s := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hrR htailDensity_int
        (htailModel_int.const_mul avg_r) ?_
      intro s hs
      have hs_pos : 0 < s := lt_trans hr hs.1
      have hmodel_pos_s : 0 < data.radialModelDensity s := data.radialModelDensity_pos s hs_pos
      have hratio_sr : q s ≤ q r := data.densityRatio_antitone hr hs_pos hs.1.le
      have hratio_ra : q r ≤ avg_r := by
        simpa [avg_r] using hratio_le_average hr
      have hratio_sa : q s ≤ avg_r := le_trans hratio_sr hratio_ra
      calc
        data.radialDensity s = q s * data.radialModelDensity s := by
          simp [q, div_mul_cancel₀ _ hmodel_pos_s.ne']
        _ ≤ avg_r * data.radialModelDensity s := by
          exact mul_le_mul_of_nonneg_right hratio_sa (le_of_lt hmodel_pos_s)
    have hvol_split :
        data.growthData.volume R =
          data.growthData.volume r + ∫ s in r..R, data.radialDensity s := by
      rw [data.volume_eq_integral R hR.le, data.volume_eq_integral r hr.le]
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (data.density_integrable r hr.le) htailDensity_int
    have hmodel_split :
        data.growthData.modelVolume R =
          data.growthData.modelVolume r + ∫ s in r..R, data.radialModelDensity s := by
      rw [data.modelVolume_eq_integral R hR.le, data.modelVolume_eq_integral r hr.le]
      symm
      exact intervalIntegral.integral_add_adjacent_intervals
        (data.modelDensity_integrable r hr.le) htailModel_int
    have hbase :
        data.growthData.volume r = avg_r * data.growthData.modelVolume r := by
      calc
        data.growthData.volume r
            = (data.growthData.volume r / data.growthData.modelVolume r) *
                data.growthData.modelVolume r := by
                  field_simp [hmodelVolume_pos_r.ne']
        _ = avg_r * data.growthData.modelVolume r := by
              rfl
    have hupper :
        data.growthData.volume R ≤ avg_r * data.growthData.modelVolume R := by
      rw [hvol_split, hmodel_split, hbase]
      calc
        avg_r * data.growthData.modelVolume r + ∫ s in r..R, data.radialDensity s
          ≤ avg_r * data.growthData.modelVolume r +
              ∫ s in r..R, avg_r * data.radialModelDensity s := by
                gcongr
        _ = avg_r * (data.growthData.modelVolume r +
              ∫ s in r..R, data.radialModelDensity s) := by
              rw [intervalIntegral.integral_const_mul]
              ring
    exact (div_le_iff₀ hmodelVolume_pos_R).2 <| by
      simpa [bishopGromovRatio, avg_r, mul_comm, mul_left_comm, mul_assoc] using hupper

/-! ### Bridge-free Bishop-Gromov construction

The `BishopGromovConstruction` in `VolumeConstruction.lean` carries `monotonicityFromLocal`
as an external bridge field. Here we provide a derived version that eliminates that bridge
by carrying the full density representation, from which monotonicity follows via
`bishopGromov_monotonicity_of_density_growth`. -/

/-- Bridge-free Bishop-Gromov construction. Carries the full density representation
from which monotonicity is *derived* via the proved Chebyshev integral inequality,
rather than assumed as an external bridge function. -/
structure BishopGromovConstructionFromDensity where
  densityData : VolumeGrowthFromDensityData (n := n)

/-- The growth data from a density-based construction. -/
def BishopGromovConstructionFromDensity.growthData
    (c : BishopGromovConstructionFromDensity (n := n)) :
    VolumeGrowthData :=
  c.densityData.growthData

/-- The local data from a density-based construction. -/
def BishopGromovConstructionFromDensity.localData
    (c : BishopGromovConstructionFromDensity (n := n)) :
    VolumeDensityComparisonData (n := n) :=
  c.densityData.localData

/-- **Bridge-free Bishop-Gromov monotonicity.** Derived directly from the proved
Chebyshev integral inequality — no external bridge field needed. -/
theorem bishopGromov_of_densityConstruction
    (construction : BishopGromovConstructionFromDensity (n := n))
    (hlocal : HasLogJacobianDifferentialInequality construction.localData) :
    HasBishopGromovMonotonicity construction.growthData :=
  bishopGromov_monotonicity_of_density_growth construction.densityData hlocal

/-- Convert a density-based construction to the legacy bridge-based one.
This shows the bridge field `monotonicityFromLocal` is derivable. -/
def BishopGromovConstructionFromDensity.toLegacy
    (c : BishopGromovConstructionFromDensity (n := n)) :
    BishopGromovConstruction (n := n) where
  localData := c.localData
  growthData := c.growthData
  monotonicityFromLocal := fun hlocal =>
    bishopGromov_monotonicity_of_density_growth c.densityData hlocal

end Comparison
