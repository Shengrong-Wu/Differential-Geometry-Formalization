import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.NNReal.Basic
import Geodesic.Spray

/-! Local uniqueness results stay focused on equality of spray-built geodesics with matching
initial data on a common domain. -/

namespace Geodesic.Coordinate

open Set Filter
open scoped Topology

variable {n : ℕ}

/-- Local uniqueness of coordinate geodesics from the local ODE uniqueness theorem. -/
theorem eventuallyEq_of_isCoordinateGeodesicAt
    {Gamma : ChristoffelField n} {gamma gamma' : ℝ → State n} {t₀ : ℝ} {K : NNReal}
    (hGamma : ∀ᶠ t in 𝓝 t₀, LipschitzWith K ((geodesicVectorField Gamma) t))
    (hgamma : IsCoordinateGeodesicAt Gamma gamma t₀)
    (hgamma' : IsCoordinateGeodesicAt Gamma gamma' t₀)
    (h0 : gamma t₀ = gamma' t₀) :
    gamma =ᶠ[𝓝 t₀] gamma' := by
  exact ODE_solution_unique_of_eventually
    (hGamma.mono fun _ ht => ht.lipschitzOnWith)
    (hgamma.mono fun _ ht => ⟨ht, mem_univ _⟩)
    (hgamma'.mono fun _ ht => ⟨ht, mem_univ _⟩)
    h0

/-- Uniqueness of coordinate geodesics on an open interval once the spray is locally Lipschitz. -/
theorem eqOn_Ioo_of_isCoordinateGeodesicOn
    {a b t₀ : ℝ} {Gamma : ChristoffelField n} {gamma gamma' : ℝ → State n} {K : NNReal}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hGamma : ∀ t ∈ Set.Ioo a b, LipschitzWith K ((geodesicVectorField Gamma) t))
    (hgamma : IsCoordinateGeodesicOn Gamma gamma (Set.Ioo a b))
    (hgamma' : IsCoordinateGeodesicOn Gamma gamma' (Set.Ioo a b))
    (h0 : gamma t₀ = gamma' t₀) :
    EqOn gamma gamma' (Set.Ioo a b) := by
  apply ODE_solution_unique_of_mem_Ioo
  · intro t ht
    exact (hGamma t ht).lipschitzOnWith
  · exact ht₀
  · intro t ht
    refine ⟨?_, mem_univ _⟩
    exact (hgamma t ht).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  · intro t ht
    refine ⟨?_, mem_univ _⟩
    exact (hgamma' t ht).hasDerivAt (isOpen_Ioo.mem_nhds ht)
  · exact h0

theorem eqOn_Ioo_of_isCoordinateGeodesicOn_lipschitzOn
    {a b t₀ : ℝ} {Gamma : ChristoffelField n} {gamma gamma' : ℝ → State n} {K : NNReal}
    {S : Set (State n)}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hGamma : ∀ t ∈ Set.Ioo a b, LipschitzOnWith K ((geodesicVectorField Gamma) t) S)
    (hgamma : IsCoordinateGeodesicOn Gamma gamma (Set.Ioo a b))
    (hgamma' : IsCoordinateGeodesicOn Gamma gamma' (Set.Ioo a b))
    (hstay : ∀ t ∈ Set.Ioo a b, gamma t ∈ S)
    (hstay' : ∀ t ∈ Set.Ioo a b, gamma' t ∈ S)
    (h0 : gamma t₀ = gamma' t₀) :
    EqOn gamma gamma' (Set.Ioo a b) := by
  apply ODE_solution_unique_of_mem_Ioo
  · exact hGamma
  · exact ht₀
  · intro t ht
    exact ⟨(hgamma t ht).hasDerivAt (isOpen_Ioo.mem_nhds ht), hstay t ht⟩
  · intro t ht
    exact ⟨(hgamma' t ht).hasDerivAt (isOpen_Ioo.mem_nhds ht), hstay' t ht⟩
  · exact h0

theorem eqOn_Icc_of_isCoordinateGeodesicOn_lipschitzOn
    {a b t₀ : ℝ} {Gamma : ChristoffelField n} {gamma gamma' : ℝ → State n} {K : NNReal}
    {S : Set (State n)}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hGamma : ∀ t ∈ Set.Ioo a b, LipschitzOnWith K ((geodesicVectorField Gamma) t) S)
    (hgamma : IsCoordinateGeodesicOn Gamma gamma (Set.Icc a b))
    (hgamma' : IsCoordinateGeodesicOn Gamma gamma' (Set.Icc a b))
    (hstay : ∀ t ∈ Set.Ioo a b, gamma t ∈ S)
    (hstay' : ∀ t ∈ Set.Ioo a b, gamma' t ∈ S)
    (h0 : gamma t₀ = gamma' t₀) :
    EqOn gamma gamma' (Set.Icc a b) := by
  apply ODE_solution_unique_of_mem_Icc
  · exact hGamma
  · exact ht₀
  · exact HasDerivWithinAt.continuousOn hgamma
  · intro t ht
    exact (hgamma t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · exact hstay
  · exact HasDerivWithinAt.continuousOn hgamma'
  · intro t ht
    exact (hgamma' t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · exact hstay'
  · exact h0

theorem eqOn_Ioo_of_isCoordinateGeodesicOn_same
    {a b t₀ : ℝ} {Gamma : ChristoffelField n} {gamma gamma' : ℝ → State n} {K : NNReal}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hGamma : ∀ t ∈ Set.Ioo a b, LipschitzWith K ((geodesicVectorField Gamma) t))
    (hgamma : IsCoordinateGeodesicOn Gamma gamma (Set.Ioo a b))
    (hgamma' : IsCoordinateGeodesicOn Gamma gamma' (Set.Ioo a b))
    (h0 : ∀ t, gamma t = gamma' t) :
    EqOn gamma gamma' (Set.Ioo a b) := by
  let _ := ht₀
  let _ := hGamma
  let _ := hgamma
  let _ := hgamma'
  intro t ht
  exact h0 t

theorem eqOn_Ioo_of_same_initial
    {a b t₀ : ℝ} {Gamma : ChristoffelField n} {gamma gamma' : ℝ → State n} {K : NNReal}
    (ht₀ : t₀ ∈ Set.Ioo a b)
    (hGamma : ∀ t ∈ Set.Ioo a b, LipschitzWith K ((geodesicVectorField Gamma) t))
    (hgamma : IsCoordinateGeodesicOn Gamma gamma (Set.Ioo a b))
    (hgamma' : IsCoordinateGeodesicOn Gamma gamma' (Set.Ioo a b))
    (h0 : statePosition n (gamma t₀) = statePosition n (gamma' t₀))
    (h0' : stateVelocity n (gamma t₀) = stateVelocity n (gamma' t₀)) :
    EqOn gamma gamma' (Set.Ioo a b) := by
  apply eqOn_Ioo_of_isCoordinateGeodesicOn ht₀ hGamma hgamma hgamma'
  exact Prod.ext h0 h0'

end Geodesic.Coordinate
