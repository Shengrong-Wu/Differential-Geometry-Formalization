import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The scalar comparison model layer stays domain-aware in this batch: `sn`, `modelPosDomain`,
and the derivative helpers are the owner interface consumed by the scalar comparison route. -/

namespace Comparison

/-- The standard scalar model function used in comparison geometry. -/
noncomputable def sn (k r : ℝ) : ℝ :=
  if _hk : 0 < k then
    Real.sin (Real.sqrt k * r) / Real.sqrt k
  else if _h0 : k = 0 then
    r
  else
    Real.sinh (Real.sqrt (-k) * r) / Real.sqrt (-k)

/-- The first interval on which the constant-curvature model `sn k` stays positive and can be used
as a denominator in Sturm comparison arguments. For `k ≤ 0` this is the positive half-line. -/
noncomputable def modelPosDomain (k : ℝ) : Set ℝ :=
  if _hk : 0 < k then
    Set.Ioo 0 (Real.pi / Real.sqrt k)
  else
    Set.Ioi 0

/-- A scalar function satisfies the one-dimensional constant-curvature Jacobi model equation. This
is kept abstract at the package layer; the analytic ODE proof can refine it later. -/
def SolvesModelJacobiODE (k : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ r, HasDerivAt f (deriv f r) r ∧ HasDerivAt (deriv f) (-k * f r) r

theorem solvesModelJacobiODE_iff
    {k : ℝ} {f : ℝ → ℝ} :
    SolvesModelJacobiODE k f ↔
      ∀ r, HasDerivAt f (deriv f r) r ∧ HasDerivAt (deriv f) (-k * f r) r :=
  Iff.rfl

/-- The standard scalar-model initial conditions for comparison geometry. -/
def HasModelInitialConditions (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ deriv f 0 = 1

theorem hasModelInitialConditions_iff
    {f : ℝ → ℝ} :
    HasModelInitialConditions f ↔ f 0 = 0 ∧ deriv f 0 = 1 :=
  Iff.rfl

/-- Pointwise norm comparison on a fixed domain between a geometric Jacobi norm and the scalar
model. -/
def SatisfiesModelNormBoundOn
    (s : Set ℝ) (jacobiNorm model : ℝ → ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, t ∈ s → jacobiNorm t ≤ model t

/-- Pointwise norm comparison between a geometric Jacobi norm and the scalar model on the first
positive model interval. This corrects the positive-curvature domain story for later Rauch/Sturm
comparison. -/
def SatisfiesModelNormBound
    (k : ℝ) (jacobiNorm model : ℝ → ℝ) : Prop :=
  SatisfiesModelNormBoundOn (modelPosDomain k) jacobiNorm model

@[simp] theorem sn_of_zero (r : ℝ) :
    sn 0 r = r := by
  simp [sn]

theorem solvesModelJacobiODE_id_zero :
    SolvesModelJacobiODE 0 (fun r : ℝ => r) := by
  intro r
  refine ⟨?_, ?_⟩
  · simpa using (hasDerivAt_id r)
  · simpa using (hasDerivAt_const r (1 : ℝ))

theorem hasModelInitialConditions_id :
    HasModelInitialConditions (fun r : ℝ => r) := by
  simp [HasModelInitialConditions]

theorem sn_solvesModelJacobiODE_zero :
    SolvesModelJacobiODE 0 (sn 0) := by
  have hsn : sn 0 = (fun r : ℝ => r) := by
    funext r
    exact sn_of_zero r
  simpa [hsn] using solvesModelJacobiODE_id_zero

theorem sn_hasModelInitialConditions_zero :
    HasModelInitialConditions (sn 0) := by
  have hsn : sn 0 = (fun r : ℝ => r) := by
    funext r
    exact sn_of_zero r
  simpa [hsn] using hasModelInitialConditions_id

theorem hasDerivAt_sn_pos
    {k : ℝ} (hk : 0 < k) (r : ℝ) :
    HasDerivAt (sn k) (Real.cos (Real.sqrt k * r)) r := by
  have hk0 : Real.sqrt k ≠ 0 := Real.sqrt_ne_zero'.mpr hk
  have hinner : HasDerivAt (fun x : ℝ => Real.sqrt k * x) (Real.sqrt k) r := by
    simpa using ((hasDerivAt_const r (Real.sqrt k)).mul (hasDerivAt_id r))
  have hsin :
      HasDerivAt
        (fun x : ℝ => Real.sin (Real.sqrt k * x))
        (Real.cos (Real.sqrt k * r) * Real.sqrt k) r := by
    simpa using (Real.hasDerivAt_sin (Real.sqrt k * r)).comp r hinner
  have hdiv :
      HasDerivAt
        (fun x : ℝ => Real.sin (Real.sqrt k * x) / Real.sqrt k)
        ((Real.cos (Real.sqrt k * r) * Real.sqrt k) / Real.sqrt k) r := by
    simpa using hsin.div_const (Real.sqrt k)
  have hsn :
      sn k = fun x : ℝ => Real.sin (Real.sqrt k * x) / Real.sqrt k := by
    funext x
    simp [sn, hk]
  simpa [hsn, hk0] using hdiv

theorem deriv_sn_pos
    {k : ℝ} (hk : 0 < k) :
    deriv (sn k) = fun r : ℝ => Real.cos (Real.sqrt k * r) := by
  funext r
  exact (hasDerivAt_sn_pos hk r).deriv

theorem hasDerivAt_deriv_sn_pos
    {k : ℝ} (hk : 0 < k) (r : ℝ) :
    HasDerivAt (deriv (sn k)) (-k * sn k r) r := by
  have hinner : HasDerivAt (fun x : ℝ => Real.sqrt k * x) (Real.sqrt k) r := by
    simpa using ((hasDerivAt_const r (Real.sqrt k)).mul (hasDerivAt_id r))
  have hcos :
      HasDerivAt
        (fun x : ℝ => Real.cos (Real.sqrt k * x))
        (-Real.sin (Real.sqrt k * r) * Real.sqrt k) r := by
    simpa using (Real.hasDerivAt_cos (Real.sqrt k * r)).comp r hinner
  have hk0 : Real.sqrt k ≠ 0 := Real.sqrt_ne_zero'.mpr hk
  rw [deriv_sn_pos hk]
  convert hcos using 1
  have hsnr : sn k r = Real.sin (Real.sqrt k * r) / Real.sqrt k := by
    simp [sn, hk]
  rw [hsnr]
  field_simp [hk0]
  rw [Real.sq_sqrt (le_of_lt hk)]

theorem sn_solvesModelJacobiODE_pos
    {k : ℝ} (hk : 0 < k) :
    SolvesModelJacobiODE k (sn k) := by
  intro r
  exact ⟨by simpa [deriv_sn_pos hk] using hasDerivAt_sn_pos hk r,
    hasDerivAt_deriv_sn_pos hk r⟩

theorem sn_hasModelInitialConditions_pos
    {k : ℝ} (hk : 0 < k) :
    HasModelInitialConditions (sn k) := by
  constructor
  · simp [sn, hk]
  · simpa using (hasDerivAt_sn_pos hk 0).deriv

theorem hasDerivAt_sn_neg
    {k : ℝ} (hk : k < 0) (r : ℝ) :
    HasDerivAt (sn k) (Real.cosh (Real.sqrt (-k) * r)) r := by
  have hk0 : Real.sqrt (-k) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hk)
  have hinner : HasDerivAt (fun x : ℝ => Real.sqrt (-k) * x) (Real.sqrt (-k)) r := by
    simpa using ((hasDerivAt_const r (Real.sqrt (-k))).mul (hasDerivAt_id r))
  have hsinh :
      HasDerivAt
        (fun x : ℝ => Real.sinh (Real.sqrt (-k) * x))
        (Real.cosh (Real.sqrt (-k) * r) * Real.sqrt (-k)) r := by
    simpa using (Real.hasDerivAt_sinh (Real.sqrt (-k) * r)).comp r hinner
  have hdiv :
      HasDerivAt
        (fun x : ℝ => Real.sinh (Real.sqrt (-k) * x) / Real.sqrt (-k))
        ((Real.cosh (Real.sqrt (-k) * r) * Real.sqrt (-k)) / Real.sqrt (-k)) r := by
    simpa using hsinh.div_const (Real.sqrt (-k))
  have hnot : ¬ 0 < k := not_lt_of_ge (le_of_lt hk)
  have hkz : k ≠ 0 := hk.ne
  have hsn :
      sn k = fun x : ℝ => Real.sinh (Real.sqrt (-k) * x) / Real.sqrt (-k) := by
    funext x
    simp [sn, hnot, hkz]
  simpa [hsn, hk0] using hdiv

theorem deriv_sn_neg
    {k : ℝ} (hk : k < 0) :
    deriv (sn k) = fun r : ℝ => Real.cosh (Real.sqrt (-k) * r) := by
  funext r
  exact (hasDerivAt_sn_neg hk r).deriv

theorem hasDerivAt_deriv_sn_neg
    {k : ℝ} (hk : k < 0) (r : ℝ) :
    HasDerivAt (deriv (sn k)) (-k * sn k r) r := by
  have hinner : HasDerivAt (fun x : ℝ => Real.sqrt (-k) * x) (Real.sqrt (-k)) r := by
    simpa using ((hasDerivAt_const r (Real.sqrt (-k))).mul (hasDerivAt_id r))
  have hcosh :
      HasDerivAt
        (fun x : ℝ => Real.cosh (Real.sqrt (-k) * x))
        (Real.sinh (Real.sqrt (-k) * r) * Real.sqrt (-k)) r := by
    simpa using (Real.hasDerivAt_cosh (Real.sqrt (-k) * r)).comp r hinner
  have hk0 : Real.sqrt (-k) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hk)
  rw [deriv_sn_neg hk]
  convert hcosh using 1
  have hnot : ¬ 0 < k := not_lt_of_ge (le_of_lt hk)
  have hsnr : sn k r = Real.sinh (Real.sqrt (-k) * r) / Real.sqrt (-k) := by
    simp [sn, hnot, hk.ne]
  rw [hsnr]
  field_simp [hk0]
  rw [Real.sq_sqrt (by linarith)]
  ring

theorem sn_solvesModelJacobiODE_neg
    {k : ℝ} (hk : k < 0) :
    SolvesModelJacobiODE k (sn k) := by
  intro r
  exact ⟨by simpa [deriv_sn_neg hk] using hasDerivAt_sn_neg hk r,
    hasDerivAt_deriv_sn_neg hk r⟩

theorem sn_hasModelInitialConditions_neg
    {k : ℝ} (hk : k < 0) :
    HasModelInitialConditions (sn k) := by
  constructor
  · have hnot : ¬ 0 < k := not_lt_of_ge (le_of_lt hk)
    simp [sn, hnot, hk.ne]
  · simpa using (hasDerivAt_sn_neg hk 0).deriv

theorem sn_solvesModelJacobiODE
    (k : ℝ) :
    SolvesModelJacobiODE k (sn k) := by
  by_cases hk : 0 < k
  · exact sn_solvesModelJacobiODE_pos hk
  · by_cases h0 : k = 0
    · subst h0
      exact sn_solvesModelJacobiODE_zero
    · exact sn_solvesModelJacobiODE_neg (lt_of_le_of_ne (le_of_not_gt hk) h0)

theorem sn_hasModelInitialConditions
    (k : ℝ) :
    HasModelInitialConditions (sn k) := by
  by_cases hk : 0 < k
  · exact sn_hasModelInitialConditions_pos hk
  · by_cases h0 : k = 0
    · subst h0
      exact sn_hasModelInitialConditions_zero
    · exact sn_hasModelInitialConditions_neg (lt_of_le_of_ne (le_of_not_gt hk) h0)

theorem hasDerivAt_sn
    (k r : ℝ) :
    HasDerivAt (sn k) (deriv (sn k) r) r :=
  (sn_solvesModelJacobiODE k r).1

theorem hasDerivAt_deriv_sn
    (k r : ℝ) :
    HasDerivAt (deriv (sn k)) (-k * sn k r) r :=
  (sn_solvesModelJacobiODE k r).2

@[simp] theorem deriv_sn_zero
    (k : ℝ) :
    deriv (sn k) 0 = 1 :=
  (sn_hasModelInitialConditions k).2

theorem modelPosDomain_downward_closed
    {k s t : ℝ}
    (hs : s ∈ modelPosDomain k)
    (ht0 : 0 < t)
    (hts : t < s) :
    t ∈ modelPosDomain k := by
  by_cases hk : 0 < k
  · have hs' : s ∈ Set.Ioo 0 (Real.pi / Real.sqrt k) := by
      simpa [modelPosDomain, hk] using hs
    have ht' : t ∈ Set.Ioo 0 (Real.pi / Real.sqrt k) := ⟨ht0, lt_of_lt_of_le hts hs'.2.le⟩
    simpa [modelPosDomain, hk] using ht'
  · have ht' : t ∈ Set.Ioi (0 : ℝ) := ht0
    simpa [modelPosDomain, hk] using ht'

theorem modelNormBound_of_pointwise
    {k : ℝ}
    {jacobiNorm model : ℝ → ℝ}
    (h : ∀ ⦃t : ℝ⦄, t ∈ modelPosDomain k → jacobiNorm t ≤ model t) :
    SatisfiesModelNormBound k jacobiNorm model :=
  h

end Comparison
