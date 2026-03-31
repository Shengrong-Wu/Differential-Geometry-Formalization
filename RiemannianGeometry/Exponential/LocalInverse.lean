import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Exponential.DifferentialAtZero

namespace Exponential.Coordinate

open scoped Topology

variable {n : ℕ}

private theorem hasStrictFDerivAt_ofStrict
    {exp : LocalExponentialMap n}
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    HasStrictFDerivAt exp.toFun
      ((velocityPositionEquiv n : Velocity n →L[ℝ] Position n)) 0 := by
  simpa [StrictDifferentialAtZeroIsId, StrictDifferentialAtZero] using hstrict

/-- The chart-level inverse function theorem applied to a coordinate exponential map with identity
differential at the origin. -/
noncomputable def localExpPartialHomeomorph
    (exp : LocalExponentialMap n)
    (hcont : ContDiffAt ℝ 1 exp.toFun 0)
    (hdiff : DifferentialAtZeroIsId exp) :
    OpenPartialHomeomorph (Velocity n) (Position n) :=
  ContDiffAt.toOpenPartialHomeomorph exp.toFun hcont
    (by
      change HasFDerivAt exp.toFun ((velocityPositionEquiv n : Velocity n →L[ℝ] Position n)) 0
      simpa [DifferentialAtZeroIsId, DifferentialAtZero] using hdiff)
    (by norm_num)

/-- The chart-level inverse function theorem applied to a coordinate exponential map with strict
identity differential at the origin. -/
noncomputable def localExpPartialHomeomorphOfStrict
    (exp : LocalExponentialMap n)
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    OpenPartialHomeomorph (Velocity n) (Position n) :=
  (hasStrictFDerivAt_ofStrict (n := n) hstrict).toOpenPartialHomeomorph exp.toFun

/-- Variant of `localExpPartialHomeomorphOfStrict` whose source is guaranteed to be
a subset of `exp.source`. Built by intersecting the IFT neighborhood with `exp.source`
before constructing the partial homeomorphism via `ApproximatesLinearOn.toOpenPartialHomeomorph`. -/
noncomputable def localExpPartialHomeomorphOfStrictInSource
    (exp : LocalExponentialMap n)
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    OpenPartialHomeomorph (Velocity n) (Position n) :=
  let hf := hasStrictFDerivAt_ofStrict (n := n) hstrict
  let f' := (velocityPositionEquiv n : Velocity n ≃L[ℝ] Position n)
  let hU := Classical.choose_spec hf.approximates_deriv_on_open_nhds
  ApproximatesLinearOn.toOpenPartialHomeomorph exp.toFun
    (Classical.choose hf.approximates_deriv_on_open_nhds ∩ exp.source)
    (hU.2.2.mono_set Set.inter_subset_left)
    (f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' =>
      NNReal.half_lt_self <| ne_of_gt <| inv_pos.2 hf')
    (hU.2.1.inter exp.source_open)

@[simp] theorem localExpPartialHomeomorphOfStrictInSource_coe
    (exp : LocalExponentialMap n)
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    ⇑(localExpPartialHomeomorphOfStrictInSource exp hstrict) = exp.toFun := rfl

theorem localExpPartialHomeomorphOfStrictInSource_source_subset
    (exp : LocalExponentialMap n)
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    (localExpPartialHomeomorphOfStrictInSource exp hstrict).source ⊆ exp.source :=
  Set.inter_subset_right

theorem zero_mem_localExpInSource_source
    {exp : LocalExponentialMap n}
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    (0 : Velocity n) ∈ (localExpPartialHomeomorphOfStrictInSource exp hstrict).source :=
  ⟨(Classical.choose_spec
      (hasStrictFDerivAt_ofStrict (n := n) hstrict).approximates_deriv_on_open_nhds).1,
    exp.zero_mem⟩

theorem base_mem_localExpInSource_target
    {exp : LocalExponentialMap n}
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    exp.toFun 0 ∈ (localExpPartialHomeomorphOfStrictInSource exp hstrict).target :=
  (localExpPartialHomeomorphOfStrictInSource exp hstrict).map_source
    (zero_mem_localExpInSource_source hstrict)

theorem zero_mem_localExp_source
    {exp : LocalExponentialMap n}
    (hcont : ContDiffAt ℝ 1 exp.toFun 0)
    (hdiff : DifferentialAtZeroIsId exp) :
    0 ∈ (localExpPartialHomeomorph exp hcont hdiff).source :=
  by
    simpa [localExpPartialHomeomorph] using
      ContDiffAt.mem_toOpenPartialHomeomorph_source hcont
        (by
          change HasFDerivAt exp.toFun
            ((velocityPositionEquiv n : Velocity n →L[ℝ] Position n)) 0
          simpa [DifferentialAtZeroIsId, DifferentialAtZero] using hdiff)
        (by norm_num)

theorem zero_mem_localExp_source_ofStrict
    {exp : LocalExponentialMap n}
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    0 ∈ (localExpPartialHomeomorphOfStrict exp hstrict).source := by
  simpa [localExpPartialHomeomorphOfStrict] using
    (hasStrictFDerivAt_ofStrict (n := n) hstrict).mem_toOpenPartialHomeomorph_source

theorem base_mem_localExp_target
    {exp : LocalExponentialMap n}
    (hcont : ContDiffAt ℝ 1 exp.toFun 0)
    (hdiff : DifferentialAtZeroIsId exp) :
    exp.toFun 0 ∈ (localExpPartialHomeomorph exp hcont hdiff).target :=
  by
    simpa [localExpPartialHomeomorph] using
      ContDiffAt.image_mem_toOpenPartialHomeomorph_target hcont
        (by
          change HasFDerivAt exp.toFun
            ((velocityPositionEquiv n : Velocity n →L[ℝ] Position n)) 0
          simpa [DifferentialAtZeroIsId, DifferentialAtZero] using hdiff)
        (by norm_num)

theorem base_mem_localExp_target_ofStrict
    {exp : LocalExponentialMap n}
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    exp.toFun 0 ∈ (localExpPartialHomeomorphOfStrict exp hstrict).target := by
  simpa [localExpPartialHomeomorphOfStrict] using
    (hasStrictFDerivAt_ofStrict (n := n) hstrict).image_mem_toOpenPartialHomeomorph_target

noncomputable def localExpInverse
    (exp : LocalExponentialMap n)
    (hcont : ContDiffAt ℝ 1 exp.toFun 0)
    (hdiff : DifferentialAtZeroIsId exp) :
    Position n → Velocity n :=
  (localExpPartialHomeomorph exp hcont hdiff).symm

noncomputable def localExpInverseOfStrict
    (exp : LocalExponentialMap n)
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    Position n → Velocity n :=
  (localExpPartialHomeomorphOfStrict exp hstrict).symm

theorem localExpInverse_base
    {exp : LocalExponentialMap n}
    (hzero : exp.toFun 0 = exp.basePoint)
    (hcont : ContDiffAt ℝ 1 exp.toFun 0)
    (hdiff : DifferentialAtZeroIsId exp) :
    localExpInverse exp hcont hdiff exp.basePoint = 0 := by
  rw [← hzero]
  simpa [localExpInverse, localExpPartialHomeomorph] using
    (localExpPartialHomeomorph exp hcont hdiff).left_inv
      (zero_mem_localExp_source hcont hdiff)

theorem localExpInverse_base_ofStrict
    {exp : LocalExponentialMap n}
    (hzero : exp.toFun 0 = exp.basePoint)
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    localExpInverseOfStrict exp hstrict exp.basePoint = 0 := by
  rw [← hzero]
  simpa [localExpInverseOfStrict, localExpPartialHomeomorphOfStrict] using
    (localExpPartialHomeomorphOfStrict exp hstrict).left_inv
      (zero_mem_localExp_source_ofStrict hstrict)

theorem localExp_source_target_mem
    {exp : LocalExponentialMap n}
    (hcont : ContDiffAt ℝ 1 exp.toFun 0)
    (hdiff : DifferentialAtZeroIsId exp) :
    0 ∈ (localExpPartialHomeomorph exp hcont hdiff).source ∧
      exp.toFun 0 ∈ (localExpPartialHomeomorph exp hcont hdiff).target := by
  exact ⟨zero_mem_localExp_source hcont hdiff, base_mem_localExp_target hcont hdiff⟩

theorem localExp_leftInverse
    {exp : LocalExponentialMap n}
    (hcont : ContDiffAt ℝ 1 exp.toFun 0)
    (hdiff : DifferentialAtZeroIsId exp) :
    Set.EqOn
      (fun v => localExpInverse exp hcont hdiff (exp.toFun v))
      id
      (localExpPartialHomeomorph exp hcont hdiff).source := by
  intro v hv
  simpa [localExpInverse] using
    (localExpPartialHomeomorph exp hcont hdiff).left_inv hv

theorem localExp_leftInverse_ofStrict
    {exp : LocalExponentialMap n}
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    Set.EqOn
      (fun v => localExpInverseOfStrict exp hstrict (exp.toFun v))
      id
      (localExpPartialHomeomorphOfStrict exp hstrict).source := by
  intro v hv
  simpa [localExpInverseOfStrict] using
    (localExpPartialHomeomorphOfStrict exp hstrict).left_inv hv

theorem localExp_rightInverse
    {exp : LocalExponentialMap n}
    (hcont : ContDiffAt ℝ 1 exp.toFun 0)
    (hdiff : DifferentialAtZeroIsId exp) :
    Set.EqOn
      (fun x => exp.toFun (localExpInverse exp hcont hdiff x))
      id
      (localExpPartialHomeomorph exp hcont hdiff).target := by
  intro x hx
  simpa [localExpInverse] using
    (localExpPartialHomeomorph exp hcont hdiff).right_inv hx

theorem localExp_rightInverse_ofStrict
    {exp : LocalExponentialMap n}
    (hstrict : StrictDifferentialAtZeroIsId exp) :
    Set.EqOn
      (fun x => exp.toFun (localExpInverseOfStrict exp hstrict x))
      id
      (localExpPartialHomeomorphOfStrict exp hstrict).target := by
  intro x hx
  simpa [localExpInverseOfStrict] using
    (localExpPartialHomeomorphOfStrict exp hstrict).right_inv hx

end Exponential.Coordinate
