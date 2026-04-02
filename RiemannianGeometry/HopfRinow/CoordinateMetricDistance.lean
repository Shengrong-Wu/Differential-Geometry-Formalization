import Minimization.NormalCoordinateKinematics

/-! # Coordinate Riemannian path-distance candidate

This file starts the honest metric-aware Hopf-Rinow route on the fixed coordinate model
`Position n = Fin n → ℝ`.

The existing Hopf-Rinow interfaces are still phrased over the ambient `PseudoMetricSpace`
structure on `Position n`, while the local analytic/minimization branch proves statements for the
coordinate Riemannian metric field `g`. The purpose of this file is to package the first owner
layer for the missing path-metric:

- coordinate paths with a chosen velocity witness,
- their `g`-length,
- the induced infimum distance candidate.

At this stage we only prove the basic facts needed to show the definition is meaningful:

- every endpoint pair admits at least one such path (affine path),
- every path length is nonnegative,
- the candidate distance is nonnegative,
- the candidate distance from a point to itself is `0`.

The triangle inequality / symmetry / identification with local radial minimizers are left to later
owner files. -/

namespace HopfRinow

open scoped Topology

variable {n : ℕ}

/-- A coordinate path from `p` to `q` on `[0,1]`, together with a chosen coordinate velocity
witness. -/
structure CoordinateMetricPath
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) where
  γ : ℝ → Exponential.Coordinate.Position n
  T : ℝ → Exponential.Coordinate.Velocity n
  velocity :
    Minimization.Coordinate.HasCoordinateVelocityOn γ T (Set.Icc (0 : ℝ) 1)
  source : γ 0 = p
  target : γ 1 = q

namespace CoordinateMetricPath

@[simp] theorem quadraticForm_neg
    (g : Metric.Coordinate.Tensor2 n)
    (v : Exponential.Coordinate.Velocity n) :
    Metric.Coordinate.quadraticForm g (-v) = Metric.Coordinate.quadraticForm g v := by
  unfold Metric.Coordinate.quadraticForm
  simp

@[simp] theorem metricSpeed_neg
    (g : Exponential.Coordinate.MetricField n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (T : ℝ → Exponential.Coordinate.Velocity n)
    (t : ℝ) :
    Minimization.Coordinate.metricSpeed (n := n) g γ (fun τ => -T τ) t =
      Minimization.Coordinate.metricSpeed (n := n) g γ T t := by
  simp [Minimization.Coordinate.metricSpeed]

/-- The `g`-length of a coordinate path with chosen velocity witness. -/
noncomputable def length
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q) : ℝ :=
  Minimization.Coordinate.metricCurveLength (n := n) g c.γ 0 1 c.T

theorem length_nonneg
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q) :
    0 ≤ c.length := by
  unfold length Minimization.Coordinate.metricCurveLength
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun t _ => Minimization.Coordinate.metricSpeed_nonneg (n := n) g c.γ c.T t)

/-- Constant path at a point. -/
def constant
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n) :
    CoordinateMetricPath (n := n) g p p where
  γ := fun _ => p
  T := fun _ => (0 : Exponential.Coordinate.Velocity n)
  velocity := by
    intro t ht
    simpa using (hasDerivAt_const t (c := p)).hasDerivWithinAt
  source := rfl
  target := rfl

theorem constant_length_eq_zero
    {g : Exponential.Coordinate.MetricField n}
    {p : Exponential.Coordinate.Position n} :
    CoordinateMetricPath.length (constant (n := n) g p) = 0 := by
  unfold CoordinateMetricPath.length constant
  simp [Minimization.Coordinate.metricCurveLength, Minimization.Coordinate.metricSpeed,
    Metric.Coordinate.quadraticForm]

/-- Affine path between two coordinate points. -/
def affine
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    CoordinateMetricPath (n := n) g p q where
  γ := fun t => p + t • (q - p)
  T := fun _ => q - p
  velocity := by
    intro t ht
    simpa using (((hasDerivAt_id t).smul_const (q - p)).const_add p).hasDerivWithinAt
  source := by simp
  target := by simp

/-- Time reversal of a coordinate path. -/
def reverse
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q) :
    CoordinateMetricPath (n := n) g q p where
  γ := fun t => c.γ (1 - t)
  T := fun t => -c.T (1 - t)
  velocity := by
    intro t ht
    have hmaps : Set.MapsTo (fun τ : ℝ => 1 - τ) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
      intro τ hτ
      constructor <;> linarith [hτ.1, hτ.2]
    have hinner : HasDerivWithinAt (fun τ : ℝ => 1 - τ) (-1) (Set.Icc (0 : ℝ) 1) t := by
      simpa using ((hasDerivAt_id t).const_sub (1 : ℝ)).hasDerivWithinAt
    have houter :
        HasDerivWithinAt c.γ (c.T (1 - t)) (Set.Icc (0 : ℝ) 1) (1 - t) :=
      c.velocity (1 - t) (hmaps ht)
    simpa [Function.comp, neg_one_smul] using
      (houter.hasFDerivWithinAt.comp_hasDerivWithinAt
        (x := t) hinner hmaps)
  source := by simpa using c.target
  target := by simpa using c.source

@[simp] theorem reverse_length_eq
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q) :
    c.reverse.length = c.length := by
  unfold length reverse Minimization.Coordinate.metricCurveLength
  have hcongr :
      (∫ t in (0 : ℝ)..1,
        Minimization.Coordinate.metricSpeed (n := n) g
          (fun τ => c.γ (1 - τ)) (fun τ => -c.T (1 - τ)) t) =
      ∫ t in (0 : ℝ)..1,
        Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T (1 - t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t
    intro ht
    rw [metricSpeed_neg]
    rfl
  calc
    ∫ t in (0 : ℝ)..1,
        Minimization.Coordinate.metricSpeed (n := n) g
          (fun τ => c.γ (1 - τ)) (fun τ => -c.T (1 - τ)) t
      = ∫ t in (0 : ℝ)..1,
          Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T (1 - t) := hcongr
    _ = ∫ t in (0 : ℝ)..1, Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T t := by
          calc
            ∫ t in (0 : ℝ)..1, Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T (1 - t)
              = -∫ t in (1 : ℝ)..0, Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T t := by
                  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
                    (intervalIntegral.integral_comp_mul_add
                      (f := fun t =>
                        Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T t)
                      (a := (0 : ℝ)) (b := (1 : ℝ)) (c := (-1 : ℝ)) (by norm_num) (1 : ℝ))
            _ = ∫ t in (0 : ℝ)..1, Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T t := by
                  rw [intervalIntegral.integral_symm]
                  ring

private theorem quadraticForm_smul
    (g : Metric.Coordinate.Tensor2 n)
    (a : ℝ)
    (v : Exponential.Coordinate.Velocity n) :
    Metric.Coordinate.quadraticForm g (a • v) =
      a ^ 2 * Metric.Coordinate.quadraticForm g v := by
  unfold Metric.Coordinate.quadraticForm
  simp_rw [Pi.smul_apply]
  calc
    ∑ i : Fin n, ∑ j : Fin n, (a * v i) * g i j * (a * v j)
      = ∑ i : Fin n, ∑ j : Fin n, a ^ 2 * (v i * g i j * v j) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = ∑ i : Fin n, a ^ 2 * ∑ j : Fin n, v i * g i j * v j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [Finset.mul_sum]
    _ = a ^ 2 * ∑ i : Fin n, ∑ j : Fin n, v i * g i j * v j := by
          rw [Finset.mul_sum]

private theorem sqrt_mul_sq
    (a q : ℝ) :
    Real.sqrt (a ^ 2 * q) = |a| * Real.sqrt q := by
  by_cases hq : 0 ≤ q
  · rw [Real.sqrt_mul (sq_nonneg a) q, Real.sqrt_sq_eq_abs]
  · have hq' : q ≤ 0 := le_of_not_ge hq
    have hmul : a ^ 2 * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) hq'
    rw [Real.sqrt_eq_zero_of_nonpos hmul, Real.sqrt_eq_zero_of_nonpos hq']
    ring

@[simp] theorem metricSpeed_smul
    (g : Exponential.Coordinate.MetricField n)
    (γ : ℝ → Exponential.Coordinate.Position n)
    (T : ℝ → Exponential.Coordinate.Velocity n)
    {a : ℝ}
    (ha : 0 ≤ a)
    (t : ℝ) :
    Minimization.Coordinate.metricSpeed (n := n) g γ (fun s => a • T s) t =
      a * Minimization.Coordinate.metricSpeed (n := n) g γ T t := by
  unfold Minimization.Coordinate.metricSpeed
  rw [quadraticForm_smul, sqrt_mul_sq, abs_of_nonneg ha]

/-- Prefix reparametrization of a coordinate-metric path to the subinterval `[0, t]`. -/
def prefixPath
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    CoordinateMetricPath (n := n) g p (c.γ t) where
  γ := fun s => c.γ (t * s)
  T := fun s => t • c.T (t * s)
  velocity := by
    intro s hs
    have hmaps : Set.MapsTo (fun τ : ℝ => t * τ) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
      intro τ hτ
      constructor
      · exact mul_nonneg ht.1 hτ.1
      · have hmul : t * τ ≤ t * 1 := mul_le_mul_of_nonneg_left hτ.2 ht.1
        have ht_one : t * 1 ≤ 1 := by simpa using ht.2
        exact le_trans hmul ht_one
    have hinner :
        HasDerivWithinAt (fun τ : ℝ => t * τ) t (Set.Icc (0 : ℝ) 1) s := by
      simpa [smul_eq_mul, mul_comm] using (((hasDerivAt_id s).smul_const t).hasDerivWithinAt)
    have houter :
        HasDerivWithinAt c.γ (c.T (t * s)) (Set.Icc (0 : ℝ) 1) (t * s) :=
      c.velocity (t * s) (hmaps hs)
    simpa [Function.comp] using
      (houter.hasFDerivWithinAt.comp_hasDerivWithinAt
        (x := s) hinner hmaps)
  source := by simpa [zero_mul] using c.source
  target := by simp

@[simp] theorem prefixPath_length_eq
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (c.prefixPath t ht).length =
      Minimization.Coordinate.metricCurveLength (n := n) g c.γ 0 t c.T := by
  unfold CoordinateMetricPath.length prefixPath Minimization.Coordinate.metricCurveLength
  have hcongr :
      (∫ s in (0 : ℝ)..1,
        Minimization.Coordinate.metricSpeed (n := n) g
          (fun τ => c.γ (t * τ))
          (fun τ => t • c.T (t * τ)) s) =
      ∫ s in (0 : ℝ)..1,
        t * Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T (t * s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s
    intro hs
    rw [metricSpeed_smul (n := n) g (fun τ => c.γ (t * τ)) (fun τ => c.T (t * τ)) ht.1]
    rfl
  calc
    ∫ s in (0 : ℝ)..1,
        Minimization.Coordinate.metricSpeed (n := n) g
          (fun τ => c.γ (t * τ))
          (fun τ => t • c.T (t * τ)) s
      = ∫ s in (0 : ℝ)..1,
          t * Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T (t * s) := hcongr
    _ = t * ∫ s in (0 : ℝ)..1, Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T (t * s) :=
          by rw [intervalIntegral.integral_const_mul]
    _ = ∫ s in (0 : ℝ)..t, Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T s := by
          simpa [smul_eq_mul, zero_mul, one_mul] using
            (intervalIntegral.smul_integral_comp_mul_left
              (f := fun s : ℝ => Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T s)
              (a := (0 : ℝ)) (b := (1 : ℝ)) (c := t))

/-- Suffix reparametrization of a coordinate-metric path to the subinterval `[t, 1]`. -/
def suffixPath
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    CoordinateMetricPath (n := n) g (c.γ t) q where
  γ := fun s => c.γ (t + (1 - t) * s)
  T := fun s => (1 - t) • c.T (t + (1 - t) * s)
  velocity := by
    intro s hs
    have hmaps :
        Set.MapsTo (fun τ : ℝ => t + (1 - t) * τ) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) := by
      intro τ hτ
      constructor
      · nlinarith [ht.1, hτ.1, hτ.2]
      · nlinarith [ht.2, hτ.1, hτ.2]
    have hinner :
        HasDerivWithinAt (fun τ : ℝ => t + (1 - t) * τ) (1 - t) (Set.Icc (0 : ℝ) 1) s := by
      simpa [smul_eq_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
        ((((hasDerivAt_id s).smul_const (1 - t)).const_add t).hasDerivWithinAt)
    have houter :
        HasDerivWithinAt c.γ (c.T (t + (1 - t) * s)) (Set.Icc (0 : ℝ) 1) (t + (1 - t) * s) :=
      c.velocity (t + (1 - t) * s) (hmaps hs)
    simpa [Function.comp] using
      (houter.hasFDerivWithinAt.comp_hasDerivWithinAt
        (x := s) hinner hmaps)
  source := by simp
  target := by simpa [c.target]

@[simp] theorem suffixPath_length_eq
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q)
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (c.suffixPath t ht).length =
      Minimization.Coordinate.metricCurveLength (n := n) g c.γ t 1 c.T := by
  unfold CoordinateMetricPath.length suffixPath Minimization.Coordinate.metricCurveLength
  have hcongr :
      (∫ s in (0 : ℝ)..1,
        Minimization.Coordinate.metricSpeed (n := n) g
          (fun τ => c.γ (t + (1 - t) * τ))
          (fun τ => (1 - t) • c.T (t + (1 - t) * τ)) s) =
      ∫ s in (0 : ℝ)..1,
        (1 - t) * Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T
          (t + (1 - t) * s) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s
    intro hs
    rw [metricSpeed_smul (n := n) g
      (fun τ => c.γ (t + (1 - t) * τ))
      (fun τ => c.T (t + (1 - t) * τ))
      (sub_nonneg.mpr ht.2)]
    rfl
  calc
    ∫ s in (0 : ℝ)..1,
        Minimization.Coordinate.metricSpeed (n := n) g
          (fun τ => c.γ (t + (1 - t) * τ))
          (fun τ => (1 - t) • c.T (t + (1 - t) * τ)) s
      = ∫ s in (0 : ℝ)..1,
          (1 - t) * Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T
            (t + (1 - t) * s) := hcongr
    _ = (1 - t) * ∫ s in (0 : ℝ)..1,
          Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T
            (t + (1 - t) * s) := by
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ s in t..1, Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T s := by
          simpa [smul_eq_mul, zero_mul, one_mul, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc] using
            (intervalIntegral.smul_integral_comp_mul_add
              (f := fun s : ℝ => Minimization.Coordinate.metricSpeed (n := n) g c.γ c.T s)
              (a := (0 : ℝ)) (b := (1 : ℝ)) (c := (1 - t)) (d := t))

end CoordinateMetricPath

/-- The set of path lengths of coordinate paths from `p` to `q` for the coordinate metric `g`. -/
def coordinateMetricLengthSet
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) : Set ℝ :=
  Set.range (fun c : CoordinateMetricPath (n := n) g p q => c.length)

theorem coordinateMetricLengthSet_nonempty
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    (coordinateMetricLengthSet (n := n) g p q).Nonempty := by
  refine ⟨(CoordinateMetricPath.affine (n := n) g p q).length, ?_⟩
  exact ⟨CoordinateMetricPath.affine (n := n) g p q, rfl⟩

theorem coordinateMetricLengthSet_bddBelow
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    BddBelow (coordinateMetricLengthSet (n := n) g p q) := by
  refine ⟨0, ?_⟩
  intro ℓ hℓ
  rcases hℓ with ⟨c, rfl⟩
  exact c.length_nonneg

/-- The infimum path-distance candidate induced by the coordinate Riemannian metric `g`. -/
noncomputable def coordinateMetricDistCandidate
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) : ℝ :=
  sInf (coordinateMetricLengthSet (n := n) g p q)

theorem coordinateMetricDistCandidate_nonneg
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    0 ≤ coordinateMetricDistCandidate (n := n) g p q := by
  unfold coordinateMetricDistCandidate
  exact le_csInf
    (coordinateMetricLengthSet_nonempty (n := n) g p q)
    (fun b hb => by
      rcases hb with ⟨c, rfl⟩
      exact c.length_nonneg)

theorem coordinateMetricDistCandidate_le_length
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q) :
    coordinateMetricDistCandidate (n := n) g p q ≤ c.length := by
  unfold coordinateMetricDistCandidate
  exact csInf_le
    (coordinateMetricLengthSet_bddBelow (n := n) g p q)
    ⟨c, rfl⟩

@[simp] theorem coordinateMetricDistCandidate_self
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n) :
    coordinateMetricDistCandidate (n := n) g p p = 0 := by
  refine le_antisymm ?_ ?_
  · calc
      coordinateMetricDistCandidate (n := n) g p p
        ≤ (CoordinateMetricPath.constant (n := n) g p).length :=
          coordinateMetricDistCandidate_le_length
            (c := CoordinateMetricPath.constant (n := n) g p)
      _ = 0 := CoordinateMetricPath.constant_length_eq_zero
  · exact coordinateMetricDistCandidate_nonneg (n := n) g p p

@[simp] theorem coordinateMetricDistCandidate_symm
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    coordinateMetricDistCandidate (n := n) g p q =
      coordinateMetricDistCandidate (n := n) g q p := by
  refine le_antisymm ?_ ?_
  · exact le_csInf
      (coordinateMetricLengthSet_nonempty (n := n) g q p)
      (by
        intro b hb
        rcases hb with ⟨c, rfl⟩
        simpa using
          (coordinateMetricDistCandidate_le_length
            (c := CoordinateMetricPath.reverse c)))
  · exact le_csInf
      (coordinateMetricLengthSet_nonempty (n := n) g p q)
      (by
        intro b hb
        rcases hb with ⟨c, rfl⟩
        simpa using
          (coordinateMetricDistCandidate_le_length
            (c := CoordinateMetricPath.reverse c)))

/-- A finite chain of coordinate-metric paths. This is the honest concatenation-friendly owner
layer: the local objects remain genuine `C¹` paths, while global path concatenation is represented
by list-style composition instead of forcing differentiability at junctions. -/
inductive CoordinateMetricChain
    (g : Exponential.Coordinate.MetricField n) :
    Exponential.Coordinate.Position n → Exponential.Coordinate.Position n → Type where
  | nil (p : Exponential.Coordinate.Position n) :
      CoordinateMetricChain g p p
  | cons {p q r : Exponential.Coordinate.Position n}
      (c : CoordinateMetricPath (n := n) g p q)
      (cs : CoordinateMetricChain g q r) :
      CoordinateMetricChain g p r

namespace CoordinateMetricChain

/-- Total `g`-length of a finite chain of coordinate paths. -/
noncomputable def length
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (cs : CoordinateMetricChain (n := n) g p q) : ℝ :=
  match cs with
  | .nil _ => 0
  | .cons c cs => c.length + length cs

@[simp] theorem length_nil
    {g : Exponential.Coordinate.MetricField n}
    {p : Exponential.Coordinate.Position n} :
    length (CoordinateMetricChain.nil (n := n) (g := g) p) = 0 := rfl

@[simp] theorem length_cons
    {g : Exponential.Coordinate.MetricField n}
    {p q r : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q)
    (cs : CoordinateMetricChain (n := n) g q r) :
    length (CoordinateMetricChain.cons c cs) = c.length + length cs := rfl

theorem length_nonneg
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (cs : CoordinateMetricChain (n := n) g p q) :
    0 ≤ cs.length := by
  induction cs with
  | nil _ => simp [length]
  | cons c cs ih =>
      simp [length, c.length_nonneg, ih, add_nonneg]

/-- View a single coordinate path as a one-segment chain. -/
def ofPath
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q) :
    CoordinateMetricChain (n := n) g p q :=
  .cons c (.nil _)

@[simp] theorem length_ofPath
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (c : CoordinateMetricPath (n := n) g p q) :
    (ofPath c).length = c.length := by
  simp [ofPath, length]

/-- Concatenate two finite chains. -/
def append
    {g : Exponential.Coordinate.MetricField n}
    {p q r : Exponential.Coordinate.Position n}
    (cs₁ : CoordinateMetricChain (n := n) g p q)
    (cs₂ : CoordinateMetricChain (n := n) g q r) :
    CoordinateMetricChain (n := n) g p r :=
  match cs₁ with
  | .nil _ => cs₂
  | .cons c cs => .cons c (append cs cs₂)

@[simp] theorem append_nil
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (cs : CoordinateMetricChain (n := n) g p q) :
    append cs (.nil q) = cs := by
  induction cs with
  | nil _ => rfl
  | cons c cs ih => simp [append, ih]

@[simp] theorem nil_append
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (cs : CoordinateMetricChain (n := n) g p q) :
    append (.nil p) cs = cs := rfl

@[simp] theorem length_append
    {g : Exponential.Coordinate.MetricField n}
    {p q r : Exponential.Coordinate.Position n}
    (cs₁ : CoordinateMetricChain (n := n) g p q)
    (cs₂ : CoordinateMetricChain (n := n) g q r) :
    (append cs₁ cs₂).length = cs₁.length + cs₂.length := by
  induction cs₁ with
  | nil _ =>
      simp [append, length]
  | cons c cs ih =>
      simp [append, length, ih, add_assoc]

/-- Reverse a finite chain. -/
def reverse
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (cs : CoordinateMetricChain (n := n) g p q) :
    CoordinateMetricChain (n := n) g q p :=
  match cs with
  | .nil p => .nil p
  | .cons c cs => append (reverse cs) (ofPath c.reverse)

@[simp] theorem length_reverse
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (cs : CoordinateMetricChain (n := n) g p q) :
    cs.reverse.length = cs.length := by
  induction cs with
  | nil _ => simp [reverse, length]
  | cons c cs ih =>
      simp [reverse, length_append, ih, c.reverse_length_eq, length, add_comm]

end CoordinateMetricChain

/-- The set of chain lengths from `p` to `q` for the coordinate metric `g`. -/
def coordinateMetricChainLengthSet
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) : Set ℝ :=
  Set.range (fun cs : CoordinateMetricChain (n := n) g p q => cs.length)

theorem coordinateMetricChainLengthSet_nonempty
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    (coordinateMetricChainLengthSet (n := n) g p q).Nonempty := by
  refine ⟨(CoordinateMetricChain.ofPath (CoordinateMetricPath.affine (n := n) g p q)).length, ?_⟩
  exact ⟨CoordinateMetricChain.ofPath (CoordinateMetricPath.affine (n := n) g p q), rfl⟩

theorem coordinateMetricChainLengthSet_bddBelow
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    BddBelow (coordinateMetricChainLengthSet (n := n) g p q) := by
  refine ⟨0, ?_⟩
  intro ℓ hℓ
  rcases hℓ with ⟨cs, rfl⟩
  exact cs.length_nonneg

/-- The concatenation-friendly coordinate-Riemannian distance candidate. -/
noncomputable def coordinateMetricChainDist
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) : ℝ :=
  sInf (coordinateMetricChainLengthSet (n := n) g p q)

theorem coordinateMetricChainDist_nonneg
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    0 ≤ coordinateMetricChainDist (n := n) g p q := by
  unfold coordinateMetricChainDist
  exact le_csInf
    (coordinateMetricChainLengthSet_nonempty (n := n) g p q)
    (fun b hb => by
      rcases hb with ⟨cs, rfl⟩
      exact cs.length_nonneg)

theorem coordinateMetricChainDist_le_length
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    (cs : CoordinateMetricChain (n := n) g p q) :
    coordinateMetricChainDist (n := n) g p q ≤ cs.length := by
  unfold coordinateMetricChainDist
  exact csInf_le
    (coordinateMetricChainLengthSet_bddBelow (n := n) g p q)
    ⟨cs, rfl⟩

@[simp] theorem coordinateMetricChainDist_self
    (g : Exponential.Coordinate.MetricField n)
    (p : Exponential.Coordinate.Position n) :
    coordinateMetricChainDist (n := n) g p p = 0 := by
  refine le_antisymm ?_ ?_
  · simpa using
      (coordinateMetricChainDist_le_length
        (cs := CoordinateMetricChain.nil (n := n) p))
  · exact coordinateMetricChainDist_nonneg (n := n) g p p

@[simp] theorem coordinateMetricChainDist_symm
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    coordinateMetricChainDist (n := n) g p q =
      coordinateMetricChainDist (n := n) g q p := by
  refine le_antisymm ?_ ?_
  · exact le_csInf
      (coordinateMetricChainLengthSet_nonempty (n := n) g q p)
      (by
        intro b hb
        rcases hb with ⟨cs, rfl⟩
        simpa using
          (coordinateMetricChainDist_le_length
            (cs := CoordinateMetricChain.reverse cs)))
  · exact le_csInf
      (coordinateMetricChainLengthSet_nonempty (n := n) g p q)
      (by
        intro b hb
        rcases hb with ⟨cs, rfl⟩
        simpa using
          (coordinateMetricChainDist_le_length
            (cs := CoordinateMetricChain.reverse cs)))

theorem coordinateMetricChainDist_le_add_length
    {g : Exponential.Coordinate.MetricField n}
    {p q r : Exponential.Coordinate.Position n}
    (cs : CoordinateMetricChain (n := n) g q r) :
    coordinateMetricChainDist (n := n) g p r ≤
      coordinateMetricChainDist (n := n) g p q + cs.length := by
  have hsub :
      coordinateMetricChainDist (n := n) g p r - cs.length ≤
        coordinateMetricChainDist (n := n) g p q := by
    unfold coordinateMetricChainDist
    apply le_csInf
    · exact coordinateMetricChainLengthSet_nonempty (n := n) g p q
    · intro b hb
      rcases hb with ⟨cs', rfl⟩
      have happend :
          sInf (coordinateMetricChainLengthSet (n := n) g p r) ≤
            (CoordinateMetricChain.append cs' cs).length :=
        coordinateMetricChainDist_le_length
          (cs := CoordinateMetricChain.append cs' cs)
      rw [CoordinateMetricChain.length_append] at happend
      linarith
  linarith

theorem coordinateMetricChainDist_triangle
    (g : Exponential.Coordinate.MetricField n)
    (p q r : Exponential.Coordinate.Position n) :
    coordinateMetricChainDist (n := n) g p r ≤
      coordinateMetricChainDist (n := n) g p q +
        coordinateMetricChainDist (n := n) g q r := by
  by_contra htriangle
  let dpr := coordinateMetricChainDist (n := n) g p r
  let dpq := coordinateMetricChainDist (n := n) g p q
  let dqr := coordinateMetricChainDist (n := n) g q r
  have hdpr : dpr = coordinateMetricChainDist (n := n) g p r := rfl
  have hdpq : dpq = coordinateMetricChainDist (n := n) g p q := rfl
  have hdqr : dqr = coordinateMetricChainDist (n := n) g q r := rfl
  have hlt : dpq + dqr < dpr := by
    simpa [dpr, dpq, dqr] using lt_of_not_ge htriangle
  let ε : ℝ := (dpr - (dpq + dqr)) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  have hεeq : dpq + dqr + 2 * ε = dpr := by
    dsimp [ε]
    ring
  have hdpq_lt : coordinateMetricChainDist (n := n) g p q < dpq + ε := by
    rw [← hdpq]
    linarith
  have hdqr_lt : coordinateMetricChainDist (n := n) g q r < dqr + ε := by
    rw [← hdqr]
    linarith
  have hcs₁ :
      ∃ cs : CoordinateMetricChain (n := n) g p q, cs.length < dpq + ε := by
    obtain ⟨ℓ, hℓmem, hℓlt⟩ := exists_lt_of_csInf_lt
      (coordinateMetricChainLengthSet_nonempty (n := n) g p q) (by
        simpa [coordinateMetricChainDist] using hdpq_lt)
    rcases hℓmem with ⟨cs, rfl⟩
    exact ⟨cs, hℓlt⟩
  have hcs₂ :
      ∃ cs : CoordinateMetricChain (n := n) g q r, cs.length < dqr + ε := by
    obtain ⟨ℓ, hℓmem, hℓlt⟩ := exists_lt_of_csInf_lt
      (coordinateMetricChainLengthSet_nonempty (n := n) g q r) (by
        simpa [coordinateMetricChainDist] using hdqr_lt)
    rcases hℓmem with ⟨cs, rfl⟩
    exact ⟨cs, hℓlt⟩
  rcases hcs₁ with ⟨cs₁, hlen₁⟩
  rcases hcs₂ with ⟨cs₂, hlen₂⟩
  have happend :
      dpr ≤ (CoordinateMetricChain.append cs₁ cs₂).length := by
    rw [hdpr]
    exact coordinateMetricChainDist_le_length
      (cs := CoordinateMetricChain.append cs₁ cs₂)
  rw [CoordinateMetricChain.length_append] at happend
  have : (CoordinateMetricChain.append cs₁ cs₂).length < dpr := by
    rw [CoordinateMetricChain.length_append]
    rw [← hεeq]
    linarith
  linarith

theorem coordinateMetricChainDist_le_candidate
    (g : Exponential.Coordinate.MetricField n)
    (p q : Exponential.Coordinate.Position n) :
    coordinateMetricChainDist (n := n) g p q ≤
      coordinateMetricDistCandidate (n := n) g p q := by
  unfold coordinateMetricDistCandidate
  apply le_csInf
  · exact coordinateMetricLengthSet_nonempty (n := n) g p q
  · intro b hb
    rcases hb with ⟨c, rfl⟩
    simpa [CoordinateMetricChain.length_ofPath] using
      (coordinateMetricChainDist_le_length
        (cs := CoordinateMetricChain.ofPath c))

/-! ### Chain calibration: potential-function lower bounds on chain distance

A **calibration** (or potential function) for the coordinate-metric chain distance is a function
`φ : Position n → ℝ` satisfying `φ y - φ x ≤ c.length` for every admissible one-step move
(i.e., every `CoordinateMetricPath` from `x` to `y`).

Telescoping along a chain then gives `φ q - φ p ≤ chain.length` for any chain from `p` to `q`,
and taking the infimum yields `φ q - φ p ≤ coordinateMetricChainDist g p q`.

The main application: instantiate `φ = metricNormalRadius g Gamma p` to get the reverse
inequality `metricNormalRadius ≤ chainDist`, completing the distance identification. -/

/-- Telescoping along a chain: if `φ` is subadditive on each segment, it bounds the chain length
from below. -/
theorem CoordinateMetricChain.calibration_le_length
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    {φ : Exponential.Coordinate.Position n → ℝ}
    (hcalib : ∀ (x y : Exponential.Coordinate.Position n)
      (c : CoordinateMetricPath (n := n) g x y),
        φ y - φ x ≤ c.length)
    (cs : CoordinateMetricChain (n := n) g p q) :
    φ q - φ p ≤ cs.length := by
  induction cs with
  | nil _ => simp [CoordinateMetricChain.length]
  | cons seg tail ih =>
      simp only [CoordinateMetricChain.length_cons]
      linarith [hcalib _ _ seg, ih]

/-- The chain calibration lemma: a calibration gives a lower bound on chain distance. -/
theorem coordinateMetricChainDist_ge_of_calibration
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    {φ : Exponential.Coordinate.Position n → ℝ}
    (hcalib : ∀ (x y : Exponential.Coordinate.Position n)
      (c : CoordinateMetricPath (n := n) g x y),
        φ y - φ x ≤ c.length) :
    φ q - φ p ≤ coordinateMetricChainDist (n := n) g p q := by
  unfold coordinateMetricChainDist
  apply le_csInf
  · exact coordinateMetricChainLengthSet_nonempty (n := n) g p q
  · intro b hb
    rcases hb with ⟨cs, rfl⟩
    exact CoordinateMetricChain.calibration_le_length hcalib cs

/-- Specialization: if `φ p = 0` and `φ` calibrates, then `φ q ≤ chainDist`. -/
theorem coordinateMetricChainDist_ge_of_calibration_zero
    {g : Exponential.Coordinate.MetricField n}
    {p q : Exponential.Coordinate.Position n}
    {φ : Exponential.Coordinate.Position n → ℝ}
    (hφp : φ p = 0)
    (hcalib : ∀ (x y : Exponential.Coordinate.Position n)
      (c : CoordinateMetricPath (n := n) g x y),
        φ y - φ x ≤ c.length) :
    φ q ≤ coordinateMetricChainDist (n := n) g p q := by
  have := coordinateMetricChainDist_ge_of_calibration hcalib (p := p) (q := q)
  linarith

end HopfRinow
