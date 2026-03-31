import LeviCivita.LocalExistence
import LeviCivita.LeviCivita
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Smooth coordinate fields and tensor packages live here; downstream exponential and Gauss
files reuse these concrete coordinate-field interfaces without reopening the core theory. -/

open scoped BigOperators Topology
open BigOperators Finset

namespace LeviCivita.CoordinateField

noncomputable section

variable {n : ℕ}

/-- The flat coordinate model `ℝ^n`, represented as `Fin n → ℝ`. -/
abbrev Coord (n : ℕ) := Fin n → ℝ

/-- The `dir`-th standard coordinate vector. -/
def coordBasis (dir : Fin n) : Coord n :=
  Pi.basisFun ℝ (Fin n) dir

/-- Smooth real-valued scalar fields on `ℝ^n`. -/
structure SmoothScalarField (n : ℕ) where
  toFun : Coord n → ℝ
  smooth' : ContDiff ℝ ⊤ toFun

/-- Smooth `ℝ^n`-valued vector fields on `ℝ^n`, expressed componentwise. -/
structure SmoothVectorField (n : ℕ) where
  toFun : Coord n → Coord n
  smooth' : ∀ i, ContDiff ℝ ⊤ (fun x => toFun x i)

/-- Smooth coordinate metric coefficient fields `g_{ij}(x)`. -/
structure SmoothTensor2Field (n : ℕ) where
  toFun : Fin n → Fin n → Coord n → ℝ
  smooth' : ∀ i j, ContDiff ℝ ⊤ (toFun i j)

/-- Smooth Christoffel coefficient fields `Γ^k_{ij}(x)`. -/
structure SmoothChristoffelField (n : ℕ) where
  toFun : Fin n → Fin n → Fin n → Coord n → ℝ
  smooth' : ∀ k i j, ContDiff ℝ ⊤ (toFun k i j)

instance : CoeFun (SmoothScalarField n) (fun _ => Coord n → ℝ) where
  coe f := f.toFun

instance : CoeFun (SmoothVectorField n) (fun _ => Coord n → Coord n) where
  coe X := X.toFun

instance : CoeFun (SmoothTensor2Field n) (fun _ => Fin n → Fin n → Coord n → ℝ) where
  coe g := g.toFun

instance : CoeFun (SmoothChristoffelField n) (fun _ => Fin n → Fin n → Fin n → Coord n → ℝ) where
  coe Γ := Γ.toFun

@[ext] theorem SmoothScalarField.ext {f g : SmoothScalarField n} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk ff hf =>
    cases g with
    | mk gg hg =>
      simp at h
      have : ff = gg := funext h
      subst this
      rfl

@[ext] theorem SmoothVectorField.ext {X Y : SmoothVectorField n}
    (h : ∀ x i, X x i = Y x i) : X = Y := by
  cases X with
  | mk f hf =>
    cases Y with
    | mk g hg =>
      simp at h
      have : f = g := by
        funext x
        funext i
        exact h x i
      subst this
      rfl

private theorem SmoothScalarField.toFun_injective :
    Function.Injective (fun f : SmoothScalarField n => f.toFun) := by
  intro f g h
  ext x
  exact congrFun h x

private theorem SmoothVectorField.toFun_injective :
    Function.Injective (fun X : SmoothVectorField n => X.toFun) := by
  intro X Y h
  ext x i
  exact congrFun (congrFun h x) i

instance : Zero (SmoothScalarField n) where
  zero :=
    { toFun := fun _ => 0
      smooth' := by simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : Coord n => (0 : ℝ)) }

instance : One (SmoothScalarField n) where
  one :=
    { toFun := fun _ => 1
      smooth' := by simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : Coord n => (1 : ℝ)) }

instance : Add (SmoothScalarField n) where
  add f g :=
    { toFun := fun x => f x + g x
      smooth' := by simpa using f.smooth'.add g.smooth' }

instance : Neg (SmoothScalarField n) where
  neg f :=
    { toFun := fun x => -f x
      smooth' := by simpa using f.smooth'.neg }

instance : Sub (SmoothScalarField n) where
  sub f g := f + (-g)

instance : Mul (SmoothScalarField n) where
  mul f g :=
    { toFun := fun x => f x * g x
      smooth' := by simpa using f.smooth'.mul g.smooth' }

instance (m : Nat) : OfNat (SmoothScalarField n) m where
  ofNat :=
    { toFun := fun _ => m
      smooth' := by simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : Coord n => (m : ℝ)) }

instance : SMul (SmoothScalarField n) (SmoothScalarField n) where
  smul f g := f * g

instance : Zero (SmoothVectorField n) where
  zero :=
    { toFun := fun _ _ => 0
      smooth' := by
        intro i
        simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : Coord n => (0 : ℝ)) }

instance : Add (SmoothVectorField n) where
  add X Y :=
    { toFun := fun x i => X x i + Y x i
      smooth' := by
        intro i
        simpa using (X.smooth' i).add (Y.smooth' i) }

instance : Neg (SmoothVectorField n) where
  neg X :=
    { toFun := fun x i => -X x i
      smooth' := by
        intro i
        simpa using (X.smooth' i).neg }

instance : Sub (SmoothVectorField n) where
  sub X Y := X + (-Y)

instance : SMul (SmoothScalarField n) (SmoothVectorField n) where
  smul f X :=
    { toFun := fun x i => f x * X x i
      smooth' := by
        intro i
        simpa using f.smooth'.mul (X.smooth' i) }

@[simp] theorem smoothScalar_add_apply (f g : SmoothScalarField n) (x : Coord n) :
    (f + g) x = f x + g x := rfl

@[simp] theorem smoothScalar_sub_apply (f g : SmoothScalarField n) (x : Coord n) :
    (f - g) x = f x - g x := rfl

@[simp] theorem smoothScalar_mul_apply (f g : SmoothScalarField n) (x : Coord n) :
    (f * g) x = f x * g x := rfl

@[simp] theorem smoothVector_zero_apply (x : Coord n) (i : Fin n) :
    (0 : SmoothVectorField n) x i = 0 := rfl

@[simp] theorem smoothVector_add_apply (X Y : SmoothVectorField n) (x : Coord n) (i : Fin n) :
    (X + Y) x i = X x i + Y x i := rfl

@[simp] theorem smoothVector_sub_apply (X Y : SmoothVectorField n) (x : Coord n) (i : Fin n) :
    (X - Y) x i = X x i - Y x i := rfl

@[simp] theorem smoothVector_smul_apply
    (f : SmoothScalarField n) (X : SmoothVectorField n) (x : Coord n) (i : Fin n) :
    (f • X) x i = f x * X x i := rfl

/-- The constant scalar field with value `c`. -/
def constScalarField (c : ℝ) : SmoothScalarField n :=
  { toFun := fun _ => c
    smooth' := by simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : Coord n => c) }

/-- The constant vector field with value `v`. -/
def constVectorField (v : Coord n) : SmoothVectorField n :=
  { toFun := fun _ => v
    smooth' := by
      intro i
      simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : Coord n => v i) }

/-- The `i`-th standard coordinate vector field. -/
def basisVectorField (i : Fin n) : SmoothVectorField n :=
  constVectorField (coordBasis i)

/-- The `(i,j)` coefficient of a smooth tensor field as a smooth scalar field. -/
def SmoothTensor2Field.component (g : SmoothTensor2Field n) (i j : Fin n) : SmoothScalarField n :=
  { toFun := g i j
    smooth' := g.smooth' i j }

/-- The `i`-th component of a smooth vector field as a smooth scalar field. -/
def SmoothVectorField.component (X : SmoothVectorField n) (i : Fin n) : SmoothScalarField n :=
  { toFun := fun x => X x i
    smooth' := X.smooth' i }

@[simp] theorem SmoothTensor2Field.component_apply
    (g : SmoothTensor2Field n) (i j : Fin n) (x : Coord n) :
    g.component i j x = g i j x := rfl

@[simp] theorem SmoothVectorField.component_apply
    (X : SmoothVectorField n) (i : Fin n) (x : Coord n) :
    X.component i x = X x i := rfl

theorem SmoothScalarField.differentiableAt (f : SmoothScalarField n) (x : Coord n) :
    DifferentiableAt ℝ f x :=
  f.smooth'.contDiffAt.differentiableAt (by simp)

theorem SmoothVectorField.differentiableAt_component (X : SmoothVectorField n)
    (i : Fin n) (x : Coord n) :
    DifferentiableAt ℝ (fun y => X y i) x :=
  (X.smooth' i).contDiffAt.differentiableAt (by simp)

/-- The coordinate partial derivative `∂_{dir}` of a smooth scalar field. -/
def pderivScalar (f : SmoothScalarField n) (dir : Fin n) : SmoothScalarField n :=
  { toFun := fun x => fderiv ℝ f x (coordBasis dir)
    smooth' := by
      simpa using
        ((f.smooth').fderiv_right (m := ⊤) (by simp)).clm_apply
          (contDiff_const : ContDiff ℝ ⊤ fun _ : Coord n => coordBasis dir) }

/-- The coordinate partial derivative `∂_{dir}` of a smooth vector field. -/
def pderivVector (X : SmoothVectorField n) (dir : Fin n) : SmoothVectorField n :=
  { toFun := fun x i => fderiv ℝ (fun y => X y i) x (coordBasis dir)
    smooth' := by
      intro i
      simpa using
        (((X.smooth' i).fderiv_right (m := ⊤) (by simp)).clm_apply
          (contDiff_const : ContDiff ℝ ⊤ fun _ : Coord n => coordBasis dir)) }

@[simp] theorem pderivScalar_apply (f : SmoothScalarField n) (dir : Fin n) (x : Coord n) :
    pderivScalar f dir x = fderiv ℝ f x (coordBasis dir) := rfl

@[simp] theorem pderivVector_apply (X : SmoothVectorField n) (dir : Fin n)
    (x : Coord n) (i : Fin n) :
    pderivVector X dir x i = fderiv ℝ (fun y => X y i) x (coordBasis dir) := rfl

theorem pderivScalar_add (f g : SmoothScalarField n) (dir : Fin n) (x : Coord n) :
    pderivScalar (f + g) dir x = pderivScalar f dir x + pderivScalar g dir x := by
  unfold pderivScalar
  simpa using congrArg (fun L => L (coordBasis dir)) <|
    fderiv_add (f.differentiableAt x) (g.differentiableAt x)

theorem pderivScalar_mul (f g : SmoothScalarField n) (dir : Fin n) (x : Coord n) :
    pderivScalar (f * g) dir x =
      pderivScalar f dir x * g x + f x * pderivScalar g dir x := by
  unfold pderivScalar
  simpa [smul_eq_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
    congrArg (fun L => L (coordBasis dir)) <|
      fderiv_fun_mul (f.differentiableAt x) (g.differentiableAt x)

theorem pderivVector_add_apply (X Y : SmoothVectorField n) (dir : Fin n)
    (x : Coord n) (i : Fin n) :
    pderivVector (X + Y) dir x i = pderivVector X dir x i + pderivVector Y dir x i := by
  unfold pderivVector
  simpa using congrArg (fun L => L (coordBasis dir)) <|
    fderiv_add (X.differentiableAt_component i x) (Y.differentiableAt_component i x)

theorem pderivVector_smul_apply (f : SmoothScalarField n) (X : SmoothVectorField n)
    (dir : Fin n) (x : Coord n) (i : Fin n) :
    pderivVector (f • X) dir x i =
      pderivScalar f dir x * X x i + f x * pderivVector X dir x i := by
  unfold pderivVector pderivScalar
  simpa [smul_eq_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
    congrArg (fun L => L (coordBasis dir)) <|
      fderiv_fun_mul (f.differentiableAt x) (X.differentiableAt_component i x)

/-- The directional derivative `X(f)`. -/
def directionalDerivative (X : SmoothVectorField n) (f : SmoothScalarField n) :
    SmoothScalarField n :=
  { toFun := fun x => ∑ i : Fin n, X x i * pderivScalar f i x
    smooth' := by
      refine ContDiff.sum ?_
      intro i hi
      simpa using (X.smooth' i).mul (pderivScalar f i).smooth' }

@[simp] theorem directionalDerivative_apply
    (X : SmoothVectorField n) (f : SmoothScalarField n) (x : Coord n) :
    directionalDerivative X f x = ∑ i : Fin n, X x i * pderivScalar f i x := rfl

/-- The coordinate Lie bracket of smooth vector fields. -/
def lieBracket (X Y : SmoothVectorField n) : SmoothVectorField n :=
  { toFun := fun x k =>
      ∑ i : Fin n, (X x i * pderivVector Y i x k - Y x i * pderivVector X i x k)
    smooth' := by
      intro k
      refine ContDiff.sum ?_
      intro i hi
      simpa using ((X.smooth' i).mul ((pderivVector Y i).smooth' k)).sub
        ((Y.smooth' i).mul ((pderivVector X i).smooth' k)) }

@[simp] theorem lieBracket_apply
    (X Y : SmoothVectorField n) (x : Coord n) (k : Fin n) :
    lieBracket X Y x k =
      ∑ i : Fin n, (X x i * pderivVector Y i x k - Y x i * pderivVector X i x k) := rfl

/-- The smooth coordinate metric pairing associated to a coefficient field `g_{ij}(x)`. -/
def coordinateMetricPairing (g : SmoothTensor2Field n) :
    LeviCivita.MetricPairing (SmoothVectorField n) (SmoothScalarField n) :=
  fun X Y =>
    { toFun := fun x => ∑ i : Fin n, ∑ j : Fin n, X x i * g i j x * Y x j
      smooth' := by
        refine ContDiff.sum ?_
        intro i hi
        refine ContDiff.sum ?_
        intro j hj
        simpa [mul_assoc] using ((X.smooth' i).mul (g.smooth' i j)).mul (Y.smooth' j) }

/-- The coordinate connection context on smooth fields. -/
def coordinateConnectionContext (n : ℕ) :
    LeviCivita.ConnectionContext (SmoothVectorField n) (SmoothScalarField n) where
  bracket := lieBracket
  deriv := directionalDerivative

/-- Coordinate covariant derivative attached to a smooth Christoffel field. -/
noncomputable def covariantDerivative
    (Γ : SmoothChristoffelField n) :
    LeviCivita.CovariantDerivative (SmoothVectorField n) (SmoothScalarField n)
      (coordinateConnectionContext n) where
  toFun X Y :=
    { toFun := fun x k =>
        (∑ i : Fin n, X x i * pderivVector Y i x k) +
          ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j
      smooth' := by
        intro k
        refine (ContDiff.sum ?_).add (ContDiff.sum ?_)
        · intro i hi
          simpa using (X.smooth' i).mul ((pderivVector Y i).smooth' k)
        · intro i hi
          refine ContDiff.sum ?_
          intro j hj
          simpa [mul_assoc] using ((X.smooth' i).mul (Γ.smooth' k i j)).mul (Y.smooth' j) }
  add_left X Y Z := by
    ext x k
    change
      (∑ i : Fin n, (X + Y) x i * pderivVector Z i x k) +
        ∑ i : Fin n, ∑ j : Fin n, (X + Y) x i * Γ k i j x * Z x j
      =
      ((∑ i : Fin n, X x i * pderivVector Z i x k) +
        ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Z x j) +
      ((∑ i : Fin n, Y x i * pderivVector Z i x k) +
        ∑ i : Fin n, ∑ j : Fin n, Y x i * Γ k i j x * Z x j)
    simp [smoothVector_add_apply, add_mul, Finset.sum_add_distrib,
      add_assoc, add_left_comm, add_comm]
  smul_left f X Y := by
    ext x k
    change
      (∑ i : Fin n, (f • X) x i * pderivVector Y i x k) +
        ∑ i : Fin n, ∑ j : Fin n, (f • X) x i * Γ k i j x * Y x j
      =
      f x *
        ((∑ i : Fin n, X x i * pderivVector Y i x k) +
          ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j)
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [smoothVector_smul_apply]
      ring
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [smoothVector_smul_apply]
      ring
  add_right X Y Z := by
    ext x k
    have hderiv : ∀ i : Fin n,
        pderivVector (Y + Z) i x k = pderivVector Y i x k + pderivVector Z i x k := by
      intro i
      exact pderivVector_add_apply Y Z i x k
    change
      (∑ i : Fin n, X x i * pderivVector (Y + Z) i x k) +
        ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * (Y + Z) x j
      =
      ((∑ i : Fin n, X x i * pderivVector Y i x k) +
        ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j) +
      ((∑ i : Fin n, X x i * pderivVector Z i x k) +
        ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Z x j)
    simp_rw [hderiv]
    simp only [smoothVector_add_apply, mul_add, Finset.sum_add_distrib,
      add_assoc, add_left_comm]
  leibniz X Y f := by
    ext x k
    have hderiv :
        ∀ i : Fin n,
          pderivVector (f • Y) i x k =
            pderivScalar f i x * Y x k + f x * pderivVector Y i x k := by
      intro i
      exact pderivVector_smul_apply f Y i x k
    simp_rw [hderiv]
    simp only [coordinateConnectionContext, directionalDerivative, smoothVector_smul_apply]
    change
      (∑ i : Fin n, X x i * (pderivScalar f i x * Y x k + f x * pderivVector Y i x k)) +
        ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * (f x * Y x j)
      =
      (∑ i : Fin n, X x i * pderivScalar f i x) * Y x k +
        f x *
          ((∑ i : Fin n, X x i * pderivVector Y i x k) +
            ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j)
    simp only [mul_add, Finset.sum_add_distrib, add_assoc]
    have h1 :
        ∑ i : Fin n, X x i * pderivScalar f i x * Y x k =
          (∑ i : Fin n, X x i * pderivScalar f i x) * Y x k := by
      rw [Finset.sum_mul]
    have h2 :
        ∑ i : Fin n, X x i * f x * pderivVector Y i x k =
          f x * ∑ i : Fin n, X x i * pderivVector Y i x k := by
      calc
        ∑ i : Fin n, X x i * f x * pderivVector Y i x k
            = ∑ i : Fin n, f x * (X x i * pderivVector Y i x k) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = f x * ∑ i : Fin n, X x i * pderivVector Y i x k := by
              rw [Finset.mul_sum]
    have h3 :
        ∑ i : Fin n, ∑ j : Fin n, f x * X x i * Γ k i j x * Y x j =
          f x * ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, f x * X x i * Γ k i j x * Y x j
            = ∑ i : Fin n, f x * (∑ j : Fin n, X x i * Γ k i j x * Y x j) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = f x * ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j := by
              rw [Finset.mul_sum]
    have h1' :
        ∑ i : Fin n, X x i * (pderivScalar f i x * Y x k) =
          (∑ i : Fin n, X x i * pderivScalar f i x) * Y x k := by
      calc
        ∑ i : Fin n, X x i * (pderivScalar f i x * Y x k)
            = ∑ i : Fin n, X x i * pderivScalar f i x * Y x k := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = (∑ i : Fin n, X x i * pderivScalar f i x) * Y x k := h1
    have h2' :
        ∑ i : Fin n, X x i * (f x * pderivVector Y i x k) =
          f x * ∑ i : Fin n, X x i * pderivVector Y i x k := by
      calc
        ∑ i : Fin n, X x i * (f x * pderivVector Y i x k)
            = ∑ i : Fin n, X x i * f x * pderivVector Y i x k := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = f x * ∑ i : Fin n, X x i * pderivVector Y i x k := h2
    have h3' :
        ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * (f x * Y x j) =
          f x * ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * (f x * Y x j)
            = ∑ i : Fin n, ∑ j : Fin n, f x * X x i * Γ k i j x * Y x j := by
                apply Finset.sum_congr rfl
                intro i hi
                apply Finset.sum_congr rfl
                intro j hj
                ring
        _ = f x * ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j := h3
    rw [h1', h2', h3']

@[simp] theorem covariantDerivative_apply
    (Γ : SmoothChristoffelField n) (X Y : SmoothVectorField n) (x : Coord n) (k : Fin n) :
    covariantDerivative Γ X Y x k =
      (∑ i : Fin n, X x i * pderivVector Y i x k) +
        ∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j := rfl

/-- The coefficient field `g_{ij}(x)` evaluated at a point `x`. -/
def tensorAt (g : SmoothTensor2Field n) (x : Coord n) : Metric.Coordinate.Tensor2 n :=
  fun i j => g i j x

/-- Pointwise symmetry of a smooth coordinate metric field. -/
def IsSymmetricField (g : SmoothTensor2Field n) : Prop :=
  ∀ x : Coord n, Metric.Coordinate.IsSymmetric (tensorAt g x)

/-- Pointwise inverse-pair relation between smooth metric and inverse-metric fields. -/
def IsInversePairField (g gInv : SmoothTensor2Field n) : Prop :=
  ∀ x : Coord n, Metric.Coordinate.IsInversePair (tensorAt g x) (tensorAt gInv x)

/-- The coordinate derivative field `∂_dir g_{ij}` attached to a smooth metric coefficient field. -/
def metricDerivative (g : SmoothTensor2Field n) (dir i j : Fin n) (x : Coord n) : ℝ :=
  pderivScalar (g.component i j) dir x

@[simp] theorem pderivScalar_vectorComponent
    (X : SmoothVectorField n) (dir i : Fin n) (x : Coord n) :
    pderivScalar (X.component i) dir x = pderivVector X dir x i := rfl

@[simp] theorem pderivScalar_tensorComponent
    (g : SmoothTensor2Field n) (dir i j : Fin n) (x : Coord n) :
    pderivScalar (g.component i j) dir x = metricDerivative g dir i j x := rfl

theorem metricDerivative_smooth (g : SmoothTensor2Field n) (dir i j : Fin n) :
    ContDiff ℝ ⊤ (fun x => metricDerivative g dir i j x) :=
  (pderivScalar (g.component i j) dir).smooth'

theorem SmoothTensor2Field.differentiableAt_component (g : SmoothTensor2Field n)
    (i j : Fin n) (x : Coord n) :
    DifferentiableAt ℝ (fun y => g i j y) x :=
  (g.smooth' i j).contDiffAt.differentiableAt (by simp)

theorem metricDerivative_eq_fderiv (g : SmoothTensor2Field n) (dir i j : Fin n) (x : Coord n) :
    metricDerivative g dir i j x = fderiv ℝ (fun y => g i j y) x (coordBasis dir) := by
  rfl

theorem metricDerivative_symm
    {g : SmoothTensor2Field n} (hg : IsSymmetricField g) :
    ∀ dir i j x, metricDerivative g dir i j x = metricDerivative g dir j i x := by
  intro dir i j x
  have hfun : (fun y => g i j y) = fun y => g j i y := by
    funext y
    exact hg y i j
  simpa [metricDerivative_eq_fderiv] using congrArg
    (fun f : Coord n → ℝ => fderiv ℝ f x (coordBasis dir)) hfun

/-- The explicit smooth Levi-Civita Christoffel field attached to a metric field `g`. -/
noncomputable def leviCivitaChristoffelField
    (gInv g : SmoothTensor2Field n) : SmoothChristoffelField n :=
  { toFun := fun k i j x =>
      LeviCivita.Coordinate.leviCivitaChristoffel
        (tensorAt gInv x)
        (fun dir a b => metricDerivative g dir a b x) k i j
    smooth' := by
      intro k i j
      unfold LeviCivita.Coordinate.leviCivitaChristoffel
      refine contDiff_const.mul ?_
      refine ContDiff.sum ?_
      intro l hl
      have hgInvkl : ContDiff ℝ ⊤ (fun x => gInv k l x) := gInv.smooth' k l
      have hd1 : ContDiff ℝ ⊤ (fun x => metricDerivative g i j l x) :=
        metricDerivative_smooth g i j l
      have hd2 : ContDiff ℝ ⊤ (fun x => metricDerivative g j i l x) :=
        metricDerivative_smooth g j i l
      have hd3 : ContDiff ℝ ⊤ (fun x => metricDerivative g l i j x) :=
        metricDerivative_smooth g l i j
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        hgInvkl.mul ((hd1.add hd2).sub hd3) }

theorem pderiv_coordinateMetricPairing_apply
    (g : SmoothTensor2Field n) (Y Z : SmoothVectorField n)
    (dir : Fin n) (x : Coord n) :
    pderivScalar (coordinateMetricPairing g Y Z) dir x =
      ∑ j : Fin n, ∑ k : Fin n,
        (pderivVector Y dir x j * g j k x * Z x k
          + Y x j * metricDerivative g dir j k x * Z x k
          + Y x j * g j k x * pderivVector Z dir x k) := by
  classical
  let A : Fin n → Fin n → Coord n → ℝ :=
    fun j k y => Y y j * (g j k y * Z y k)
  have hdiff : ∀ j k : Fin n, DifferentiableAt ℝ (A j k) x := by
    intro j k
    have hsmooth : ContDiff ℝ ⊤ (A j k) := by
      simpa [A] using (Y.smooth' j).mul ((g.smooth' j k).mul (Z.smooth' k))
    exact hsmooth.contDiffAt.differentiableAt (by simp)
  have hsum_inner :
      ∀ j : Fin n, fderiv ℝ (∑ k : Fin n, A j k) x = ∑ k : Fin n, fderiv ℝ (A j k) x := by
    intro j
    exact fderiv_sum (x := x) (u := Finset.univ) (A := fun k => A j k) (by
      intro k hk
      exact hdiff j k)
  have hsum :
      fderiv ℝ (∑ j : Fin n, ∑ k : Fin n, A j k) x = ∑ j : Fin n, ∑ k : Fin n, fderiv ℝ (A j k) x := by
    calc
      fderiv ℝ (∑ j : Fin n, ∑ k : Fin n, A j k) x = ∑ j : Fin n, fderiv ℝ (∑ k : Fin n, A j k) x := by
        exact fderiv_sum (x := x) (u := Finset.univ) (A := fun j => ∑ k : Fin n, A j k) (by
          intro j hj
          exact DifferentiableAt.sum (u := Finset.univ) (A := fun k => A j k) (by
            intro k hk
            exact hdiff j k))
      _ = ∑ j : Fin n, ∑ k : Fin n, fderiv ℝ (A j k) x := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hsum_inner j
  have hsum' :
      fderiv ℝ (fun y => ∑ j : Fin n, ∑ k : Fin n, A j k y) x =
        ∑ j : Fin n, ∑ k : Fin n, fderiv ℝ (A j k) x := by
    have hfun : (fun y => ∑ j : Fin n, ∑ k : Fin n, A j k y) = ∑ j : Fin n, ∑ k : Fin n, A j k := by
      funext y
      simp [Finset.sum_apply]
    simpa [hfun] using hsum
  have hA :
      ∀ j k : Fin n,
        fderiv ℝ (A j k) x (coordBasis dir) =
          pderivVector Y dir x j * g j k x * Z x k
            + Y x j * metricDerivative g dir j k x * Z x k
            + Y x j * g j k x * pderivVector Z dir x k := by
    intro j k
    have hterm :
        pderivScalar (Y.component j * (g.component j k * Z.component k)) dir x =
          pderivVector Y dir x j * g j k x * Z x k
            + Y x j * metricDerivative g dir j k x * Z x k
            + Y x j * g j k x * pderivVector Z dir x k := by
      rw [pderivScalar_mul, pderivScalar_mul]
      simp [SmoothVectorField.component, SmoothTensor2Field.component, metricDerivative, mul_assoc]
      ring_nf
    simpa [A, pderivScalar] using hterm
  have hpair :
      (coordinateMetricPairing g Y Z : Coord n → ℝ) = fun y => ∑ j : Fin n, ∑ k : Fin n, A j k y := by
    funext y
    simp [coordinateMetricPairing, A, mul_assoc]
  have hsum_eval :
      (fderiv ℝ (fun y => ∑ j : Fin n, ∑ k : Fin n, A j k y) x) (coordBasis dir) =
        ∑ j : Fin n, ∑ k : Fin n, fderiv ℝ (A j k) x (coordBasis dir) := by
    simpa [Finset.sum_apply] using congrArg (fun L => L (coordBasis dir)) hsum'
  change (fderiv ℝ (coordinateMetricPairing g Y Z) x) (coordBasis dir) =
    ∑ j : Fin n, ∑ k : Fin n,
      (pderivVector Y dir x j * g j k x * Z x k
        + Y x j * metricDerivative g dir j k x * Z x k
        + Y x j * g j k x * pderivVector Z dir x k)
  rw [hpair, hsum_eval]
  simp_rw [hA]

theorem directionalDerivative_coordinateMetricPairing_apply
    (g : SmoothTensor2Field n) (X Y Z : SmoothVectorField n) (x : Coord n) :
    directionalDerivative X (coordinateMetricPairing g Y Z) x =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * pderivVector Y i x j * g j k x * Z x k) +
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * Y x j * metricDerivative g i j k x * Z x k) +
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * Y x j * g j k x * pderivVector Z i x k) := by
  rw [directionalDerivative_apply]
  have hcoord :
      ∀ i : Fin n,
        pderivScalar (coordinateMetricPairing g Y Z) i x =
          ∑ j : Fin n, ∑ k : Fin n,
            (pderivVector Y i x j * g j k x * Z x k
              + Y x j * metricDerivative g i j k x * Z x k
              + Y x j * g j k x * pderivVector Z i x k) := by
    intro i
    exact pderiv_coordinateMetricPairing_apply g Y Z i x
  simp_rw [hcoord]
  calc
    ∑ i : Fin n,
        X x i *
          (∑ j : Fin n, ∑ k : Fin n,
            (pderivVector Y i x j * g j k x * Z x k
              + Y x j * metricDerivative g i j k x * Z x k
              + Y x j * g j k x * pderivVector Z i x k))
        =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (X x i * pderivVector Y i x j * g j k x * Z x k
          + X x i * Y x j * metricDerivative g i j k x * Z x k
          + X x i * Y x j * g j k x * pderivVector Z i x k) := by
            simp_rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * pderivVector Y i x j * g j k x * Z x k) +
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * Y x j * metricDerivative g i j k x * Z x k) +
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * Y x j * g j k x * pderivVector Z i x k) := by
            simp_rw [Finset.sum_add_distrib]

theorem coordinateMetricPairing_covariantDerivative_left_apply
    (g : SmoothTensor2Field n) (Γ : SmoothChristoffelField n)
    (X Y Z : SmoothVectorField n) (x : Coord n) :
    coordinateMetricPairing g (covariantDerivative Γ X Y) Z x =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * pderivVector Y i x j * g j k x * Z x k) +
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k) := by
  have hderiv :
      ∑ j : Fin n, ∑ k : Fin n,
          (∑ i : Fin n, X x i * pderivVector Y i x j) * g j k x * Z x k =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          X x i * pderivVector Y i x j * g j k x * Z x k := by
    calc
      ∑ j : Fin n, ∑ k : Fin n,
          (∑ i : Fin n, X x i * pderivVector Y i x j) * g j k x * Z x k
          =
        ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n,
          X x i * pderivVector Y i x j * g j k x * Z x k := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            calc
              (∑ i : Fin n, X x i * pderivVector Y i x j) * g j k x * Z x k
                  = (∑ i : Fin n, X x i * pderivVector Y i x j) * (g j k x * Z x k) := by ring
              _ = ∑ i : Fin n, X x i * pderivVector Y i x j * (g j k x * Z x k) := by
                    rw [Finset.sum_mul]
              _ = ∑ i : Fin n, X x i * pderivVector Y i x j * g j k x * Z x k := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    ring
      _ = ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n,
            X x i * pderivVector Y i x j * g j k x * Z x k := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            X x i * pderivVector Y i x j * g j k x * Z x k := by
              rw [Finset.sum_comm]
  have hgamma :
      ∑ j : Fin n, ∑ k : Fin n,
          (∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * g j k x * Z x k
        =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k := by
    calc
      ∑ j : Fin n, ∑ k : Fin n,
          (∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * g j k x * Z x k
          =
        ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin n, ∑ m : Fin n,
          X x i * Γ j i m x * Y x m * g j k x * Z x k := by
            apply Finset.sum_congr rfl
            intro j hj
            apply Finset.sum_congr rfl
            intro k hk
            calc
              (∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * g j k x * Z x k
                  = (∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * (g j k x * Z x k) := by ring
              _ = ∑ i : Fin n, (∑ m : Fin n, X x i * Γ j i m x * Y x m) * (g j k x * Z x k) := by
                    rw [Finset.sum_mul]
              _ = ∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m * (g j k x * Z x k) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [Finset.sum_mul]
              _ = ∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m * g j k x * Z x k := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    apply Finset.sum_congr rfl
                    intro m hm
                    ring
      _ = ∑ j : Fin n, ∑ i : Fin n, ∑ k : Fin n, ∑ m : Fin n,
            X x i * Γ j i m x * Y x m * g j k x * Z x k := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ m : Fin n,
            X x i * Γ j i m x * Y x m * g j k x * Z x k := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ m : Fin n, ∑ k : Fin n,
            X x i * Γ j i m x * Y x m * g j k x * Z x k := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ m : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            X x i * Γ j i m x * Y x m * g j k x * Z x k := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ m : Fin n, ∑ k : Fin n, ∑ j : Fin n,
            X x i * Γ j i m x * Y x m * g j k x * Z x k := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.sum_comm]
      _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              calc
                ∑ m : Fin n, X x i * Γ m i j x * Y x j * g m k x * Z x k
                    = ∑ m : Fin n, X x i * Y x j * (g m k x * Γ m i j x) * Z x k := by
                        apply Finset.sum_congr rfl
                        intro m hm
                        ring
                _ = X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k := by
                      rw [← Finset.sum_mul]
                      congr 1
                      rw [← Finset.mul_sum]
  calc
    coordinateMetricPairing g (covariantDerivative Γ X Y) Z x
        =
      ∑ j : Fin n, ∑ k : Fin n,
        (((∑ i : Fin n, X x i * pderivVector Y i x j) +
            ∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * g j k x) * Z x k := by
              simp [coordinateMetricPairing, covariantDerivative_apply, mul_assoc]
    _ =
      ∑ j : Fin n, ∑ k : Fin n,
        (∑ i : Fin n, X x i * pderivVector Y i x j) * g j k x * Z x k +
        ∑ j : Fin n, ∑ k : Fin n,
          (∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * g j k x * Z x k := by
            simp_rw [add_mul]
            calc
              ∑ j : Fin n, ∑ k : Fin n,
                  ((∑ i : Fin n, X x i * pderivVector Y i x j) * g j k x * Z x k +
                    (∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * g j k x * Z x k)
                  =
                ∑ j : Fin n,
                  ((∑ k : Fin n, (∑ i : Fin n, X x i * pderivVector Y i x j) * g j k x * Z x k) +
                    ∑ k : Fin n,
                      (∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * g j k x * Z x k) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [Finset.sum_add_distrib]
              _ =
                ∑ j : Fin n, ∑ k : Fin n, (∑ i : Fin n, X x i * pderivVector Y i x j) * g j k x * Z x k +
                ∑ j : Fin n, ∑ k : Fin n,
                  (∑ i : Fin n, ∑ m : Fin n, X x i * Γ j i m x * Y x m) * g j k x * Z x k := by
                    rw [Finset.sum_add_distrib]
    _ =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * pderivVector Y i x j * g j k x * Z x k) +
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k) := by
            rw [hderiv, hgamma]

theorem covariantDerivative_torsionFree_of_lower_symm
    (Γ : SmoothChristoffelField n)
    (hsymm : ∀ x k i j, Γ k i j x = Γ k j i x) :
    LeviCivita.TorsionFree (coordinateConnectionContext n) (covariantDerivative Γ) := by
  intro X Y
  ext x k
  let Γx : LeviCivita.Coordinate.ChristoffelSymbol n := fun kk i j => Γ kk i j x
  have hΓx : ∀ kk i j, Γx kk i j = Γx kk j i := by
    intro kk i j
    exact hsymm x kk i j
  have hpoint :
      LeviCivita.TorsionFree (LeviCivita.Coordinate.flatConnectionContext n)
        (LeviCivita.Coordinate.christoffelToCovariantDerivative Γx) :=
    LeviCivita.Coordinate.christoffelToCovariantDerivative_torsionFree Γx hΓx
  have hgamma :
      (∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j) -
        (∑ i : Fin n, ∑ j : Fin n, Y x i * Γ k i j x * X x j) = 0 := by
    have hk := congrFun (hpoint (X x) (Y x)) k
    simpa [Γx, LeviCivita.Coordinate.christoffelToCovariantDerivative,
      LeviCivita.Coordinate.flatConnectionContext] using hk
  calc
    covariantDerivative Γ X Y x k - covariantDerivative Γ Y X x k
        = ((∑ i : Fin n, X x i * pderivVector Y i x k) -
            ∑ i : Fin n, Y x i * pderivVector X i x k) +
          ((∑ i : Fin n, ∑ j : Fin n, X x i * Γ k i j x * Y x j) -
            ∑ i : Fin n, ∑ j : Fin n, Y x i * Γ k i j x * X x j) := by
            simp [covariantDerivative_apply]
            ring
    _ = (∑ i : Fin n, X x i * pderivVector Y i x k) -
          ∑ i : Fin n, Y x i * pderivVector X i x k := by
            rw [hgamma]
            ring
    _ = lieBracket X Y x k := by
          simp [lieBracket_apply]

theorem leviCivitaChristoffelField_lower_symm
    (gInv g : SmoothTensor2Field n)
    (hg : IsSymmetricField g) :
    ∀ x k i j,
      leviCivitaChristoffelField gInv g k i j x =
        leviCivitaChristoffelField gInv g k j i x := by
  intro x k i j
  exact LeviCivita.Coordinate.leviCivitaChristoffel_lower_symm
    (tensorAt gInv x)
    (fun μ a b => metricDerivative g μ a b x)
    (fun μ a b => metricDerivative_symm hg μ a b x) k i j

theorem leviCivitaCovariantDerivative_torsionFree
    (gInv g : SmoothTensor2Field n)
    (hg : IsSymmetricField g) :
    LeviCivita.TorsionFree (coordinateConnectionContext n)
      (covariantDerivative (leviCivitaChristoffelField gInv g)) := by
  exact covariantDerivative_torsionFree_of_lower_symm
    (leviCivitaChristoffelField gInv g)
    (leviCivitaChristoffelField_lower_symm gInv g hg)

theorem metric_contract_leviCivitaChristoffelField
    (g gInv : SmoothTensor2Field n)
    (hg : IsSymmetricField g)
    (hgInv : IsSymmetricField gInv)
    (hpair : IsInversePairField g gInv) :
    ∀ x m i j,
      ∑ k : Fin n, g m k x * leviCivitaChristoffelField gInv g k i j x =
        (1 / 2 : ℝ) * (metricDerivative g i j m x + metricDerivative g j i m x - metricDerivative g m i j x) := by
  intro x m i j
  simpa [tensorAt, leviCivitaChristoffelField] using
    LeviCivita.Coordinate.metric_contract_leviCivitaChristoffel
      (tensorAt g x)
      (tensorAt gInv x)
      (fun dir a b => metricDerivative g dir a b x)
      (hg x)
      (hgInv x)
      (hpair x)
      m i j

theorem leviCivitaChristoffel_metricMiddle
    (g gInv : SmoothTensor2Field n)
    (hg : IsSymmetricField g)
    (hgInv : IsSymmetricField gInv)
    (hpair : IsInversePairField g gInv) :
    ∀ x i j k,
      (∑ m : Fin n, g m k x * leviCivitaChristoffelField gInv g m i j x) +
        (∑ m : Fin n, g j m x * leviCivitaChristoffelField gInv g m i k x) =
          metricDerivative g i j k x := by
  intro x i j k
  have h1 :
      ∑ m : Fin n, g m k x * leviCivitaChristoffelField gInv g m i j x =
        (1 / 2 : ℝ) *
          (metricDerivative g i j k x + metricDerivative g j i k x - metricDerivative g k i j x) := by
    calc
      ∑ m : Fin n, g m k x * leviCivitaChristoffelField gInv g m i j x
          = ∑ m : Fin n, g k m x * leviCivitaChristoffelField gInv g m i j x := by
              apply Finset.sum_congr rfl
              intro m hm
              have hmk : g m k x = g k m x := by
                simpa [tensorAt] using hg x m k
              rw [hmk]
      _ = (1 / 2 : ℝ) *
            (metricDerivative g i j k x + metricDerivative g j i k x - metricDerivative g k i j x) := by
            simpa using metric_contract_leviCivitaChristoffelField g gInv hg hgInv hpair x k i j
  have h2 :
      ∑ m : Fin n, g j m x * leviCivitaChristoffelField gInv g m i k x =
        (1 / 2 : ℝ) *
          (metricDerivative g i k j x + metricDerivative g k i j x - metricDerivative g j i k x) := by
    simpa using metric_contract_leviCivitaChristoffelField g gInv hg hgInv hpair x j i k
  have hs1 : metricDerivative g i j k x = metricDerivative g i k j x :=
    metricDerivative_symm hg i j k x
  linarith

theorem coordinateMetricPairing_symm
    {g : SmoothTensor2Field n} (hg : IsSymmetricField g) :
    ∀ X Y, coordinateMetricPairing g X Y = coordinateMetricPairing g Y X := by
  intro X Y
  ext x
  simpa [coordinateMetricPairing, tensorAt] using
    Metric.Coordinate.bilinForm_comm (hg x) (X x) (Y x)

theorem coordinateMetricPairing_sub_left
    (g : SmoothTensor2Field n) (X Y Z : SmoothVectorField n) :
    coordinateMetricPairing g (X - Y) Z =
      coordinateMetricPairing g X Z - coordinateMetricPairing g Y Z := by
  ext x
  simp [coordinateMetricPairing, sub_mul,
    Finset.sum_sub_distrib]

theorem leviCivitaCovariantDerivative_metricCompatible
    (g gInv : SmoothTensor2Field n)
    (hg : IsSymmetricField g)
    (hgInv : IsSymmetricField gInv)
    (hpair : IsInversePairField g gInv) :
    LeviCivita.MetricCompatible (coordinateMetricPairing g) (coordinateConnectionContext n)
      (covariantDerivative (leviCivitaChristoffelField gInv g)) := by
  intro X Y Z
  ext x
  let Γ := leviCivitaChristoffelField gInv g
  let d1 :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      X x i * pderivVector Y i x j * g j k x * Z x k
  let d2 :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      X x i * Y x j * metricDerivative g i j k x * Z x k
  let d3 :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      X x i * Y x j * g j k x * pderivVector Z i x k
  let c1 :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k
  let c2 :=
    ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      X x i * Y x j * (∑ m : Fin n, g j m x * Γ m i k x) * Z x k
  have hleft :
      coordinateMetricPairing g (covariantDerivative Γ X Y) Z x = d1 + c1 := by
    simpa [Γ, d1, c1] using
      coordinateMetricPairing_covariantDerivative_left_apply g Γ X Y Z x
  have hrightSwap :
      coordinateMetricPairing g (covariantDerivative Γ X Z) Y x =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          X x i * pderivVector Z i x j * g j k x * Y x k) +
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          X x i * Z x j * (∑ m : Fin n, g m k x * Γ m i j x) * Y x k) := by
    simpa [Γ] using
      coordinateMetricPairing_covariantDerivative_left_apply g Γ X Z Y x
  have hright :
      coordinateMetricPairing g Y (covariantDerivative Γ X Z) x = d3 + c2 := by
    calc
      coordinateMetricPairing g Y (covariantDerivative Γ X Z) x
          = coordinateMetricPairing g (covariantDerivative Γ X Z) Y x := by
              exact congrArg (fun s : SmoothScalarField n => s x)
                (coordinateMetricPairing_symm (g := g) hg Y (covariantDerivative Γ X Z))
      _ =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          X x i * pderivVector Z i x j * g j k x * Y x k) +
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          X x i * Z x j * (∑ m : Fin n, g m k x * Γ m i j x) * Y x k) := hrightSwap
      _ = d3 + c2 := by
          have hDswap :
              (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                X x i * pderivVector Z i x j * g j k x * Y x k) = d3 := by
            calc
              (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                X x i * pderivVector Z i x j * g j k x * Y x k)
                  = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
                      X x i * pderivVector Z i x k * g k j x * Y x j := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        rw [Finset.sum_comm]
              _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
                    X x i * pderivVector Z i x k * g j k x * Y x j := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      apply Finset.sum_congr rfl
                      intro k hk
                      apply Finset.sum_congr rfl
                      intro j hj
                      have hgjk : g k j x = g j k x := by
                        simpa [tensorAt] using hg x k j
                      rw [hgjk]
              _ = d3 := by
                      unfold d3
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro j hj
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
          have hGswap :
              (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                X x i * Z x j * (∑ m : Fin n, g m k x * Γ m i j x) * Y x k) = c2 := by
            calc
              (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                X x i * Z x j * (∑ m : Fin n, g m k x * Γ m i j x) * Y x k)
                  = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
                      X x i * Z x k * (∑ m : Fin n, g m j x * Γ m i k x) * Y x j := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        rw [Finset.sum_comm]
              _ = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
                    X x i * Z x k * (∑ m : Fin n, g j m x * Γ m i k x) * Y x j := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      apply Finset.sum_congr rfl
                      intro k hk
                      apply Finset.sum_congr rfl
                      intro j hj
                      have hsum :
                          ∑ m : Fin n, g m j x * Γ m i k x =
                            ∑ m : Fin n, g j m x * Γ m i k x := by
                              apply Finset.sum_congr rfl
                              intro m hm
                              have hgjm : g m j x = g j m x := by
                                simpa [tensorAt] using hg x m j
                              rw [hgjm]
                      rw [hsum]
              _ = c2 := by
                      unfold c2
                      apply Finset.sum_congr rfl
                      intro i hi
                      rw [Finset.sum_comm]
                      apply Finset.sum_congr rfl
                      intro j hj
                      apply Finset.sum_congr rfl
                      intro k hk
                      ring
          rw [hDswap, hGswap]
  have hmid :
      d2 = c1 + c2 := by
    calc
      d2 =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          X x i * Y x j *
            ((∑ m : Fin n, g m k x * Γ m i j x) +
              (∑ m : Fin n, g j m x * Γ m i k x)) * Z x k := by
              unfold d2
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              rw [leviCivitaChristoffel_metricMiddle g gInv hg hgInv hpair x i j k]
      _ =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k +
            X x i * Y x j * (∑ m : Fin n, g j m x * Γ m i k x) * Z x k) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              ring
      _ = c1 + c2 := by
            simpa [c1, c2] using
              (show
                ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                  (X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k +
                    X x i * Y x j * (∑ m : Fin n, g j m x * Γ m i k x) * Z x k) =
                  (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                    X x i * Y x j * (∑ m : Fin n, g m k x * Γ m i j x) * Z x k) +
                  (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                    X x i * Y x j * (∑ m : Fin n, g j m x * Γ m i k x) * Z x k) by
                  simp_rw [Finset.sum_add_distrib])
  calc
    directionalDerivative X (coordinateMetricPairing g Y Z) x = d1 + d2 + d3 := by
      simpa [d1, d2, d3] using
        directionalDerivative_coordinateMetricPairing_apply g X Y Z x
    _ = (d1 + c1) + (d3 + c2) := by
          rw [hmid]
          ring
    _ = coordinateMetricPairing g (covariantDerivative Γ X Y) Z x +
          coordinateMetricPairing g Y (covariantDerivative Γ X Z) x := by
          rw [hleft, hright]

theorem coordinateMetricExtensional_of_inversePair
    (g gInv : SmoothTensor2Field n)
    (hg : IsSymmetricField g)
    (hpair : IsInversePairField g gInv) :
    LeviCivita.MetricExtensional (coordinateMetricPairing g) := by
  intro X Y h
  ext x p
  have hxy : X x = Y x := by
    have hpoint :
        ∀ W : Coord n,
          LeviCivita.Coordinate.coordinateMetricPairing (tensorAt g x) (X x) W =
            LeviCivita.Coordinate.coordinateMetricPairing (tensorAt g x) (Y x) W := by
      intro W
      have hx := congrArg (fun s : SmoothScalarField n => s x) (h (constVectorField W))
      simpa [coordinateMetricPairing, LeviCivita.Coordinate.coordinateMetricPairing, tensorAt] using hx
    exact
      LeviCivita.Coordinate.coordinateMetricExtensional_of_inversePair
        (tensorAt g x) (tensorAt gInv x) (hg x) (hpair x) (X x) (Y x) hpoint
  exact congrFun hxy p

theorem two_smul_cancel
    {a b : SmoothScalarField n} (h : (2 : SmoothScalarField n) • a = (2 : SmoothScalarField n) • b) :
    a = b := by
  ext x
  have hx := congrArg (fun s : SmoothScalarField n => s x) h
  change (2 : ℝ) * a x = (2 : ℝ) * b x at hx
  linarith

theorem isLeviCivita_koszulFormula_smoothScalar
    {g : LeviCivita.MetricPairing (SmoothVectorField n) (SmoothScalarField n)}
    (hgsymm : ∀ X Y, g X Y = g Y X)
    (hgsub : ∀ X Y Z, g (X - Y) Z = g X Z - g Y Z)
    {nabla : LeviCivita.CovariantDerivative (SmoothVectorField n) (SmoothScalarField n)
      (coordinateConnectionContext n)}
    (hlc : LeviCivita.IsLeviCivita g (coordinateConnectionContext n) nabla) :
    LeviCivita.KoszulFormula g (coordinateConnectionContext n) nabla := by
  intro X Y Z
  ext x
  obtain ⟨hmc, htf⟩ := hlc
  unfold LeviCivita.koszulRHS
  have hb1 : (coordinateConnectionContext n).bracket X Y = nabla X Y - nabla Y X := (htf X Y).symm
  have hb2 : (coordinateConnectionContext n).bracket Y Z = nabla Y Z - nabla Z Y := (htf Y Z).symm
  have hb3 : (coordinateConnectionContext n).bracket Z X = nabla Z X - nabla X Z := (htf Z X).symm
  rw [hb1, hb2, hb3,
      hgsub (nabla X Y) (nabla Y X) Z,
      hgsub (nabla Y Z) (nabla Z Y) X,
      hgsub (nabla Z X) (nabla X Z) Y]
  have hmc1 :
      (coordinateConnectionContext n).deriv X (g Y Z) x =
        g (nabla X Y) Z x + g Y (nabla X Z) x := by
    simpa using congrArg (fun s : SmoothScalarField n => s x) (hmc X Y Z)
  have hmc2 :
      (coordinateConnectionContext n).deriv Y (g Z X) x =
        g (nabla Y Z) X x + g Z (nabla Y X) x := by
    simpa using congrArg (fun s : SmoothScalarField n => s x) (hmc Y Z X)
  have hmc3 :
      (coordinateConnectionContext n).deriv Z (g X Y) x =
        g (nabla Z X) Y x + g X (nabla Z Y) x := by
    simpa using congrArg (fun s : SmoothScalarField n => s x) (hmc Z X Y)
  have hs1 : g Y (nabla X Z) x = g (nabla X Z) Y x := by
    simpa using congrArg (fun s : SmoothScalarField n => s x) (hgsymm Y (nabla X Z))
  have hs2 : g Z (nabla Y X) x = g (nabla Y X) Z x := by
    simpa using congrArg (fun s : SmoothScalarField n => s x) (hgsymm Z (nabla Y X))
  have hs3 : g X (nabla Z Y) x = g (nabla Z Y) X x := by
    simpa using congrArg (fun s : SmoothScalarField n => s x) (hgsymm X (nabla Z Y))
  have htwo :
      ((2 : SmoothScalarField n) • g (nabla X Y) Z) x =
        g (nabla X Y) Z x + g (nabla X Y) Z x := by
    change (2 : ℝ) * g (nabla X Y) Z x = _
    ring
  rw [htwo]
  simp [smoothScalar_add_apply, smoothScalar_sub_apply] at hmc1 hmc2 hmc3 hs1 hs2 hs3 htwo ⊢
  linarith [hmc1, hmc2, hmc3, hs1, hs2, hs3]

theorem leviCivitaCovariantDerivative_isLeviCivita
    (g gInv : SmoothTensor2Field n)
    (hg : IsSymmetricField g)
    (hgInv : IsSymmetricField gInv)
    (hpair : IsInversePairField g gInv) :
    LeviCivita.IsLeviCivita
      (coordinateMetricPairing g)
      (coordinateConnectionContext n)
      (covariantDerivative (leviCivitaChristoffelField gInv g)) := by
  exact LeviCivita.mk_isLeviCivita
    (leviCivitaCovariantDerivative_metricCompatible g gInv hg hgInv hpair)
    (leviCivitaCovariantDerivative_torsionFree gInv g hg)

theorem existsUnique_coordinateFieldLeviCivita
    (g gInv : SmoothTensor2Field n)
    (hg : IsSymmetricField g)
    (hgInv : IsSymmetricField gInv)
    (hpair : IsInversePairField g gInv) :
    ∃! nabla :
      LeviCivita.CovariantDerivative (SmoothVectorField n) (SmoothScalarField n)
        (coordinateConnectionContext n),
      LeviCivita.IsLeviCivita (coordinateMetricPairing g) (coordinateConnectionContext n) nabla := by
  apply LeviCivita.existsUnique_isLeviCivita
  · exact coordinateMetricExtensional_of_inversePair g gInv hg hpair
  · exact fun _ _ h => two_smul_cancel h
  · intro nabla hnabla
    exact isLeviCivita_koszulFormula_smoothScalar
      (coordinateMetricPairing_symm (g := g) hg)
      (coordinateMetricPairing_sub_left g)
      hnabla
  · exact ⟨covariantDerivative (leviCivitaChristoffelField gInv g),
      leviCivitaCovariantDerivative_isLeviCivita g gInv hg hgInv hpair⟩

theorem leviCivita_eq_coordinateField
    (g gInv : SmoothTensor2Field n)
    (hg : IsSymmetricField g)
    (hgInv : IsSymmetricField gInv)
    (hpair : IsInversePairField g gInv) :
    LeviCivita.leviCivita
      (coordinateMetricExtensional_of_inversePair g gInv hg hpair)
      (fun _ _ h => two_smul_cancel h)
      (fun {_nabla} hnabla =>
        isLeviCivita_koszulFormula_smoothScalar
          (coordinateMetricPairing_symm (g := g) hg)
          (coordinateMetricPairing_sub_left g)
          hnabla)
      ⟨covariantDerivative (leviCivitaChristoffelField gInv g),
        leviCivitaCovariantDerivative_isLeviCivita g gInv hg hgInv hpair⟩
      =
    covariantDerivative (leviCivitaChristoffelField gInv g) := by
  exact LeviCivita.leviCivita_unique
    (coordinateMetricExtensional_of_inversePair g gInv hg hpair)
    (fun _ _ h => two_smul_cancel h)
    (fun {_nabla} hnabla =>
      isLeviCivita_koszulFormula_smoothScalar
        (coordinateMetricPairing_symm (g := g) hg)
        (coordinateMetricPairing_sub_left g)
        hnabla)
    ⟨covariantDerivative (leviCivitaChristoffelField gInv g),
      leviCivitaCovariantDerivative_isLeviCivita g gInv hg hgInv hpair⟩
    (leviCivitaCovariantDerivative_isLeviCivita g gInv hg hgInv hpair)

end

end LeviCivita.CoordinateField
