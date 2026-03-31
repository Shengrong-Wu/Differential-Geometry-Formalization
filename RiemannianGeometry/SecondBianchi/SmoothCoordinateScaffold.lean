import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.StdBasis
import SecondBianchi.ConcreteCoordinateBianchi

open BigOperators Finset
open scoped Topology

namespace SecondBianchi.Coordinate

noncomputable section

variable {n : ℕ}

/-- The flat coordinate model used for the smooth instantiation layer. -/
abbrev CoordSpace (n : ℕ) := Fin n → ℝ

/-- The `dir`-th standard coordinate vector in `Fin n → ℝ`. -/
def coordBasis (dir : Fin n) : CoordSpace n :=
  Pi.basisFun ℝ (Fin n) dir

/--
A smooth matrix-valued 1-form coefficient field on the flat coordinate space.

This carrier keeps the full smooth coefficient function, so directional derivatives
at a point are definable from the data itself instead of being irretrievably lost
after evaluation.
-/
structure SmoothForm1 (n : ℕ) where
  toFun : Fin n → Fin n → Fin n → CoordSpace n → ℝ
  smooth' : ∀ i j k, ContDiff ℝ ⊤ (toFun i j k)

/-- A smooth matrix-valued 2-form coefficient field on the flat coordinate space. -/
structure SmoothForm2 (n : ℕ) where
  toFun : Fin n → Fin n → Fin n → Fin n → CoordSpace n → ℝ
  smooth' : ∀ i j k l, ContDiff ℝ ⊤ (toFun i j k l)

/-- A smooth matrix-valued 3-form coefficient field on the flat coordinate space. -/
structure SmoothForm3 (n : ℕ) where
  toFun : Fin n → Fin n → Fin n → Fin n → Fin n → CoordSpace n → ℝ
  smooth' : ∀ i j e k l, ContDiff ℝ ⊤ (toFun i j e k l)

instance : CoeFun (SmoothForm1 n) (fun _ => Fin n → Fin n → Fin n → CoordSpace n → ℝ) where
  coe A := A.toFun

instance : CoeFun (SmoothForm2 n) (fun _ => Fin n → Fin n → Fin n → Fin n → CoordSpace n → ℝ) where
  coe R := R.toFun

instance : CoeFun (SmoothForm3 n)
    (fun _ => Fin n → Fin n → Fin n → Fin n → Fin n → CoordSpace n → ℝ) where
  coe T := T.toFun

instance : Zero (SmoothForm1 n) where
  zero :=
    { toFun := fun _ _ _ _ => 0
      smooth' := by
        intro _ _ _
        simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : CoordSpace n => (0 : ℝ)) }

instance : Add (SmoothForm1 n) where
  add A B :=
    { toFun := fun i j k x => A i j k x + B i j k x
      smooth' := by
        intro i j k
        simpa using (A.smooth' i j k).add (B.smooth' i j k) }

instance : Neg (SmoothForm1 n) where
  neg A :=
    { toFun := fun i j k x => -A i j k x
      smooth' := by
        intro i j k
        simpa using (A.smooth' i j k).neg }

instance : Sub (SmoothForm1 n) where
  sub A B := A + (-B)

instance : SMul ℕ (SmoothForm1 n) where
  smul m A :=
    { toFun := fun i j k x => m • A i j k x
      smooth' := by
        intro i j k
        simpa using (A.smooth' i j k).const_smul m }

instance : SMul ℤ (SmoothForm1 n) where
  smul m A :=
    { toFun := fun i j k x => m • A i j k x
      smooth' := by
        intro i j k
        simpa using (A.smooth' i j k).const_smul m }

instance : Zero (SmoothForm2 n) where
  zero :=
    { toFun := fun _ _ _ _ _ => 0
      smooth' := by
        intro _ _ _ _
        simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : CoordSpace n => (0 : ℝ)) }

instance : Add (SmoothForm2 n) where
  add R S :=
    { toFun := fun i j k l x => R i j k l x + S i j k l x
      smooth' := by
        intro i j k l
        simpa using (R.smooth' i j k l).add (S.smooth' i j k l) }

instance : Neg (SmoothForm2 n) where
  neg R :=
    { toFun := fun i j k l x => -R i j k l x
      smooth' := by
        intro i j k l
        simpa using (R.smooth' i j k l).neg }

instance : Sub (SmoothForm2 n) where
  sub R S := R + (-S)

instance : SMul ℕ (SmoothForm2 n) where
  smul m R :=
    { toFun := fun i j k l x => m • R i j k l x
      smooth' := by
        intro i j k l
        simpa using (R.smooth' i j k l).const_smul m }

instance : SMul ℤ (SmoothForm2 n) where
  smul m R :=
    { toFun := fun i j k l x => m • R i j k l x
      smooth' := by
        intro i j k l
        simpa using (R.smooth' i j k l).const_smul m }

instance : Zero (SmoothForm3 n) where
  zero :=
    { toFun := fun _ _ _ _ _ _ => 0
      smooth' := by
        intro _ _ _ _ _
        simpa using (contDiff_const : ContDiff ℝ ⊤ fun _ : CoordSpace n => (0 : ℝ)) }

instance : Add (SmoothForm3 n) where
  add T U :=
    { toFun := fun i j e k l x => T i j e k l x + U i j e k l x
      smooth' := by
        intro i j e k l
        simpa using (T.smooth' i j e k l).add (U.smooth' i j e k l) }

instance : Neg (SmoothForm3 n) where
  neg T :=
    { toFun := fun i j e k l x => -T i j e k l x
      smooth' := by
        intro i j e k l
        simpa using (T.smooth' i j e k l).neg }

instance : Sub (SmoothForm3 n) where
  sub T U := T + (-U)

instance : SMul ℕ (SmoothForm3 n) where
  smul m T :=
    { toFun := fun i j e k l x => m • T i j e k l x
      smooth' := by
        intro i j e k l
        simpa using (T.smooth' i j e k l).const_smul m }

instance : SMul ℤ (SmoothForm3 n) where
  smul m T :=
    { toFun := fun i j e k l x => m • T i j e k l x
      smooth' := by
        intro i j e k l
        simpa using (T.smooth' i j e k l).const_smul m }

private theorem SmoothForm1.toFun_injective :
    Function.Injective (fun A : SmoothForm1 n => A.toFun) := by
  intro A B h
  cases A
  cases B
  cases h
  rfl

private theorem SmoothForm2.toFun_injective :
    Function.Injective (fun R : SmoothForm2 n => R.toFun) := by
  intro R S h
  cases R
  cases S
  cases h
  rfl

private theorem SmoothForm3.toFun_injective :
    Function.Injective (fun T : SmoothForm3 n => T.toFun) := by
  intro T U h
  cases T
  cases U
  cases h
  rfl

instance : AddCommGroup (SmoothForm1 n) :=
  Function.Injective.addCommGroup (fun A : SmoothForm1 n => A.toFun)
    SmoothForm1.toFun_injective rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : AddCommGroup (SmoothForm2 n) :=
  Function.Injective.addCommGroup (fun R : SmoothForm2 n => R.toFun)
    SmoothForm2.toFun_injective rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : AddCommGroup (SmoothForm3 n) :=
  Function.Injective.addCommGroup (fun T : SmoothForm3 n => T.toFun)
    SmoothForm3.toFun_injective rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Evaluate a smooth coefficient field at a point, forgetting derivative data. -/
def SmoothForm1.eval (A : SmoothForm1 n) (x : CoordSpace n) : Form1 n :=
  fun i j k => A i j k x

/-- Evaluate a smooth 2-form coefficient field at a point. -/
def SmoothForm2.eval (R : SmoothForm2 n) (x : CoordSpace n) : Form2 n :=
  fun i j k l => R i j k l x

/-- Evaluate a smooth 3-form coefficient field at a point. -/
def SmoothForm3.eval (T : SmoothForm3 n) (x : CoordSpace n) : Form3 n :=
  fun i j e k l => T i j e k l x

@[ext] theorem SmoothForm1.ext {A B : SmoothForm1 n}
    (h : ∀ i j k x, A i j k x = B i j k x) : A = B :=
  SmoothForm1.toFun_injective <| by
    funext i j k x
    exact h i j k x

@[ext] theorem SmoothForm2.ext {R S : SmoothForm2 n}
    (h : ∀ i j k l x, R i j k l x = S i j k l x) : R = S :=
  SmoothForm2.toFun_injective <| by
    funext i j k l x
    exact h i j k l x

@[ext] theorem SmoothForm3.ext {T U : SmoothForm3 n}
    (h : ∀ i j e k l x, T i j e k l x = U i j e k l x) : T = U :=
  SmoothForm3.toFun_injective <| by
    funext i j e k l x
    exact h i j e k l x

@[simp] theorem SmoothForm1.eval_add (A B : SmoothForm1 n) (x : CoordSpace n) :
    (A + B).eval x = A.eval x + B.eval x := rfl

@[simp] theorem SmoothForm1.eval_neg (A : SmoothForm1 n) (x : CoordSpace n) :
    (-A).eval x = -A.eval x := rfl

@[simp] theorem SmoothForm1.eval_sub (A B : SmoothForm1 n) (x : CoordSpace n) :
    (A - B).eval x = A.eval x - B.eval x := rfl

@[simp] theorem SmoothForm2.eval_add (R S : SmoothForm2 n) (x : CoordSpace n) :
    (R + S).eval x = R.eval x + S.eval x := rfl

@[simp] theorem SmoothForm2.eval_neg (R : SmoothForm2 n) (x : CoordSpace n) :
    (-R).eval x = -R.eval x := rfl

@[simp] theorem SmoothForm2.eval_sub (R S : SmoothForm2 n) (x : CoordSpace n) :
    (R - S).eval x = R.eval x - S.eval x := rfl

@[simp] theorem SmoothForm3.eval_add (T U : SmoothForm3 n) (x : CoordSpace n) :
    (T + U).eval x = T.eval x + U.eval x := rfl

@[simp] theorem SmoothForm3.eval_neg (T : SmoothForm3 n) (x : CoordSpace n) :
    (-T).eval x = -T.eval x := rfl

@[simp] theorem SmoothForm3.eval_sub (T U : SmoothForm3 n) (x : CoordSpace n) :
    (T - U).eval x = T.eval x - U.eval x := rfl

private theorem SmoothForm1.differentiableAt
    (A : SmoothForm1 n) (i j k : Fin n) (x : CoordSpace n) :
    DifferentiableAt ℝ (A i j k) x :=
  (A.smooth' i j k).contDiffAt.differentiableAt (by simp)

private theorem SmoothForm2.differentiableAt
    (R : SmoothForm2 n) (i j k l : Fin n) (x : CoordSpace n) :
    DifferentiableAt ℝ (R i j k l) x :=
  (R.smooth' i j k l).contDiffAt.differentiableAt (by simp)

/-- Directional derivative of a smooth 1-form coefficient in a coordinate direction. -/
def smoothPderiv1
    (A : SmoothForm1 n) (dir i j k : Fin n) (x : CoordSpace n) : ℝ :=
  fderiv ℝ (A i j k) x (coordBasis dir)

/-- Directional derivative of a smooth 2-form coefficient in a coordinate direction. -/
def smoothPderiv2
    (R : SmoothForm2 n) (dir i j k l : Fin n) (x : CoordSpace n) : ℝ :=
  fderiv ℝ (R i j k l) x (coordBasis dir)

private theorem smoothPderiv1_contDiff
    (A : SmoothForm1 n) (dir i j k : Fin n) :
    ContDiff ℝ ⊤ (fun x => smoothPderiv1 A dir i j k x) := by
  unfold smoothPderiv1
  simpa using
    ((A.smooth' i j k).fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiff_const : ContDiff ℝ ⊤ fun _ : CoordSpace n => coordBasis dir)

private theorem smoothPderiv2_contDiff
    (R : SmoothForm2 n) (dir i j k l : Fin n) :
    ContDiff ℝ ⊤ (fun x => smoothPderiv2 R dir i j k l x) := by
  unfold smoothPderiv2
  simpa using
    ((R.smooth' i j k l).fderiv_right (m := ⊤) (by simp)).clm_apply
      (contDiff_const : ContDiff ℝ ⊤ fun _ : CoordSpace n => coordBasis dir)

/-- Smooth wedge product of two connection-coefficient fields. -/
def smoothWedge11 (A B : SmoothForm1 n) : SmoothForm2 n :=
  { toFun := fun i j k l x => ∑ m : Fin n, (A i m k x * B m j l x - A i m l x * B m j k x)
    smooth' := by
      intro i j k l
      refine ContDiff.sum ?_
      intro m hm
      simpa using ((A.smooth' i m k).mul (B.smooth' m j l)).sub
        ((A.smooth' i m l).mul (B.smooth' m j k)) }

/-- Smooth wedge product `Ω¹ ⊗ Ω² → Ω³`. -/
def smoothWedge12 (A : SmoothForm1 n) (R : SmoothForm2 n) : SmoothForm3 n :=
  { toFun := fun i j e k l x =>
      ∑ m : Fin n, (A i m e x * R m j k l x + A i m k x * R m j l e x + A i m l x * R m j e k x)
    smooth' := by
      intro i j e k l
      refine ContDiff.sum ?_
      intro m hm
      simpa [add_assoc] using
        ((A.smooth' i m e).mul (R.smooth' m j k l)).add
          (((A.smooth' i m k).mul (R.smooth' m j l e)).add
            ((A.smooth' i m l).mul (R.smooth' m j e k))) }

/-- Smooth wedge product `Ω² ⊗ Ω¹ → Ω³`. -/
def smoothWedge21 (R : SmoothForm2 n) (A : SmoothForm1 n) : SmoothForm3 n :=
  { toFun := fun i j e k l x =>
      ∑ m : Fin n, (R i m e k x * A m j l x + R i m k l x * A m j e x + R i m l e x * A m j k x)
    smooth' := by
      intro i j e k l
      refine ContDiff.sum ?_
      intro m hm
      simpa [add_assoc] using
        ((R.smooth' i m e k).mul (A.smooth' m j l)).add
          (((R.smooth' i m k l).mul (A.smooth' m j e)).add
            ((R.smooth' i m l e).mul (A.smooth' m j k))) }

/-- Smooth coordinate exterior derivative of a connection-coefficient field. -/
def smoothD1 (A : SmoothForm1 n) : SmoothForm2 n :=
  { toFun := fun i j k l x => smoothPderiv1 A k i j l x - smoothPderiv1 A l i j k x
    smooth' := by
      intro i j k l
      exact (smoothPderiv1_contDiff A k i j l).sub (smoothPderiv1_contDiff A l i j k) }

/-- Smooth coordinate exterior derivative of a curvature-coefficient field. -/
def smoothD2 (R : SmoothForm2 n) : SmoothForm3 n :=
  { toFun := fun i j e k l x =>
      smoothPderiv2 R e i j k l x +
        smoothPderiv2 R k i j l e x +
        smoothPderiv2 R l i j e k x
    smooth' := by
      intro i j e k l
      exact ((smoothPderiv2_contDiff R e i j k l).add
        (smoothPderiv2_contDiff R k i j l e)).add
        (smoothPderiv2_contDiff R l i j e k) }

/-- The concrete coordinate exterior derivative of a smooth 1-form, evaluated at `x`. -/
def evalConcreteD1 (A : SmoothForm1 n) (x : CoordSpace n) : Form2 n :=
  fun i j k l => smoothPderiv1 A k i j l x - smoothPderiv1 A l i j k x

/-- The concrete coordinate exterior derivative of a smooth 2-form, evaluated at `x`. -/
def evalConcreteD2 (R : SmoothForm2 n) (x : CoordSpace n) : Form3 n :=
  fun i j e k l =>
    smoothPderiv2 R e i j k l x +
      smoothPderiv2 R k i j l e x +
      smoothPderiv2 R l i j e k x

@[simp] theorem smoothWedge11_eval (A B : SmoothForm1 n) (x : CoordSpace n) :
    (smoothWedge11 A B).eval x = wedge11 n (A.eval x) (B.eval x) := rfl

@[simp] theorem smoothWedge12_eval (A : SmoothForm1 n) (R : SmoothForm2 n) (x : CoordSpace n) :
    (smoothWedge12 A R).eval x = wedge12 n (A.eval x) (R.eval x) := rfl

@[simp] theorem smoothWedge21_eval (R : SmoothForm2 n) (A : SmoothForm1 n) (x : CoordSpace n) :
    (smoothWedge21 R A).eval x = wedge21 n (R.eval x) (A.eval x) := rfl

@[simp] theorem smoothD1_eval (A : SmoothForm1 n) (x : CoordSpace n) :
    (smoothD1 A).eval x = evalConcreteD1 A x := rfl

@[simp] theorem smoothD2_eval (R : SmoothForm2 n) (x : CoordSpace n) :
    (smoothD2 R).eval x = evalConcreteD2 R x := rfl

theorem smoothPderiv2_add
    (R S : SmoothForm2 n) (dir i j k l : Fin n) (x : CoordSpace n) :
    smoothPderiv2 (R + S) dir i j k l x =
      smoothPderiv2 R dir i j k l x + smoothPderiv2 S dir i j k l x := by
  unfold smoothPderiv2
  change (fderiv ℝ (R.toFun i j k l + S.toFun i j k l) x) (coordBasis dir) =
    (fderiv ℝ (R.toFun i j k l) x) (coordBasis dir) +
      (fderiv ℝ (S.toFun i j k l) x) (coordBasis dir)
  rw [fderiv_add (R.differentiableAt i j k l x) (S.differentiableAt i j k l x)]
  rfl

theorem evalConcreteD2_add
    (R S : SmoothForm2 n) (x : CoordSpace n) :
    evalConcreteD2 (R + S) x = evalConcreteD2 R x + evalConcreteD2 S x := by
  ext i j e k l
  unfold evalConcreteD2
  rw [smoothPderiv2_add, smoothPderiv2_add, smoothPderiv2_add]
  simp [Pi.add_apply, add_assoc, add_left_comm]

/--
Coordinate mixed second partials commute for smooth coefficients.

This is the Schwarz-theorem ingredient needed for the `d2_d1 = 0` part of the
smooth instantiation.
-/
theorem smoothSecondPartial_comm
    (A : SmoothForm1 n) (i j k dir₁ dir₂ : Fin n) (x : CoordSpace n) :
    iteratedFDeriv ℝ 2 (A i j k) x ![coordBasis dir₁, coordBasis dir₂] =
      iteratedFDeriv ℝ 2 (A i j k) x ![coordBasis dir₂, coordBasis dir₁] := by
  have hsym : IsSymmSndFDerivAt ℝ (A i j k) x :=
    (A.smooth' i j k).contDiffAt.isSymmSndFDerivAt (by simp)
  exact IsSymmSndFDerivAt.iteratedFDeriv_cons
    (hf := hsym) (x := x) (v := coordBasis dir₁) (w := coordBasis dir₂)

end

end SecondBianchi.Coordinate
