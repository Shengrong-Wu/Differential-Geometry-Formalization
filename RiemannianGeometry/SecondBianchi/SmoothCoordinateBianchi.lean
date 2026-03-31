import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import SecondBianchi.SmoothCoordinateScaffold

open BigOperators Finset

namespace SecondBianchi.Coordinate

noncomputable section

variable {n : ℕ}

private lemma mfs (a : ℝ) (f : Fin n → ℝ) :
    a * ∑ i : Fin n, f i = ∑ i : Fin n, a * f i := by
  rw [Finset.mul_sum]

private lemma fsm (f : Fin n → ℝ) (c : ℝ) :
    (∑ m : Fin n, f m) * c = ∑ m : Fin n, f m * c := by
  rw [Finset.sum_mul]

theorem smoothD2_add
    (R S : SmoothForm2 n) :
    smoothD2 (R + S) = smoothD2 R + smoothD2 S := by
  ext i j e k l x
  change evalConcreteD2 (R + S) x i j e k l =
    (evalConcreteD2 R x + evalConcreteD2 S x) i j e k l
  rw [evalConcreteD2_add]

private theorem smoothWedge12_add_right
    (A : SmoothForm1 n) (R S : SmoothForm2 n) :
    smoothWedge12 A (R + S) = smoothWedge12 A R + smoothWedge12 A S := by
  ext i j e k l x
  change wedge12 n (A.eval x) ((R + S).eval x) i j e k l =
    (wedge12 n (A.eval x) (R.eval x) + wedge12 n (A.eval x) (S.eval x)) i j e k l
  rw [SmoothForm2.eval_add]
  simp [wedge12, mul_add, Finset.sum_add_distrib, add_assoc]
  ring

private theorem smoothWedge21_add_left
    (R S : SmoothForm2 n) (A : SmoothForm1 n) :
    smoothWedge21 (R + S) A = smoothWedge21 R A + smoothWedge21 S A := by
  ext i j e k l x
  change wedge21 n ((R + S).eval x) (A.eval x) i j e k l =
    (wedge21 n (R.eval x) (A.eval x) + wedge21 n (S.eval x) (A.eval x)) i j e k l
  rw [SmoothForm2.eval_add]
  simp [wedge21, add_mul, Finset.sum_add_distrib, add_assoc]
  ring

private theorem smoothWedge_assoc
    (A B C : SmoothForm1 n) :
    smoothWedge12 A (smoothWedge11 B C) = smoothWedge21 (smoothWedge11 A B) C := by
  ext i j e k l x
  simp only [smoothWedge12, smoothWedge11, smoothWedge21]
  simp_rw [mfs _ _]
  simp_rw [← sum_add_distrib]
  simp_rw [fsm _ _]
  simp_rw [← sum_add_distrib]
  rw [sum_comm (s := univ) (t := univ)]
  congr 1
  ext p
  congr 1
  ext m
  ring

private theorem smoothSecondPartial_eq
    (A : SmoothForm1 n) (i j k dir₁ dir₂ : Fin n) (x : CoordSpace n) :
    fderiv ℝ (fun y => smoothPderiv1 A dir₁ i j k y) x (coordBasis dir₂) =
      iteratedFDeriv ℝ 2 (A i j k) x ![coordBasis dir₂, coordBasis dir₁] := by
  unfold smoothPderiv1
  have hcont : ContDiff ℝ 1 (fderiv ℝ (A i j k)) :=
    (A.smooth' i j k).fderiv_right (m := 1) (by simp)
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ (A i j k)) x :=
    hcont.contDiffAt.differentiableAt one_ne_zero
  rw [fderiv_clm_apply hfdiff (differentiableAt_const (coordBasis dir₁))]
  simp [iteratedFDeriv_two_apply]

private theorem smoothPderiv1_differentiableAt
    (A : SmoothForm1 n) (dir i j k : Fin n) (x : CoordSpace n) :
    DifferentiableAt ℝ (fun y => smoothPderiv1 A dir i j k y) x := by
  have hcont : ContDiff ℝ ⊤ (fun y => smoothPderiv1 A dir i j k y) := by
    unfold smoothPderiv1
    simpa using
      ((A.smooth' i j k).fderiv_right (m := ⊤) (by simp)).clm_apply
        (contDiff_const : ContDiff ℝ ⊤ fun _ : CoordSpace n => coordBasis dir)
  exact hcont.contDiffAt.differentiableAt (by simp)

private theorem smoothForm1_differentiableAt
    (A : SmoothForm1 n) (i j k : Fin n) (x : CoordSpace n) :
    DifferentiableAt ℝ (A i j k) x :=
  (A.smooth' i j k).contDiffAt.differentiableAt (by simp)

private theorem smoothPderiv2_wedge11
    (A B : SmoothForm1 n) (dir i j k l : Fin n) (x : CoordSpace n) :
    smoothPderiv2 (smoothWedge11 A B) dir i j k l x =
      ∑ m : Fin n,
        (smoothPderiv1 A dir i m k x * B m j l x
          + A i m k x * smoothPderiv1 B dir m j l x
          - smoothPderiv1 A dir i m l x * B m j k x
          - A i m l x * smoothPderiv1 B dir m j k x) := by
  unfold smoothPderiv2 smoothWedge11
  change
    (fderiv ℝ
        (fun y => ∑ m : Fin n, (A i m k y * B m j l y - A i m l y * B m j k y)) x)
      (coordBasis dir) =
      ∑ m : Fin n,
        (smoothPderiv1 A dir i m k x * B m j l x
          + A i m k x * smoothPderiv1 B dir m j l x
          - smoothPderiv1 A dir i m l x * B m j k x
          - A i m l x * smoothPderiv1 B dir m j k x)
  rw [fderiv_fun_sum]
  · have hsum :
        (∑ m : Fin n, fderiv ℝ (fun y => A i m k y * B m j l y - A i m l y * B m j k y) x)
            (coordBasis dir) =
          ∑ m : Fin n,
            (fderiv ℝ (fun y => A i m k y * B m j l y - A i m l y * B m j k y) x)
              (coordBasis dir) := by
      simp [ContinuousLinearMap.sum_apply]
    rw [hsum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hsub :
        fderiv ℝ
            (fun y => A i m k y * B m j l y - A i m l y * B m j k y) x
            (coordBasis dir) =
          fderiv ℝ (fun y => A i m k y * B m j l y) x (coordBasis dir) -
            fderiv ℝ (fun y => A i m l y * B m j k y) x (coordBasis dir) := by
      exact congrArg (fun L => L (coordBasis dir)) <|
        fderiv_sub
          ((smoothForm1_differentiableAt A i m k x).mul (smoothForm1_differentiableAt B m j l x))
          ((smoothForm1_differentiableAt A i m l x).mul (smoothForm1_differentiableAt B m j k x))
    rw [hsub]
    have hmul₁ :
        fderiv ℝ (fun y => A i m k y * B m j l y) x (coordBasis dir) =
          smoothPderiv1 A dir i m k x * B m j l x +
            A i m k x * smoothPderiv1 B dir m j l x := by
      simpa [smoothPderiv1, smul_eq_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
        congrArg (fun L => L (coordBasis dir)) <|
          fderiv_fun_mul (smoothForm1_differentiableAt A i m k x)
            (smoothForm1_differentiableAt B m j l x)
    have hmul₂ :
        fderiv ℝ (fun y => A i m l y * B m j k y) x (coordBasis dir) =
          smoothPderiv1 A dir i m l x * B m j k x +
            A i m l x * smoothPderiv1 B dir m j k x := by
      simpa [smoothPderiv1, smul_eq_mul, mul_comm, add_comm, add_left_comm, add_assoc] using
        congrArg (fun L => L (coordBasis dir)) <|
          fderiv_fun_mul (smoothForm1_differentiableAt A i m l x)
            (smoothForm1_differentiableAt B m j k x)
    rw [hmul₁, hmul₂]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · intro m hm
    exact
      ((smoothForm1_differentiableAt A i m k x).mul (smoothForm1_differentiableAt B m j l x)).sub
        ((smoothForm1_differentiableAt A i m l x).mul (smoothForm1_differentiableAt B m j k x))

theorem smoothD2_smoothD1_eq_zero
    (A : SmoothForm1 n) :
    smoothD2 (smoothD1 A) = 0 := by
  ext i j e k l x
  change
    fderiv ℝ (fun y => smoothPderiv1 A k i j l y - smoothPderiv1 A l i j k y) x
        (coordBasis e) +
      fderiv ℝ (fun y => smoothPderiv1 A l i j e y - smoothPderiv1 A e i j l y) x
        (coordBasis k) +
      fderiv ℝ (fun y => smoothPderiv1 A e i j k y - smoothPderiv1 A k i j e y) x
        (coordBasis l) = 0
  have h₁ :
      fderiv ℝ (fun y => smoothPderiv1 A k i j l y - smoothPderiv1 A l i j k y) x
          (coordBasis e) =
        fderiv ℝ (fun y => smoothPderiv1 A k i j l y) x (coordBasis e) -
          fderiv ℝ (fun y => smoothPderiv1 A l i j k y) x (coordBasis e) := by
    exact congrArg (fun L => L (coordBasis e)) <|
      fderiv_sub
        (smoothPderiv1_differentiableAt A k i j l x)
        (smoothPderiv1_differentiableAt A l i j k x)
  have h₂ :
      fderiv ℝ (fun y => smoothPderiv1 A l i j e y - smoothPderiv1 A e i j l y) x
          (coordBasis k) =
        fderiv ℝ (fun y => smoothPderiv1 A l i j e y) x (coordBasis k) -
          fderiv ℝ (fun y => smoothPderiv1 A e i j l y) x (coordBasis k) := by
    exact congrArg (fun L => L (coordBasis k)) <|
      fderiv_sub
        (smoothPderiv1_differentiableAt A l i j e x)
        (smoothPderiv1_differentiableAt A e i j l x)
  have h₃ :
      fderiv ℝ (fun y => smoothPderiv1 A e i j k y - smoothPderiv1 A k i j e y) x
          (coordBasis l) =
        fderiv ℝ (fun y => smoothPderiv1 A e i j k y) x (coordBasis l) -
          fderiv ℝ (fun y => smoothPderiv1 A k i j e y) x (coordBasis l) := by
    exact congrArg (fun L => L (coordBasis l)) <|
      fderiv_sub
        (smoothPderiv1_differentiableAt A e i j k x)
        (smoothPderiv1_differentiableAt A k i j e x)
  rw [h₁, h₂, h₃]
  rw [smoothSecondPartial_eq A i j l k e x]
  rw [smoothSecondPartial_eq A i j k l e x]
  rw [smoothSecondPartial_eq A i j e l k x]
  rw [smoothSecondPartial_eq A i j l e k x]
  rw [smoothSecondPartial_eq A i j k e l x]
  rw [smoothSecondPartial_eq A i j e k l x]
  rw [smoothSecondPartial_comm A i j l k e x]
  rw [smoothSecondPartial_comm A i j e l k x]
  rw [smoothSecondPartial_comm A i j k e l x]
  ring

theorem eval_smoothD2_wedge11
    (A B : SmoothForm1 n) (x : CoordSpace n) :
    (smoothD2 (smoothWedge11 A B)).eval x =
      wedge21 n (evalConcreteD1 A x) (B.eval x) -
        wedge12 n (A.eval x) (evalConcreteD1 B x) := by
  ext i j e k l
  change
    evalConcreteD2 (smoothWedge11 A B) x i j e k l =
      (wedge21 n (evalConcreteD1 A x) (B.eval x) -
        wedge12 n (A.eval x) (evalConcreteD1 B x)) i j e k l
  unfold evalConcreteD2
  rw [smoothPderiv2_wedge11 A B e i j k l x]
  rw [smoothPderiv2_wedge11 A B k i j l e x]
  rw [smoothPderiv2_wedge11 A B l i j e k x]
  unfold wedge21 wedge12 evalConcreteD1
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg]
  simp [SmoothForm1.eval]
  simp_rw [add_mul, mul_add, neg_mul, mul_neg]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [Finset.sum_neg_distrib]
  ring_nf

theorem smoothD2_wedge11
    (A B : SmoothForm1 n) :
    smoothD2 (smoothWedge11 A B) = smoothWedge21 (smoothD1 A) B - smoothWedge12 A (smoothD1 B) := by
  ext i j e k l x
  have h := congrArg (fun T : Form3 n => T i j e k l) (eval_smoothD2_wedge11 A B x)
  simpa [SmoothForm3.eval_sub, smoothWedge21_eval, smoothWedge12_eval, smoothD1_eval] using h

def smoothAlgebra (n : ℕ) : LocalConnectionAlgebra where
  Ω1 := SmoothForm1 n
  Ω2 := SmoothForm2 n
  Ω3 := SmoothForm3 n
  d1 := smoothD1
  d2 := smoothD2
  wedge11 := smoothWedge11
  wedge12 := smoothWedge12
  wedge21 := smoothWedge21
  d2_add := smoothD2_add
  wedge12_add_right := smoothWedge12_add_right
  wedge21_add_left := smoothWedge21_add_left
  d2_d1_eq_zero := smoothD2_smoothD1_eq_zero
  d2_wedge11 := smoothD2_wedge11
  wedge_assoc := smoothWedge_assoc

def smoothProjection (x : CoordSpace n) :
    ComponentProjection (smoothAlgebra n)
      (Fin n × Fin n × Fin n × Fin n × Fin n) ℝ where
  proj := fun ω ⟨i, j, e, k, l⟩ => SmoothForm3.eval ω x i j e k l
  proj_zero := by
    intro ⟨i, j, e, k, l⟩
    rfl

@[simp] theorem smoothCurvature_eval
    (A : SmoothForm1 n) (x : CoordSpace n) :
    (curvature (smoothAlgebra n) ⟨A⟩).eval x =
      evalConcreteD1 A x + wedge11 n (A.eval x) (A.eval x) := by
  rfl

theorem smoothCurvature_antisym
    (A : SmoothForm1 n) :
    ∀ x i j k l : Fin n,
      (curvature (smoothAlgebra n) ⟨A⟩).eval x i j k l =
        -((curvature (smoothAlgebra n) ⟨A⟩).eval x i j l k) := by
  intro x i j k l
  simp [smoothCurvature_eval, evalConcreteD1, wedge11]
  ring

theorem smooth_proj_eq_explicit
    (A : SmoothForm1 n) (x : CoordSpace n) (i j e k l : Fin n) :
    let conn : ConnectionForm (smoothAlgebra n) := ⟨A⟩
    let R := curvature (smoothAlgebra n) conn
    (smoothProjection (n := n) x).proj
        (covariantExterior (smoothAlgebra n) conn R) (i, j, e, k, l) =
      (smoothD2 R).eval x i j e k l
        + ∑ m : Fin n,
            (A.eval x i m e * R.eval x m j k l
              + A.eval x i m k * R.eval x m j l e
              + A.eval x i m l * R.eval x m j e k)
        - ∑ m : Fin n,
            (R.eval x i m e k * A.eval x m j l
              + R.eval x i m k l * A.eval x m j e
              + R.eval x i m l e * A.eval x m j k) := by
  simp [smoothProjection, covariantExterior, smoothAlgebra, wedge12, wedge21]

theorem smooth_second_bianchi_component
    (A : SmoothForm1 n) :
    let conn : ConnectionForm (smoothAlgebra n) := ⟨A⟩
    let R := curvature (smoothAlgebra n) conn
    ∀ x i j e k l : Fin n,
      (smoothD2 R).eval x i j e k l
        + ∑ m : Fin n,
            (A.eval x i m e * R.eval x m j k l
              + A.eval x i m k * R.eval x m j l e
              + A.eval x i m l * R.eval x m j e k)
        - ∑ m : Fin n,
            (R.eval x i m e k * A.eval x m j l
              + R.eval x i m k l * A.eval x m j e
              + R.eval x i m l e * A.eval x m j k) = 0 := by
  intro conn R x i j e k l
  have h := second_bianchi_in_components
    (smoothAlgebra n) conn (smoothProjection (n := n) x) (i, j, e, k, l)
  rw [smooth_proj_eq_explicit (A := A) (x := x) i j e k l] at h
  exact h

private lemma sum_sub_four
    (f g h t : Fin n → ℝ) :
    (∑ m : Fin n, (f m - g m - h m - t m)) =
      (∑ m : Fin n, f m) - (∑ m : Fin n, g m) - (∑ m : Fin n, h m) - (∑ m : Fin n, t m) := by
  simp [sub_eq_add_neg, Finset.sum_add_distrib, add_assoc]

private lemma extra_terms_cancel
    (A : Form1 n) (R : Form2 n)
    (htf : ∀ i j k : Fin n, A i j k = A i k j)
    (hRantisym : ∀ i j k l : Fin n, R i j k l = -R i j l k)
    (i j e k l : Fin n) :
    (∑ m : Fin n,
      (-A m k e * R i j m l
        - A m l e * R i j k m
        - A m l k * R i j m e
        - A m e k * R i j l m
        - A m e l * R i j m k
        - A m k l * R i j e m)) = 0 := by
  calc
    _ = ∑ m : Fin n,
      (-A m k e * (R i j m l + R i j l m)
        - A m l e * (R i j k m + R i j m k)
        - A m l k * (R i j m e + R i j e m)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [htf m e k, htf m e l, htf m k l]
          ring
    _ = ∑ _m : Fin n, (0 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [hRantisym i j m l, hRantisym i j k m, hRantisym i j m e]
          ring
    _ = 0 := by simp

theorem cyclicCovariant_eq_component_formula_of_d2
    (pderiv : PartialTerm n) (A : Form1 n) (R : Form2 n) (d2R : Form3 n)
    (hd2 :
      ∀ i j e k l : Fin n,
        d2R i j e k l =
          pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k)
    (htf : ∀ i j k : Fin n, A i j k = A i k j)
    (hRantisym : ∀ i j k l : Fin n, R i j k l = -R i j l k)
    (i j e k l : Fin n) :
    cyclicCovariantDerivative pderiv A R i j e k l =
      d2R i j e k l
        + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
        - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k) := by
  let X : ℝ :=
    ∑ m : Fin n,
      (-A m k e * R i j m l
        - A m l e * R i j k m
        - A m l k * R i j m e
        - A m e k * R i j l m
        - A m e l * R i j m k
        - A m k l * R i j e m)
  have hsplit :
      cyclicCovariantDerivative pderiv A R i j e k l =
        d2R i j e k l
          + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
          - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
          + X := by
    rw [cyclicCovariantDerivative, covariantDerivative, covariantDerivative, covariantDerivative, hd2]
    rw [sum_sub_four
        (f := fun m => A i m e * R m j k l)
        (g := fun m => R i m k l * A m j e)
        (h := fun m => A m k e * R i j m l)
        (t := fun m => A m l e * R i j k m)]
    rw [sum_sub_four
        (f := fun m => A i m k * R m j l e)
        (g := fun m => R i m l e * A m j k)
        (h := fun m => A m l k * R i j m e)
        (t := fun m => A m e k * R i j l m)]
    rw [sum_sub_four
        (f := fun m => A i m l * R m j e k)
        (g := fun m => R i m e k * A m j l)
        (h := fun m => A m e l * R i j m k)
        (t := fun m => A m k l * R i j e m)]
    set Pe : ℝ := ∑ m : Fin n, A i m e * R m j k l with hPe
    set Pk : ℝ := ∑ m : Fin n, A i m k * R m j l e with hPk
    set Pl : ℝ := ∑ m : Fin n, A i m l * R m j e k with hPl
    set Nek : ℝ := ∑ m : Fin n, R i m e k * A m j l with hNek
    set Nke : ℝ := ∑ m : Fin n, R i m k l * A m j e with hNke
    set Nle : ℝ := ∑ m : Fin n, R i m l e * A m j k with hNle
    set X₁ : ℝ := ∑ m : Fin n, A m k e * R i j m l with hX₁
    set X₂ : ℝ := ∑ m : Fin n, A m l e * R i j k m with hX₂
    set X₃ : ℝ := ∑ m : Fin n, A m l k * R i j m e with hX₃
    set X₄ : ℝ := ∑ m : Fin n, A m e k * R i j l m with hX₄
    set X₅ : ℝ := ∑ m : Fin n, A m e l * R i j m k with hX₅
    set X₆ : ℝ := ∑ m : Fin n, A m k l * R i j e m with hX₆
    have hgroup :
        (pderiv R e i j k l + (Pe - Nke - X₁ - X₂)) +
            ((pderiv R k i j l e + (Pk - Nle - X₃ - X₄)) +
              (pderiv R l i j e k + (Pl - Nek - X₅ - X₆))) =
          (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k) +
            ((Pe + Pk + Pl) - (Nek + Nke + Nle) + (-X₁ - X₂ - X₃ - X₄ - X₅ - X₆)) := by
      abel_nf
    have hpos :
        Pe + Pk + Pl =
          ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k) := by
      rw [hPe, hPk, hPl]
      simp [Finset.sum_add_distrib, add_assoc]
    have hneg :
        Nek + Nke + Nle =
          ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k) := by
      rw [hNek, hNke, hNle]
      simp [Finset.sum_add_distrib, add_assoc]
    have hextra :
        -X₁ - X₂ - X₃ - X₄ - X₅ - X₆ = X := by
      rw [hX₁, hX₂, hX₃, hX₄, hX₅, hX₆]
      dsimp [X]
      simp [sub_eq_add_neg, Finset.sum_add_distrib, add_assoc]
    have h1 :
        pderiv R e i j k l + (Pe - Nke - X₁ - X₂) +
            (pderiv R k i j l e + (Pk - Nle - X₃ - X₄)) +
          (pderiv R l i j e k + (Pl - Nek - X₅ - X₆)) =
          (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k) +
            ((Pe + Pk + Pl) - (Nek + Nke + Nle) + (-X₁ - X₂ - X₃ - X₄ - X₅ - X₆)) := by
      simpa [add_assoc] using hgroup
    have h23 :
        (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k) +
            ((Pe + Pk + Pl) - (Nek + Nke + Nle) + (-X₁ - X₂ - X₃ - X₄ - X₅ - X₆)) =
          (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k)
            + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
            - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
            + X := by
      rw [hpos, hneg, hextra]
      abel_nf
    have h24 :
        (pderiv R e i j k l + pderiv R k i j l e + pderiv R l i j e k)
            + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
            - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
            + X =
          d2R i j e k l
            + ∑ m : Fin n, (A i m e * R m j k l + A i m k * R m j l e + A i m l * R m j e k)
            - ∑ m : Fin n, (R i m e k * A m j l + R i m k l * A m j e + R i m l e * A m j k)
            + X := by
      linarith [hd2 i j e k l]
    exact
      (h1.trans (by simpa [add_assoc] using h23)).trans
        (by simpa [add_assoc] using h24)
  have hX : X = 0 := by
    dsimp [X]
    exact extra_terms_cancel A R htf hRantisym i j e k l
  rw [hX] at hsplit
  simpa [sub_eq_add_neg, add_assoc] using hsplit

def smoothPartialTermAt (R : SmoothForm2 n) (x : CoordSpace n) : PartialTerm n :=
  fun _ dir i j k l => smoothPderiv2 R dir i j k l x

theorem smooth_second_bianchi_cyclic
    (A : SmoothForm1 n)
    (htf : ∀ x i j k : Fin n, A i j k x = A i k j x) :
    ∀ x i j e k l : Fin n,
      cyclicCovariantDerivative
        (smoothPartialTermAt (curvature (smoothAlgebra n) ⟨A⟩) x)
        (A.eval x)
        ((curvature (smoothAlgebra n) ⟨A⟩).eval x) i j e k l = 0 := by
  intro x i j e k l
  let R : SmoothForm2 n := curvature (smoothAlgebra n) ⟨A⟩
  have hbridge :=
    cyclicCovariant_eq_component_formula_of_d2
      (pderiv := smoothPartialTermAt R x)
      (A := A.eval x)
      (R := R.eval x)
      (d2R := (smoothD2 R).eval x)
      (hd2 := by
        intro i j e k l
        rfl)
      (htf := htf x)
      (hRantisym := smoothCurvature_antisym (n := n) A x)
      i j e k l
  rw [hbridge]
  simpa [R] using smooth_second_bianchi_component (n := n) A x i j e k l

end

end SecondBianchi.Coordinate
