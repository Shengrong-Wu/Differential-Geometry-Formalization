import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Comparison.RauchNormCore
import ParallelTransport.Frames
import Curvature.SectionalRicci

open scoped BigOperators
open BigOperators Finset

namespace Comparison

open ParallelTransport

variable {n : ℕ}

/-- The fixed-fiber lift determined by a frame along the reference geodesic. -/
noncomputable def frameLift
    (E : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (t : ℝ) (ξ : CoordinateVector n) : CoordinateVector n :=
  ∑ i : Fin n, ξ i • E.vec i t

/-- A time-dependent normalized sectional upper bound in the coordinate metric carried along the
reference geodesic. This is the sign/scale-correct formulation actually used by the Rayleigh
reduction: for a unit tangent `T t` and an orthogonal vector `X`,
`⟪R(X,T)T, X⟫ ≤ k ⟪X,X⟫`. -/
def NormalizedSectionalUpperBoundAlongCoordinate
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong (CoordinateVector n))
    (k : ℝ) : Prop :=
  ∀ t X,
    coordinatePairingAt (g t) (T t) (T t) = 1 →
    coordinatePairingAt (g t) X (T t) = 0 →
    coordinatePairingAt (g t) (R X (T t) (T t)) X ≤
      k * coordinatePairingAt (g t) X X

/-- Pointwise frame data for the coordinate curvature bridge. The key remaining geometric input is
that `A(t) ξ` gives the coordinates of `R(lift ξ, T)T` in the chosen orthonormal normal frame.
This is the concrete owner-local form of the second Rauch gap. -/
structure CoordinateFrameCurvatureBridgeData
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong (CoordinateVector n))
    (sys : Jacobi.CoordinateJacobiSystem n) where
  frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n)
  tangent_unit :
    ∀ t, coordinatePairingAt (g t) (T t) (T t) = 1
  frame_orthonormal :
    ∀ t i j,
      coordinatePairingAt (g t) (frame.vec i t) (frame.vec j t) =
        if i = j then 1 else 0
  frame_normal :
    ∀ t i,
      coordinatePairingAt (g t) (frame.vec i t) (T t) = 0
  curvatureCoords :
    ∀ t ξ i,
      (Matrix.mulVec (sys.A t) ξ) i =
        coordinatePairingAt (g t) (R (frameLift frame t ξ) (T t) (T t)) (frame.vec i t)

private theorem coordinatePairingAt_smul_right
    (g : Matrix (Fin n) (Fin n) ℝ)
    (v w : CoordinateVector n) (a : ℝ) :
    coordinatePairingAt g v (a • w) = a * coordinatePairingAt g v w := by
  simp [coordinatePairingAt, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_left_comm, mul_comm]

private theorem coordinatePairingAt_smul_left
    (g : Matrix (Fin n) (Fin n) ℝ)
    (v w : CoordinateVector n) (a : ℝ) :
    coordinatePairingAt g (a • v) w = a * coordinatePairingAt g v w := by
  simp [coordinatePairingAt, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_left_comm, mul_comm]

private theorem coordinatePairingAt_add_right
    (g : Matrix (Fin n) (Fin n) ℝ)
    (v w z : CoordinateVector n) :
    coordinatePairingAt g v (w + z) =
      coordinatePairingAt g v w + coordinatePairingAt g v z := by
  simp [coordinatePairingAt, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul, mul_add, add_assoc, add_left_comm, add_comm]

private theorem coordinatePairingAt_add_left
    (g : Matrix (Fin n) (Fin n) ℝ)
    (v w z : CoordinateVector n) :
    coordinatePairingAt g (v + w) z =
      coordinatePairingAt g v z + coordinatePairingAt g w z := by
  simp [coordinatePairingAt, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul, mul_add, add_assoc, add_left_comm, add_comm]

private theorem coordinatePairingAt_sum_smul_right
    (g : Matrix (Fin n) (Fin n) ℝ)
    (v : CoordinateVector n)
    (E : Fin n → CoordinateVector n)
    (ξ : CoordinateVector n) :
    coordinatePairingAt g v (∑ i : Fin n, ξ i • E i) =
      ∑ i : Fin n, ξ i * coordinatePairingAt g v (E i) := by
  classical
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?base ?step
  · simp [coordinatePairingAt]
  · intro i s hi hs
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coordinatePairingAt_add_right]
    rw [coordinatePairingAt_smul_right]
    simp [hi, hs, add_comm, add_left_comm, add_assoc]

private theorem coordinatePairingAt_sum_smul_left
    (g : Matrix (Fin n) (Fin n) ℝ)
    (E : Fin n → CoordinateVector n)
    (ξ : CoordinateVector n)
    (v : CoordinateVector n) :
    coordinatePairingAt g (∑ i : Fin n, ξ i • E i) v =
      ∑ i : Fin n, ξ i * coordinatePairingAt g (E i) v := by
  classical
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?base ?step
  · simp [coordinatePairingAt]
  · intro i s hi hs
    rw [Finset.sum_insert hi, Finset.sum_insert hi, coordinatePairingAt_add_left]
    rw [coordinatePairingAt_smul_left]
    simp [hi, hs, add_comm, add_left_comm, add_assoc]

private theorem coordinatePairingAt_frameLift_frame
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {bridge : CoordinateFrameCurvatureBridgeData g R T sys}
    (t : ℝ) (ξ : CoordinateVector n) (j : Fin n) :
    coordinatePairingAt (g t) (frameLift bridge.frame t ξ) (bridge.frame.vec j t) = ξ j := by
  rw [frameLift, coordinatePairingAt_sum_smul_left]
  calc
    ∑ i : Fin n, ξ i * coordinatePairingAt (g t) (bridge.frame.vec i t) (bridge.frame.vec j t)
        = ∑ i : Fin n, ξ i * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [bridge.frame_orthonormal t i j]
    _ = ξ j := by
          simp

private theorem coordinatePairingAt_curvature_frameLift
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {bridge : CoordinateFrameCurvatureBridgeData g R T sys}
    (t : ℝ) (ξ : CoordinateVector n) :
    coordinatePairingAt (g t)
        (R (frameLift bridge.frame t ξ) (T t) (T t))
        (frameLift bridge.frame t ξ) =
      ∑ i : Fin n,
        ξ i *
          coordinatePairingAt (g t)
            (R (frameLift bridge.frame t ξ) (T t) (T t))
            (bridge.frame.vec i t) := by
  rw [frameLift, coordinatePairingAt_sum_smul_right]

private theorem frameLift_normal
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {bridge : CoordinateFrameCurvatureBridgeData g R T sys}
    (t : ℝ) (ξ : CoordinateVector n) :
    coordinatePairingAt (g t) (frameLift bridge.frame t ξ) (T t) = 0 := by
  rw [frameLift, coordinatePairingAt_sum_smul_left]
  have hterm :
      ∀ i : Fin n,
        ξ i * coordinatePairingAt (g t) (bridge.frame.vec i t) (T t) = 0 := by
    intro i
    rw [bridge.frame_normal t i, mul_zero]
  simpa [hterm]

private theorem frameLift_norm_sq
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {bridge : CoordinateFrameCurvatureBridgeData g R T sys}
    (t : ℝ) (ξ : CoordinateVector n) :
    coordinatePairingAt (g t) (frameLift bridge.frame t ξ) (frameLift bridge.frame t ξ) =
      vecNormSq ξ := by
  rw [frameLift, coordinatePairingAt_sum_smul_right]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hpair :
      coordinatePairingAt (g t) (∑ j : Fin n, ξ j • bridge.frame.vec j t) (bridge.frame.vec i t) =
        ξ i := by
    simpa [frameLift] using coordinatePairingAt_frameLift_frame (bridge := bridge) t ξ i
  rw [hpair]
  simp [vecNormSq, sq]

private theorem matrixQuadForm_eq_frameLift_curvature
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    (bridge : CoordinateFrameCurvatureBridgeData g R T sys)
    (t : ℝ) (ξ : CoordinateVector n) :
    matrixQuadForm (sys.A t) ξ =
      coordinatePairingAt (g t)
        (R (frameLift bridge.frame t ξ) (T t) (T t))
        (frameLift bridge.frame t ξ) := by
  calc
    matrixQuadForm (sys.A t) ξ
        = ∑ i : Fin n, (Matrix.mulVec (sys.A t) ξ) i * ξ i := by
            simp [matrixQuadForm, vecInner]
    _ = ∑ i : Fin n,
          ξ i *
            coordinatePairingAt (g t)
              (R (frameLift bridge.frame t ξ) (T t) (T t))
              (bridge.frame.vec i t) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [bridge.curvatureCoords t ξ i]
          ring
    _ = coordinatePairingAt (g t)
          (R (frameLift bridge.frame t ξ) (T t) (T t))
          (frameLift bridge.frame t ξ) := by
          symm
          exact coordinatePairingAt_curvature_frameLift (bridge := bridge) t ξ

private theorem coordinatePairingAt_frameLift_frame_of_pointwise_orthonormal
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (t : ℝ) (ξ : CoordinateVector n) (j : Fin n)
    (horth :
      ∀ i j,
        coordinatePairingAt (g t) (frame.vec i t) (frame.vec j t) =
          if i = j then 1 else 0) :
    coordinatePairingAt (g t) (frameLift frame t ξ) (frame.vec j t) = ξ j := by
  rw [frameLift, coordinatePairingAt_sum_smul_left]
  calc
    ∑ i : Fin n, ξ i * coordinatePairingAt (g t) (frame.vec i t) (frame.vec j t)
        = ∑ i : Fin n, ξ i * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [horth i j]
    _ = ξ j := by
          simp

private noncomputable def frameLiftLinearMap
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (t : ℝ) : CoordinateVector n →ₗ[ℝ] CoordinateVector n where
  toFun := frameLift frame t
  map_add' := by
    intro ξ η
    ext i
    simp [frameLift, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro a ξ
    ext i
    simp [frameLift, Finset.mul_sum, mul_assoc]

private noncomputable def frameCoeffLinearMap
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (t : ℝ) : CoordinateVector n →ₗ[ℝ] CoordinateVector n where
  toFun := fun v i => coordinatePairingAt (g t) v (frame.vec i t)
  map_add' := by
    intro v w
    ext i
    simp [coordinatePairingAt_add_left]
  map_smul' := by
    intro a v
    ext i
    simp [coordinatePairingAt_smul_left]

/-- In a pointwise orthonormal frame, a vector is recovered from its metric pairings with the
frame vectors. This is the owner-level reconstruction lemma needed to pass from the matrix
curvature-coordinate identity to the field-specific one. -/
theorem frameLift_pairingCoeffs_eq_self_of_pointwise_orthonormal
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (t : ℝ) (v : CoordinateVector n)
    (horth :
      ∀ i j,
        coordinatePairingAt (g t) (frame.vec i t) (frame.vec j t) =
          if i = j then 1 else 0) :
    frameLift frame t (fun i => coordinatePairingAt (g t) v (frame.vec i t)) = v := by
  let F : CoordinateVector n →ₗ[ℝ] CoordinateVector n := frameLiftLinearMap frame t
  let L : CoordinateVector n →ₗ[ℝ] CoordinateVector n := frameCoeffLinearMap g frame t
  have hleft : Function.LeftInverse L F := by
    intro ξ
    ext i
    change coordinatePairingAt (g t) (frameLift frame t ξ) (frame.vec i t) = ξ i
    simpa using
      coordinatePairingAt_frameLift_frame_of_pointwise_orthonormal
        (g := g) frame t ξ i horth
  have hsurj : Function.Surjective F := by
    refine
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (K := ℝ) (V := CoordinateVector n) (V₂ := CoordinateVector n) rfl).mp ?_
    exact hleft.injective
  obtain ⟨ξ, rfl⟩ := hsurj v
  have hcoeff :
      (fun i =>
        coordinatePairingAt (g t) (frameLift frame t ξ) (frame.vec i t)) = ξ := by
    funext i
    simpa using
      coordinatePairingAt_frameLift_frame_of_pointwise_orthonormal
        (g := g) frame t ξ i horth
  simpa [F, frameLiftLinearMap, hcoeff]

private theorem frameLift_normal_of_pointwise_normal
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (t : ℝ) (ξ : CoordinateVector n)
    (hnormal :
      ∀ i,
        coordinatePairingAt (g t) (frame.vec i t) (T t) = 0) :
    coordinatePairingAt (g t) (frameLift frame t ξ) (T t) = 0 := by
  rw [frameLift, coordinatePairingAt_sum_smul_left]
  have hterm :
      ∀ i : Fin n,
        ξ i * coordinatePairingAt (g t) (frame.vec i t) (T t) = 0 := by
    intro i
    rw [hnormal i, mul_zero]
  simpa [hterm]

private theorem frameLift_norm_sq_of_pointwise_orthonormal
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (t : ℝ) (ξ : CoordinateVector n)
    (horth :
      ∀ i j,
        coordinatePairingAt (g t) (frame.vec i t) (frame.vec j t) =
          if i = j then 1 else 0) :
    coordinatePairingAt (g t) (frameLift frame t ξ) (frameLift frame t ξ) =
      vecNormSq ξ := by
  rw [frameLift, coordinatePairingAt_sum_smul_right]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hpair :
      coordinatePairingAt (g t) (∑ j : Fin n, ξ j • frame.vec j t) (frame.vec i t) =
        ξ i := by
    simpa [frameLift] using
      coordinatePairingAt_frameLift_frame_of_pointwise_orthonormal
        (g := g) frame t ξ i horth
  rw [hpair]
  simp [vecNormSq, sq]

private theorem matrixQuadForm_eq_frameLift_curvature_of_pointwiseCoords
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (t : ℝ) (ξ : CoordinateVector n)
    (hcurv :
      ∀ i,
        (Matrix.mulVec (sys.A t) ξ) i =
          coordinatePairingAt (g t)
            (R (frameLift frame t ξ) (T t) (T t))
            (frame.vec i t)) :
    matrixQuadForm (sys.A t) ξ =
      coordinatePairingAt (g t)
        (R (frameLift frame t ξ) (T t) (T t))
        (frameLift frame t ξ) := by
  calc
    matrixQuadForm (sys.A t) ξ
        = ∑ i : Fin n, (Matrix.mulVec (sys.A t) ξ) i * ξ i := by
            simp [matrixQuadForm, vecInner]
    _ = ∑ i : Fin n,
          ξ i *
            coordinatePairingAt (g t)
              (R (frameLift frame t ξ) (T t) (T t))
              (frame.vec i t) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hcurv i]
          ring
    _ = coordinatePairingAt (g t)
          (R (frameLift frame t ξ) (T t) (T t))
          (frameLift frame t ξ) := by
          symm
          rw [frameLift, coordinatePairingAt_sum_smul_right]

/-- Pointwise local Rayleigh bound in a chosen orthonormal normal frame. This is the honest local
coordinate curvature step needed by the active lower-Rauch path. -/
theorem hasRayleighUpperBoundOn_of_coordinateFrame
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {s : Set ℝ} {k : ℝ}
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (hsec : NormalizedSectionalUpperBoundAlongCoordinate (n := n) g R T k)
    (htangent_unit :
      ∀ t ∈ s, coordinatePairingAt (g t) (T t) (T t) = 1)
    (hframe_orthonormal :
      ∀ t ∈ s, ∀ i j,
        coordinatePairingAt (g t) (frame.vec i t) (frame.vec j t) =
          if i = j then 1 else 0)
    (hframe_normal :
      ∀ t ∈ s, ∀ i,
        coordinatePairingAt (g t) (frame.vec i t) (T t) = 0)
    (hcurvatureCoords :
      ∀ t ∈ s, ∀ ξ i,
        (Matrix.mulVec (sys.A t) ξ) i =
          coordinatePairingAt (g t)
            (R (frameLift frame t ξ) (T t) (T t))
            (frame.vec i t)) :
    HasRayleighUpperBoundOn sys.A s k := by
  intro t ht ξ
  calc
    matrixQuadForm (sys.A t) ξ
        = coordinatePairingAt (g t)
            (R (frameLift frame t ξ) (T t) (T t))
            (frameLift frame t ξ) := by
              exact matrixQuadForm_eq_frameLift_curvature_of_pointwiseCoords
                (g := g) (R := R) (T := T) (sys := sys) frame t ξ
                (hcurvatureCoords t ht ξ)
    _ ≤ k * coordinatePairingAt (g t) (frameLift frame t ξ) (frameLift frame t ξ) := by
          exact hsec t (frameLift frame t ξ) (htangent_unit t ht)
            (frameLift_normal_of_pointwise_normal
              (g := g) (T := T) frame t ξ (hframe_normal t ht))
    _ = k * vecNormSq ξ := by
          rw [frameLift_norm_sq_of_pointwise_orthonormal
            (g := g) frame t ξ (hframe_orthonormal t ht)]

/-- Pointwise local Rayleigh bound from a direct quadratic-form curvature identity in a chosen
orthonormal normal frame. This is the weaker bridge actually needed by the Rayleigh side of the
lower-Rauch route when the full componentwise `matrixCurvatureCoords` theorem is unavailable. -/
theorem hasRayleighUpperBoundOn_of_coordinateFrameQuadratic
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {s : Set ℝ} {k : ℝ}
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (hsec : NormalizedSectionalUpperBoundAlongCoordinate (n := n) g R T k)
    (htangent_unit :
      ∀ t ∈ s, coordinatePairingAt (g t) (T t) (T t) = 1)
    (hframe_orthonormal :
      ∀ t ∈ s, ∀ i j,
        coordinatePairingAt (g t) (frame.vec i t) (frame.vec j t) =
          if i = j then 1 else 0)
    (hframe_normal :
      ∀ t ∈ s, ∀ i,
        coordinatePairingAt (g t) (frame.vec i t) (T t) = 0)
    (hcurvatureQuad :
      ∀ t ∈ s, ∀ ξ,
        matrixQuadForm (sys.A t) ξ =
          coordinatePairingAt (g t)
            (R (frameLift frame t ξ) (T t) (T t))
            (frameLift frame t ξ)) :
    HasRayleighUpperBoundOn sys.A s k := by
  intro t ht ξ
  calc
    matrixQuadForm (sys.A t) ξ
        = coordinatePairingAt (g t)
            (R (frameLift frame t ξ) (T t) (T t))
            (frameLift frame t ξ) := hcurvatureQuad t ht ξ
    _ ≤ k * coordinatePairingAt (g t) (frameLift frame t ξ) (frameLift frame t ξ) := by
          exact hsec t (frameLift frame t ξ) (htangent_unit t ht)
            (frameLift_normal_of_pointwise_normal
              (g := g) (T := T) frame t ξ (hframe_normal t ht))
    _ = k * vecNormSq ξ := by
          rw [frameLift_norm_sq_of_pointwise_orthonormal
            (g := g) frame t ξ (hframe_orthonormal t ht)]

/-- Concrete coordinate-frame version of the second Rauch gap: if the Jacobi coefficient matrix
records the coordinates of the curvature vector in an orthonormal normal frame along a unit-speed
geodesic, then the normalized sectional-curvature upper bound implies the Rayleigh inequality
needed by the norm-squared core. -/
theorem hasRayleighUpperBound_of_coordinateFrameCurvatureBridge
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong (CoordinateVector n)}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {k : ℝ}
    (hsec : NormalizedSectionalUpperBoundAlongCoordinate (n := n) g R T k)
    (bridge : CoordinateFrameCurvatureBridgeData (n := n) g R T sys) :
    HasRayleighUpperBound sys.A k := by
  intro t ξ
  calc
    matrixQuadForm (sys.A t) ξ
        = coordinatePairingAt (g t)
            (R (frameLift bridge.frame t ξ) (T t) (T t))
            (frameLift bridge.frame t ξ) := by
              exact matrixQuadForm_eq_frameLift_curvature bridge t ξ
    _ ≤ k * coordinatePairingAt (g t) (frameLift bridge.frame t ξ) (frameLift bridge.frame t ξ) := by
          exact hsec t (frameLift bridge.frame t ξ) (bridge.tangent_unit t)
            (frameLift_normal (bridge := bridge) t ξ)
    _ = k * vecNormSq ξ := by
          rw [frameLift_norm_sq (bridge := bridge) t ξ]

/-! ### Curvature linearity bridge

When the curvature tensor is linear in its first argument (as it always is in actual Riemannian
geometry), the full componentwise matrix curvature-coordinate bridge follows algebraically from the
basis-column identity `A(t)_ij = ⟨R(eⱼ(t), T(t)) T(t), eᵢ(t)⟩_g`. This eliminates the need to
postulate `matrixCurvatureCoords` directly. -/

private theorem curvature_sum_smul_left
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {R : Curvature.CurvatureTensor C}
    (hadd : ∀ (x y z w : CoordinateVector n), R (x + y) z w = R x z w + R y z w)
    (hsmul : ∀ (a : ℝ) (x y z : CoordinateVector n), R (a • x) y z = a • R x y z)
    (E : Fin n → CoordinateVector n) (ξ : CoordinateVector n)
    (y z : CoordinateVector n) :
    R (∑ i : Fin n, ξ i • E i) y z = ∑ i : Fin n, ξ i • R (E i) y z := by
  classical
  refine Finset.induction_on (s := (Finset.univ : Finset (Fin n))) ?base ?step
  · simp only [Finset.sum_empty]
    calc R (0 : CoordinateVector n) y z
        = R ((0 : ℝ) • (0 : CoordinateVector n)) y z := by rw [zero_smul]
      _ = (0 : ℝ) • R (0 : CoordinateVector n) y z := hsmul 0 0 y z
      _ = 0 := zero_smul _ _
  · intro i s hi hs
    rw [Finset.sum_insert hi, hadd, hs, hsmul, Finset.sum_insert hi]

/-- The full componentwise matrix curvature-coordinate bridge, derived from curvature linearity
in the first argument and the basis-column identity `A(t)_ij = ⟨R(eⱼ(t), T(t)) T(t), eᵢ(t)⟩_g`.

Given:
* `hadd` / `hsmul` — `R` is additive and homogeneous in its first slot,
* `hbasis` — each matrix entry `A(t)_ij` equals the metric pairing of `R(eⱼ, T)T` with `eᵢ`,

the full `(A(t)·ξ)ᵢ = ⟨R(∑ⱼ ξⱼ eⱼ, T)T, eᵢ⟩_g` follows algebraically. -/
theorem matrixCurvatureCoords_of_basisAndLinearity
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    {sys : Jacobi.CoordinateJacobiSystem n}
    {g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {R : Curvature.CurvatureTensor C}
    {T : FieldAlong (CoordinateVector n)}
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (hadd : ∀ (x y z w : CoordinateVector n), R (x + y) z w = R x z w + R y z w)
    (hsmul : ∀ (a : ℝ) (x y z : CoordinateVector n), R (a • x) y z = a • R x y z)
    {t : ℝ}
    (hbasis : ∀ i j,
      sys.A t i j =
        coordinatePairingAt (g t) (R (frame.vec j t) (T t) (T t)) (frame.vec i t))
    (ξ : CoordinateVector n) (i : Fin n) :
    (Matrix.mulVec (sys.A t) ξ) i =
      coordinatePairingAt (g t) (R (frameLift frame t ξ) (T t) (T t)) (frame.vec i t) := by
  have hcurv_expand :
      R (frameLift frame t ξ) (T t) (T t) =
        ∑ j : Fin n, ξ j • R (frame.vec j t) (T t) (T t) := by
    simp only [frameLift]
    exact curvature_sum_smul_left hadd hsmul (fun j => frame.vec j t) ξ (T t) (T t)
  rw [hcurv_expand, coordinatePairingAt_sum_smul_left]
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hbasis i j]
  ring

/-- The canonical Jacobi coefficient matrix built from curvature: `A(t)_ij := ⟨R(eⱼ(t), T(t))T(t), eᵢ(t)⟩_g`.
With this definition, the basis-column identity `basisCurvatureCoords` holds by `rfl`. -/
noncomputable def canonicalJacobiSystemOfCurvature
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R : Curvature.CurvatureTensor C)
    (T : FieldAlong (CoordinateVector n))
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (Acont : ∀ i j, Continuous fun t =>
      coordinatePairingAt (g t) (R (frame.vec j t) (T t) (T t)) (frame.vec i t)) :
    Jacobi.CoordinateJacobiSystem n where
  A t i j := coordinatePairingAt (g t) (R (frame.vec j t) (T t) (T t)) (frame.vec i t)
  Acont := Acont

@[simp] theorem canonicalJacobiSystemOfCurvature_A
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (g : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (R : Curvature.CurvatureTensor C)
    (T : FieldAlong (CoordinateVector n))
    (frame : ParallelTransport.ParallelFrame (Fin n) (CoordinateVector n))
    (Acont : ∀ i j, Continuous fun t =>
      coordinatePairingAt (g t) (R (frame.vec j t) (T t) (T t)) (frame.vec i t))
    (t : ℝ) (i j : Fin n) :
    (canonicalJacobiSystemOfCurvature g R T frame Acont).A t i j =
      coordinatePairingAt (g t) (R (frame.vec j t) (T t) (T t)) (frame.vec i t) :=
  rfl

end Comparison
