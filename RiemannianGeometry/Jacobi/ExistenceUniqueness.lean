import Geodesic.LocalUniqueness
import Jacobi.Basic
import ParallelTransport.Frames

namespace Jacobi

universe u v

/-- A concrete operator assigning the Jacobi field for each initial value/derivative pair. -/
structure JacobiOperator (V : Type u) where
  solve : InitialData V → ParallelTransport.FieldAlong V

instance {V : Type u} : CoeFun (JacobiOperator V) (fun _ => InitialData V → ParallelTransport.FieldAlong V) where
  coe := JacobiOperator.solve

theorem jacobiOperator_ext
    {V : Type u} {J J' : JacobiOperator V}
    (hsolve : ∀ data t, J data t = J' data t) :
    J = J' := by
  cases J with
  | mk solve =>
      cases J' with
      | mk solve' =>
          have hsolve' : solve = solve' := by
            funext data t
            exact hsolve data t
          simp [hsolve']

theorem jacobiOperator_ext_iff
    {V : Type u} {J J' : JacobiOperator V} :
    J = J' ↔ ∀ data t, J data t = J' data t := by
  constructor
  · intro h data t
    simpa [h]
  · intro h
    exact jacobiOperator_ext h

/-- The theorem-level specification for a concrete Jacobi solver. -/
def IsJacobiOperator
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    (R : Curvature.CurvatureTensor C)
    (T : ParallelTransport.FieldAlong V)
    (nablaTT : AlongSecondDerivative V)
    (J : JacobiOperator V) : Prop :=
  ∀ data : InitialData V,
    J data 0 = data.value ∧
      nablaTT (J data) 0 = data.deriv ∧
      IsJacobiField R T nablaTT (J data) ∧
      ∀ W : ParallelTransport.FieldAlong V,
        W 0 = data.value ∧ nablaTT W 0 = data.deriv ∧ IsJacobiField R T nablaTT W →
          W = J data

theorem isJacobiOperator_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J : JacobiOperator V} :
    IsJacobiOperator R T nablaTT J ↔
      ∀ data : InitialData V,
        J data 0 = data.value ∧
          nablaTT (J data) 0 = data.deriv ∧
          IsJacobiField R T nablaTT (J data) ∧
          ∀ W : ParallelTransport.FieldAlong V,
            W 0 = data.value ∧ nablaTT W 0 = data.deriv ∧ IsJacobiField R T nablaTT W →
              W = J data :=
  Iff.rfl

theorem eq_of_isJacobiOperator
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J : JacobiOperator V}
    (hJ : IsJacobiOperator R T nablaTT J)
    {data : InitialData V}
    {W : ParallelTransport.FieldAlong V}
    (hW : W 0 = data.value ∧ nablaTT W 0 = data.deriv ∧ IsJacobiField R T nablaTT W) :
    W = J data :=
  (hJ data).2.2.2 W hW

theorem isJacobiOperator_spec
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J : JacobiOperator V}
    (hJ : IsJacobiOperator R T nablaTT J)
    (data : InitialData V) :
    J data 0 = data.value ∧
      nablaTT (J data) 0 = data.deriv ∧
      IsJacobiField R T nablaTT (J data) := by
  exact ⟨(hJ data).1, (hJ data).2.1, (hJ data).2.2.1⟩

theorem isJacobiOperator_eq_iff
    {V : Type u} {S : Type v}
    [AddGroup V] [SMul S V]
    {C : LeviCivita.ConnectionContext V S}
    {R : Curvature.CurvatureTensor C}
    {T : ParallelTransport.FieldAlong V}
    {nablaTT : AlongSecondDerivative V}
    {J : JacobiOperator V}
    (hJ : IsJacobiOperator R T nablaTT J)
    {data : InitialData V}
    {W : ParallelTransport.FieldAlong V} :
    W = J data ↔
      W 0 = data.value ∧ nablaTT W 0 = data.deriv ∧ IsJacobiField R T nablaTT W := by
  constructor
  · intro h
    subst h
    exact isJacobiOperator_spec hJ data
  · intro hW
    exact eq_of_isJacobiOperator hJ hW

section Coordinate

open ParallelTransport
open Set ODE

variable {n : ℕ}

/-- Fields along the parameter interval with values in the fixed coordinate model fiber `ℝ^n`. -/
abbrev CoordinateFieldAlong (n : ℕ) := ParallelTransport.FieldAlong (CoordinateVector n)

/-- First-order state space for the coordinate Jacobi equation. -/
abbrev JacobiState (n : ℕ) := CoordinateVector n × CoordinateVector n

/-- Concrete coefficient data for the coordinate Jacobi equation
`J'' + A(t) J = 0`. -/
structure CoordinateJacobiSystem (n : ℕ) where
  A : ℝ → Matrix (Fin n) (Fin n) ℝ
  Acont : ∀ i j, Continuous fun t => A t i j

/-- The first-order state-space vector field attached to `J'' + A(t) J = 0`. -/
def jacobiVectorField
    (sys : CoordinateJacobiSystem n) :
    ℝ → JacobiState n → JacobiState n :=
  fun t z => (z.2, coordinateParallelRhs sys.A t z.1)

theorem lipschitzWith_jacobiVectorField
    (sys : CoordinateJacobiSystem n) {t : ℝ} {K : NNReal}
    (hcoeff : coordinateCoeffBound (sys.A t) ≤ K)
    (hK : (1 : ℝ) ≤ K) :
    LipschitzWith K (jacobiVectorField (n := n) sys t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rcases z with ⟨x, u⟩
  rcases w with ⟨y, v⟩
  rw [Prod.dist_eq]
  refine max_le_iff.mpr ⟨?_, ?_⟩
  · calc
      dist u v ≤ dist (x, u) (y, v) := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      _ ≤ K * dist (x, u) (y, v) := by
        have hdist_nonneg : 0 ≤ dist (x, u) (y, v) := dist_nonneg
        nlinarith
  · calc
      dist (coordinateParallelRhs sys.A t x) (coordinateParallelRhs sys.A t y)
        ≤ K * dist x y :=
          (lipschitzWith_coordinateParallelRhs sys.A hcoeff).dist_le_mul x y
      _ ≤ K * dist (x, u) (y, v) := by
        rw [Prod.dist_eq]
        gcongr
        exact le_max_left _ _

/-- In the current fixed-fiber coordinate model, the Jacobi equation already is the coordinate
second-order ODE in the ambient `Fin n → ℝ` coordinates. A parallel frame can still be supplied,
but no extra coordinate-extraction API is presently bundled into `ParallelFrame`. -/
theorem jacobiODE_from_parallelFrame
    {C : LeviCivita.ConnectionContext (CoordinateVector n) ℝ}
    (T : CoordinateFieldAlong n)
    (R : Curvature.CurvatureTensor C)
    (nablaTT : AlongSecondDerivative (CoordinateVector n))
    (frame : ParallelFrame (Fin n) (CoordinateVector n)) :
    ∀ J : CoordinateFieldAlong n,
      IsJacobiField R T nablaTT J ↔
        ∀ t, nablaTT J t + R (J t) (T t) (T t) = 0 := by
  intro J
  let _ := frame
  rfl

/-- Local existence and uniqueness for the concrete coordinate Jacobi state system. The theorem is
stated on the interval `[-ε, ε]`, which is the natural uniqueness domain provided by the ODE
theory. -/
theorem existsUnique_coordinateJacobiState
    (sys : CoordinateJacobiSystem n)
    {ε : ℝ} (hε : 0 < ε) {a r L K : NNReal}
    (hK : (1 : ℝ) ≤ K)
    (hcoeff : ∀ t ∈ Set.Icc (-ε) ε, coordinateCoeffBound (sys.A t) ≤ K)
    (hpl : IsPicardLindelof (jacobiVectorField (n := n) sys)
      (coordinateInitialPoint ε hε) (0 : JacobiState n) a r L K)
    {J0 J0' : CoordinateVector n}
    (hz0 : (J0, J0') ∈ Metric.closedBall (0 : JacobiState n) r) :
    ∃ Z : ℝ → JacobiState n,
      Z 0 = (J0, J0') ∧
      (∀ t ∈ Set.Icc (-ε) ε,
        HasDerivWithinAt Z (jacobiVectorField (n := n) sys t (Z t)) (Set.Icc (-ε) ε) t) ∧
      ∀ W : ℝ → JacobiState n,
        W 0 = (J0, J0') →
        (∀ t ∈ Set.Icc (-ε) ε,
          HasDerivWithinAt W (jacobiVectorField (n := n) sys t (W t)) (Set.Icc (-ε) ε) t) →
        Set.EqOn W Z (Set.Icc (-ε) ε) := by
  obtain ⟨Z, hZ0, hZ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hz0
  refine ⟨Z, ?_, hZ, ?_⟩
  · simpa [coordinateInitialPoint] using hZ0
  · intro W hW0 hW
    have hcontW : ContinuousOn W (Set.Icc (-ε) ε) := by
      intro t ht
      exact (hW t ht).continuousWithinAt
    have hcontZ : ContinuousOn Z (Set.Icc (-ε) ε) := by
      intro t ht
      exact (hZ t ht).continuousWithinAt
    have hderivW :
        ∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt W (jacobiVectorField (n := n) sys t (W t)) t := by
      intro t ht
      exact (hW t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hderivZ :
        ∀ t ∈ Set.Ioo (-ε) ε,
          HasDerivAt Z (jacobiVectorField (n := n) sys t (Z t)) t := by
      intro t ht
      exact (hZ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hv :
        ∀ t ∈ Set.Ioo (-ε) ε,
          LipschitzOnWith K (jacobiVectorField (n := n) sys t) (Set.univ : Set (JacobiState n)) := by
      intro t ht
      exact
        (lipschitzWith_jacobiVectorField (n := n) sys
          (hcoeff t (Ioo_subset_Icc_self ht)) hK).lipschitzOnWith
    have heq :
        Set.EqOn W Z (Set.Icc (-ε) ε) := by
      have hZ00 : Z 0 = (J0, J0') := by
        simpa [coordinateInitialPoint] using hZ0
      apply (ODE_solution_unique_of_mem_Icc (t₀ := 0))
      · exact hv
      · constructor <;> linarith
      · exact hcontW
      · exact hderivW
      · intro t ht
        trivial
      · exact hcontZ
      · exact hderivZ
      · intro t ht
        trivial
      · exact hW0.trans hZ00.symm
    exact heq

end Coordinate

end Jacobi
