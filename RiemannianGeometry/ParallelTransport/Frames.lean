import ParallelTransport.Isometry

namespace ParallelTransport

universe u

/-- A frame along the chosen parameter interval in a fixed trivialized fiber. -/
structure ParallelFrame (ι : Type*) (V : Type u) where
  vec : ι → FieldAlong V

/-- Build a transported frame from a genuine transport operator and an initial family of vectors. -/
def frameOfTransport
    {ι : Type*} {V : Type u} (T : TransportOperator V) (e₀ : ι → V) :
    ParallelFrame ι V where
  vec i := T (e₀ i)

@[simp] theorem frameOfTransport_apply
    {ι : Type*} {V : Type u} (T : TransportOperator V) (e₀ : ι → V) (i : ι) (t : ℝ) :
    (frameOfTransport T e₀).vec i t = T (e₀ i) t :=
  rfl

theorem parallelFrame_ext
    {ι : Type*} {V : Type u} {E E' : ParallelFrame ι V}
    (h : ∀ i t, E.vec i t = E'.vec i t) :
    E = E' := by
  cases E with
  | mk f =>
      cases E' with
      | mk g =>
          have hvec : f = g := by
            funext i t
            exact h i t
          simp [hvec]

theorem parallelFrame_ext_iff
    {ι : Type*} {V : Type u} {E E' : ParallelFrame ι V} :
    E = E' ↔ ∀ i t, E.vec i t = E'.vec i t := by
  constructor
  · intro h i t
    simp [h]
  · intro h
    exact parallelFrame_ext h

theorem frameOfTransport_initial
    {ι : Type*} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {nablaT : AlongDerivative V}
    (T : TransportOperator V) (e₀ : ι → V)
    (hT : IsTransportOperator nablaT T) (i : ι) :
    (frameOfTransport T e₀).vec i 0 = e₀ i := by
  simpa [frameOfTransport] using (hT.2.2 (e₀ i)).1

theorem frameOfTransport_isParallel
    {ι : Type*} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {nablaT : AlongDerivative V}
    (T : TransportOperator V) (e₀ : ι → V)
    (hT : IsTransportOperator nablaT T) (i : ι) :
    IsParallelAlong nablaT ((frameOfTransport T e₀).vec i) := by
  simpa [frameOfTransport] using (hT.2.2 (e₀ i)).2.1

/-- Every time slice of the frame is orthonormal on the stated time domain.

This remains a coordinate/trivialized notion: the fiber type `V` is fixed. -/
def IsOrthonormalFrame
    {ι : Type*} {V : Type u}
    (g : PairingAlong V) (δ : ι → ι → ℝ) (s : Set ℝ) (E : ParallelFrame ι V) : Prop :=
  ∀ i j t, t ∈ s → g t (E.vec i t) (E.vec j t) = δ i j

theorem isOrthonormalFrame_iff
    {ι : Type*} {V : Type u}
    {g : PairingAlong V} {δ : ι → ι → ℝ} {s : Set ℝ} {E : ParallelFrame ι V} :
    IsOrthonormalFrame g δ s E ↔
      ∀ i j t, t ∈ s → g t (E.vec i t) (E.vec j t) = δ i j :=
  Iff.rfl

theorem isOrthonormalFrame_of_transport
    {ι : Type*} {V : Type u}
    {g : PairingAlong V} {δ : ι → ι → ℝ}
    (T : TransportOperator V) (e₀ : ι → V)
    (hT : PreservesPairing g T)
    (h₀ : ∀ i j, g 0 (e₀ i) (e₀ j) = δ i j) :
    IsOrthonormalFrame g δ (transportDomain T) (frameOfTransport T e₀) := by
  intro i j t ht
  simpa [frameOfTransport] using (hT.2 (e₀ i) (e₀ j) t ht).trans (h₀ i j)

theorem isOrthonormalFrame_at_zero_of_initial
    {ι : Type*} {V : Type u}
    {g : PairingAlong V} {δ : ι → ι → ℝ} {s : Set ℝ} {E : ParallelFrame ι V}
    (h0 : 0 ∈ s)
    (hE : IsOrthonormalFrame g δ s E) :
    ∀ i j, g 0 (E.vec i 0) (E.vec j 0) = δ i j := by
  intro i j
  exact hE i j 0 h0

section Coordinate

variable {n : ℕ}

/-- The transported coordinate basis along the chosen curve in the fixed trivialized fiber `ℝ^n`. -/
noncomputable def coordinateParallelFrame
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j) :
    ParallelFrame (Fin n) (CoordinateVector n) :=
  frameOfTransport (coordinateParallelTransport A hAcont) coordinateBasisVector

@[simp] theorem coordinateParallelFrame_apply
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (i : Fin n) (t : ℝ) :
    (coordinateParallelFrame A hAcont).vec i t =
      coordinateParallelTransport A hAcont (coordinateBasisVector i) t :=
  rfl

theorem coordinateParallelFrame_initial
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (i : Fin n) :
    (coordinateParallelFrame A hAcont).vec i 0 = coordinateBasisVector i := by
  simpa [coordinateParallelFrame] using
    (frameOfTransport_initial
      (T := coordinateParallelTransport A hAcont)
      (e₀ := coordinateBasisVector)
      (nablaT := coordinateParallelAlongDerivative A hAcont)
      (hT := coordinateParallelTransport_isTransportOperator A hAcont) i)

theorem coordinateParallelFrame_isParallel
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (i : Fin n) :
    IsParallelAlong (coordinateParallelAlongDerivative A hAcont)
      ((coordinateParallelFrame A hAcont).vec i) := by
  simpa [coordinateParallelFrame] using
    (frameOfTransport_isParallel
      (T := coordinateParallelTransport A hAcont)
      (e₀ := coordinateBasisVector)
      (nablaT := coordinateParallelAlongDerivative A hAcont)
      (hT := coordinateParallelTransport_isTransportOperator A hAcont) i)

theorem coordinateParallelFrame_isOrthonormal
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hAcont : ∀ i j, Continuous fun t => A t i j)
    (g dg : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hgcont : ∀ i j, Continuous fun t => g t i j)
    (hdg : ∀ t i j, HasDerivAt (fun s => g s i j) (dg t i j) t)
    (hcompat :
      ∀ t ∈ Set.Ioo (-(coordinateTransportData A hAcont).ε)
          (coordinateTransportData A hAcont).ε,
        dg t = Matrix.transpose (A t) * g t + g t * A t)
    (δ : Fin n → Fin n → ℝ)
    (h₀ : ∀ i j,
      coordinatePairing g 0 (coordinateBasisVector i) (coordinateBasisVector j) = δ i j) :
    IsOrthonormalFrame (coordinatePairing g) δ
      (transportDomain (coordinateParallelTransport A hAcont))
      (coordinateParallelFrame A hAcont) := by
  refine isOrthonormalFrame_of_transport
    (T := coordinateParallelTransport A hAcont)
    (e₀ := coordinateBasisVector)
    (hT := coordinateParallelTransport_preservesPairing A hAcont g dg hgcont hdg hcompat)
    h₀

end Coordinate

end ParallelTransport
