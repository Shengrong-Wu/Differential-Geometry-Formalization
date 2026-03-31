import SecondBianchi.SecondBianchi

namespace SecondBianchi

universe u v w x y

/--
A `ComponentProjection` packages the operation of reading off the coefficient
of a chosen component from a degree-3 form.

In the intended geometric application, `Index` is a tuple of local frame
indices such as `(a, b, c, i, j)`, and `proj ω idx` is the coefficient of
`θ^a ∧ θ^b ∧ θ^c ⊗ e_i ⊗ e^j` in the 3-form `ω`.

The bridge from the invariant theorem `d_∇ Ω = 0` to the indexed statement
`∇_[a] R_{bc]}{}^i{}_j = 0` is then:

1. define a projection extracting the relevant local coefficient;
2. prove that, for the curvature 3-form, that coefficient is the cyclic
   covariant derivative of the curvature components;
3. apply `second_bianchi_in_components`.
-/
structure ComponentProjection (A : LocalConnectionAlgebra) (Index : Type x)
    (Coeff : Type y) [Zero Coeff] where
  proj : A.Ω3 → Index → Coeff
  proj_zero : ∀ idx, proj 0 idx = 0

theorem second_bianchi_through
    (A : LocalConnectionAlgebra) (conn : ConnectionForm A)
    {β : Type x} [Zero β] (φ : A.Ω3 → β) (hφ0 : φ 0 = 0) :
    φ (covariantExterior A conn (curvature A conn)) = 0 := by
  rw [second_bianchi_identity, hφ0]

theorem second_bianchi_in_components
    (A : LocalConnectionAlgebra) (conn : ConnectionForm A)
    {Index : Type x} {Coeff : Type y} [Zero Coeff]
    (P : ComponentProjection A Index Coeff) :
    ∀ idx, P.proj (covariantExterior A conn (curvature A conn)) idx = 0 := by
  intro idx
  exact second_bianchi_through A conn (fun ω => P.proj ω idx) (P.proj_zero idx)

/--
This is the theorem you ultimately want to instantiate.

To use it for the classical indexed second Bianchi identity, prove a lemma of
the shape

`P.proj (covariantExterior A conn (curvature A conn)) (a, b, c, i, j)
    = ∇_[a] R_{bc]}{}^i{}_j`

for your chosen local frame/coframe representation. The vanishing conclusion
then follows immediately from `second_bianchi_in_components`.
-/
theorem indexed_second_bianchi
    (A : LocalConnectionAlgebra) (conn : ConnectionForm A)
    {Index : Type x} {Coeff : Type y} [Zero Coeff]
    (P : ComponentProjection A Index Coeff)
    (cyclicCovDerivCurvature : Index → Coeff)
    (hcomponents :
      ∀ idx,
        P.proj (covariantExterior A conn (curvature A conn)) idx =
          cyclicCovDerivCurvature idx) :
    ∀ idx, cyclicCovDerivCurvature idx = 0 := by
  intro idx
  rw [← hcomponents idx]
  exact second_bianchi_in_components A conn P idx

end SecondBianchi
