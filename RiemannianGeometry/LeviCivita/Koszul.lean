import LeviCivita.Basic

namespace LeviCivita

universe u v

/-- The right-hand side of the Koszul formula. -/
def koszulRHS
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [Add S] [Sub S]
    (g : MetricPairing V S) (C : ConnectionContext V S) (X Y Z : V) : S :=
  C.deriv X (g Y Z)
    + C.deriv Y (g Z X)
    - C.deriv Z (g X Y)
    + g (C.bracket X Y) Z
    - g (C.bracket Y Z) X
    + g (C.bracket Z X) Y

/-- An abstract connection satisfies the Koszul formula. -/
def KoszulFormula
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S] [Sub S] [OfNat S 2] [SMul S S]
    (g : MetricPairing V S) (C : ConnectionContext V S)
    (nabla : CovariantDerivative V S C) : Prop :=
  ∀ X Y Z, (2 : S) • g (nabla X Y) Z = koszulRHS g C X Y Z

/-- Uniqueness from the Koszul formula, assuming extensionality/nondegeneracy of the metric. -/
theorem eq_of_koszulFormula
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S] [Sub S] [OfNat S 2] [SMul S S]
    {g : MetricPairing V S} {C : ConnectionContext V S}
    (hg : MetricExtensional g)
    (hcancel : ∀ a b : S, (2 : S) • a = (2 : S) • b → a = b)
    {nabla nabla' : CovariantDerivative V S C}
    (hnabla : KoszulFormula g C nabla)
    (hnabla' : KoszulFormula g C nabla') :
    nabla = nabla' := by
  cases nabla with
  | mk f hf1 hf2 hf3 hf4 =>
    cases nabla' with
    | mk f' hf1' hf2' hf3' hf4' =>
      have hfun : f = f' := by
        funext X Y
        apply hg
        intro Z
        have h1 := hnabla X Y Z
        have h2 := hnabla' X Y Z
        exact hcancel _ _ (h1.trans h2.symm)
      subst hfun
      simp

/-!
## Koszul formula from IsLeviCivita

For a real-valued metric pairing that is symmetric and subtractive in the first slot,
the Koszul formula `2 g(∇_X Y, Z) = koszulRHS` is a *consequence* of metric compatibility and
torsion-freeness. This lets downstream code drop the `hk` hypothesis.

The derivation uses three inputs:
1. Metric compatibility: X(g(Y,Z)) = g(∇_X Y, Z) + g(Y, ∇_X Z)
2. Torsion-freeness: ∇_X Y - ∇_Y X = [X,Y]
3. Symmetry of g: g(U,V) = g(V,U)

Combined, the six Koszul terms telescope into 2·g(∇_X Y, Z).
-/

/-- For real-valued metrics that are symmetric and additive in the first argument,
any Levi-Civita connection satisfies the Koszul formula. -/
theorem isLeviCivita_koszulFormula_real
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    {C : ConnectionContext V ℝ}
    {g : MetricPairing V ℝ}
    (hgsymm : ∀ X Y, g X Y = g Y X)
    (hgsub  : ∀ X Y Z, g (X - Y) Z = g X Z - g Y Z)
    {nabla : CovariantDerivative V ℝ C}
    (hlc : IsLeviCivita g C nabla) :
    KoszulFormula g C nabla := by
  intro X Y Z
  obtain ⟨hmc, htf⟩ := hlc
  unfold koszulRHS
  -- Replace Lie brackets by torsion-free differences
  have hb1 : C.bracket X Y = nabla X Y - nabla Y X := (htf X Y).symm
  have hb2 : C.bracket Y Z = nabla Y Z - nabla Z Y := (htf Y Z).symm
  have hb3 : C.bracket Z X = nabla Z X - nabla X Z := (htf Z X).symm
  rw [hb1, hb2, hb3,
      hgsub (nabla X Y) (nabla Y X) Z,
      hgsub (nabla Y Z) (nabla Z Y) X,
      hgsub (nabla Z X) (nabla X Z) Y]
  -- Expand metric-compatibility: X(g(Y,Z)) = g(∇_X Y, Z) + g(Y, ∇_X Z)
  have hmc1 := hmc X Y Z
  have hmc2 := hmc Y Z X
  have hmc3 := hmc Z X Y
  -- Symmetry: g(Y, ∇_X Z) = g(∇_X Z, Y), etc.
  have hs1 := hgsymm Y (nabla X Z)
  have hs2 := hgsymm Z (nabla Y X)
  have hs3 := hgsymm X (nabla Z Y)
  -- (2 : ℝ) • x = x + x in ℝ
  have htwo : (2 : ℝ) • g (nabla X Y) Z = g (nabla X Y) Z + g (nabla X Y) Z := two_smul ℝ _
  linarith

end LeviCivita
