import LeviCivita.LocalExistence

namespace LeviCivita

universe u v

theorem existsUnique_of_exists_koszul
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S] [Sub S] [OfNat S 2] [SMul S S]
    {g : MetricPairing V S} {C : ConnectionContext V S}
    (hg : MetricExtensional g)
    (hcancel : ∀ a b : S, (2 : S) • a = (2 : S) • b → a = b)
    (hex : ∃ nabla : CovariantDerivative V S C, KoszulFormula g C nabla) :
    ∃! nabla : CovariantDerivative V S C, KoszulFormula g C nabla := by
  rcases hex with ⟨nabla, hnabla⟩
  refine ⟨nabla, hnabla, ?_⟩
  intro nabla' hnabla'
  exact (eq_of_koszulFormula (nabla := nabla) (nabla' := nabla') hg hcancel hnabla hnabla').symm

theorem existsUnique_isLeviCivita
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S] [Sub S] [OfNat S 2] [SMul S S]
    {g : MetricPairing V S} {C : ConnectionContext V S}
    (hg : MetricExtensional g)
    (hcancel : ∀ a b : S, (2 : S) • a = (2 : S) • b → a = b)
    (hk : ∀ ⦃nabla : CovariantDerivative V S C⦄,
      IsLeviCivita g C nabla → KoszulFormula g C nabla)
    (hex : ∃ nabla : CovariantDerivative V S C, IsLeviCivita g C nabla) :
    ∃! nabla : CovariantDerivative V S C, IsLeviCivita g C nabla := by
  rcases hex with ⟨nabla, hnabla⟩
  refine ⟨nabla, hnabla, ?_⟩
  intro nabla' hnabla'
  exact (eq_of_koszulFormula
    (nabla := nabla)
    (nabla' := nabla')
    hg
    hcancel
    (hk hnabla)
    (hk hnabla')).symm

theorem existsUnique_isLeviCivita_real
    {V : Type u}
    [Add V] [Sub V] [SMul ℝ V]
    {g : MetricPairing V ℝ} {C : ConnectionContext V ℝ}
    (hg : MetricExtensional g)
    (hk : ∀ ⦃nabla : CovariantDerivative V ℝ C⦄,
      IsLeviCivita g C nabla → KoszulFormula g C nabla)
    (hex : ∃ nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla) :
    ∃! nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla := by
  exact existsUnique_isLeviCivita hg (fun _ _ h => two_smul_cancel_real h) hk hex

/-- For a symmetric, subtractive real-valued metric, the Koszul formula follows automatically
from `IsLeviCivita`, so the existence-uniqueness theorem does not require an external `hk`
proof. -/
theorem existsUnique_isLeviCivita_real_symm
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    {g : MetricPairing V ℝ} {C : ConnectionContext V ℝ}
    (hg     : MetricExtensional g)
    (hgsymm : ∀ X Y, g X Y = g Y X)
    (hgsub  : ∀ X Y Z, g (X - Y) Z = g X Z - g Y Z)
    (hex    : ∃ nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla) :
    ∃! nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla :=
  existsUnique_isLeviCivita_real hg
    (fun _nabla hn => isLeviCivita_koszulFormula_real hgsymm hgsub hn)
    hex

end LeviCivita
