import LeviCivita.Globalization

namespace LeviCivita

universe u v

noncomputable def leviCivita
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S] [Sub S] [OfNat S 2] [SMul S S]
    {g : MetricPairing V S} {C : ConnectionContext V S}
    (hg : MetricExtensional g)
    (hcancel : ∀ a b : S, (2 : S) • a = (2 : S) • b → a = b)
    (hk : ∀ ⦃nabla : CovariantDerivative V S C⦄,
      IsLeviCivita g C nabla → KoszulFormula g C nabla)
    (hex : ∃ nabla : CovariantDerivative V S C, IsLeviCivita g C nabla) :
    CovariantDerivative V S C :=
  Classical.choose (existsUnique_isLeviCivita hg hcancel hk hex)

theorem isLeviCivita_leviCivita
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S] [Sub S] [OfNat S 2] [SMul S S]
    {g : MetricPairing V S} {C : ConnectionContext V S}
    (hg : MetricExtensional g)
    (hcancel : ∀ a b : S, (2 : S) • a = (2 : S) • b → a = b)
    (hk : ∀ ⦃nabla : CovariantDerivative V S C⦄,
      IsLeviCivita g C nabla → KoszulFormula g C nabla)
    (hex : ∃ nabla : CovariantDerivative V S C, IsLeviCivita g C nabla) :
    IsLeviCivita g C (leviCivita hg hcancel hk hex) :=
  (Classical.choose_spec (existsUnique_isLeviCivita hg hcancel hk hex)).1

theorem leviCivita_unique
    {V : Type u} {S : Type v}
    [Add V] [Sub V] [SMul S V] [Add S] [Sub S] [OfNat S 2] [SMul S S]
    {g : MetricPairing V S} {C : ConnectionContext V S}
    (hg : MetricExtensional g)
    (hcancel : ∀ a b : S, (2 : S) • a = (2 : S) • b → a = b)
    (hk : ∀ ⦃nabla : CovariantDerivative V S C⦄,
      IsLeviCivita g C nabla → KoszulFormula g C nabla)
    (hex : ∃ nabla : CovariantDerivative V S C, IsLeviCivita g C nabla)
    {nabla : CovariantDerivative V S C}
    (hnabla : IsLeviCivita g C nabla) :
    leviCivita hg hcancel hk hex = nabla := by
  exact ((Classical.choose_spec (existsUnique_isLeviCivita hg hcancel hk hex)).2 nabla hnabla).symm

noncomputable def leviCivitaReal
    {V : Type u}
    [Add V] [Sub V] [SMul ℝ V]
    {g : MetricPairing V ℝ} {C : ConnectionContext V ℝ}
    (hg : MetricExtensional g)
    (hk : ∀ ⦃nabla : CovariantDerivative V ℝ C⦄,
      IsLeviCivita g C nabla → KoszulFormula g C nabla)
    (hex : ∃ nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla) :
    CovariantDerivative V ℝ C :=
  leviCivita hg (fun _ _ h => two_smul_cancel_real h) hk hex

theorem isLeviCivita_leviCivitaReal
    {V : Type u}
    [Add V] [Sub V] [SMul ℝ V]
    {g : MetricPairing V ℝ} {C : ConnectionContext V ℝ}
    (hg : MetricExtensional g)
    (hk : ∀ ⦃nabla : CovariantDerivative V ℝ C⦄,
      IsLeviCivita g C nabla → KoszulFormula g C nabla)
    (hex : ∃ nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla) :
    IsLeviCivita g C (leviCivitaReal hg hk hex) :=
  isLeviCivita_leviCivita hg (fun _ _ h => two_smul_cancel_real h) hk hex

theorem leviCivitaReal_unique
    {V : Type u}
    [Add V] [Sub V] [SMul ℝ V]
    {g : MetricPairing V ℝ} {C : ConnectionContext V ℝ}
    (hg : MetricExtensional g)
    (hk : ∀ ⦃nabla : CovariantDerivative V ℝ C⦄,
      IsLeviCivita g C nabla → KoszulFormula g C nabla)
    (hex : ∃ nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla)
    {nabla : CovariantDerivative V ℝ C}
    (hnabla : IsLeviCivita g C nabla) :
    leviCivitaReal hg hk hex = nabla := by
  exact leviCivita_unique hg (fun _ _ h => two_smul_cancel_real h) hk hex hnabla

/-!
## Levi-Civita connection for symmetric bilinear real-valued metrics

When the metric pairing `g` is symmetric (`g X Y = g Y X`) and subtractive in the first slot
(`g (X - Y) Z = g X Z - g Y Z`), the Koszul formula is a theorem rather than a hypothesis.
The three declarations below therefore need only: extensionality, symmetry, subtractivity,
and an existence witness — no separate `hk` argument.
-/

/-- Choose the Levi-Civita connection for a symmetric, subtractive real-valued metric. -/
noncomputable def leviCivitaRealSymm
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    {g : MetricPairing V ℝ} {C : ConnectionContext V ℝ}
    (hg     : MetricExtensional g)
    (hgsymm : ∀ X Y, g X Y = g Y X)
    (hgsub  : ∀ X Y Z, g (X - Y) Z = g X Z - g Y Z)
    (hex    : ∃ nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla) :
    CovariantDerivative V ℝ C :=
  Classical.choose (existsUnique_isLeviCivita_real_symm hg hgsymm hgsub hex)

theorem isLeviCivita_leviCivitaRealSymm
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    {g : MetricPairing V ℝ} {C : ConnectionContext V ℝ}
    (hg     : MetricExtensional g)
    (hgsymm : ∀ X Y, g X Y = g Y X)
    (hgsub  : ∀ X Y Z, g (X - Y) Z = g X Z - g Y Z)
    (hex    : ∃ nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla) :
    IsLeviCivita g C (leviCivitaRealSymm hg hgsymm hgsub hex) :=
  (Classical.choose_spec (existsUnique_isLeviCivita_real_symm hg hgsymm hgsub hex)).1

theorem leviCivitaRealSymm_unique
    {V : Type u} [AddCommGroup V] [Module ℝ V]
    {g : MetricPairing V ℝ} {C : ConnectionContext V ℝ}
    (hg     : MetricExtensional g)
    (hgsymm : ∀ X Y, g X Y = g Y X)
    (hgsub  : ∀ X Y Z, g (X - Y) Z = g X Z - g Y Z)
    (hex    : ∃ nabla : CovariantDerivative V ℝ C, IsLeviCivita g C nabla)
    {nabla  : CovariantDerivative V ℝ C}
    (hnabla : IsLeviCivita g C nabla) :
    leviCivitaRealSymm hg hgsymm hgsub hex = nabla :=
  ((Classical.choose_spec (existsUnique_isLeviCivita_real_symm hg hgsymm hgsub hex)).2
    nabla hnabla).symm

/-- Once the coordinate lift is known to satisfy the abstract Levi-Civita predicate, the chosen
`leviCivitaRealSymm` connection agrees with that explicit coordinate construction. -/
theorem leviCivitaRealSymm_eq_coordinateLiftOf
    {n : ℕ}
    (g : Metric.Coordinate.Tensor2 n)
    (gInv : Metric.Coordinate.InverseTensor2 n)
    (dg : Coordinate.MetricDerivative n)
    (hg : Metric.Coordinate.IsSymmetric g)
    (hpair : Metric.Coordinate.IsInversePair g gInv)
    (h_isLC :
      IsLeviCivita
        (LeviCivita.Coordinate.coordinateMetricPairing g)
        (LeviCivita.Coordinate.flatConnectionContext n)
        (LeviCivita.Coordinate.christoffelToCovariantDerivative
          (LeviCivita.Coordinate.localLeviCivitaConnection gInv dg))) :
    leviCivitaRealSymm
      (LeviCivita.Coordinate.coordinateMetricExtensional_of_inversePair g gInv hg hpair)
      (LeviCivita.Coordinate.coordinateMetricPairing_symm (g := g) hg)
      (LeviCivita.Coordinate.coordinateMetricPairing_sub_left g)
      ⟨LeviCivita.Coordinate.christoffelToCovariantDerivative
          (LeviCivita.Coordinate.localLeviCivitaConnection gInv dg), h_isLC⟩ =
    LeviCivita.Coordinate.christoffelToCovariantDerivative
      (LeviCivita.Coordinate.localLeviCivitaConnection gInv dg) := by
  exact leviCivitaRealSymm_unique
    (LeviCivita.Coordinate.coordinateMetricExtensional_of_inversePair g gInv hg hpair)
    (LeviCivita.Coordinate.coordinateMetricPairing_symm (g := g) hg)
    (LeviCivita.Coordinate.coordinateMetricPairing_sub_left g)
    ⟨_, h_isLC⟩
    h_isLC

end LeviCivita
