import ODE.Linearized

/-! # Global linearised CLM (no smallness hypothesis)

Extends the short-time linearised solution from `ODE/Linearized.lean` to the full interval
by piecewise extension with overlap uniqueness. -/

namespace ODE.Autonomous

open Set Metric Real Filter NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## Piecewise extension of linearised solutions -/

set_option maxHeartbeats 8000000 in
/-- Extend a `LinearizedSolutionData` from half-width `T'` to `T' + δ`.

The proof:
1. Build local solutions at the forward and backward endpoints.
2. Prove overlap agreement by ODE uniqueness.
3. Define the 3-piece function.
4. Prove `HasDerivWithinAt` using `EventuallyEq` at interior points and `.union` at junctions.
5. Derive `ContinuousOn` from `HasDerivWithinAt.continuousWithinAt`. -/
theorem linearizedSolutionData_extend
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ}
    (hAcont : ContinuousOn A (Icc (t₀ - T) (t₀ + T)))
    {M : ℝ≥0}
    (hAbnd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖A t‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ) (hMδ : (↑M : ℝ) * δ ≤ 1 / 2)
    {T' : ℝ} (hT' : 0 ≤ T') (hext : T' + δ ≤ T)
    {v : E}
    (J : LinearizedSolutionData A t₀ T' v) :
    Nonempty (LinearizedSolutionData A t₀ (T' + δ) v) := by
  -- Build endpoint local solutions
  have hTδ := hext  -- T' + δ ≤ T
  have hsub_fwd : Icc ((t₀ + T') - δ) ((t₀ + T') + δ) ⊆ Icc (t₀ - T) (t₀ + T) :=
    Icc_subset_Icc (by linarith [hT', hTδ]) (by linarith [hTδ])
  have hsub_bwd : Icc ((t₀ - T') - δ) ((t₀ - T') + δ) ⊆ Icc (t₀ - T) (t₀ + T) :=
    Icc_subset_Icc (by linarith [hTδ]) (by linarith [hT', hTδ])
  obtain ⟨S_fwd⟩ := exists_linearizedSolutionData_on_sub hAcont hAbnd hδ hMδ hsub_fwd (J.sol (t₀ + T'))
  obtain ⟨S_bwd⟩ := exists_linearizedSolutionData_on_sub hAcont hAbnd hδ hMδ hsub_bwd (J.sol (t₀ - T'))
  -- Use T' + δ directly instead of aliasing (T' + δ) (avoids linarith opacity issues)
  -- Lipschitz for uniqueness
  have hAlip : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith M (A t : E → E) univ := by
    intro t ht; exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hAbnd t ht)).lipschitzOnWith
  -- Junction agreement: from the initial conditions of S_fwd and S_bwd
  -- S_fwd.initial : S_fwd.sol(t₀+T') = J.sol(t₀+T')
  -- S_bwd.initial : S_bwd.sol(t₀-T') = J.sol(t₀-T')
  -- 3-piece function
  set sol' : ℝ → E := fun s =>
    if s < t₀ - T' then S_bwd.sol s
    else if s ≤ t₀ + T' then J.sol s
    else S_fwd.sol s
  -- Agreement
  have eqB : ∀ s, s < t₀ - T' → sol' s = S_bwd.sol s := fun s h => by
    show (if s < t₀ - T' then _ else _) = _; simp [h]
  have eqM : ∀ s, t₀ - T' ≤ s → s ≤ t₀ + T' → sol' s = J.sol s := fun s h1 h2 => by
    show (if s < t₀ - T' then _ else if s ≤ t₀ + T' then _ else _) = _
    simp [show ¬(s < t₀ - T') from not_lt.mpr h1, h2]
  have eqF : ∀ s, t₀ + T' < s → sol' s = S_fwd.sol s := fun s h => by
    show (if s < t₀ - T' then _ else if s ≤ t₀ + T' then _ else _) = _
    simp [show ¬(s < t₀ - T') from by linarith, show ¬(s ≤ t₀ + T') from not_le.mpr h]
  -- Junction values (from initial conditions of local solutions)
  have hjF : J.sol (t₀ + T') = S_fwd.sol (t₀ + T') := S_fwd.initial.symm
  have hjB : J.sol (t₀ - T') = S_bwd.sol (t₀ - T') := S_bwd.initial.symm
  -- Initial
  have hsol_init : sol' t₀ = v := by rw [eqM t₀ (by linarith) (by linarith), J.initial]
  -- HasDerivWithinAt at each point (5 cases)
  -- Interior: use EventuallyEq.hasDerivWithinAt_iff with nhds filter from Iio/Ioo/Ioi_mem_nhds
  -- Junction: use HasDerivWithinAt.union on Iic ∩ Icc and Ici ∩ Icc, with congr from overlap
  -- Subset helpers for .mono
  have hBwd_sub_ext : Icc ((t₀ - T') - δ) ((t₀ - T') + δ) ⊆ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) := by
    apply Icc_subset_Icc <;> linarith [hT']
  have hJ_sub_ext : Icc (t₀ - T') (t₀ + T') ⊆ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) := by
    apply Icc_subset_Icc <;> linarith [hδ.le]
  have hFwd_sub_ext : Icc ((t₀ + T') - δ) ((t₀ + T') + δ) ⊆ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) := by
    apply Icc_subset_Icc <;> linarith [hT']
  have hIic_bwd_sub : Iic (t₀ - T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) ⊆
      Icc ((t₀ - T') - δ) ((t₀ - T') + δ) := by
    intro x ⟨hx1, hx2⟩; constructor
    · -- (t₀ - T') - δ ≤ x from t₀ - (T' + δ) ≤ x
      have h := hx2.1
      show (t₀ - T') - δ ≤ x
      linarith
    · -- x ≤ (t₀ - T') + δ from x ≤ t₀ - T' and δ ≥ 0
      show x ≤ (t₀ - T') + δ
      have : x ≤ t₀ - T' := hx1
      linarith [hδ.le]
  -- Note: The junction proofs use HasDerivWithinAt.congr_set to handle the mismatch between
  -- J's domain [t₀-T', t₀+T'] and the intersection Ici/Iic ∩ Icc that extends beyond it.
  -- At the junction point, nhdsWithin on both sets generates the same one-sided filter.
  -- Union identity
  have hIcc_union (c : ℝ) : Iic c ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) ∪
      Ici c ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) = Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro h; by_cases hxc : x ≤ c <;> [left; right] <;> exact ⟨by linarith, h⟩
  -- Forward junction subset helper
  have hIci_fwd_sub : Ici (t₀ + T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) ⊆
      Icc ((t₀ + T') - δ) ((t₀ + T') + δ) := by
    intro x ⟨hx1, hx2⟩
    simp only [mem_Ici] at hx1
    exact ⟨by linarith, by linarith [hx2.2]⟩
  have hsol_solves : ∀ s ∈ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)),
      HasDerivWithinAt sol' (A s (sol' s)) (Icc (t₀ - (T' + δ)) (t₀ + (T' + δ))) s := by
    intro s hs
    by_cases h1 : s < t₀ - T'
    · -- Case 1: Interior backward — sol' = S_bwd.sol near s; extend from Icc bwd_local to Icc ext via mono_of_mem
      rw [eqB s h1]
      have hbwd : HasDerivWithinAt S_bwd.sol (A s (S_bwd.sol s))
          (Icc ((t₀ - T') - δ) ((t₀ - T') + δ)) s :=
        S_bwd.solves s ⟨by linarith [hs.1], by linarith⟩
      exact ((Filter.EventuallyEq.hasDerivWithinAt_iff
        ((Filter.eventually_of_mem (Iio_mem_nhds h1) (fun x hx => eqB x hx)).filter_mono
          nhdsWithin_le_nhds) (eqB s h1)).mpr
        (HasDerivWithinAt.mono_of_mem_nhdsWithin hbwd
          (Filter.mem_of_superset
            (inter_mem_nhdsWithin _ (Iio_mem_nhds h1))
            (fun x ⟨hx1, hx2⟩ => ⟨by linarith [hx1.1], by linarith [mem_Iio.mp hx2]⟩))))
    · push_neg at h1
      by_cases h2 : s = t₀ - T'
      · -- Case 2: Backward junction — union of Iic and Ici halves
        subst h2; rw [eqM _ le_rfl (by linarith)]
        -- Set identities: Iic c ∩ Icc ext = Icc ext_lo c, Ici c ∩ Icc ext = Icc c ext_hi
        have hIic_eq : Iic (t₀ - T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) =
            Icc (t₀ - (T' + δ)) (t₀ - T') := by
          ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
          exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, by linarith [hT', hδ.le]⟩⟩
        have hIci_eq : Ici (t₀ - T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) =
            Icc (t₀ - T') (t₀ + (T' + δ)) := by
          ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
          exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, by linarith [hT', hδ.le], h2⟩⟩
        have hsolB : sol' (t₀ - T') = S_bwd.sol (t₀ - T') :=
          (eqM _ le_rfl (by linarith)).trans hjB
        -- Left half: S_bwd on Icc(ext_lo, t₀-T')
        have hleft : HasDerivWithinAt sol' (A (t₀ - T') (J.sol (t₀ - T')))
            (Iic (t₀ - T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ))) (t₀ - T') := by
          rw [hIic_eq, hjB]
          refine ((S_bwd.solves (t₀ - T') ⟨by linarith, by linarith⟩).mono
              (Icc_subset_Icc (by linarith) (by linarith))).congr (fun x hx => ?_) hsolB
          simp only [mem_Icc] at hx
          rcases lt_or_eq_of_le hx.2 with hxlt | hxeq
          · exact eqB x hxlt
          · rw [hxeq]; exact hsolB
        -- Right half: J (with congr_set) or S_fwd when T' = 0
        have hright : HasDerivWithinAt sol' (A (t₀ - T') (J.sol (t₀ - T')))
            (Ici (t₀ - T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ))) (t₀ - T') := by
          rw [hIci_eq]
          by_cases hT'pos : T' = 0
          · -- T' = 0: use S_fwd directly
            subst hT'pos; simp only [sub_zero, add_zero, zero_add] at hjF hjB eqM eqF eqB hsolB ⊢
            rw [hjF]
            have hS := S_fwd.solves t₀ ⟨by linarith, by linarith⟩
            simp only [sub_zero, add_zero] at hS
            refine (hS.mono (Icc_subset_Icc (by linarith) le_rfl)).congr (fun x hx => ?_) ?_
            · simp only [mem_Icc] at hx
              rcases eq_or_lt_of_le hx.1 with hxeq | hxgt
              · rw [← hxeq]; exact (eqM t₀ le_rfl le_rfl).trans hjF
              · exact eqF x hxgt
            · exact (eqM t₀ le_rfl le_rfl).trans hjF
          · -- T' > 0: J.solves + congr + congr_set to enlarge
            have hT'pos' : 0 < T' := lt_of_le_of_ne hT' (Ne.symm hT'pos)
            have hsolJ : sol' (t₀ - T') = J.sol (t₀ - T') := eqM _ le_rfl (by linarith)
            have hJ' : HasDerivWithinAt sol' (A (t₀ - T') (J.sol (t₀ - T')))
                (Icc (t₀ - T') (t₀ + T')) (t₀ - T') :=
              (J.solves (t₀ - T') ⟨le_rfl, by linarith⟩).congr
                (fun x hx => eqM x hx.1 hx.2) hsolJ
            exact hJ'.congr_set (Eventually.set_eq (Filter.eventually_of_mem
              (Ioo_mem_nhds (by linarith : (t₀ - T') - δ < t₀ - T')
                (by linarith : t₀ - T' < t₀ + T'))
              (fun x hx => by
                rw [mem_Ioo] at hx; simp only [mem_Icc]
                exact ⟨fun ⟨h1, _⟩ => ⟨h1, by linarith⟩,
                       fun ⟨h1, _⟩ => ⟨h1, by linarith⟩⟩)))
        rw [← hIcc_union (t₀ - T')]; exact hleft.union hright
      · have h3 : t₀ - T' < s := lt_of_le_of_ne h1 (Ne.symm h2)
        by_cases h4 : s ≤ t₀ + T'
        · by_cases h5 : s = t₀ + T'
          · -- Case 4: Forward junction — union of Iic and Ici halves
            subst h5; rw [eqM _ (by linarith) le_rfl]
            -- Set identities
            have hIic_eq : Iic (t₀ + T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) =
                Icc (t₀ - (T' + δ)) (t₀ + T') := by
              ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
              exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, by linarith [hT', hδ.le]⟩⟩
            have hIci_eq : Ici (t₀ + T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) =
                Icc (t₀ + T') (t₀ + (T' + δ)) := by
              ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
              exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, by linarith [hT', hδ.le], h2⟩⟩
            have hsolF : sol' (t₀ + T') = S_fwd.sol (t₀ + T') :=
              (eqM _ (by linarith) le_rfl).trans hjF
            -- Left half: J (with congr_set) or S_bwd when T' = 0
            have hleft : HasDerivWithinAt sol' (A (t₀ + T') (J.sol (t₀ + T')))
                (Iic (t₀ + T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ))) (t₀ + T') := by
              rw [hIic_eq]
              by_cases hT'pos : T' = 0
              · -- T' = 0: use S_bwd directly
                subst hT'pos; simp only [sub_zero, add_zero, zero_add] at hjF hjB eqM eqB eqF hsolF ⊢
                rw [hjB]
                have hS := S_bwd.solves t₀ ⟨by linarith, by linarith⟩
                simp only [sub_zero, add_zero] at hS
                refine (hS.mono (Icc_subset_Icc le_rfl (by linarith))).congr (fun x hx => ?_) ?_
                · simp only [mem_Icc] at hx
                  rcases lt_or_eq_of_le hx.2 with hxlt | hxeq
                  · exact eqB x hxlt
                  · rw [hxeq]; exact (eqM t₀ le_rfl le_rfl).trans hjB
                · exact (eqM t₀ le_rfl le_rfl).trans hjB
              · -- T' > 0: J.solves + congr + congr_set to enlarge
                have hT'pos' : 0 < T' := lt_of_le_of_ne hT' (Ne.symm hT'pos)
                have hsolJ : sol' (t₀ + T') = J.sol (t₀ + T') := eqM _ (by linarith) le_rfl
                have hJ' : HasDerivWithinAt sol' (A (t₀ + T') (J.sol (t₀ + T')))
                    (Icc (t₀ - T') (t₀ + T')) (t₀ + T') :=
                  (J.solves (t₀ + T') ⟨by linarith, le_rfl⟩).congr
                    (fun x hx => eqM x hx.1 hx.2) hsolJ
                exact hJ'.congr_set (Eventually.set_eq (Filter.eventually_of_mem
                  (Ioo_mem_nhds (by linarith : t₀ - T' < t₀ + T')
                    (by linarith : t₀ + T' < (t₀ + T') + δ))
                  (fun x hx => by
                    rw [mem_Ioo] at hx; simp only [mem_Icc]
                    exact ⟨fun ⟨_, h2⟩ => ⟨by linarith, h2⟩,
                           fun ⟨_, h2⟩ => ⟨by linarith, h2⟩⟩)))
            -- Right half: S_fwd on Icc(t₀+T', ext_hi)
            have hright : HasDerivWithinAt sol' (A (t₀ + T') (J.sol (t₀ + T')))
                (Ici (t₀ + T') ∩ Icc (t₀ - (T' + δ)) (t₀ + (T' + δ))) (t₀ + T') := by
              rw [hIci_eq, hjF]
              refine ((S_fwd.solves (t₀ + T') ⟨by linarith, by linarith⟩).mono
                  (Icc_subset_Icc (by linarith) (by linarith))).congr (fun x hx => ?_) hsolF
              simp only [mem_Icc] at hx
              rcases eq_or_lt_of_le hx.1 with hxeq | hxgt
              · rw [← hxeq]; exact hsolF
              · exact eqF x hxgt
            rw [← hIcc_union (t₀ + T')]; exact hleft.union hright
          · -- Case 3: Interior middle — s strictly interior to J's domain; use HasDerivAt
            have h6 : s < t₀ + T' := lt_of_le_of_ne h4 h5
            rw [eqM s h1 h4]
            have hJ_at : HasDerivAt J.sol (A s (J.sol s)) s :=
              (J.solves s ⟨h1, h4⟩).hasDerivAt (Icc_mem_nhds h3 h6)
            exact ((Filter.EventuallyEq.hasDerivWithinAt_iff
              ((Filter.eventually_of_mem (Ioo_mem_nhds h3 h6)
                (fun x ⟨hx1, hx2⟩ => eqM x hx1.le hx2.le)).filter_mono nhdsWithin_le_nhds)
              (eqM s h1 h4)).mpr hJ_at.hasDerivWithinAt)
        · -- Case 5: Interior forward — split at strict interior vs right endpoint
          push_neg at h4
          rw [eqF s h4]
          -- If s is strictly inside S_fwd's domain, use HasDerivAt; otherwise use mono
          by_cases h7 : s < (t₀ + T') + δ
          · -- s strictly interior to S_fwd domain
            have hFwd_at : HasDerivAt S_fwd.sol (A s (S_fwd.sol s)) s :=
              (S_fwd.solves s ⟨by linarith [h4], by linarith [h7]⟩).hasDerivAt
                (Icc_mem_nhds (by linarith [h4]) h7)
            exact ((Filter.EventuallyEq.hasDerivWithinAt_iff
              ((Filter.eventually_of_mem (Ioi_mem_nhds h4)
                (fun x hx => eqF x hx)).filter_mono nhdsWithin_le_nhds)
              (eqF s h4)).mpr hFwd_at.hasDerivWithinAt)
          · -- s = right endpoint (t₀+T')+δ; congr_set since both domains agree near s
            push_neg at h7
            have hs_eq : s = (t₀ + T') + δ := le_antisymm (by linarith [hs.2]) h7
            have hS : HasDerivWithinAt S_fwd.sol (A s (S_fwd.sol s))
                (Icc ((t₀ + T') - δ) ((t₀ + T') + δ)) s :=
              S_fwd.solves s ⟨by linarith [h4], by linarith [hs.2]⟩
            -- Near s = t₀+T'+δ, both Icc domains agree (lower bound doesn't matter near s)
            have hsetEq : Icc ((t₀ + T') - δ) ((t₀ + T') + δ) =ᶠ[𝓝 s]
                Icc (t₀ - (T' + δ)) (t₀ + (T' + δ)) :=
              Eventually.set_eq
                (Filter.eventually_of_mem
                  (Ioo_mem_nhds h4 (show s < s + δ from by linarith [hδ]))
                  (fun x hx => by
                    simp only [mem_Icc]
                    constructor
                    · rintro ⟨_, h_hi⟩
                      exact ⟨by linarith [hx.1, hT', hδ.le], by linarith [h_hi]⟩
                    · rintro ⟨_, h_hi⟩
                      exact ⟨by linarith [hx.1, hδ.le], by linarith [h_hi]⟩))
            exact ((Filter.EventuallyEq.hasDerivWithinAt_iff
              ((Filter.eventually_of_mem (Ioi_mem_nhds h4)
                (fun x hx => eqF x hx)).filter_mono nhdsWithin_le_nhds)
              (eqF s h4)).mpr (hS.congr_set hsetEq))
  have hsol_cont : ContinuousOn sol' (Icc (t₀ - (T' + δ)) (t₀ + (T' + δ))) :=
    fun s hs => (hsol_solves s hs).continuousWithinAt
  exact ⟨{ sol := sol', initial := hsol_init, solves := hsol_solves, continuousOn := hsol_cont }⟩

/-! ## Global existence and CLM -/

set_option maxHeartbeats 6400000 in
theorem exists_linearizedSolution_clm_on_Icc
    {A : ℝ → E →L[ℝ] E} {t₀ T : ℝ}
    (hT : 0 < T)
    (hAcont : ContinuousOn A (Icc (t₀ - T) (t₀ + T)))
    {M : ℝ≥0}
    (hAbnd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖A t‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    ∃ (J : ∀ v : E, LinearizedSolutionData A t₀ T v)
      (L : E →L[ℝ] E), ∀ v : E, L v = (J v).sol t := by
  classical
  set δ : ℝ := min T (1 / (2 * ↑M + 1))
  have hδ_pos : 0 < δ := lt_min hT (by positivity)
  have hδ_le_T : δ ≤ T := min_le_left _ _
  have hMδ : (↑M : ℝ) * δ ≤ 1 / 2 := by
    calc (↑M : ℝ) * δ ≤ ↑M * (1 / (2 * ↑M + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (NNReal.coe_nonneg M)
      _ ≤ 1 / 2 := by
          rw [show (↑M : ℝ) * (1 / (2 * ↑M + 1)) = ↑M / (2 * ↑M + 1) from by ring]
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ↑M + 1)]; linarith
  have hexists : ∀ v : E, Nonempty (LinearizedSolutionData A t₀ T v) := by
    intro v
    have hδT : (δ : ℝ) ≤ T := hδ_le_T
    have hsub₀ : Icc (t₀ - δ) (t₀ + δ) ⊆ Icc (t₀ - T) (t₀ + T) := by
      apply Icc_subset_Icc <;> linarith [hδT]
    obtain ⟨S₀⟩ := exists_linearizedSolutionData_on_sub hAcont hAbnd hδ_pos hMδ hsub₀ v
    set N := Nat.ceil (T / δ)
    suffices ∀ k : ℕ, Nonempty (LinearizedSolutionData A t₀ (min ((↑k + 1) * δ) T) v) by
      have hNδ : T ≤ (↑N + 1) * δ := by
        have h1 : T / δ ≤ ↑N := Nat.le_ceil (T / δ)
        have h2 : T ≤ ↑N * δ := (div_le_iff₀ hδ_pos).mp h1
        linarith [show (↑N + 1) * δ = ↑N * δ + δ from by ring]
      have := this N; rwa [min_eq_right hNδ] at this
    intro k
    induction k with
    | zero => simp only [Nat.cast_zero, zero_add, one_mul]; rw [min_eq_left hδ_le_T]; exact ⟨S₀⟩
    | succ n ih =>
      obtain ⟨Jn⟩ := ih
      by_cases hcap : T ≤ (↑n + 1) * δ
      · rw [min_eq_right hcap] at Jn
        rw [show min ((↑(n + 1) + 1) * δ) T = T from by
          rw [show (↑(n + 1) : ℝ) + 1 = ↑n + 2 from by push_cast; ring]
          exact min_eq_right (le_trans hcap (by nlinarith [hδ_pos]))]
        exact ⟨Jn⟩
      · push_neg at hcap; rw [min_eq_left hcap.le] at Jn
        by_cases h_next : (↑n + 2) * δ ≤ T
        · rw [show min ((↑(n + 1) + 1) * δ) T = (↑n + 1) * δ + δ from by
            rw [show (↑(n + 1) : ℝ) + 1 = ↑n + 2 from by push_cast; ring]
            rw [min_eq_left h_next, show (↑n + 2) * δ = (↑n + 1) * δ + δ from by ring]]
          exact linearizedSolutionData_extend hAcont hAbnd hδ_pos hMδ (by positivity) (by linarith) Jn
        · push_neg at h_next
          set δ' := T - (↑n + 1) * δ with hδ'_def
          rw [show min ((↑(n + 1) + 1) * δ) T = T from by
            rw [show (↑(n + 1) : ℝ) + 1 = ↑n + 2 from by push_cast; ring]
            exact min_eq_right h_next.le]
          rw [show T = (↑n + 1) * δ + δ' from by simp [hδ'_def]]
          exact linearizedSolutionData_extend hAcont hAbnd (by linarith : 0 < δ')
            (le_trans (mul_le_mul_of_nonneg_left (show δ' ≤ δ from by linarith)
              (NNReal.coe_nonneg M)) hMδ) (by positivity) (by linarith) Jn
  let J : ∀ v : E, LinearizedSolutionData A t₀ T v := fun v => Classical.choice (hexists v)
  have hAlip : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith M (A s : E → E) univ := by
    intro s hs; exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hAbnd s hs)).lipschitzOnWith
  let Llin : E →ₗ[ℝ] E :=
    { toFun := fun v => (J v).sol t
      map_add' := fun v₁ v₂ => by
        simpa using linearizedSolution_add_eq (J v₁) (J v₂) hT hAlip (J (v₁ + v₂)) t ht
      map_smul' := fun c v => by
        simpa using linearizedSolution_smul_eq (J v) hT hAlip (J (c • v)) t ht }
  let C : ℝ≥0 := ⟨exp (M * T), by positivity⟩
  refine ⟨J, Llin.mkContinuous C (fun v => by
    simpa [Llin, C, mul_comm] using linearizedSolution_norm_le (J v) hT hAbnd ht), ?_⟩
  intro v; rfl

end ODE.Autonomous
