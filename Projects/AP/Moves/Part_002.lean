import Projects.AP.Moves.Part_001

namespace AP

theorem AState.aNbhdsIcoPrev_eq_of_tr {s s₁ s₂ p} [hs : sys.WF s] [hs₁ : AState s₁]
(h : sys.tr s₁ p = some s₂) (h₁ : sys.Reachable s s₁) :
s.aNbhdsIcoPrev s₂ = s.aNbhdsIcoPrev s₁ ∪ if s = s₁ then ∅ else s₁.prev.aPos.nbhd (s.pw) := by
  have h₁' := h₁
  rw [sys.reachable_iff_exi_trs] at h₁
  choose ps h₁ using h₁
  simp [State.aNbhdsIcoPrev, State.aVisitedIcoPrev, State.diff_eq_of_trs_full h₁,
    State.diff_eq_of_tr h]
  induction ps using List.reverseRecOn
  · simp at h₁
    simp [h₁]
  nm ps p' ih; clear ih
  simp at h₁ ⊢
  choose s' h₁ h₂ using h₁
  have hs' : sys.WF s'; grind
  simp [State.prev_eq_of_tr h, State.prev_eq_of_tr h₂]
  simp [State.aVisitedIco]
  induction ps using List.reverseRecOn
  · simp at h₁ ⊢
    subst h₁
    split_ifs with h₃; simp
    ext p₂
    simp [State.prev_eq_of_tr h₂]
  nm ps p₂ ih; clear ih
  simp at h₁ ⊢
  choose s₀ h₁ h₃ using h₁
  have hs₀ : sys.WF s₀; grind
  have H₁ : sys.trs s (ps ++ [p₂, p']) = (s₁, []); simp_all
  have H₂ : sys.trs s (ps ++ [p₂]) = (s', []); simp_all
  have H₃ : s ≠ s₁; rintro rfl; have H₃ := State.length_hist_eq_of_trs_eq H₁; simp at H₃
  have H₄ : s ≠ s'; rintro rfl; have H₃ := State.length_hist_eq_of_trs_eq H₂; simp at H₃
  simp [H₃, H₄]; ext q
  simp [State.prev_eq_of_tr h₂, State.prev_eq_of_tr h₃]
  replace hs' : DState s'; grind
  replace hs₀ : AState s₀; grind
  have H₅ : sys.Reachable s s₀; grind
  obtain ⟨f, hf, n, H₆⟩ := sys.exi_simulate_of_reachable H₅
  rw [@aVisitedIcc_eq_of_tr s s₀ s' p₂ _ _ h₃ H₅]
  nth_rw 1 [or_comm]
  simp
  congr!
  rw [AState.aPos_eq_of_tr h₃]

theorem State.aNbhdsIcoPrev_eq_of_tr {s s₁ s₂ p} [hs : sys.WF s]
(h : sys.tr s₁ p = some s₂) (h₁ : sys.Reachable s s₁) :
s.aNbhdsIcoPrev s₂ = s.aNbhdsIcoPrev s₁ ∪ if s = s₁ then ∅ else s₁.prev.aPos.nbhd (s.pw) := by
  have hs₁ : sys.WF s₁; grind
  replace hs₁ := s₁.aState_or_dState
  rcases hs₁ with hs₁ | hs₁
  · exact AState.aNbhdsIcoPrev_eq_of_tr h h₁
  · exact DState.aNbhdsIcoPrev_eq_of_tr h h₁

@[simp]
theorem State.aNbhdsIcoPrev_self {s : State} : s.aNbhdsIcoPrev s = ∅ := by
  simp [aNbhdsIcoPrev]

@[simp]
instance init_reachable {s} [hs : sys.WF s] : sys.Reachable s.init s := by
  rw [State.wf_iff'] at hs; rw [State.init]; grind

theorem State.wf_iff {s} : sys.WF s ↔ ∃ ps, sys.trs s.init ps = (s, []) := by
  rw [sys.wf_def]; constructor
  · rintro ⟨s₀, h₁, h₂⟩
    have h₃ := h₁
    have h₄ := h₂
    rw [sys.reachable_iff_exi_trs] at h₂
    choose ps h₂ using h₂
    use ps
    rw [init]
    rw [initial_iff] at h₁
    rwa [pw_eq_of_reachable h₄, aPos₀_eq_of_reachable h₄, h₁]
  · rintro ⟨ps, h⟩
    have hs : sys.WF s; grind
    use s.init
    simp; simp [init]

theorem init_eq_of_tr {s s₁ p} [hs : sys.WF s]
(h : sys.tr s p = some s₁) : s₁.init = s.init := by
  simp [State.init, pw_eq_of_tr h, State.aPos₀_eq_of_tr h]

theorem init_eq_of_trs {s s₁ ps ps'} [hs : sys.WF s]
(h : sys.trs s ps = (s₁, ps')) : s₁.init = s.init := by
  replace h := sys.exi_trs_full_of_trs h
  choose ps₁ h₁ h₂ using h
  clear! ps
  rename' ps₁ => ps
  induction ps using List.reverseRecOn generalizing s₁
  · simp at h₂; rw [h₂]
  nm ps₁ p ih
  simp at h₂
  choose s' h₂ h₃ using h₂
  specialize ih h₂
  have hs' : sys.WF s'; grind
  grind [init_eq_of_tr h₃]

theorem init_eq_of_reachable {s s₁} [hs : sys.WF s]
(h : sys.Reachable s s₁) : s₁.init = s.init := by
  rw [sys.reachable_iff_exi_trs] at h; choose ps h using h; exact init_eq_of_trs h

@[simp]
theorem State.odd_length_hist {s} [hs : sys.WF s] : Odd s.hist.length ↔ s.aTurn = false := by
  rw [wf_iff] at hs
  choose ps h using hs
  induction ps using List.reverseRecOn generalizing s
  · simp at h; rw [←h]; simp
  nm ps p ih
  simp at h
  choose s₁ h₁ h₂ using h
  have hs₁ : sys.WF s₁; grind
  rw [init_eq_of_tr h₂] at h₁
  specialize ih h₁
  rw [length_hist_eq_of_tr h₂, aTurn_eq_of_tr h₂]
  contrapose!; simpa

@[simp]
theorem State.even_length_hist {s} [hs : sys.WF s] : Even s.hist.length ↔ s.aTurn = true := by
  contrapose!; simp

@[simp]
theorem State.odd_length_hist_sub_one {s} [hs : sys.WF s] :
Odd (s.hist.length - 1) ↔ s.aTurn = true := by
  rw [←Nat.odd_add_two, length_hist_sub_one_add]; simp

@[simp]
theorem State.even_length_hist_sub_one {s} [hs : sys.WF s] :
Even (s.hist.length - 1) ↔ s.aTurn = false := by
  rw [←Nat.even_add_two, length_hist_sub_one_add]; simp

@[simp] theorem taken_init {s : State} : s.init.taken = ∅ := rfl
@[simp] theorem aPos_init {s : State} : s.init.aPos = s.aPos₀ := rfl
@[simp] theorem hist_init {s : State} : s.init.hist = [s.aPos₀] := rfl
@[simp] theorem init_init {s : State} : s.init.init = s.init := rfl

@[simp] theorem Strat.a_ofFn {f} : (ofFn f).a = .mk f := rfl
@[simp] theorem Strat.d_ofFn {f} : (ofFn f).d = .mk f := rfl

@[simp, instance]
theorem Strat.wf_ofFn {f} : ofFn f |>.WF := by
  simp [wf_iff]

@[simp]
theorem Strat.f_ofFn {f} : (ofFn f).f = mkStratFn f := by
  ext s :1; simp [ofFn, Strat.f]

theorem State.eq_of_reachable_and_hist_eq {s s₁ s₂} (h₁ : sys.Reachable s s₁)
(h₂ : sys.Reachable s s₂) (h₃ : s₁.hist = s₂.hist) : s₁ = s₂ := by
  rw [System.reachable_iff_exi_trs] at h₁ h₂
  choose ps₁ h₁ using h₁
  choose ps₂ h₂ using h₂
  have h₄ := hist_eq_of_trs h₁
  have h₅ := hist_eq_of_trs h₂
  simp at h₄ h₅
  simp [h₃] at h₄
  simp [h₄] at h₅
  subst h₅
  simp [h₁] at h₂
  exact h₂

theorem State.eq_of_reachable_and_length_hist_eq {s s₁ s₂ s₃}
(h₁ : sys.Reachable s s₁) (h₂ : sys.Reachable s s₂) (h₃ : sys.Reachable s₁ s₃)
(h₄ : sys.Reachable s₂ s₃) (h₅ : s₁.hist.length = s₂.hist.length) : s₁ = s₂ := by
  apply eq_of_reachable_and_hist_eq h₁ h₂
  apply List.eq_of_suffix_and_length_eq (zs := s₃.hist) _ _ h₅
  · exact hist_suffix_of_reachable h₃
  · exact hist_suffix_of_reachable h₄

theorem point_eq_of_tr_eq_tr {s s' p₁ p₂} (h₁ : sys.tr s p₁ = some s')
(h₂ : sys.tr s p₂ = some s') : p₁ = p₂ := by
  have h₃ := hist_eq_of_tr h₁
  have h₄ := hist_eq_of_tr h₂
  simp [h₃] at h₄
  exact h₄

-- #check 0 #exit

-- theorem State.simulate_diffStrat {s s₁} [hs : sys.WF s] (h : sys.Reachable s s₁) :
-- sys.simulate (s.diffStrat s₁).f s (s.diff s₁) = (s₁, 0) := by
--   obtain ⟨f, hf, n, h₁⟩ := sys.reachable_iff_exi_simulate.mp h
--   obtain ⟨ps, h₂⟩ := sys.reachable_iff_exi_trs.mp h
--   
--   have hn : ps.length = n
--   ·
--     have h₃ := length_hist_eq_of_simulate_eq h₁
--     have h₄ := length_hist_eq_of_trs_eq h₂
--     grind
--   
--   generalize hg : (s.diffStrat s₁).f = g
--   
--   replace hg : ∀ ⦃s'⦄, (∃ k < n, sys.simulate f s k = (s', 0)) →
--     g s' = (s.diffTrs s₁)[s.diff s']!
--   ·
--     rintro s' ⟨k, hk, h₃⟩
--     subst hg
--     simp [diffStrat, diffTrs_eq_of_trs_full h₂, diff_eq_of_simulate_full h₃]
--     obtain ⟨ps₁, ps₂, p, H₁, rfl⟩ : ∃ (ps₁ ps₂ : List PointZ) (p : PointZ),
--       ps₁.length = k ∧ ps₁ ++ p :: ps₂ = ps
--     ·
--       use ps.take k, ps.drop (k + 1), ps[k]!
--       simp
--       use by omega
--       rw [List.ext_getElem_iff]
--       simp
--       grind
--     subst H₁
--     simp at hn ⊢
--     subst hn
--     rw [add_comm _ 1] at h₁
--     simp at h₁
--     choose sx h₁ sy h₄ h₅ using h₁
--     simp [h₃] at h₁
--     subst h₁
--     -- simp [sys.validTr_of_eq_some h₄]
--     simp at h₂
--     choose sx' h₂ sy' h₆ h₇ using h₂
--     obtain rfl : sx' = s'
--     ·
--       apply eq_of_reachable_and_length_hist_eq (s := s) (s₃ := s₁)
--       iterate 4 grind
--       rw [length_hist_eq_of_simulate_eq h₃, length_hist_eq_of_trs_eq h₂]
--       rfl
--     rename' sx' => sx
--     obtain rfl : sy = sy'
--     ·
--       apply eq_of_reachable_and_length_hist_eq (s := sx) (s₃ := s₁)
--       iterate 4 grind
--       rw [length_hist_eq_of_tr h₆, length_hist_eq_of_tr h₄]
--     obtain rfl := point_eq_of_tr_eq_tr h₄ h₆
--     simp [sys.validTr_of_eq_some h₆]
--   
--   apply And.right (a := n = 0 ∨ ∃ k < n, sys.simulate f s k = (s, 0))
--   rw [diff_eq_of_simulate_full h₁]
--   
--   induction n generalizing s ps; simp_all
--   nm n ih
--   rw [System.simulate_succ_full'] at h₁ ⊢
--   choose sx h₁ h₃ using h₁
--   simp
--   use sx
--   cases ps
--   ·
--     clear ih
--     exfalso
--     simp at h₂
--     subst h₂
--     have h₄ := sys.reachable_of_tr h₁
--     have h₅ := sys.reachable_of_simulate h₃
--     have h₆ := sys.eq_of_tree_and_reachable h₄ h₅
--     simp [h₆] at h₁
--   nm p ps
--   simp at h₂ hn
--   choose sx' h₂ h₄ using h₂
--   obtain rfl : sx = sx'
--   ·
--     apply eq_of_reachable_and_length_hist_eq (s := s) (s₃ := s₁)
--     iterate 4 grind
--     rw [length_hist_eq_of_tr h₁, length_hist_eq_of_tr h₂]
--   obtain rfl := point_eq_of_tr_eq_tr h₁ h₂
--   clear h₂
--   have hsx : sys.WF sx; grind
--   
--   specialize @ih sx _ (by grind) h₃ ps h₄ hn _
--   ·
--     clear ih
--     rintro s' ⟨k, hk, H⟩
--     sorry
--   sorry