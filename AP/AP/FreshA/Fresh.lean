import AP.AP.FreshA.Nbhd

namespace AP

def AStrat.Fresh (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.Fresh1 s fsp ∧ ∀ (d : DStrat), d.WF → ∀ s₁ p p',
  (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → sys.validTr s₁ p' → p' ≠ p → p' ∉ s.aVisited s₁

def AStrat.FreshAux (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aPos ∉ fsp.get 0 ∧ ∀ (d : DStrat), d.WF → ∀ n, ∃ s₁ s₂,
  sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (s₁, 0) ∧ sys.tr s₁ (a.f s₁) = some s₂ ∧
  s₂.aHwsDisj (fsp.offset (n * 2 + 1)
  |>.insertSet 0 (s.aVisited s₁ |>.bind (·.nbhd s.pw)).toSet
  |>.insertSet 2 (s₁.aPos.nbhd s.pw).toSet)

def aFreshCnd (s : State) (fsp : FSP) (s₂ : State) : Prop :=
  s₂.aHwsDisj # fsp.offset (s₂.diff s)
  |>.insertSet 0 (s.aVisited s₂.prev |>.bind (·.nbhd s.pw)).toSet
  |>.insertSet 2 (s₂.prev.aPos.nbhd s.pw).toSet

noncomputable
def aFresh (s : State) (fsp : FSP) : AStrat :=
  aSeek # aFresh1Cnd s fsp

-----

theorem AStrat.Fresh.fresh1 {a : AStrat} {s fsp} (h : a.Fresh s fsp) : a.Fresh1 s fsp := h.1
theorem AStrat.Fresh.wf {a : AStrat} {s fsp} (h : a.Fresh s fsp) : a.WF := h.fresh1.wf

theorem AStrat.fresh_iff_alt₁ {a : AStrat} {s fsp} : a.Fresh s fsp ↔
a.Fresh1 s fsp ∧ ∀ (d : DStrat), d.WF → ∀ s₁ p p',
(s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → sys.validTr s₁ p' → p' ∉ s.aVisited s₁ := by
  rw [Fresh]
  symm; use by tauto
  rintro ⟨h₁, h₂⟩
  use h₁
  intro d hd s₁ p p' h₃ h₄
  by_cases h₅ : p' ≠ p; grind
  push_neg at h₅; symm at h₅; subst h₅
  clear h₂ h₄
  rcases h₁ with ⟨ha, h₁, h₂⟩
  grind

theorem AStrat.fresh_iff_alt₂ {a : AStrat} {s fsp} [hs : sys.WF s] : a.Fresh s fsp ↔
a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF → ∀ s₁ p p',
(s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → sys.validTr s₁ p' → p' ∉ s.aVisited s₁ := by
  rw [fresh_iff_alt₁]
  constructor
  · rintro ⟨⟨ha, h₁, h₂⟩, h₃⟩; use ha, h₁
  rintro ⟨ha, h₁, h₂⟩
  refine ⟨⟨ha, h₁, ?_⟩, h₂⟩
  intro d hd s₁ p h₃ h₄
  contrapose! h₄; clear h₄
  apply h₂ d hd s₁ p p h₃; clear h₂
  exact State.validTr_of_mem_aPtsSimAt h₃

@[simp]
instance {s fsp} : aFresh s fsp |>.WF := by
  unfold aFresh; infer_instance

theorem AState.aForallWinsDisj_of_freshAux {s fsp} {a : AStrat} [hs : AState s]
(h : a.FreshAux s fsp) : s.aForallWinsDisj fsp a := by
  choose ha h₀ h using h
  intro d hd n
  specialize h d hd
  induction n using Nat.mod_2_ind <;> nm n
  · cases n; simpa; nm n
    specialize h n
    simp at h
    choose s₁ h₁ s₂ h₂ h₃ using h
    have hs₁ := AState.of_simulate_mul_two_eq_full h₁
    have hs₂ := DState.of_tr h₂
    simp [Nat.add_mul, h₁, h₂]
    choose a₁ ha₁ h₃ using h₃
    specialize h₃ d hd 1
    simp at h₃
    choose s₃ h₃ h₄ using h₃
    use s₃, h₃
    simp [FSP.hasLe, FSP.insertSet] at h₄ ⊢
    intro k hk
    have h₅ := h₄ 0
    specialize h₄ 1
    simp at h₄ h₅
    choose h₅ h₆ using h₅
    rw [Nat.le_add_one_iff] at hk
    rcases hk with hk | rfl
    · exact h₆ k hk
    · exact h₄
  · specialize h n
    choose s₁ s₂ h₁ h₂ h₃ using h
    have hs₁ := AState.of_simulate_mul_two_eq_full h₁
    simp [h₁, h₂]
    replace h₃ := State.aPos_notMem_of_aHwsDisj h₃
    simp at h₃
    simp [FSP.hasLe]
    exact h₃.2

-- theorem AState.fresh_of_freshAux {s fsp} {a : AStrat} [hs : AState s]
-- (h : a.FreshAux s fsp) : a.Fresh s fsp := by
--   have H₀ := h
--   choose ha h₀ h using h
--   rw [AStrat.fresh_iff_alt₂]
--   use ha, aForallWinsDisj_of_freshAux H₀
--   intro d hd s₁ p p' h₁ ⟨s', h₁'⟩
--   rw [State.mem_aPtsSimAt_iff_simulate_tr] at h₁
--   choose hs₁ n h₁ s₂ h₂ h₃ using h₁
--   simp at h₂ h₃; subst h₃
--   obtain ⟨n, rfl⟩ := Nat.even_iff_exi.mp # even_of_simulate h₁
--   specialize h d hd n
--   simp [h₁, h₂] at h
--   rw [←AState.aPos_eq_of_tr h₁']
--   choose a₁ ha₁ h using h
--   specialize h d hd 0
--   simp at h
--   replace h := h.1
--   contrapose! h
--   -- specialize h _ H₁
--   -- contrapose! h; clear h
--   -- rw [AState.tr_eq_some_iff] at h₁' h₂
--   -- rcases h₁' with ⟨⟨H₂, H₃, H₄⟩, rfl⟩
--   -- rcases h₂ with ⟨⟨H₅, H₆, H₇⟩, rfl⟩
--   -- simp
--   -- dsimp at H₁

-- #check 0 #exit

-- theorem AState.exi_fresh1_of_aHwsDisj {s fsp} [hs : AState s]
-- (h : s.aHwsDisj fsp) : ∃ (a : AStrat), a.Fresh1 s fsp := by
--   use aFresh1 s fsp
--   apply hs.fresh1_of_fresh1Aux
--   use inferInstance
--   use State.aPos_notMem_of_aHwsDisj h
--   intro d hd n
--   induction n
--   · simp
--     have h₁ := @hs.aSeek_exi_tr_of (P := aFresh1Cnd s fsp)
--     specialize h₁ _
--     · clear h₁
--       unfold aFresh1Cnd
--       replace h := aHwsDisj_insert_one_aPos h
--       choose a₁ ha₁ h using h
--       have h₁ := h d hd 1
--       simp at h₁
--       choose s₁ h₁ h₂ using h₁
--       use a₁.f s, s₁, h₁, a₁, ha₁
--       simp [State.diff_eq_of_tr h₁, State.prev_eq_of_tr h₁]
--       intro d₁ hd₁ n
--       specialize h d₁ hd₁ (n + 1)
--       simp_rw [sys.simulate_succ_full'] at h
--       simp [h₁] at h
--       choose s₂ h h₃ using h
--       use s₂, h
--       simp [FSP.hasLe, FSP.insert, FSP.insertSet, FSP.next] at h₃ ⊢
--       grind
--     unfold aFresh1
--     choose s₂ h₁ h₂ using h₁
--     use s₂, h₁
--     unfold aFresh1Cnd at h₂
--     simp [State.diff_eq_of_tr h₁, State.prev_eq_of_tr h₁] at h₂
--     exact h₂
--   nm n ih
--   choose s₁ s₂ h₁ h₂ h₃ using ih
--   have hs₁ := AState.of_simulate_mul_two_eq' h₁
--   have hs₂ := DState.of_tr h₂
--   choose s₃ h₄ using hd.validTr s₂
--   have hs₃ := AState.of_tr h₄
--   simp [Nat.add_mul, h₁, h₂, h₄]
--   have G₁ := sys.reachable_of_simulate_eq h₁
--   have G₂ := sys.reachable_right G₁ h₂
--   have G₃ := sys.reachable_right G₂ h₄
--   have h₅ := @hs₃.aSeek_exi_tr_of (P := aFresh1Cnd s fsp)
--   specialize h₅ _
--   · clear h₅
--     unfold aFresh1Cnd
--     replace h₃ := DState.aHwsDisj_insert_two_aPos h₃
--     choose a₁ ha₁ h₃ using h₃
--     have H₁ := h₃ d hd 2
--     simp [h₄] at H₁
--     choose s₄ H₁ H₂ using H₁
--     use a₁.f s₃, s₄, H₁, a₁, ha₁
--     rw [State.diff_eq_of_tr H₁ G₃, State.diff_eq_of_tr h₄ G₂, State.diff_eq_of_tr h₂ G₁]
--     rw [State.diff_eq_of_simulate_full h₁]
--     rw [State.prev_eq_of_tr H₁, DState.aVisited_eq_of_tr h₄ G₂, AState.aVisited_eq_of_tr h₂ G₁]
--     intro d₁ hd₁ n₁
--     specialize h₃ (d₁.set s₂ # d.f s₂) (DStrat.wf_set_of_tr h₄) (n₁ + 2)
--     simp_rw [sys.simulate_succ_full'] at h₃
--     simp [h₄, H₁] at h₃
--     choose s₅ H₃ H₄ using h₃
--     use s₅
--     have hs₄ := sys.wf_of_tr H₁
--     split_ands
--     · convert H₃ using 1
--       symm
--       apply State.simulate_set_d_eq_of_length_hist_lt ⟨_, h₄⟩
--       rw [length_hist_eq_of_tr H₁, length_hist_eq_of_tr h₄]
--       omega
--     simp
--     rw [←AState.aPos_eq_of_tr h₂]
--     simp [FSP.hasLe] at H₄ ⊢
--     simp [Nat.add_assoc]
--     intro k hk
--     cases k
--     rotate_left
--     · nm k
--       specialize H₄ (k + 3) (by omega)
--       simp at H₄ ⊢
--       ring_nf at H₄ ⊢
--       exact H₄
--     simp
--     split_ands
--     · specialize H₄ 2 (by omega)
--       simp at H₄
--       exact H₄.1
--     · specialize H₄ 0 (by omega)
--       simp at H₄
--       exact H₄.1
--     · intro k hk
--       iterate 2 rw [Nat.le_add_one_iff] at hk
--       rcases hk with ((hr | rfl) | rfl)
--       · specialize H₄ 0 (by omega)
--         simp at H₄
--         exact H₄.2 k hr
--       · specialize H₄ 1 (by omega)
--         simp at H₄
--         exact H₄
--       · specialize H₄ 2 (by omega)
--         simp at H₄
--         exact H₄.2
--   choose s₄ h₅ h₆ using h₅
--   use s₄, h₅
--   unfold aFresh1Cnd at h₆
--   rw [State.diff_eq_of_tr h₅ G₃, State.diff_eq_of_tr h₄ G₂, State.diff_eq_of_tr h₂ G₁] at h₆
--   rw [State.diff_eq_of_simulate_full h₁] at h₆
--   simp [Nat.add_assoc] at h₆ ⊢
--   have hs₄ := DState.of_tr h₅
--   rw [State.prev_eq_of_tr h₅] at h₆
--   exact h₆

-- theorem State.aPtsSimAt_state_eq_of_point_eq_of_fresh1 {s : State} {a : AStrat} {d : DStrat}
-- {s₁ s₂ p fsp} [hs : sys.WF s] [hd : d.WF] (h : a.Fresh1 s fsp)
-- (h₁ : (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩) (h₂ : (s₂, p) ∈ s.aPtsSimAt ⟨a, d⟩) : s₁ = s₂ := by
--   choose ha h₃ h₄ using h
--   specialize h₄ d hd
--   have H₁ := h₄ _ _ h₁
--   have H₂ := h₄ _ _ h₂
--   clear h₄
--   rw [mem_aPtsSimAt_iff_simulate_tr] at h₁ h₂
--   choose hs₁ n₁ h₁ s₁' h₅ h₆ using h₁
--   choose hs₂ n₂ h₂ s₂' h₇ h₈ using h₂
--   simp at h₅ h₆ h₇ h₈
--   by_cases H₃ : n₁ = n₂
--   · subst H₃
--     simp [h₁] at h₂
--     exact h₂
--   exfalso
--   wlog H₄ : n₁ < n₂ with ih
--   · push_neg at H₄
--     specialize @ih s a d s₂ s₁ p fsp _ _ ha h₃
--     grind
--   clear H₃
--   apply H₂; clear H₂
--   rw [mem_aVisited_iff h₂]
--   right
--   use n₁, H₄, s₁, hs₁, h₁
--   simpa