import AP.AP.FreshA.Tile
import AP.AP.Moves

namespace AP

def AStrat.Fresh1 (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aForallWinsDisj fsp a ∧ ∀ (d : DStrat), d.WF →
  ∀ s₁ p, (s₁, p) ∈ s.aPtsSimAt ⟨a, d⟩ → p ∉ s.aVisited s₁

def AStrat.Fresh1Alt (a : AStrat) (s : State) (fsp : FSP) : Prop :=
  a.WF ∧ s.aPos ∉ fsp.get 0 ∧ ∀ (d : DStrat), d.WF → ∀ n, ∃ s₁ s₂,
  sys.simulate (Strat.f ⟨a, d⟩) s (n * 2) = (s₁, 0) ∧ sys.tr s₁ (a.f s₁) = some s₂ ∧
  s₂.aHwsDisj (fsp.offset (n * 2 + 1) |>.insertSet 0 (s.aVisited s₁).toSet)

def aFresh1Cnd (s : State) (fsp : FSP) (s₂ : State) : Prop :=
  s₂.aHwsDisj (fsp.offset (s₂.diff s) |>.insertSet 0 (s.aVisited s₂.prev).toSet)

noncomputable
def aFresh1 (s : State) (fsp : FSP) : AStrat :=
  aSeek # aFresh1Cnd s fsp

-- #check 0 #exit

-----

theorem AStrat.Fresh1.wf {a : AStrat} {s fsp} (h : a.Fresh1 s fsp) : a.WF := h.1

theorem State.false_of_aState_and_dState s [hs₁ : AState s] [hs₂ : DState s] : False := by
  have h₁ := hs₁.2; rw [hs₂.2] at h₁; simp at h₁

theorem AState.even_of_simulate {s s₁ f n} [hs : AState s] [hs₁ : AState s₁]
(h : sys.simulate f s n = (s₁, 0)) : Even n := by
  by_contra h₁; simp at h₁
  obtain ⟨n, rfl⟩ := h₁
  rw [mul_comm] at h
  have h₁ := DState.of_simulate_mul_two_add_one_eq_full h
  exact s₁.false_of_aState_and_dState

theorem AState.aSeek_exi_tr_of {s P} [hs : AState s]
(h : ∃ p s₁, sys.tr s p = some s₁ ∧ P s₁) :
∃ s₁, sys.tr s (aSeek P |>.f s) = some s₁ ∧ P s₁ := by
  simp [aSeek]
  rw [choose?_eq_of_exi]
  rotate_left; exact h
  simp
  have h₁ := Classical.epsilon_spec h
  generalize hp : Classical.epsilon (λ p => ∃ s₁, sys.tr s p = some s₁ ∧ P s₁) = p at h₁ ⊢
  choose s₁ h₁ h₂ using h₁
  simpa [sys.validTr_of_eq_some h₁, h₁]

theorem AState.ne_of_tr {s s₁ p} [hs : AState s]
(h : sys.tr s p = some s₁) : p ≠ s.aPos := by
  rw [tr_eq_some_iff] at h; grind

theorem AState.aPos_ne_of_tr {s s₁ p} [hs : AState s]
(h : sys.tr s p = some s₁) : s₁.aPos ≠ s.aPos := by
  rw [tr_eq_some_iff] at h; grind

theorem State.aPos_notMem_of_aWinsDisj {s : State} {fsp a d}
(h : s.aWinsDisj fsp ⟨a, d⟩) : s.aPos ∉ fsp.get 0 := by
  specialize h 0; simp at h; exact h

theorem State.aPos_notMem_of_aForallWinsDisj {s : State} {fsp a}
(h : s.aForallWinsDisj fsp a) : s.aPos ∉ fsp.get 0 :=
  aPos_notMem_of_aWinsDisj # h default inferInstance

theorem State.aPos_notMem_of_aHwsDisj {s : State} {fsp}
(h : s.aHwsDisj fsp) : s.aPos ∉ fsp.get 0 := by
  choose a ha h using h; exact aPos_notMem_of_aForallWinsDisj h

theorem State.hasTr_of_aWinsDisj {s fsp a d} [hs : sys.WF s]
(h : s.aWinsDisj fsp ⟨a, d⟩) : sys.hasTr s := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs
  rotate_left; simp
  specialize h 1
  choose s₁ h₁ h₂ using h
  simp at h₁
  use a.f s, s₁

theorem State.hasTr_of_aForallWinsDisj {s fsp a} [hs : sys.WF s]
(h : s.aForallWinsDisj fsp a) : sys.hasTr s :=
  hasTr_of_aWinsDisj # h default inferInstance

theorem State.hasTr_of_aHwsDisj {s fsp} [hs : sys.WF s]
(h : s.aHwsDisj fsp) : sys.hasTr s := by
  choose a ha h using h; exact hasTr_of_aForallWinsDisj h

@[simp]
instance {s fsp} : aFresh1 s fsp |>.WF := by
  unfold aFresh1; infer_instance

theorem AState.aForallWinsDisj_of_fresh1Alt {s fsp} {a : AStrat} [hs : AState s]
(h : a.Fresh1Alt s fsp) : s.aForallWinsDisj fsp a := by
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

theorem AState.fresh1_of_alt {s fsp} {a : AStrat} [hs : AState s]
(h : a.Fresh1Alt s fsp) : a.Fresh1 s fsp := by
  have H₀ := h
  choose ha h₀ h using h
  use ha, aForallWinsDisj_of_fresh1Alt H₀
  intro d hd s₁ p h₁
  rw [State.mem_aPtsSimAt_iff_simulate_tr] at h₁
  choose hs₁ n h₁ s₂ h₂ h₃ using h₁
  simp at h₂ h₃; subst h₃
  obtain ⟨n, rfl⟩ := Nat.even_iff_exi.mp # even_of_simulate h₁
  specialize h d hd n
  simp [h₁, h₂] at h
  rw [←AState.aPos_eq_of_tr h₂]
  choose a₁ ha₁ h using h
  specialize h d hd 0
  simp at h
  exact h.1

theorem AState.exi_fresh1_of_aHwsDisj {s fsp} [hs : AState s]
(h : s.aHwsDisj fsp) : ∃ (a : AStrat), a.Fresh1 s fsp := by
  use aFresh1 s fsp
  apply hs.fresh1_of_alt
  use inferInstance
  use State.aPos_notMem_of_aHwsDisj h
  intro d hd n
  induction n
  · simp
    have h₁ := @hs.aSeek_exi_tr_of (P := aFresh1Cnd s fsp)
    specialize h₁ _
    · clear h₁
      unfold aFresh1Cnd
      replace h := aHwsDisj_insert_one_aPos h
      choose a₁ ha₁ h using h
      have h₁ := h d hd 1
      simp at h₁
      choose s₁ h₁ h₂ using h₁
      use a₁.f s, s₁, h₁, a₁, ha₁
      simp [State.diff_eq_of_tr h₁, State.prev_eq_of_tr h₁]
      intro d₁ hd₁ n
      specialize h d₁ hd₁ (n + 1)
      simp_rw [sys.simulate_succ_full'] at h
      simp [h₁] at h
      choose s₂ h h₃ using h
      use s₂, h
      simp [FSP.hasLe, FSP.insert, FSP.insertSet, FSP.next] at h₃ ⊢
      grind
    unfold aFresh1
    choose s₂ h₁ h₂ using h₁
    use s₂, h₁
    unfold aFresh1Cnd at h₂
    simp [State.diff_eq_of_tr h₁, State.prev_eq_of_tr h₁] at h₂
    exact h₂
  nm n ih
  choose s₁ s₂ h₁ h₂ h₃ using ih
  have hs₁ := AState.of_simulate_mul_two_eq' h₁
  have hs₂ := DState.of_tr h₂
  choose s₃ h₄ using hd.validTr s₂
  have hs₃ := AState.of_tr h₄
  simp [Nat.add_mul, h₁, h₂, h₄]
  have G₁ := sys.reachable_of_simulate_eq h₁
  have G₂ := sys.reachable_right G₁ h₂
  have G₃ := sys.reachable_right G₂ h₄
  have h₅ := @hs₃.aSeek_exi_tr_of (P := aFresh1Cnd s fsp)
  specialize h₅ _
  · clear h₅
    unfold aFresh1Cnd
    replace h₃ := DState.aHwsDisj_insert_two_aPos h₃
    choose a₁ ha₁ h₃ using h₃
    have H₁ := h₃ d hd 2
    simp [h₄] at H₁
    choose s₄ H₁ H₂ using H₁
    use a₁.f s₃, s₄, H₁, a₁, ha₁
    rw [State.diff_eq_of_tr H₁ G₃, State.diff_eq_of_tr h₄ G₂, State.diff_eq_of_tr h₂ G₁]
    rw [State.diff_eq_of_simulate_full h₁]
    rw [State.prev_eq_of_tr H₁, DState.aVisited_eq_of_tr h₄ G₂, AState.aVisited_eq_of_tr h₂ G₁]
    intro d₁ hd₁ n₁
    specialize h₃ (d₁.set s₂ # d.f s₂) (DStrat.wf_set_of_tr h₄) (n₁ + 2)
    simp_rw [sys.simulate_succ_full'] at h₃
    simp [h₄, H₁] at h₃
    choose s₅ H₃ H₄ using h₃
    use s₅
    have hs₄ := sys.wf_of_tr H₁
    split_ands
    · convert H₃ using 1
      symm
      apply State.simulate_set_d_eq_of_length_hist_lt ⟨_, h₄⟩
      rw [length_hist_eq_of_tr H₁, length_hist_eq_of_tr h₄]
      omega
    simp
    rw [←AState.aPos_eq_of_tr h₂]
    simp [FSP.hasLe] at H₄ ⊢
    simp [Nat.add_assoc]
    intro k hk
    cases k
    rotate_left
    · nm k
      specialize H₄ (k + 3) (by omega)
      simp at H₄ ⊢
      ring_nf at H₄ ⊢
      exact H₄
    simp
    split_ands
    · specialize H₄ 2 (by omega)
      simp at H₄
      exact H₄.1
    · specialize H₄ 0 (by omega)
      simp at H₄
      exact H₄.1
    · intro k hk
      iterate 2 rw [Nat.le_add_one_iff] at hk
      rcases hk with ((hr | rfl) | rfl)
      · specialize H₄ 0 (by omega)
        simp at H₄
        exact H₄.2 k hr
      · specialize H₄ 1 (by omega)
        simp at H₄
        exact H₄
      · specialize H₄ 2 (by omega)
        simp at H₄
        exact H₄.2
  choose s₄ h₅ h₆ using h₅
  use s₄, h₅
  unfold aFresh1Cnd at h₆
  rw [State.diff_eq_of_tr h₅ G₃, State.diff_eq_of_tr h₄ G₂, State.diff_eq_of_tr h₂ G₁] at h₆
  rw [State.diff_eq_of_simulate_full h₁] at h₆
  simp [Nat.add_assoc] at h₆ ⊢
  have hs₄ := DState.of_tr h₅
  rw [State.prev_eq_of_tr h₅] at h₆
  exact h₆