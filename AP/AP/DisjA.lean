import AP.AP.FSP

namespace AP

def State.aWinsDisj (s : State) (fsp : FSP) (st : Strat) : Prop :=
  ∀ n, ∃ s₁, sys.simulate st.f s n = (s₁, 0) ∧ ¬fsp.hasLe n s₁.aPos

def State.aForallWinsDisj (s : State) (fsp : FSP) (a : AStrat) : Prop :=
  ∀ (d : DStrat), d.WF → s.aWinsDisj fsp ⟨a, d⟩

def State.aHwsDisj (s : State) (fsp : FSP) : Prop :=
  ∃ (a : AStrat), a.WF ∧ s.aForallWinsDisj fsp a

theorem AState.tr_of_aForallWinsDisj {s fsp} {a : AStrat}
[hs : AState s] (h₁ : s.aForallWinsDisj fsp a) :
∃ p s', sys.tr s p = some s' ∧ s'.aForallWinsDisj fsp.next a := by
  use a.f s
  obtain ⟨s', h₂⟩ : ∃ s', sys.tr s (a.f s) = some s'
  · specialize h₁ default inferInstance 1
    simp at h₁
    obtain ⟨s', h₁, -⟩ := h₁
    split at h₁; simp at h₁
    nm x s₁ h₂; use s₁
  use s', h₂
  intro d Hd
  intro n
  specialize h₁ d Hd (n + 1)
  obtain ⟨s₁, h₁, h₃⟩ := h₁
  simp [h₂] at h₁; simp; use s₁

theorem AState.tr_of_aHwsDisj {s fsp} [hs : AState s] (h : s.aHwsDisj fsp) :
∃ p s', sys.tr s p = some s' ∧ s'.aHwsDisj fsp.next := by
  obtain ⟨a, ha, h⟩ := h
  obtain ⟨p, s', h₁, h₂⟩ := hs.tr_of_aForallWinsDisj h
  use p, s', h₁, a

theorem DState.tr_of_aForallWinsDisj {s s' p fsp} {a : AStrat}
[hs : DState s] [ha : a.WF] (h₁ : s.aForallWinsDisj fsp a)
(h₂ : sys.tr s p = some s') : s'.aForallWinsDisj fsp.next a := by
  intro d Hd n
  specialize h₁ (d.set s p) (d.wf_set_of_tr h₂) (n + 1)
  obtain ⟨s₁, h₁, h₃⟩ := h₁
  use s₁
  simp [h₃]
  clear h₃
  simp [h₂] at h₁
  convert h₁ using 1; symm
  have hs' := sys.wf_of_tr h₂
  apply simulate_set_d_eq_of_length_hist_lt ⟨_, h₂⟩
  exact State.length_hist_lt_of_tr h₂

theorem DState.tr_of_aHwsDisj {s s' p fsp} [hs : DState s] (h₁ : s.aHwsDisj fsp)
(h₂ : sys.tr s p = some s') : s'.aHwsDisj fsp.next := by
  obtain ⟨a, ha, h₁⟩ := h₁
  use a, ha, tr_of_aForallWinsDisj h₁ h₂

theorem State.aWinsDisj_iff {s : State} {fsp} {st : Strat} :
s.aWinsDisj fsp st ↔ s.aWins st ∧ ∀ n, ¬fsp.hasLe n (sys.simulate st.f s n).1.aPos := by
  constructor
  · intro h
    constructor
    · intro n
      specialize h n
      aesop
    intro n
    specialize h n
    aesop
  rintro ⟨h₁, h₂⟩
  intro n
  simp [Prod.ext_iff]
  specialize h₁ n
  aesop

theorem State.aWinsDisj_of_congr {s : State} {fsp₁ fsp₂ : FSP} {st : Strat}
(h₁ : s.aWinsDisj fsp₁ st) (h₂ : ∀ n, fsp₂.hasLe n (sys.simulate st.f s n).1.aPos →
∃ k, fsp₁.hasLe k (sys.simulate st.f s k).1.aPos) : s.aWinsDisj fsp₂ st := by
  rw [aWinsDisj_iff] at h₁ ⊢
  rcases h₁ with ⟨h₁, h₃⟩
  use h₁; clear h₁
  intro n
  contrapose! h₃
  specialize h₂ n h₃
  exact h₂

theorem State.aWinsDisj_insertSet_of_le {s : State} {fsp : FSP} {st ps m n}
(h₁ : s.aWinsDisj (fsp.insertSet m ps) st) (h₂ : m ≤ n) :
s.aWinsDisj (fsp.insertSet n ps) st := by
  intro k
  specialize h₁ k
  obtain ⟨s₁, h₁, h₃⟩ := h₁
  use s₁, h₁
  contrapose! h₃
  exact fsp.hasLe_insertSet_of_le_and_le h₃ h₂

theorem State.aWinsDisj_insert_of_le {s : State} {fsp : FSP} {st p m n}
(h₁ : s.aWinsDisj (fsp.insert m p) st) (h₂ : m ≤ n) :
s.aWinsDisj (fsp.insert n p) st := s.aWinsDisj_insertSet_of_le h₁ h₂

theorem State.aForallWinsDisj_insertSet_of_le {s : State} {fsp : FSP} {a ps m n}
(h₁ : s.aForallWinsDisj (fsp.insertSet m ps) a) (h₂ : m ≤ n) :
s.aForallWinsDisj (fsp.insertSet n ps) a :=
  λ d hd => aWinsDisj_insertSet_of_le (h₁ d hd) h₂

theorem State.aForallWinsDisj_insert_of_le {s : State} {fsp : FSP} {a p m n}
(h₁ : s.aForallWinsDisj (fsp.insert m p) a) (h₂ : m ≤ n) :
s.aForallWinsDisj (fsp.insert n p) a := s.aForallWinsDisj_insertSet_of_le h₁ h₂

theorem State.aHwsDisj_insertSet_of_le {s : State} {fsp : FSP} {ps m n}
(h₁ : s.aHwsDisj (fsp.insertSet m ps)) (h₂ : m ≤ n) :
s.aHwsDisj (fsp.insertSet n ps) := by
  obtain ⟨a, ha, h₁⟩ := h₁; exact ⟨a, ha, aForallWinsDisj_insertSet_of_le h₁ h₂⟩

theorem State.aHwsDisj_insert_of_le {s : State} {fsp : FSP} {p m n}
(h₁ : s.aHwsDisj (fsp.insert m p)) (h₂ : m ≤ n) :
s.aHwsDisj (fsp.insert n p) := s.aHwsDisj_insertSet_of_le h₁ h₂

theorem State.aForallWinsDisj_insert_of_mem_taken {s fsp p} {a : AStrat}
[hs : sys.WF s] (h₁ : s.aForallWinsDisj fsp a) (h₂ : p ∈ s.taken) :
s.aForallWinsDisj (fsp.insert 0 p) a := by
  unfold aForallWinsDisj at h₁ ⊢
  intro d Hd
  specialize h₁ d Hd
  apply aWinsDisj_of_congr h₁; clear h₁
  intro n h₁
  obtain ⟨k, hk, h₁⟩ := h₁
  use n, k, hk
  generalize h₃ : (sys.simulate (Strat.f ⟨a, d⟩) s n).1 = s₁ at h₁ ⊢
  replace h₃ : sys.Reachable s s₁; subst h₃; exact sys.reachable_simulate
  have hs₁ := sys.wf_of_reachable h₃
  have h₄ := mem_taken_of_reachable h₃ h₂
  clear h₃
  cases k; simp at h₁; aesop; nm k
  rw [fsp.get_insert_of_ne # by simp] at h₁
  exact h₁

theorem State.aHwsDisj_insert_of_mem_taken {s fsp p} [hs : sys.WF s]
(h₁ : s.aHwsDisj fsp) (h₂ : p ∈ s.taken) : s.aHwsDisj (fsp.insert 0 p) := by
  obtain ⟨a, ha, h₁⟩ := h₁; use a, ha, aForallWinsDisj_insert_of_mem_taken h₁ h₂

theorem State.aWinsDisj_of_aWinsDisj_offset {s : State} {st : Strat} {fsp : FSP} {n}
(h : s.aWinsDisj (fsp.offset n) st) : s.aWinsDisj fsp st := by
  intro k; specialize h k; obtain ⟨s₁, h₁, h₂⟩ := h; use s₁, h₁
  simp at h₂; contrapose! h₂; exact fsp.hasLe_of_add_right h₂

theorem State.aForallWinsDisj_of_aForallWinsDisj_offset {s : State} {a : AStrat}
{fsp : FSP} {n} (h : s.aForallWinsDisj (fsp.offset n) a) : s.aForallWinsDisj fsp a :=
  λ d hd => aWinsDisj_of_aWinsDisj_offset # h d hd

theorem State.aHwsDisj_of_aHwsDisj_offset {s : State} {fsp : FSP} {n}
(h : s.aHwsDisj (fsp.offset n)) : s.aHwsDisj fsp := by
  obtain ⟨a, ha, h⟩ := h; use a, ha, aForallWinsDisj_of_aForallWinsDisj_offset h

theorem State.aWinsDisj_of_aWinsDisj_next {s : State} {st : Strat} {fsp : FSP}
(h : s.aWinsDisj fsp.next st) : s.aWinsDisj fsp st :=
  aWinsDisj_of_aWinsDisj_offset (n := 1) h

theorem State.aForallWinsDisj_of_aForallWinsDisj_next {s : State} {a : AStrat}
{fsp : FSP} (h : s.aForallWinsDisj fsp.next a) : s.aForallWinsDisj fsp a :=
  aForallWinsDisj_of_aForallWinsDisj_offset (n := 1) h

theorem State.aHwsDisj_of_aHwsDisj_next {s : State} {fsp : FSP}
(h : s.aHwsDisj fsp.next) : s.aHwsDisj fsp :=
  aHwsDisj_of_aHwsDisj_offset (n := 1) h

theorem State.aHwsDisj_setHist_of_aHwsDisj {s fsp hist} [hs : sys.WF s]
[hs' : sys.WF # s.setHist hist] (h : s.aHwsDisj fsp) : (s.setHist hist).aHwsDisj fsp := by
  obtain ⟨a, ha, h⟩ := h
  have H := s.exi_aWins_cnd_setHist_of (p := λ f => ∀ n, ¬fsp.hasLe n (f n).aPos)
    (a := a) (hist := hist) (by simp) (λ d hd => aWinsDisj_iff.mp (h d hd) |>.symm)
  obtain ⟨a', ha', h₁⟩ := H; use a', ha', λ d hd => aWinsDisj_iff.mpr (h₁ d hd).symm

@[simp]
theorem State.aHwsDisj_setHist_iff {s fsp hist} [hs : sys.WF s]
[hs' : sys.WF # s.setHist hist] : (s.setHist hist).aHwsDisj fsp ↔ s.aHwsDisj fsp := by
  symm; use aHwsDisj_setHist_of_aHwsDisj
  intro h; change s.setHist hist |>.setHist s.hist |>.aHwsDisj fsp
  exact aHwsDisj_setHist_of_aHwsDisj h

theorem State.aPos_not_mem_fsp_get_zero_of_aWinsDisj {s : State} {fsp} {st : Strat}
(h : s.aWinsDisj fsp st) : s.aPos ∉ fsp.get 0 := by
  specialize h 0; simp at h; exact h

theorem State.aPos_not_mem_fsp_get_zero_of_aForallWinsDisj {s : State} {fsp} {a : AStrat}
(h : s.aForallWinsDisj fsp a) : s.aPos ∉ fsp.get 0 :=
  aPos_not_mem_fsp_get_zero_of_aWinsDisj # h default inferInstance

theorem State.aPos_not_mem_fsp_get_zero_of_aHwsDisj {s : State} {fsp}
(h : s.aHwsDisj fsp) : s.aPos ∉ fsp.get 0 := by
  obtain ⟨a, ha, h⟩ := h; exact aPos_not_mem_fsp_get_zero_of_aForallWinsDisj h

structure DisjEraseTaken : Type where
  a : AStrat
  s : State
  p : PointZ
  fsp : FSP
  n : ℕ

def aDisjEraseTaken_fa (acc : DisjEraseTaken) : PointZ × DisjEraseTaken :=
  let ⟨a, s, p, fsp, n⟩ := acc
  ⟨a.f s, a, sys.tr s (a.f s) |>.get!, p, fsp.next, n + 1⟩

def aDisjEraseTaken_fd (p₁ : PointZ) (acc : DisjEraseTaken) : DisjEraseTaken :=
  let ⟨a, s, p, fsp, n⟩ := acc
  let p₂ := if p₁ ≠ p then p₁ else s.chooseDMove
  ⟨a, sys.tr s p₂ |>.get!, p₂, fsp.next, n + 1⟩

def aDisjEraseTaken (s s' : State) (p : PointZ) (a : AStrat) (fsp : FSP) : AStrat :=
  .mkFold (α := DisjEraseTaken) s' ⟨a, s, p, fsp, 0⟩
  (λ _ => aDisjEraseTaken_fa) (λ _ => aDisjEraseTaken_fd)

@[simp]
instance {s s' p a fsp} : (aDisjEraseTaken s s' p a fsp).WF := by
  unfold aDisjEraseTaken; infer_instance

-- #check 0 #exit

theorem State.aHwsDisj_erase_taken {fsp s s' p} [hs : sys.WF s] [hs' : sys.WF s']
(h : s.aHwsDisj fsp) (hpw : s'.pw = s.pw) (ht : s'.aTurn = s.aTurn)
(hpa : s'.aPos = s.aPos) (hp : s'.taken = s.taken.erase p) : s'.aHwsDisj fsp := by
  by_cases h₁ : p ∉ s.taken
  · rw [Set'.erase_eq_of_not_mem h₁] at hp
    have h₂ : s' = s.setHist s'.hist
    · ext:1 <;> first | assumption | simp
    rw [h₂] at hs' ⊢; exact aHwsDisj_setHist_of_aHwsDisj h
  push_neg at h₁
  obtain ⟨a, ha, h⟩ := h
  use aDisjEraseTaken s s' p a fsp, inferInstance
  intro d hd n
  have H := AStrat.mkFold_ind (α := DisjEraseTaken)
    (z := ⟨a, s, p, fsp, 0⟩) (s := s') (d := d) (n := n)
    (fa := λ _ => aDisjEraseTaken_fa) (fd := λ _ => aDisjEraseTaken_fd)
    (p := λ s₁' ⟨a', s₁, p, fsp', n⟩ => a = a' ∧ fsp.offset n = fsp' ∧
    s₁'.hist.length - s'.hist.length = n ∧ s₁'.aPos = s₁.aPos ∧
    s₁.aForallWinsDisj fsp a ∧ s₁.aPos ∉ fsp'.get 0)
  -- simp only [exists_and_right, exists_and_left] at H
  dsimp at H
  specialize H _ _ _
  · clear H; simp_all only [tsub_self, true_and]
    exact aPos_not_mem_fsp_get_zero_of_aWinsDisj (h d hd)
  · clear H
    rintro sa hsa ⟨a', s₁, p₁, fsp', n'⟩
    dsimp
    rintro ⟨rfl, rfl, H₁, H₂, H₃, H₄⟩
    have H₅ := H₃ default inferInstance 1
    obtain ⟨sd, H₅, H₆⟩ := H₅
    simp at H₅; split at H₅; simp at H₅
    nm x sd' H₇; clear x
    simp at H₅; subst H₅
    sorry
  · clear H; clear! a fsp p
    sorry
  obtain ⟨s₁, ⟨a', s₁', p₁, fsp', n'⟩, H₁, H₂, H₃, H₄, H₅, H₆, H₇⟩ := H
  dsimp at H₁ H₂ H₃ H₄ H₅ H₆ H₇
  subst H₂ H₃ H₄
  use s₁, H₁
  simp at H₇
  unfold FSP.hasLe
  simp
  rw [length_hist_sub_eq_of_simulate H₁] at H₇
  simpa [H₅]

-- #check 0 #exit

theorem State.aHwsDisj_of_taken_subset {fsp s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h : s.aHwsDisj fsp) (hpw : s'.pw = s.pw) (ht : s'.aTurn = s.aTurn)
(hpa : s'.aPos = s.aPos) (h₁ : s'.taken ⊆ s.taken) : s'.aHwsDisj fsp := by
  rw [Set'.subset_iff_exi_disj_union] at h₁
  obtain ⟨ps, h₁', h₁⟩ := h₁
  revert fsp s s'
  apply ps.ind
  · intro fsp s s' hs hs' h hpw ht hpa h₁' h₁
    simp at h₁
    have h₂ : s' = s.setHist s'.hist
    · ext:1 <;> first | assumption | simp
    rw [h₂] at hs' ⊢; exact aHwsDisj_setHist_of_aHwsDisj h
  clear ps
  intro ps p hp ih fsp s s' hs hs' h hpw ht hpa h₁' h₁
  simp at h₁'
  rcases h₁' with ⟨h₁', h₂'⟩
  replace h₁ : s'.taken = s.taken.erase p
  · rw [←h₁]
    ext p₁
    simp
    constructor
    · intro H
      simp [H]
      rintro rfl
      contradiction
    · rintro ⟨H₁, H₂⟩
      simp [ne_symm' H₁] at H₂
      by_contra H₃
      simp [H₃] at H₂
      sorry
  -- apply s.aHwsDisj_erase_taken h hpw ht hpa
  sorry

-- #check 0 #exit

theorem AState.aHwsDisj_nbhd_pw {s : State} {fsp : FSP} [hs : AState s]
(h : s.aHwsDisj fsp) : s.aHwsDisj # fsp.insertSet 3 # s.aPos.nbhd s.pw |>.toSet := by
  sorry