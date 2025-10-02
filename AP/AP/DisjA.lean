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

theorem State.aHwsDisj_insert_of_mem_taken {s fsp p}
[hs : sys.WF s] (h₁ : s.aHwsDisj fsp) (h₂ : p ∈ s.taken) :
s.aHwsDisj (fsp.insert 0 p) := by
  obtain ⟨a, ha, h₁⟩ := h₁; use a, ha, aForallWinsDisj_insert_of_mem_taken h₁ h₂

-- #check 0 #exit

theorem AState.aHwsDisj_insert_of_not_mem_taken {s fsp p}
[hs : AState s] (h₁ : s.aHwsDisj fsp) (h₂ : p ∉ s.taken)
(h₃ : p.dist s.aPos ≤ s.pw) : ∃ n, s.aHwsDisj (fsp.insert n p) := by
  sorry

-- #check 0 #exit

theorem State.aHwsDisj_insert_of_not_mem_taken {s fsp p}
[hs : sys.WF s] (h₁ : s.aHwsDisj fsp) (h₂ : p ∉ s.taken)
(h₃ : p.dist s.aPos ≤ s.pw) : ∃ n, s.aHwsDisj (fsp.insert n p) := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs
  · exact hs.aHwsDisj_insert_of_not_mem_taken h₁ h₂ h₃
  -- obtain ⟨p, s', h₄⟩ := hs.tr_of_aHwsDisj h₁
  sorry

#check 0 #exit

theorem State.aHwsDisj_insert {s fsp} {p : PointZ}
[hs : sys.WF s] (h₁ : s.aHwsDisj fsp) (h₂ : p.dist s.aPos ≤ s.pw) :
∃ n, s.aHwsDisj (fsp.insert n p) := by
  by_cases h₃ : p ∈ s.taken
  · use 0; exact aHwsDisj_insert_of_mem_taken h₁ h₃
  · exact aHwsDisj_insert_of_not_mem_taken h₁ h₃ h₂

theorem State.aHwsDisj_insertSet' {s fsp} {ps : Set' PointZ}
[hs : sys.WF s] (h₁ : s.aHwsDisj fsp) (h₂ : ∀ p ∈ ps, p.dist s.aPos ≤ s.pw) :
∃ n, s.aHwsDisj (fsp.insertSet n ps.toSet) := by
  induction ps using Set'.ind; simpa; clear h₁
  nm ps p hp ih
  specialize ih _
  · simp_all only [Set'.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp]
  obtain ⟨n, ih⟩ := ih
  obtain ⟨m, h₂⟩ := s.aHwsDisj_insert ih (p := p) #
    by simp_all only [Set'.mem_insert, forall_eq_or_imp]
  use max n m; simp
  rw [fsp.insertSet_set_insert]
  apply aHwsDisj_insert_of_le _ # Nat.le_max_right n m
  rw [fsp.insertSet_insert_comm] at h₂ ⊢
  exact aHwsDisj_insertSet_of_le h₂ # Nat.le_max_left n m

theorem State.aHwsDisj_insertSet_of_finite {s fsp} {ps : Set PointZ}
[hs : sys.WF s] (h₁ : s.aHwsDisj fsp) (h₂ : ps.Finite)
(h₃ : ∀ p ∈ ps, p.dist s.aPos ≤ s.pw) : ∃ n, s.aHwsDisj (fsp.insertSet n ps) := by
  have h₄ := s.aHwsDisj_insertSet' (ps := Set'.ofSet ps) h₁ #
    by simpa [Set'.mem_ofSet h₂]
  rwa [Set'.toSet_ofSet h₂] at h₄