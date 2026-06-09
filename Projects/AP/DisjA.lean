import Projects.AP.WF

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
    use s'
  use s', h₂
  intro d Hd n
  specialize h₁ d Hd (n + 1)
  obtain ⟨s₁, h₁, h₃⟩ := h₁
  simp only [System.simulate_succ_full'] at h₁
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
  simp only [System.simulate_succ_full'] at h₁
  simp [h₂] at h₁
  convert h₁ using 1; symm
  have hs' := sys.wf_of_tr h₂
  apply State.simulate_set_d_eq_of_length_hist_lt ⟨_, h₂⟩
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
  replace h₃ : sys.Reachable s s₁; grind
  have hs₁ : sys.WF s₁; grind
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

theorem State.aWins_of_aWinsDisj {fsp} {s : State} {a : AStrat} {d : DStrat}
(h : s.aWinsDisj fsp ⟨a, d⟩) : s.aWins ⟨a, d⟩ :=
  aWinsDisj_iff.mp h |>.1

theorem State.aWins_of_aForallWinsDisj {fsp} {s : State} {a : AStrat} {d : DStrat}
[hd : d.WF] (h : s.aForallWinsDisj fsp a) : s.aWins ⟨a, d⟩ :=
  aWins_of_aWinsDisj # h d hd

theorem State.forall_aWins_of_aForallWinsDisj {fsp} {s : State} {a : AStrat}
(h : s.aForallWinsDisj fsp a) : ∀ (d : DStrat) [d.WF], s.aWins ⟨a, d⟩ :=
  λ _ _ => aWins_of_aForallWinsDisj h

theorem State.aHws_of_aForallWinsDisj {fsp} {s : State} {a : AStrat} [ha : a.WF]
(h : s.aForallWinsDisj fsp a) : s.aHws :=
  ⟨a, ha, λ _ _ => aWins_of_aForallWinsDisj h⟩

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
  let p_move := if p₁ = p then s.chooseDMove else p₁
  let p_next := if p₁ = p then s.chooseDMove else p
  ⟨a, sys.tr s p_move |>.get!, p_next, fsp.next, n + 1⟩

def aDisjEraseTaken (s s' : State) (p : PointZ) (a : AStrat) (fsp : FSP) : AStrat :=
  .mkFold (α := DisjEraseTaken) s' ⟨a, s, p, fsp, 0⟩
  (λ _ => aDisjEraseTaken_fa) (λ _ => aDisjEraseTaken_fd)

theorem AState.validTr_of_aForallWinsDisj {fsp s} {a : AStrat} [hsa : AState s]
(h : s.aForallWinsDisj fsp a) : sys.validTr s (a.f s) := by
  replace h := State.forall_aWins_of_aForallWinsDisj h default 1
  simp at h; exact h

@[simp]
instance {s s' p a fsp} : (aDisjEraseTaken s s' p a fsp).WF := by
  unfold aDisjEraseTaken; infer_instance

structure DisjEraseTaken.Cnd (w₀ w : DisjEraseTaken) (s' s₁' : State) (n : ℕ) : Prop where
  h₁ : s₁'.hist.length - s'.hist.length = n
  h₂ : w.n = n
  h₃ : ∃ (d : DStrat), d.WF ∧ sys.simulate (Strat.f ⟨w.a, d⟩) w₀.s n = (w.s, 0)
  h₄ : w.p ∈ w.s.taken
  h₅ : s₁' = {w.s with taken := w.s.taken.erase w.p, hist := s₁'.hist}
  h₆ : w.s.aForallWinsDisj w.fsp w.a
  h₈ : w.a = w₀.a
  h₉ : w.fsp = w₀.fsp.offset n

theorem DisjEraseTaken.Cnd.state_eq_symm {w₀ w s' s₁' n}
(h : DisjEraseTaken.Cnd w₀ w s' s₁' n) :
w.s = {s₁' with taken := s₁'.taken.insert w.p, hist := w.s.hist} := by
  ext:1 <;> rw [h.h₅]; exact Set'.insert_erase_eq_of_mem h.h₄|>.symm

theorem State.aWinsDisj_insert_taken_of_aWinsDisj {fsp s} {st : Strat}
[hs : sys.WF s] (h : s.aWinsDisj fsp st) :
s.aWinsDisj (fsp.insertSet 0 s.taken.toSet) st := by
  rw [aWinsDisj_iff] at h ⊢
  rcases h with ⟨h₁, h₂⟩
  use h₁
  intro n
  specialize h₂ n
  simp [FSP.hasLe, FSP.insertSet] at h₂ ⊢
  intro k hk
  specialize h₂ k hk
  split_ifs with h₃ <;> simp [h₂]
  generalize hr : sys.simulate st.f s n = r at h₂ ⊢
  rcases r with ⟨s₁, r⟩; dsimp at h₂ ⊢
  have hs₁ : sys.WF s₁; grind
  have h : s₁.aPos ∉ s₁.taken; simp
  contrapose! h
  apply mem_taken_of_reachable # sys.reachable_of_simulate hr
  exact h

theorem State.aForallWinsDisj_insert_taken_of_aForallWinsDisj {fsp s} {a : AStrat}
[hs : sys.WF s] (h : s.aForallWinsDisj fsp a) :
s.aForallWinsDisj (fsp.insertSet 0 s.taken.toSet) a :=
  λ d hd => aWinsDisj_insert_taken_of_aWinsDisj # h d hd

theorem State.aHwsDisj_insert_taken_of_aHwsDisj {fsp s} [hs : sys.WF s]
(h : s.aHwsDisj fsp) : s.aHwsDisj # fsp.insertSet 0 s.taken.toSet := by
  obtain ⟨a, ha, h⟩ := h; use a, ha
  exact aForallWinsDisj_insert_taken_of_aForallWinsDisj h

theorem State.aWinsDisj_of_aWinsDisj_insertSet {fsp : FSP} {s : State} {k ps} {st : Strat}
(h : s.aWinsDisj (fsp.insertSet k ps) st) : s.aWinsDisj fsp st := by
  rw [aWinsDisj_iff] at h ⊢
  rcases h with ⟨h₁, h₂⟩
  use h₁
  intro n
  specialize h₂ n
  simp [FSP.hasLe, FSP.insertSet] at h₂ ⊢
  intro k hk
  specialize h₂ k hk
  split_ifs at h₂ with h₃
  · simp at h₂; tauto
  · exact h₂

theorem State.aForallWinsDisj_of_aForallWinsDisj_insertSet
{fsp : FSP} {s : State} {k ps} {a : AStrat}
(h : s.aForallWinsDisj (fsp.insertSet k ps) a) : s.aForallWinsDisj fsp a :=
  λ d hd => aWinsDisj_of_aWinsDisj_insertSet # h d hd

theorem State.aHwsDisj_of_aHwsDisj_insertSet {fsp : FSP} {s : State} {k ps}
(h : s.aHwsDisj # fsp.insertSet k ps) : s.aHwsDisj fsp := by
  obtain ⟨a, ha, h⟩ := h; use a, ha
  exact aForallWinsDisj_of_aForallWinsDisj_insertSet h

theorem State.aWinsDisj_of_aWinsDisj_insert {fsp : FSP} {s : State} {k p} {st : Strat}
(h : s.aWinsDisj (fsp.insert k p) st) : s.aWinsDisj fsp st :=
  aWinsDisj_of_aWinsDisj_insertSet h

theorem State.aForallWinsDisj_of_aForallWinsDisj_insert
{fsp : FSP} {s : State} {k p} {a : AStrat}
(h : s.aForallWinsDisj (fsp.insert k p) a) : s.aForallWinsDisj fsp a :=
  aForallWinsDisj_of_aForallWinsDisj_insertSet h

theorem State.aHwsDisj_of_aHwsDisj_insert {fsp : FSP} {s : State} {k p}
(h : s.aHwsDisj # fsp.insert k p) : s.aHwsDisj fsp :=
  aHwsDisj_of_aHwsDisj_insertSet h

theorem State.aHwsDisj_erase_taken {fsp s s' p} [hs : sys.WF s] [hs' : sys.WF s']
(h : s.aHwsDisj fsp) (hpw : s'.pw = s.pw) (ht : s'.aTurn = s.aTurn)
(hpa : s'.aPos = s.aPos) (hp : s'.taken = s.taken.erase p)
(h₁ : p ∈ s.taken) : s'.aHwsDisj # fsp.insert 0 p := by
  obtain ⟨a, ha, h⟩ := h
  use aDisjEraseTaken s s' p a fsp, inferInstance
  intro d hd n
  have H := AStrat.mkFold_ind (α := DisjEraseTaken)
    (z := ⟨a, s, p, fsp, 0⟩) (s := s') (d := d) (n := n)
    (fa := λ _ => aDisjEraseTaken_fa) (fd := λ _ => aDisjEraseTaken_fd)
    (p := λ s₁' w => DisjEraseTaken.Cnd ⟨a, s, p, fsp, 0⟩ w s' s₁' #
      s₁'.hist.length - s'.hist.length)
  specialize H _ _ _
  · clear H
    constructor <;> simp <;> try assumption
    · use default; infer_instance
    · ext:1 <;> simp <;> assumption
  · clear H; clear! d
    rintro sa hsa w H cnd
    have H₅' := cnd.state_eq_symm
    rcases cnd with ⟨-, H₂, ⟨d, hd, H₃⟩, H₄, H₅, H₆, H₈, H₉⟩
    dsimp at H₃ H₅ H₈ H₉
    dsimp [aDisjEraseTaken_fa]
    rw [H₈] at H₆ ⊢
    have hzs : AState w.s
    · use sys.wf_of_simulate H₃; rw [H₅']; simp
    obtain ⟨sd, h₂⟩ := hzs.validTr_of_aForallWinsDisj H₆
    generalize h₃ :
      { sd with
        taken := sd.taken.erase w.p
      , hist := a.f w.s :: sa.hist} = sd'
    use sd'
    subst h₃
    constructor
    · simp [AState.tr_eq_some_iff] at h₂ ⊢
      rcases h₂ with ⟨⟨h₂, h₃, h₄⟩, rfl⟩
      split_ands <;> (try rw [H₅]) <;> dsimp
      · exact h₂
      · simp [h₃]
      · exact h₄
    have G' := length_hist_le_of_reachable H
    have G := Nat.succ_sub G'; dsimp at G
    constructor <;> simp [h₂]
    · rw [H₂, G]
    · rw [H₈] at H₃
      use d, hd
      rw [G, sys.simulate_add, H₃]
      simp [h₂]
    · simpa [hzs.taken_eq_of_tr h₂]
    · clear! d n
      intro d hd n
      specialize H₆ d hd (n + 1)
      obtain ⟨s₁, H₆⟩ := H₆
      use s₁
      simp only [System.simulate_succ_full'] at H₆
      simp [h₂] at H₆
      simpa
    · rw [G, H₉, FSP.next_offset]
  · clear H
    intro sd hsd sa hsa p₁ w h₂ h₃ cnd
    have H₅' := cnd.state_eq_symm
    rcases cnd with ⟨-, H₂, ⟨d₁, hd₁, H₃⟩, H₄, H₅, H₆, H₈, H₉⟩
    dsimp at H₃ H₅ H₈ H₉
    dsimp [aDisjEraseTaken_fd]
    have G' := length_hist_le_of_reachable h₂
    have G := Nat.succ_sub G'; dsimp at G
    have hws : DState w.s
    · use sys.wf_of_simulate H₃; rw [H₅']; simp
    generalize h_move : (if p₁ = w.p then w.s.chooseDMove else p₁) = p_move
    generalize h_next : (if p₁ = w.p then w.s.chooseDMove else w.p) = p_next
    obtain ⟨s₂, G₂⟩ : ∃ s₂, sys.tr w.s p_move = some s₂
    · subst h_move
      split_ifs with h; simp
      simp [DState.tr_eq_some_iff] at h₃ ⊢
      rcases h₃ with ⟨⟨h₃, G₃⟩, rfl⟩
      rw [H₅']
      simp
      use h₃
    have hs₂ := AState.of_tr G₂
    have G₃ := length_hist_eq_of_tr h₃
    have G₄ : sa.hist.length - s'.hist.length = sd.hist.length - s'.hist.length + 1
    · rw [G₃, G]
    constructor <;> simp [G₂]
    · rw [length_hist_eq_of_tr h₃, G, H₂]
    · use d₁.set w.s p_move, DStrat.wf_set_of_tr G₂
      rw [G₄]
      suffices G₅ : sys.simulate (Strat.f ⟨w.a, d₁.set w.s p_move⟩) s
        (sd.hist.length - s'.hist.length) = (w.s, 0)
      · rw [sys.simulate_add]; simp [G₅, G₂]
      convert H₃ using 1
      rw [H₈]
      apply simulate_set_d_eq_of_le_length_hist_sub # sys.validTr_of_eq_some G₂
      simp [length_hist_eq_of_simulate_eq H₃]
    · simp [DState.taken_eq_of_tr G₂]
      subst h_move h_next
      split_ifs with Q₁
      · subst Q₁; simp
      · simp [H₄]
    · ext:1 <;> simp
      · rw [pw_eq_of_tr h₃, pw_eq_of_tr G₂, H₅]
      · clear G₃ G₄
        rw [DState.tr_eq_some_iff] at h₃
        rcases h₃ with ⟨⟨h₃, h₃'⟩, rfl⟩
        simp
        split_ifs at h_move h_next with hp₃
        · subst h_move h_next hp₃
          ext q
          simp
          constructor
          · rintro (rfl | G₆)
            · constructor
              · intro G₇; simp [←G₇] at H₄
              apply Set'.mem_of_subset _ H₄
              exact taken_subset_of_tr G₂
            · rw [H₅] at G₆; simp at G₆
              constructor
              · rintro rfl; simp at G₆
              rcases G₆ with ⟨G₆, G₇⟩
              apply Set'.mem_of_subset _ G₇
              exact taken_subset_of_tr G₂
          · rintro ⟨G₇, G₈⟩
            rw [or_iff_not_imp_left]
            intro G₉
            rw [H₅]
            simp
            use ne_symm' G₉
            rw [DState.tr_eq_some_iff] at G₂
            rcases G₂ with ⟨⟨G₂, G₂'⟩, rfl⟩
            simp [ne_symm' G₇] at G₈
            exact G₈
        · subst h_move h_next
          ext q
          simp
          constructor
          · intro G₆
            rcases G₆ with rfl | G₆
            · use ne_symm' hp₃, DState.mem_taken_of_tr G₂
            rw [H₅] at G₆
            simp at G₆
            rcases G₆ with ⟨G₆, G₇⟩
            use G₆
            exact mem_taken_of_tr G₂ G₇
          · rintro ⟨G₇, G₈⟩
            rw [or_iff_not_imp_left]
            intro G₉
            rw [H₅]; simp
            use G₇
            simp [DState.taken_eq_of_tr G₂, G₉] at G₈
            exact G₈
      · rw [DState.aPos_eq_of_tr h₃, DState.aPos_eq_of_tr G₂, H₅]
    · rw [H₈] at H₆ ⊢; exact DState.tr_of_aForallWinsDisj H₆ G₂
    · exact H₈
    · rw [length_hist_eq_of_tr h₃, G, H₉, FSP.next_offset]
  obtain ⟨s₁, ⟨a', s₁', p₁, fsp', n'⟩, H₁, H₂⟩ := H
  rcases H₂ with ⟨-, G₂, ⟨d₁, hd₁, H₃⟩, H₄, H₅, H₆, G₈, G₉⟩
  dsimp at *
  subst G₈
  use s₁, H₁
  rw [length_hist_sub_eq_of_simulate H₁] at G₉
  replace H₁ : n = n'
  · replace H₁ := length_hist_sub_eq_of_simulate H₁
    rw [G₂, H₁]
  subst H₁
  rw [H₅]
  simp
  rw [←G₂] at H₃
  specialize h d₁ hd₁ n
  simp [H₃] at h
  simp [FSP.hasLe] at h ⊢
  intro k hk
  specialize h k hk
  simp [FSP.insert, FSP.insertSet]
  split_ifs with h₂ <;> simp [h]
  have hs₁' : sys.WF s₁'; grind
  apply ne_of_congr (· ∈ s₁'.taken)
  simp
  apply mem_taken_of_reachable # sys.reachable_of_simulate H₃
  exact h₁

theorem State.aHwsDisj_erase_taken' {fsp s s' p} [hs : sys.WF s] [hs' : sys.WF s']
(h : s.aHwsDisj fsp) (hpw : s'.pw = s.pw) (ht : s'.aTurn = s.aTurn)
(hpa : s'.aPos = s.aPos) (hp : s'.taken = s.taken.erase p)
(h₁ : p ∈ s.taken) : s'.aHwsDisj fsp :=
  aHwsDisj_of_aHwsDisj_insert # aHwsDisj_erase_taken h hpw ht hpa hp h₁

theorem State.aHwsDisj_of_taken_subset {fsp s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h : s.aHwsDisj fsp) (hpw : s'.pw = s.pw) (ht : s'.aTurn = s.aTurn)
(hpa : s'.aPos = s.aPos) (h₁ : s'.taken ⊆ s.taken) :
s'.aHwsDisj # fsp.insertSet 0 s.taken.toSet := by
  rw [Set'.subset_iff_exi_disj_union] at h₁
  obtain ⟨ps, h₁', h₁⟩ := h₁
  revert fsp s s'
  apply ps.ind
  · intro fsp s s' hs hs' h hpw ht hpa h₁' h₁
    simp at h₁
    have h₂ : s' = s.setHist s'.hist
    · ext:1 <;> first | assumption | simp
    rw [h₂] at hs' ⊢
    apply aHwsDisj_setHist_of_aHwsDisj
    exact aHwsDisj_insert_taken_of_aHwsDisj h
  clear ps
  intro ps p hp ih fsp s s' hs hs' h hpw ht hpa h₁' h₁
  simp at h₁'
  rcases h₁' with ⟨h₁', h₂'⟩
  have H := h₁
  replace h₁ : s'.taken = (s.taken \ ps).erase p
  · clear ih
    ext p₁
    simp
    constructor
    · intro h₃
      constructor
      · rintro rfl; contradiction
      simp [←h₁, h₃]
      intro h₄
      specialize h₂' _ h₄
      contradiction
    · rintro ⟨h₃, h₄, h₅⟩
      simp [←h₁, ne_symm' h₃, h₅] at h₄
      exact h₄
  have H₁ := s.exi_taken_diff (ps := ps); specialize H₁ _
  · clear H₁
    constructor <;> simp
    · intro h₂ h₃
      simp [h₃] at h₁
      replace hs' : AState s'; use hs'; rwa [ht]
      simp at h₁
    · intro h₂ h₃
      replace hs : AState s; use hs
      have h₄ := hs.size_taken_eq_one_of_pw_eq_zero h₃
      have h₅ : p ∈ s.taken; simp [←H]
      convert h₄; rw [Set'.diff_eq_left_iff]; intro x hx
      rwa [Set'.eq_of_size_eq_one_and_mem h₄ hx h₅]
    · intro h₂ h₃
      replace hs : DState s; use hs
      have h₄ := hs.exi_aMove_of_taken_ne_empty
      specialize h₄ _
      · simp [←H]
      obtain ⟨p₁, h₄⟩ := h₄
      use p₁; simp [isSome_aMove_iff] at h₄ ⊢; simp [h₄]
  obtain ⟨s₁, hs₁, hpw₁, ht₁, hpa₁, h₃⟩ := H₁
  specialize @ih fsp s s₁ _ _ h hpw₁ ht₁ hpa₁ _ _
  · simp [h₃]; tauto
  · rw [h₃, ←H]; ext p₁; simp; constructor
    · rintro (⟨h₄, h₅⟩ | h₄) <;> simp [h₄]
    · rintro (h₄ | h₄ | h₄) <;> simp [h₄, Decidable.not_or_of_imp]
  have H₁ := s₁.aHwsDisj_erase_taken ih (p := p) (by rw [hpw, hpw₁])
    (by rw [ht, ht₁]) (by rw [hpa, hpa₁]) (by rwa [h₃]) (by simpa [h₃, ←H])
  exact aHwsDisj_of_aHwsDisj_insertSet H₁

theorem State.aHwsDisj_of_taken_subset' {fsp s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h : s.aHwsDisj fsp) (hpw : s'.pw = s.pw) (ht : s'.aTurn = s.aTurn)
(hpa : s'.aPos = s.aPos) (h₁ : s'.taken ⊆ s.taken) : s'.aHwsDisj fsp :=
  aHwsDisj_of_aHwsDisj_insertSet # aHwsDisj_of_taken_subset h hpw ht hpa h₁

open Classical in noncomputable
def dChooseFromSet (ps : Set' PointZ) : DStrat :=
  .mk # λ sd => choose? # λ p => p ∈ ps ∧ p ∉ sd.taken ∧ p ≠ sd.aPos

instance {ps} : dChooseFromSet ps |>.WF := by
  unfold dChooseFromSet; infer_instance

theorem State.eventually_simulate_dChooseFromSet_subset_taken {s}
{ps : Set' PointZ} {a : AStrat} [hs : sys.WF s] [ha : a.WF] :
eventually # λ n => ∀ s', sys.simulate (Strat.f ⟨a, dChooseFromSet ps⟩) s n = (s', 0) →
ps ⊆ s'.taken := by
  generalize hm : ps.size = m
  induction m generalizing s ps
  · simp at hm; simp [hm]
  nm m ih
  suffices ihd : ∀ s [hs : DState s] (ps : Set' PointZ), ps.size = m + 1 →
    eventually (λ n => ∀ (s' : State),
    sys.simulate (Strat.f ⟨a, dChooseFromSet ps⟩) s n = (s', 0) → ps ⊆ s'.taken)
  · replace hs := s.aState_or_dState.symm
    rcases hs with hs | hs
    · apply ihd; exact hm
    by_cases h₁ : ¬sys.hasTr s
    · use 1
      rintro n hn s' h₂
      cases n; simp at hn
      contrapose! h₁
      simp only [System.simulate_succ_full'] at h₂
      simp at h₂
      choose s₁ h₃ h₂ using h₂
      exact sys.hasTr_of_eq_some h₃
    push Not at h₁
    obtain ⟨s', h₂⟩ := a.validTr h₁
    have hs' := DState.of_tr h₂
    specialize ihd s' ps hm
    obtain ⟨N, ihd⟩ := ihd
    dsimp at ihd
    use N + 1
    intro n hn s₁ h₃
    cases n; simp at hn; nm n
    specialize ihd n (by linarith) s₁
    simp only [System.simulate_succ_full'] at h₃
    simp [h₂] at h₃
    exact ihd h₃
  clear! s ps
  intro s hs ps h
  obtain ⟨s₁, h₁⟩ := dChooseFromSet ps |>.validTr s
  have h₁' := h₁
  simp [dChooseFromSet, choose?_eq_ite] at h₁
  split_ifs at h₁ with h₂
  · have h₃ := τ_spec h₂
    generalize (τ p, p ∈ ps ∧ p ∉ s.taken ∧ ¬p = s.aPos) = p at h₁ h₃
    rcases h₃ with ⟨h₃, h₄, h₅⟩
    simp [DState.validTr_iff, ne_symm' h₅, h₄] at h₁
    have hs₁ := sys.wf_of_tr h₁
    specialize @ih s₁ (ps.erase p) hs₁ _
    · simp [Set'.size_erase h₃, h]
    obtain ⟨N, ih⟩ := ih
    dsimp at ih
    use N + 1
    intro n hn s₂ h₆
    cases n; simp at hn; nm n
    specialize ih n (by linarith) s₂
    simp only [System.simulate_succ_full'] at h₆
    simp [h₁'] at h₆
    have G := sys.reachable_of_simulate h₆
    have H₀ : p ∈ s₁.taken
    · exact DState.mem_taken_of_tr h₁
    suffices H : ps.erase p ⊆ s₂.taken
    · intro p₁ hp₁
      specialize H p₁
      simp [hp₁] at H
      by_cases h₇ : p = p₁
      · subst h₇
        exact mem_taken_of_reachable G H₀
      exact H h₇
    apply ih; clear ih
    convert h₆ using 1; clear h₆
    apply simulate_congr <;> simp
    intro k hk sd hsd H₁ H₂ H₃
    simp [dChooseFromSet]
    congr
    ext p₁
    simp
    rintro H₄ H₅ H₆ rfl
    apply H₄
    apply mem_taken_of_reachable # sys.reachable_of_simulate H₁
    exact H₀
  simp at h₁
  push Not at h₂
  by_cases h₃ : s.aPos ∉ ps
  · use 0
    intro n hn s₂ h₄ p₁ hp₁
    have H₁ := sys.reachable_of_simulate h₄
    specialize h₂ _ hp₁
    contrapose! h₂
    constructor
    · contrapose! h₂
      exact mem_taken_of_reachable H₁ h₂
    rintro rfl
    contradiction
  rename' s₁ => sa
  have hsa := AState.of_tr h₁
  push Not at h₃
  clear! m
  suffices h : eventually # λ n => ∀ (s' : State),
    sys.simulate (Strat.f ⟨a, dChooseFromSet ps⟩) s n = (s', 0) → s.aPos ∈ s'.taken
  · obtain ⟨N, h⟩ := h
    use N
    intro n hn s₁ H₁
    have H₂ := sys.reachable_of_simulate H₁
    specialize h n hn s₁ H₁
    intro p₁ hp₁
    specialize h₂ _ hp₁
    contrapose! h₂
    constructor
    · contrapose! h₂
      exact mem_taken_of_reachable H₂ h₂
    rintro rfl
    contradiction
  by_cases h₄ : ¬sys.hasTr sa
  · use 2
    intro n hn s₁ H₁
    iterate 2 cases n; simp at hn; nm n
    contrapose! h₄
    simp only [System.simulate_succ_full'] at H₁
    simp [h₁'] at H₁
    choose s₂ H₂ H₁ using H₁
    exact sys.hasTr_of_eq_some H₂
  push Not at h₄
  replace h₄ := a.validTr h₄
  obtain ⟨sd, h₄⟩ := h₄
  have hsd := DState.of_tr h₄
  obtain ⟨s₁, h₅⟩ := (dChooseFromSet ps).validTr sd
  have hs₁ := AState.of_tr h₅
  have h₅' := h₅
  simp [dChooseFromSet, choose?_eq_ite] at h₅
  split_ifs at h₅ with h₆
  rotate_left
  · exfalso; apply h₆
    clear h₅ h₅'
    use s.aPos
    rw [AState.tr_eq_some_iff] at h₄
    rcases h₄ with ⟨⟨h₄, h₅, h₆⟩, rfl⟩
    simp [←DState.aPos_eq_of_tr h₁'] at h₃ ⊢
    clear hsd
    use h₃
  have h₇ := τ_spec h₆
  generalize (τ y, y ∈ ps ∧
    y ∉ sd.taken ∧ y ≠ sd.aPos) = pa at h₅ h₇
  rcases h₇ with ⟨h₇, h₈, h₉⟩
  simp [DState.validTr_iff, ne_symm' h₉, h₈] at h₅
  use 3
  intro n hn s₂ H₂
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn; clear hn
  rw [add_comm] at H₂
  simp only [System.simulate_succ_full'] at H₂
  simp [h₁', h₄, h₅'] at H₂
  apply mem_taken_of_reachable # sys.reachable_of_simulate H₂
  simp [DState.taken_eq_of_tr h₅, AState.taken_eq_of_tr h₄]
  rw [or_iff_not_imp_right, eq_comm]
  intro H₃
  specialize h₂ _ h₇
  apply h₂
  clear h₂
  contrapose! h₈
  apply mem_taken_of_reachable _ h₈
  exact sys.reachable_of_tr h₁' |>.trans # sys.reachable_of_tr h₄

theorem State.eventually_simulate_dChooseFromSet_aPos_not_mem {s}
{ps : Set' PointZ} {a : AStrat} [hs : sys.WF s] [ha : a.WF] :
eventually # λ n => ∀ s', sys.simulate (Strat.f ⟨a, dChooseFromSet ps⟩) s n = (s', 0) →
s'.aPos ∉ ps := by
  obtain ⟨N, h⟩ := s.eventually_simulate_dChooseFromSet_subset_taken (ps := ps) (a := a)
  dsimp at h
  use N
  intro n hn s' h₁
  specialize h n hn s' h₁
  have hs' : sys.WF s'; grind
  intro h₂
  specialize h _ h₂
  simp at h

theorem State.aTurn_of_tr_aPos_ne {s s' p} [hs : sys.WF s]
(h₁ : sys.tr s p = some s') (h₂ : s'.aPos ≠ s.aPos) : s.aTurn := by
  contrapose! h₂; simp at h₂; replace hs : DState s; use hs; exact hs.aPos_eq_of_tr h₁

theorem AState.of_tr_aPos_ne {s s' p} [hs : sys.WF s]
(h₁ : sys.tr s p = some s') (h₂ : s'.aPos ≠ s.aPos) : AState s :=
  ⟨hs, s.aTurn_of_tr_aPos_ne h₁ h₂⟩

theorem State.aForallWinsDisj_of_simulate_eq {fsp : FSP} {s s' r n}
{a : AStrat} {d : DStrat} [hs : sys.WF s] [ha : a.WF] [hd : d.WF]
(h₁ : s.aForallWinsDisj fsp a) (h₂ : sys.simulate (Strat.f ⟨a, d⟩) s n = (s', r)) :
s'.aForallWinsDisj (fsp.offset n) a := by
  choose s₁ h₃ h₄ using h₁ d hd n
  simp [h₃] at h₂
  rcases h₂ with ⟨rfl, rfl⟩
  intro d₁ hd₁ k
  generalize hd₂ : DStrat.mk (λ sd => if sd.hist.length - s.hist.length < n
    then d.f sd else d₁.f sd) = d₂
  have Hd₂ : d₂.WF; subst hd₂; infer_instance
  choose s₂ h₁ h₅ using h₁ d₂ Hd₂ (n + k)
  have G₃ : sys.simulate (Strat.f ⟨a, d₂⟩) s n = (s₁, 0)
  · convert h₃ using 1
    apply simulate_congr <;> simp
    intro m hm sd hsd H₁ H₂ H₃
    rw [←hd₂]
    simp [length_hist_eq_of_simulate_eq H₁, hm]
  simp [sys.simulate_add, G₃] at h₁
  use s₂
  split_ands
  · have hs₁ : sys.WF s₁; grind
    convert h₁ using 1
    apply simulate_congr <;> simp
    intro m hm sd hsd H₁ H₂ H₃
    rw [←hd₂]
    simp [length_hist_eq_of_simulate_eq H₁, length_hist_eq_of_simulate_eq G₃]
    rw [if_neg # by omega]
    simp
  · rwa [FSP.hasLe_offset, add_comm]

theorem State.aForallWinsDisj_insertSet_zero_of {s set} {a : AStrat} {fsp : FSP}
(h₁ : s.aForallWinsDisj fsp a) (h₂ : ∀ (d : DStrat) [d.WF] n s₁,
sys.simulate (Strat.f ⟨a, d⟩) s n = (s₁, 0) → s₁.aPos ∉ set) :
s.aForallWinsDisj (fsp.insertSet 0 set) a := by
  intro d hd
  specialize h₁ d hd
  specialize h₂ d
  rw [aWinsDisj_iff] at h₁ ⊢
  rcases h₁ with ⟨h₁, h₃⟩
  use h₁
  intro n
  specialize h₁ n
  specialize h₂ n
  specialize h₃ n
  generalize sys.simulate (Strat.f ⟨a, d⟩) s n = r at h₁ h₂ h₃ ⊢
  rcases r with ⟨s₁, r⟩
  dsimp at h₁ h₃ ⊢
  subst h₁
  simp at h₂
  simp [FSP.hasLe] at h₃ ⊢
  intro k hk
  specialize h₃ k hk
  simp [FSP.insertSet]
  grind

@[simp]
theorem State.aWinsDisj_empty {s : State} {st} : s.aWinsDisj ∅ st ↔ s.aWins st := by
  simp [aWinsDisj, aWins, Prod.ext_iff]

@[simp]
theorem State.aForallWinsDisj_empty {s : State} {a} :
s.aForallWinsDisj ∅ a ↔ ∀ (d : DStrat), d.WF → s.aWins ⟨a, d⟩ := by
  simp [aForallWinsDisj]

@[simp]
theorem State.aHwsDisj_empty {s : State} : s.aHwsDisj ∅ ↔ s.aHws := by
  simp [aHwsDisj, aHws]

theorem State.aHws_of_taken_subset {s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h₁ : s.aHws) (hpw : s'.pw = s.pw) (h₂ : s'.aTurn = s.aTurn) (h₃ : s'.aPos = s.aPos)
(h₄ : s'.taken ⊆ s.taken) : s'.aHws := by
  rw [←aHwsDisj_empty] at h₁ ⊢; exact aHwsDisj_of_taken_subset' h₁ hpw h₂ h₃ h₄

theorem State.dHws_of_taken_subset {s s'} [hs : sys.WF s] [hs' : sys.WF s']
(h₁ : s.dHws) (hpw : s'.pw = s.pw) (h₂ : s'.aTurn = s.aTurn) (h₃ : s'.aPos = s.aPos)
(h₄ : s.taken ⊆ s'.taken) : s'.dHws := by
  contrapose h₁; simp at h₁ ⊢; symm at hpw h₂ h₃
  exact s'.aHws_of_taken_subset h₁ hpw h₂ h₃ h₄