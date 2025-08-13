import AP.AP.Defs

namespace AP

theorem aStrat_wf_def {a : AStrat} : a.WF ↔ ∀ {s} [sys.WF s],
sys.hasTr s → s.aTurn → sys.validTr s (a.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem dStrat_wf_def {d : DStrat} : d.WF ↔ ∀ {s} [sys.WF s],
sys.hasTr s → s.aTurn = false → sys.validTr s (d.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem strat_wf_def {st : Strat} : st.WF ↔ ∀ {s} [sys.WF s],
sys.hasTr s → sys.validTr s (st.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem strat_wf_iff {st : Strat} : st.WF ↔ st.a.WF ∧ st.d.WF := by
  rw [strat_wf_def, aStrat_wf_def, dStrat_wf_def]
  simp [System.hasTr, System.validTr, Strat.f]
  constructor
  · intro h
    constructor
    all_goals
      intro s hs p s' h₁ h₂
      specialize h _ _ h₁
      simp [h₂] at h
      exact h
  · rintro ⟨h₁, h₂⟩
    intro s hs p s' h₃
    split_ifs with h₄
    · exact h₁ _ _ h₃ h₄
    · simp at h₄; exact h₂ _ _ h₃ h₄

theorem Strat.WF.a_valid {st : Strat} [hst : st.WF] : st.a.WF := by
  rw [strat_wf_iff] at hst; exact hst.1

theorem Strat.WF.d_valid {st : Strat} [hst : st.WF] : st.d.WF := by
  rw [strat_wf_iff] at hst; exact hst.2

instance {st : Strat} [hst : st.WF] : st.a.WF := hst.a_valid
instance {st : Strat} [hst : st.WF] : st.d.WF := hst.d_valid

abbrev State.WF (s : State) : Prop := sys.WF s

@[class]
structure State.AState (s : State) : Prop where
  h_valid : s.WF
  h : s.aTurn

@[class]
structure State.DState (s : State) : Prop where
  h_valid : s.WF
  h : s.aTurn = false

theorem aState_def {s : State} : s.AState ↔ s.WF ∧ s.aTurn :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem dState_def {s : State} : s.DState ↔ s.WF ∧ s.aTurn = false :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

def State.dChooseMove (s : State) : PointZ :=
  (insert s.aPos s.taken).max! + ⟨1, 0⟩

@[simp]
theorem State.AState.turn {s : State} [hs : s.AState] : s.aTurn := by
  cases hs; assumption

@[simp]
theorem State.DState.turn {s : State} [hs : s.DState] : s.aTurn = false := by
  cases hs; assumption

theorem State.validTr_iff_of_aTurn {s : State} {p} (ht : s.aTurn) :
sys.validTr s p ↔ s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw := by
  constructor
  · rintro ⟨s', h₁⟩
    simp [sys, State.move, State.aMove, ht] at h₁
    rcases h₁ with ⟨h₁, _, rfl⟩
    exact h₁
  · rintro h
    use (s.move p).get!
    simp [sys, State.move, State.aMove, ht, h]

theorem State.validTr_iff_of_not_aTurn {s : State} {p} (ht : s.aTurn = false) :
sys.validTr s p ↔ s.aPos ≠ p ∧ p ∉ s.taken := by
  constructor
  · rintro ⟨s', h₁⟩
    simp [sys, State.move, State.dMove, ht] at h₁
    rcases h₁ with ⟨h₁, _, rfl⟩
    exact h₁
  · rintro h
    use (s.move p).get!
    simp [sys, State.move, State.dMove, ht, h]

@[simp]
theorem State.AState.validTr_iff {s : State} [hs : s.AState] {p} :
sys.validTr s p ↔ s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw := by
  apply s.validTr_iff_of_aTurn; simp

@[simp]
theorem State.DState.validTr_iff {s : State} [hs : s.DState] {p} :
sys.validTr s p ↔ s.aPos ≠ p ∧ p ∉ s.taken := by
  apply s.validTr_iff_of_not_aTurn; simp

theorem State.validTr_dChooseMove {s : State} (ht : s.aTurn = false) :
sys.validTr s s.dChooseMove := by
  rw [s.validTr_iff_of_not_aTurn ht]
  suffices h₁ : s.dChooseMove ∉ insert s.aPos s.taken
  · simp at h₁; rw [ne_comm]; exact h₁
  apply Set'.not_mem_of_max!_lt
  simp [State.dChooseMove, Point.zero_def]

theorem State.hasTr_of_not_aTurn {s : State} (ht : s.aTurn = false) : sys.hasTr s := by
  use s.dChooseMove; exact s.validTr_dChooseMove ht

@[simp]
theorem State.DState.hasTr {s : State} [hs : s.DState] : sys.hasTr s := by
  apply s.hasTr_of_not_aTurn; simp

def State.aMoves (s : State) : List PointZ := do
  let ⟨ax, ay⟩ := s.aPos
  let ds := List.map (Int.ofNat · - s.pw) #
    List.range # s.pw * 2 + 1
  let x ← ds
  let y ← ds
  let p := ⟨ax + x, ay + y⟩
  guard # sys.validTr s p
  return p

def State.aHasMove (s : State) : Bool :=
  s.aMoves ≠ []

theorem State.hasTr_iff_of_aTurn {s : State} (ht : s.aTurn) :
sys.hasTr s ↔ ∃ p, s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw := by
  simp [sys, System.hasTr_iff, move, aMove, ht]

@[simp]
theorem State.AState.hasTr_iff {s : State} [hs : s.AState] :
sys.hasTr s ↔ ∃ p, s.aPos ≠ p ∧ p ∉ s.taken ∧ p.dist s.aPos ≤ s.pw := by
  simp [s.hasTr_iff_of_aTurn]

theorem State.aHasMove_of_hasTr {s : State}
(ht : s.aTurn) (h : sys.hasTr s) : s.aHasMove := by
  simp [aHasMove, aMoves, s.hasTr_iff_of_aTurn ht] at h ⊢
  simp [sys, move, aMove, ht]; clear ht
  rcases h with ⟨p, h₁, h₂, h₃⟩
  use Int.toNat # s.pw + p.x - s.aPos.x
  constructor
  rotate_left
  use Int.toNat # s.pw + p.y - s.aPos.y
  constructor
  any_goals
    clear h₁ h₂
    cases s; nm pw taken aPos aTurn hist
    simp [PointZ.dist] at h₃ ⊢
    rw [←Int.le_iff_lt_add_one]
    rcases h₃ with ⟨h₁, h₂⟩
    rw [Int.add_sub_assoc, mul_two]
    simp
    replace h₁ := le_of_max_le_left h₁
    replace h₂ := le_of_max_le_left h₂
    linarith
  simp
  cases s; nm pw taken aPos aTurn hist
  constructor
  · simp [PointZ.dist] at h₁ h₃ ⊢; clear h₂
    convert h₁ <;> rcases h₃ with ⟨h₁, h₂⟩
    · have h₃ : max (pw + p.x - aPos.x) 0 = pw + p.x - aPos.x := by
        apply max_eq_left
        replace h₁ := le_of_max_le_right h₁
        linarith
      rw [h₃]
      ring
    · have h₃ : max (pw + p.y - aPos.y) 0 = pw + p.y - aPos.y := by
        apply max_eq_left
        replace h₂ := le_of_max_le_right h₂
        linarith
      rw [h₃]
      ring
  constructor
  · simp [PointZ.dist] at h₃ ⊢
    dsimp at h₁ h₂
    rcases h₃ with ⟨h₅, h₆⟩
    replace h₅ : max (pw + p.x - aPos.x) 0 = pw + p.x - aPos.x := by
      apply max_eq_left
      replace h₅ := le_of_max_le_right h₅
      linarith
    replace h₆ : max (pw + p.y - aPos.y) 0 = pw + p.y - aPos.y := by
      apply max_eq_left
      replace h₆ := le_of_max_le_right h₆
      linarith
    simp [h₅, h₆]
    ring_nf
    exact h₂
  dsimp at h₁ h₂ h₃ ⊢
  rw [PointZ.dist.comm]
  convert h₃
  · simp [PointZ.dist] at h₃
    rcases h₃ with ⟨h₃, h₄⟩
    replace h₃ : max (pw + p.x - aPos.x) 0 = pw + p.x - aPos.x := by
      apply max_eq_left
      replace h₃ := le_of_max_le_right h₃
      linarith
    rw [h₃]
    linarith
  · simp [PointZ.dist] at h₃
    rcases h₃ with ⟨h₃, h₄⟩
    replace h₄ : max (pw + p.y - aPos.y) 0 = pw + p.y - aPos.y := by
      apply max_eq_left
      replace h₄ := le_of_max_le_right h₄
      linarith
    rw [h₄]
    linarith

theorem State.hasTr_of_aHasMove {s : State} (ht : s.aTurn)
(h : s.aHasMove) : sys.hasTr s := by
  simp [aHasMove, aMoves, s.hasTr_iff_of_aTurn ht] at h ⊢
  simp [sys, move, aMove, ht] at h
  rcases h with ⟨x, hx, y, hy, h₁⟩
  rcases h₁ with ⟨h₁, h₂, h₃⟩
  use ⟨s.aPos.x + (x - s.pw), s.aPos.y + (y - s.pw)⟩
  use h₁, h₂
  rw [PointZ.dist.comm]
  exact h₃

theorem State.hasTr_iff_aHasMove {s : State} (ht : s.aTurn) :
sys.hasTr s ↔ s.aHasMove := ⟨s.aHasMove_of_hasTr ht, s.hasTr_of_aHasMove ht⟩

theorem State.WF.ind_turn {P : State → Prop}
(h₁ : ∀ (s : State), s.AState → P s) (h₂ : ∀ (s : State), s.DState → P s)
{s : State} (hs : s.WF) : P s := by
  cases ht : s.aTurn
  · apply h₂; constructor <;> assumption
  · apply h₁; constructor <;> assumption

@[simp]
def State.hasMove (s : State) : Bool :=
  if s.aTurn then s.aHasMove else true

theorem State.hasTr_iff_hasMove {s : State} : sys.hasTr s ↔ s.hasMove := by
  simp; cases ht : s.aTurn <;> simp
  · exact hasTr_of_not_aTurn ht
  · exact hasTr_iff_aHasMove ht

instance {s : State} : Decidable (sys.hasTr s) :=
  match h : s.hasMove with
  | true => .isTrue # by rwa [s.hasTr_iff_hasMove]
  | false => .isFalse # by rw [s.hasTr_iff_hasMove, h]; simp