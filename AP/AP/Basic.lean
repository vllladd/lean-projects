import AP.AP.Defs

namespace AP

theorem aStrat_valid_def {a : AStrat} : a.Valid ↔ ∀ {s} [sys.Valid s],
sys.hasTr s → s.aTurn → sys.validTr s (a.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem dStrat_valid_def {d : DStrat} : d.Valid ↔ ∀ {s} [sys.Valid s],
sys.hasTr s → s.aTurn = false → sys.validTr s (d.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem strat_valid_def {st : Strat} : st.Valid ↔ ∀ {s} [sys.Valid s],
sys.hasTr s → sys.validTr s (st.f s) := ⟨λ ⟨h⟩ => h, λ h => ⟨h⟩⟩

theorem strat_valid_iff {st : Strat} : st.Valid ↔ st.a.Valid ∧ st.d.Valid := by
  rw [strat_valid_def, aStrat_valid_def, dStrat_valid_def]
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

theorem Strat.Valid.a_valid {st : Strat} [hst : st.Valid] : st.a.Valid := by
  rw [strat_valid_iff] at hst; exact hst.1

theorem Strat.Valid.d_valid {st : Strat} [hst : st.Valid] : st.d.Valid := by
  rw [strat_valid_iff] at hst; exact hst.2

instance {st : Strat} [hst : st.Valid] : st.a.Valid := hst.a_valid
instance {st : Strat} [hst : st.Valid] : st.d.Valid := hst.d_valid

abbrev State.Valid (s : State) : Prop := sys.Valid s

@[class]
structure State.AState (s : State) : Prop where
  h_valid : s.Valid
  h : s.aTurn

@[class]
structure State.DState (s : State) : Prop where
  h_valid : s.Valid
  h : s.aTurn = false

theorem aState_def {s : State} : s.AState ↔ s.Valid ∧ s.aTurn :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem dState_def {s : State} : s.DState ↔ s.Valid ∧ s.aTurn = false :=
  ⟨λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

def State.dChooseMove (s : State) : PointZ :=
  (insert s.a_pos s.taken).max! + ⟨1, 0⟩

@[simp]
theorem a_valid_tr_iff {s : State} [hs : s.AState] {p} :
sys.validTr s p ↔ s.a_pos ≠ p ∧ p ∉ s.taken ∧ p.dist s.a_pos ≤ s.pw := by
  rcases hs with ⟨hs, ht⟩
  constructor
  · rintro ⟨s', h₁⟩
    simp [sys, State.move, State.aMove, ht] at h₁
    rcases h₁ with ⟨h₁, _, rfl⟩
    exact h₁
  · rintro h
    use (s.move p).get!
    simp [sys, State.move, State.aMove, ht, h]

@[simp]
theorem d_valid_tr_iff {s : State} [hs : s.DState] {p} :
sys.validTr s p ↔ s.a_pos ≠ p ∧ p ∉ s.taken := by
  rcases hs with ⟨hs, ht⟩
  constructor
  · rintro ⟨s', h₁⟩
    simp [sys, State.move, State.dMove, ht] at h₁
    rcases h₁ with ⟨h₁, _, rfl⟩
    exact h₁
  · rintro h
    use (s.move p).get!
    simp [sys, State.move, State.dMove, ht, h]

@[simp]
theorem State.DState.hasTr {s : State} [hs : s.DState] : sys.hasTr s := by
  use s.dChooseMove; simp
  suffices h₁ : s.dChooseMove ∉  insert s.a_pos s.taken
  · simp at h₁; rw [eq_comm]; exact h₁
  apply Set'.not_mem_of_max!_lt
  simp [State.dChooseMove, Point.zero_def]

theorem d_has_move {s : State} [hs : s.DState] : sys.hasTr s :=
  hs.hasTr