import AP.Reachability

noncomputable section
open scoped Classical

@[simp]
theorem not_a_wins_iff {g : Game} : ¬g.a_wins ↔ g.d_wins := by
  simp [Game.d_wins]

@[simp]
theorem not_d_wins_iff {g : Game} : ¬g.d_wins ↔ g.a_wins := by
  simp [Game.a_wins, Game.d_wins]

theorem not_d_hws_of_a_hws {pw} (h : a_hws pw) : ¬d_hws pw := by
  obtain ⟨a, h⟩ := h; simp [d_hws]; intro d; use a, h d

theorem not_a_hws_of_d_hws {pw} (h : d_hws pw) : ¬a_hws pw := by
  contrapose! h; exact not_d_hws_of_a_hws h

@[simp]
theorem game₀_a {pw a d} : (game₀ pw a d).a = a := rfl

@[simp]
theorem game₀_d {pw a d} : (game₀ pw a d).d = d := rfl

@[simp]
theorem game₀_state' {pw a d} : (game₀ pw a d).state' = state'₀ pw := rfl

@[simp]
theorem game₀_a_turn {pw a d} : ¬(game₀ pw a d).a_turn := λ h => h

-- def State'.winning pw (s : State') := ∃ a, ∀ (g : Game) n,
--   g.pw = pw → g.a = a → g.state' = s → g.a_turn → ¬(g.play n).ended

#check 0 #exit

theorem state'₀_winning_iff_a_hws {pw} : (state'₀ pw).winning pw ↔ a_hws pw := by
  simp [State'.winning, a_hws]
  rw [exists_congr]
  intro a
  apply Iff.intro <;> intro h
  · intro d n
    specialize h (game₀ pw a d) n
    simp at h

#check 0 #exit

theorem a_hws_of_not_d_hws {pw} (h : ¬d_hws pw) : a_hws pw := by
  simp [d_hws] at h
  sorry

theorem d_hws_of_not_a_hws {pw} (h : ¬a_hws pw) : d_hws pw := by
  contrapose! h; exact a_hws_of_not_d_hws h

@[simp]
theorem not_a_hws_iff {pw} : ¬a_hws pw ↔ d_hws pw :=
  ⟨d_hws_of_not_a_hws, not_a_hws_of_d_hws⟩

@[simp]
theorem not_d_hws_iff {pw} : ¬d_hws pw ↔ a_hws pw := by
  simp [not_iff_comm]