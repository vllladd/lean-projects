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
theorem game₀_state' {pw a d} : (game₀ pw a d).toState' = state'₀ pw := rfl

@[simp]
theorem game₀_a_turn {pw a d} : ¬(game₀ pw a d).a_turn := λ h => h

#check 0 #exit

def a_optimal_fn : Strat := λ s =>
  let sa := Classical.epsilon λ (sa : AState) => sa.toState = s
  let p := λ (sd : DState) => sa.move sd ∧ ∀ sa₂, sd.move sa₂ → sa₂.winning
  if ¬sa.has_move then node else some #
  if ∃ sd, p sd then Classical.epsilon p
  else Classical.epsilon 

def a_optimal : AStrat := by
  use a_optimal_fn

#check 0 #exit

theorem a_hws_of_not_d_hws {pw} (h : ¬d_hws pw) : a_hws pw := by
  simp [d_hws] at h
  sorry

#check 0 #exit

theorem d_hws_of_not_a_hws {pw} (h : ¬a_hws pw) : d_hws pw := by
  contrapose! h; exact a_hws_of_not_d_hws h

@[simp]
theorem not_a_hws_iff {pw} : ¬a_hws pw ↔ d_hws pw :=
  ⟨d_hws_of_not_a_hws, not_a_hws_of_d_hws⟩

@[simp]
theorem not_d_hws_iff {pw} : ¬d_hws pw ↔ a_hws pw := by
  simp [not_iff_comm]

theorem a_losing_iff {sa : AState} :
sa.losing ↔ ∀ sd, sa.move sd → ∃ sa₂, sd.move sa₂ ∧ sa₂.losing := by
  sorry

theorem a_winning_iff {sa : AState} :
sa.winning ↔ ∃ sd, sa.move sd ∧ ∀ sa₂, sd.move sa₂ → sa₂.winning := by
  sorry