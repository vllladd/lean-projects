import AP.Mono

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
theorem game₀_state' {pw a d} : (game₀ pw a d).toState' = state'₀ pw := rfl

def AState.a_hws (s : AState) := ∃ a, ∀ d, (s.to_game a d).a_wins
def AState.d_hws (s : AState) := ∃ d, ∀ a, (s.to_game a d).d_wins

#check 0 #exit

theorem not_d_hws_next_of_not_d_hws {sa : AState} (h : ¬sa.d_hws) :
∃ sd, sa.move sd ∧ ∀ sa₂, sd.move sa₂ → ¬sa₂.d_hws := by
  unfold AState.d_hws at h ⊢
  contrapose! h

#check 0 #exit

def AStrat.set (s : State) (p : Point) (a : AStrat) : AStrat := by

#check 0 #exit

theorem a_hws_iff_state₀_d_move_a_hws {pw} : a_hws pw ↔
∀ (s₁ : State), (state₀ pw).d_move s₁.toState' → s₁.a_hws := by
  unfold a_hws State.a_hws
  constructor
  · rintro ⟨a, h⟩ s hs
    use a
    intro d

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

theorem state_with_hist_a_hws_iff {s : State} {hist} :
{s with hist := hist}.a_hws ↔ s.a_hws := by
  sorry

example {sa : State} (h : ¬sa.d_hws) :
∃ sd, sa.a_move sd ∧ ∀ sa₂, sd.d_move sa₂ →
∃ (s : State), s.toState' = sa₂ ∧ ¬s.d_hws := by

example {sa : State} (h : ¬sa.d_hws) :
∃ sd, sa.a_move sd ∧ ∀ (sa₂ : State), sd.d_move sa₂.toState' → ¬sa₂.d_hws := by