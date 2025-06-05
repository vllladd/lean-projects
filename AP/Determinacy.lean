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
theorem game₀_state' {pw a d} : (game₀ pw a d).toState' = state'₀ pw := rfl

def AState.a_hws (s : AState) := ∃ a, ∀ d, (s.to_game a d).a_wins
def AState.d_hws (s : AState) := ∃ d, ∀ a, (s.to_game a d).d_wins

theorem a_state_move'_of_move {sa : AState} {sd}
(h : sa.move sd) : sa.move' sd := h.1

theorem d_state_move'_of_move {sd : DState} {sa}
(h : sd.move sa) : sd.move' sa := h.1

theorem game_le_of_play_size_eq_size_add {g : Game} {n x}
(h : (g.play n).size = g.size + x) : x ≤ n := by
  by_contra! h₁
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  clear h₁
  have h₁ := @game_play_size_lt_iff_play_ended g n
  by_cases h₂ : (g.play n).ended <;> simp [h₂] at h₁
  · by_cases h₃ : g.ended
    · rw [game_play_eq_of_ended h₃] at h
      simp at h
    · specialize h₁ h₃
      rw [h] at h₁
      linarith
  rw [game_play_size_eq_of_not_ended h₂] at h
  linarith

theorem game_play_size_eq_self_of_any {g : Game} {n x}
(h : (g.play n).size = g.size + x) : (g.play x).size = g.size + x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le # game_le_of_play_size_eq_size_add h
  simp at h
  by_cases he : (g.play x).ended
  · simp [game_play_eq_of_ended he] at h
    exact h
  apply game_play_size_eq_of_not_ended he

theorem game₀_play_size_eq_self_of_any {pw a d x} (n : ℕ)
(h : ((game₀ pw a d).play n).size = x) : ((game₀ pw a d).play x).size = x := by
  generalize hg : game₀ pw a d = g at *
  replace h : (g.play n).size = g.size + x :=
    by
      nth_rewrite 2 [←hg]
      simpa
  replace h := game_play_size_eq_self_of_any h
  nth_rewrite 2 [←hg] at h
  simp at h
  exact h

def d_state₀ (pw : ℕ) : DState := by
  refine' ⟨⟨state₀ pw, _⟩, _⟩ <;> simp

def a_state₀ (pw : ℕ) : AState :=
  Classical.epsilon (d_state₀ pw).move

@[simp]
theorem d_state₀_toState_eq {pw} : (d_state₀ pw).toState = state₀ pw := rfl

@[simp]
theorem state_mk_size {s' hist} : (⟨s', hist⟩ : State).size = hist.length := rfl

#check 0 #exit

theorem exi_d_state₀_move {pw} : ∃ sa, (d_state₀ pw).move sa := by
  have ⟨s, hs⟩ := d_always_has_move #
    state'_valid_of_state_valid (d_state₀ pw).h_valid
  dsimp only [d_state₀] at hs
  refine' ⟨⟨⟨⟨s, [state'₀ pw]⟩, _⟩, _⟩, _⟩
  · have ⟨g, hg⟩ := hv # game₀ pw default #
      mk_strat_const s
    refine' ⟨g.move, _, _⟩; simp [hg]
    simp [hg, Game.move]
    rw [strat_set_ap_of_eq hs]
    rfl
  · simp
  · unfold DState.move

#check 0 #exit

theorem exi_a_state_move : ∃ (sa : AState) (sd : DState), sa.move sd := by
  obtain ⟨⟨s, g, ⟨pw, a, d, n, rfl⟩, rfl⟩, h⟩ := exi_valid_state_with_size 2
  dsimp at h
  generalize hg₀ : game₀ pw a d = g₀ at h; rw [eq_comm] at hg₀
  obtain ⟨g, hg⟩ := hv # g₀.play 2
  have h₁ : g.size = 2 :=
    by
      subst hg₀ hg
      exact game₀_play_size_eq_self_of_any n h
  rw [exists_swap]
  use d_state₀ pw

#check 0 #exit

theorem not_a_state_move'_imp_move :
¬∀ (sa : AState) (sd : DState), sa.move' sd → sa.move sd := by
  push_neg
  use default

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