import AP.Strategy

noncomputable section
open scoped Classical

theorem card_grid_diff_subsingleton_of_subsingleton_pw_0_a_turn {g : Game} {n}
(h_pw : g.pw = 0) (h :  (Set.univ \ g.grid).Subsingleton)
(ht : g.a_turn) : (Set.univ \ (g.play n).grid).Subsingleton := by
  unfold State'.grid at h ⊢; cases n; exact h; nm n; rw [game_play_succ']
  have h₁ : g.move.ended := by
    simp [Game.move, ht]; split_ifs with h₂
    exact h₂; split; simp; nm m s h₁; replace h₁ := of_a_ap_eq_some' h₁
    rw [a_has_move_iff] at h₁; unfold State'.pw at h_pw; simp [h_pw] at h₁
  rwa [game_play_eq_of_ended h₁, ←State'.grid,
    game_move_grid_eq_of_move_ended h₁, State'.grid]

theorem card_grid_diff_subsingleton_of_state'₀_0_a_turn {g : Game} {n}
(h :  g.toState' = state'₀ 0) (ht : g.a_turn) :
(Set.univ \ (g.play n).grid).Subsingleton := by
  apply card_grid_diff_subsingleton_of_subsingleton_pw_0_a_turn <;>
  simp [h, ht]

theorem card_grid_diff_subsingleton_of_state'₀_0_not_a_turn {g : Game} {n}
(h :  g.toState' = state'₀ 0) (ht : ¬g.a_turn) :
(Set.univ \ (g.play n).grid).Subsingleton := by
  by_cases he : g.ended
  · simp [Game.move, he, game_play_eq_of_ended he, h]
  cases n; simp [h]; nm n; rw [game_play_succ']
  apply card_grid_diff_subsingleton_of_subsingleton_pw_0_a_turn
  · simp [h]
  · simp [Game.move, he, ht]; split; simp [h]
    nm m s h₁; simp; replace h₁ := of_d_ap_eq_some h₁
    obtain ⟨p, rfl, h₁, h₂⟩ := h₁; simp [h]
    rw [Set.diff_erase_self_eq_of_mem] <;> simp
  simp [Game.move, ht, he]; split
  · nm m h₁; simp at h₁; apply h₁
    apply d_always_has_move; simp [h]
  trivial

theorem card_grid_diff_subsingleton_of_state'₀_0 {g : Game} {n}
(h :  g.toState' = state'₀ 0) :
(Set.univ \ (g.play n).grid).Subsingleton := by
  by_cases h₁ : g.a_turn
  exact card_grid_diff_subsingleton_of_state'₀_0_a_turn h h₁
  exact card_grid_diff_subsingleton_of_state'₀_0_not_a_turn h h₁

theorem not_Reachable'_imp_reachable :
¬(∀ (s₀ s : State'), s₀.Reachable' s → s₀.reachable s) := by
  push_neg; obtain ⟨s₁, hs₁⟩ := hv #
    {state'₀ 0 with grid := Set.univ \ {(0, 1)}}
  obtain ⟨s₂, hs₂⟩ := hv #
    {state'₀ 0 with grid := Set.univ \ {(0, 1), (0, 2)}}
  dsimp at hs₁ hs₂; use state'₀ 0, s₂
  constructor
  · apply State'.Reachable'.hd s₁
    · apply State'.Reachable'.hd # state'₀ 0
      constructor; use ⟨0, 1⟩; simp [hs₁, hs₂, Set.erase]
    use ⟨0, 2⟩; simp [hs₁, hs₂, Set.erase, Set.diff_upair]
  simp [State'.reachable]; rintro g h₁ n rfl
  rw [eq_comm] at h₁; have h₂ := congrArg State'.grid hs₂
  dsimp at h₂; contrapose! h₂; clear h₂
  apply ne_of_congr λ s => (Set.univ \ s).Subsingleton
  simp [h₁]; exact card_grid_diff_subsingleton_of_state'₀_0 h₁