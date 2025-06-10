import AP.Reachability

noncomputable section
open scoped Classical

theorem point_not_mem_play_grid_of_not_mem_grid {g : Game} {p n}
(h : ¬p ∈ g.grid) : ¬p ∈ (g.play n).grid := by
  induction n
  · exact h
  nm n ih
  simp
  generalize hg₁ : g.play n = g₁ at ih ⊢; rw [eq_comm] at hg₁
  simp [Game.move]
  split_ifs with h₁ h₂; exact ih
  all_goals split <;> dsimp <;> (try exact ih); nm m s h₃
  · replace h₃ := of_a_ap_eq_some h₃
    obtain ⟨p₁, rfl, h₃, h₄⟩ := h₃
    simpa
  · replace h₃ := of_d_ap_eq_some h₃
    obtain ⟨p₁, rfl, h₃, h₄⟩ := h₃
    simp [ih]

theorem game_play_succ_toState'_ne_orig_of_move_not_ended {g : Game} {n}
(he : ¬g.move.ended) : (g.play (n + 1)).toState' ≠ g.toState' := by
  rw [game_play_succ']
  have he₀ := game_not_ended_of_move_not_ended he
  have h₁ : g.f g.toState ≠ none :=
    by
      revert he
      simp [Game.move, he₀]
      split_ifs with h₁ <;> split <;> simp <;> nm m s h₂
      · exact of_a_ap_eq_some' h₂
      · exact of_d_ap_eq_some' h₂
  simp [Game.move, he₀]
  split_ifs with ht <;> simp [ht] at h₁ <;> split <;>
    (try nm m h₁; simp at h₁; contradiction) <;> nm m s h₂
  · replace h₂ := of_a_ap_eq_some h₂
    obtain ⟨p, hs, h₂, h₃, h₄⟩ := h₂
    cases n
    · apply ne_of_congr (·.a_pos)
      simpa [hs]
    nm n
    rw [game_play_succ']
    simp [Game.move, ht]
    split
    · nm m₁ h₅
      rw [game_play_eq_of_ended trivial]
      apply ne_of_congr (·.a_pos)
      simpa [hs]
    · nm m₁ s₁ h₅
      replace h₅ := of_d_ap_eq_some h₅
      obtain ⟨p₁, hs₁, h₅, h₆⟩ := h₅
      apply ne_of_congr (p₁ ∈ ·.grid)
      have h₇ : p₁ ∈ g.grid :=
        by
          clear hs₁ s₁
          simp [hs] at h₅
          exact h₅
      simp [h₇]
      apply point_not_mem_play_grid_of_not_mem_grid
      simp [hs₁]
  · replace h₂ := of_d_ap_eq_some h₂
    obtain ⟨p, rfl, h₂, h₃⟩ := h₂
    apply ne_of_congr (p ∈ ·.grid)
    simp [h₂]
    apply point_not_mem_play_grid_of_not_mem_grid
    simp

theorem game_move_ended_of_play_succ_toState'_eq_orig {g : Game} {n}
(h : (g.play (n + 1)).toState' = g.toState') : g.move.ended := by
  contrapose! h; exact game_play_succ_toState'_ne_orig_of_move_not_ended h

@[simp]
theorem game_play_move_toState'_eq_orig_iff_move_ended {g : Game} {n} :
(g.play n).move.toState' = g.toState' ↔ g.move.ended := by
  rw [←game_play_succ]
  use game_move_ended_of_play_succ_toState'_eq_orig
  intro h; rw [game_play_to_state_eq_of_move_ended h]

theorem game_play_toState_eq_of_toState'_eq {g : Game} {n}
(h : (g.play n).toState' = g.toState') : (g.play n).toState = g.toState := by
  cases n; rfl;
  nm n; simp at h
  rw [game_play_succ']
  rw [game_play_eq_of_ended h]
  exact game_move_toState_eq_of_move_ended h

theorem game_play_toState_eq_iff_toState'_eq {g : Game} {n} :
(g.play n).toState = g.toState ↔ (g.play n).toState' = g.toState' := by
  constructor <;> intro h; rw [h]
  exact game_play_toState_eq_of_toState'_eq h

theorem game_play_toState_eq_play_to_state_iff_toState'_eq
{g : Game} {n m} :
(g.play n).toState = (g.play m).toState ↔
(g.play n).toState' = (g.play m).toState' := by
  constructor <;> intro h; rw [h]
  wlog h₁ : m ≤ n with h₂
  · symm
    apply h₂ h.symm
    linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  simp at h ⊢
  generalize g.play m = g at h ⊢; nm x; clear x
  rwa [game_play_toState_eq_iff_toState'_eq]

theorem game_play_inj_state'_of_play_not_ended {g : Game} {n k₁ k₂}
(he : ¬(g.play n).ended) (hk₁ : k₁ ≤ n) (hk₂ : k₂ ≤ n)
(h₁ : (g.play k₁).toState' = (g.play k₂).toState') :
k₁ = k₂ := by
  wlog h₂ : k₁ ≤ k₂ with ih
  · exact (ih he hk₂ hk₁ h₁.symm # by linarith).symm
  obtain ⟨k₂, rfl⟩ := Nat.exists_eq_add_of_le h₂; clear h₂
  cases k₂
  · rfl
  nm k₂
  contrapose! h₁; clear h₁
  symm
  rw [game_play_add]
  apply game_play_succ_toState'_ne_orig_of_move_not_ended
  rw [←game_play_succ]
  apply game_play_not_ended_of_le he
  linarith

theorem game_play_toState_eq_of_game_play_toState'_eq {g : Game} {n m}
(h : (g.play n).toState' = (g.play m).toState') :
(g.play n).toState = (g.play m).toState := by
  wlog h₁ : n ≤ m with ih
  · exact (ih h.symm # by linarith).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  rw [eq_comm] at h ⊢
  rwa [game_play_toState_eq_play_to_state_iff_toState'_eq]

#check 0 #exit

theorem game_toState_eq_of_valid_and_game_toState'_eq {g₁ g₂ : Game}
(h₁ : g₁.valid) (h₂ : g₂.valid) (h₃ : g₁.toState' = g₂.toState') :
g₁.toState = g₂.toState := by
  rename' g₁ => g
  rename' g₂ => g₁
  obtain ⟨pw, a, d, n, hg⟩ := h₁
  obtain ⟨pw', a₁, d₁, m, hg₁⟩ := h₂
  obtain rfl : pw = pw' :=
    by
      contrapose! h₃
      apply ne_of_congr State'.pw
      simpa [hg, hg₁]
  rw [eq_comm] at h₃ ⊢
  
  -- wlog h₁ : n ≤ m with ih
  -- · symm
  --   apply ih h₃.symm
  --   · exact hg₁
  --   · exact hg
  --   linarith
  -- obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  -- rw [game_play_add] at hg₁

#check 0 #exit

theorem exiu_valid_state_of_state_valid {s : State}
(h : s.valid) : ∃! (sv : ValidState), sv.toState' = s.toState' := by
  obtain ⟨g, ⟨pw, a, d, n, hg⟩, rfl⟩ := h
  refine' ⟨⟨g.toState, _⟩, _⟩
  · apply state_valid_of_game_valid
    simp [hg]
  simp
  intro v h₁
  ext : 1
  dsimp
  obtain ⟨s, g₁, ⟨pw₁, s₁, a₁, d₁, hg₁⟩, rfl⟩ := v
  dsimp at h₁ ⊢

#check 0 #exit

theorem exiu_valid_state_of_state'_valid {s' : State'}
(h : s'.valid) : ∃! (sv : ValidState), sv.toState' = s' := by

theorem a_state_move_of_move' {sa : AState} {sd : DState}
(h : sa.move' sd) : sa.move sd := by
  unfold AState.move
  use h
  unfold AState.move' at h
  obtain ⟨⟨s₁, g, ⟨pw, a, d, n, hg⟩, rfl⟩, h₂⟩ := sd
  dsimp at h₂ h ⊢
  have h₃ : g.valid := by simp [hg]
  rw [even_game_size_iff_d_turn_of_valid h₃] at h₂
  have h₄ := game_not_ended_of_valid_and_d_turn h₃ h₂
  obtain ⟨sd₁, h₅, h₆, h₇⟩ := exi_a_state_move_of_a_move h
  sorry

theorem a_state_move'_iff_move {sa : AState} {sd : DState} :
sa.move' sd ↔ sa.move sd := ⟨a_state_move_of_move', a_state_move'_of_move⟩