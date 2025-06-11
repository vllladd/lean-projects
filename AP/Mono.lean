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

@[simp]
theorem game_orig_eq_play_move_toState'_iff_move_ended {g : Game} {n} :
g.toState' = (g.play n).move.toState' ↔ g.move.ended := by
  rw [eq_comm]; simp

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

theorem game_play_toState_eq_play_toState_iff_toState'_eq
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
  rwa [game_play_toState_eq_play_toState_iff_toState'_eq]

def Game.congr (g₁ g₂ : Game) :=
  g₁.toState = g₂.toState ∧ (g₁.a_turn ↔ g₂.a_turn) ∧ (g₁.ended ↔ g₂.ended)

@[simp]
theorem game_merge_congr {g : Game} {pa pd a d} :
(g.merge pa pd a d).congr g := by simp [Game.congr]

@[simp]
theorem game₀_congr_game₀_iff {pw₁ pw₂ a₁ a₂ d₁ d₂} :
(game₀ pw₁ a₁ d₁).congr (game₀ pw₂ a₂ d₂) ↔ pw₁ = pw₂ := by simp [Game.congr]

@[simp]
theorem game_congr_refl {g : Game} : g.congr g := by simp [Game.congr]

@[symm]
theorem Game.congr.symm {g₁ g₂ : Game} (h : g₁.congr g₂) : g₂.congr g₁ := by
  rcases h with ⟨h₁, h₂, h₃⟩
  simp [Game.congr, h₁, h₂, h₃]

@[trans]
theorem Game.congr.trans {g₁ g₂ g₃ : Game}
(h₁ : g₁.congr g₂) (h₂ : g₂.congr g₃) : g₁.congr g₃ := by
  unfold Game.congr at h₁ h₂ ⊢
  rw [h₂.1, h₂.2.1, h₂.2.2] at h₁
  exact h₁

-- theorem game_move_toState_eq_of_toState_eq_and_move_toState'_eq {g₁ g₂ : Game}
-- (h₁ : g₁.toState = g₂.toState) (h₂ : g₁.move.toState' = g₂.move.toState') :
-- g₁.move.toState = g₂.move.toState := by
--   sorry

-- theorem game_move_toState'_eq_of_congr_and_play_succ_toState'_eq
-- {g₁ g₂ : Game} {n m} (h₁ : g₁.congr g₂)
-- (h₂ : (g₁.play (n + 1)).toState' = (g₂.play (m + 1)).toState') :
-- g₁.move.toState' = g₂.move.toState' := by
--   by_cases he₁ : g₁.ended
--   · rw [game_play_eq_of_ended he₁, h₁.1] at h₂
--     simp at h₂
--     rw [game_move_eq_of_ended he₁, h₁.1]
--     rw [game_move_toState_eq_of_move_ended h₂]
--   have he₂ : ¬g₂.ended := by rwa [←h₁.2.2]
--   sorry

-- #check 0 #exit

-- theorem game_move_toState_eq_of_congr_and_play_succ_toState'_eq
-- {g₁ g₂ : Game} {n m} (h₁ : g₁.congr g₂)
-- (h₂ : (g₁.play (n + 1)).toState' = (g₂.play (m + 1)).toState') :
-- g₁.move.toState = g₂.move.toState := by
--   apply game_move_toState_eq_of_toState_eq_and_move_toState'_eq h₁.1
--   exact game_move_toState'_eq_of_congr_and_play_succ_toState'_eq h₁ h₂

-- #check 0 #exit

-- theorem game_play_toState_eq_of_toState_eq_and_play_toState'_eq {g₁ g₂ : Game} {n m}
-- (h₁ : g₁.toState = g₂.toState) (h₂ : (g₁.play n).toState' = (g₂.play m).toState') :
-- (g₁.play n).toState = (g₂.play m).toState := by
--   induction n generalizing g₁ g₂ m
--   · cases m; exact h₁; nm m
--     simp [h₁] at h₂ ⊢
--     rw [←game_play_succ, game_play_succ', game_play_eq_of_ended h₂,
--       game_move_toState_eq_of_move_ended h₂]
--   nm n ih
--   cases m
--   · clear ih
--     rw [game_play_zero, ←h₁] at h₂ ⊢
--     simp at h₂
--     exact game_play_to_state_eq_of_move_ended h₂
--   nm m
--   specialize @ih g₁.move g₂.move m _ _
--   · exact game_move_toState_eq_of_toState_eq_and_play_succ_toState'_eq h₁ h₂
--   · simp [game_move_play]
--     simp at h₂
--     exact h₂
--   simp [game_move_play] at ih
--   simpa

theorem game_exiu_play_toState (g : Game) (n : ℕ) :
∃! (s : State), ∀ m, (g.play n).toState' = (g.play m).toState' →
s = (g.play m).toState := by
  use (g.play n).toState
  dsimp
  constructor
  · intro m hm
    rwa [game_play_toState_eq_play_toState_iff_toState'_eq]
  intro s hs
  apply hs
  rfl

#check 0 #exit

theorem game_play_toState_eq_of_toState_eq_and_play_toState'_eq_aux
{g₁ g₂ : Game} {n}
(h₁ : g₁.toState = g₂.toState) (h₂ : (g₁.play n).toState' = (g₂.play n).toState') :
(g₁.play n).toState = (g₂.play n).toState := by
  replace h₂ : ∀ k ≤ n, (g₁.play k).toState' = (g₂.play k).toState' :=
    by
      intro k hk
      induction k generalizing g₁ g₂ n
      · simp [h₁]
      nm k ih
      cases n
      · simp at hk
      nm n
      simp at hk
      specialize @ih g₁.move g₂.move n _ _ hk
      · sorry
      · simp only [game_play_succ'] at h₂
        exact h₂
      simpa only [game_play_succ']
  induction n generalizing g₁ g₂
  · simpa
  nm n ih
  have h₃ := h₂ 1 # by linarith
  simp at h₃
  specialize @ih g₁.move g₂.move _
  · sorry
  apply ih
  intro k hk
  specialize h₂ (k + 1) _
  · linarith
  simp only [game_play_succ'] at h₂
  exact h₂

#check 0 #exit

theorem game_play_toState_eq_of_toState_eq_and_play_toState'_eq {g₁ g₂ : Game} {n m}
(h₁ : g₁.toState = g₂.toState) (h₂ : (g₁.play n).toState' = (g₂.play m).toState') :
(g₁.play n).toState = (g₂.play m).toState := by
  obtain ⟨s₁, h₃, h₄⟩ := game_exiu_play_toState g₁ n
  obtain ⟨s₂, h₅, h₆⟩ := game_exiu_play_toState g₂ m
  dsimp at h₄ h₆
  have hs₁ := h₃ n rfl
  have hs₂ := h₅ m rfl
  rw [←hs₁, ←hs₂]
  specialize h₃ m _
  · rw [h₂]
    symm

#check 0 #exit

theorem game_toState_eq_of_valid_and_game_toState'_eq {g₁ g₂ : Game}
(h₁ : g₁.valid) (h₂ : g₂.valid) (h₃ : g₁.toState' = g₂.toState') :
g₁.toState = g₂.toState := by
  obtain ⟨pw, a, d, n, hg₁⟩ := h₁
  obtain ⟨pw', a₁, d₁, m, hg₂⟩ := h₂
  obtain rfl : pw = pw' :=
    by
      contrapose! h₃
      apply ne_of_congr State'.pw
      simpa [hg₁, hg₂]
  subst hg₁ hg₂
  apply game_play_toState_eq_of_congr_and_play_toState'_eq
  · simp
  exact h₃

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