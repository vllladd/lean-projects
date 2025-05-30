import AP.Basic

noncomputable section
open scoped Classical

@[simp]
theorem state₀_state {pw} : (state₀ pw).state = state'₀ pw := rfl

@[simp]
theorem state'_reachable_refl {s : State'} : s.reachable s := by
  use {Game.dflt with state := ⟨s, []⟩}, 0; simp

@[simp]
theorem state'₀_valid {pw} : (state'₀ pw).valid := by
  use pw; simp

@[simp]
theorem state'₀_d_has_move {pw} : (state'₀ pw).d_has_move := by
  apply d_always_has_move; simp

theorem d_ap_state₀_match {α : Type} {f : _ → α} {x pw} {d : D_strat} :
(match d.1.f (state₀ pw) with
| none => x
| some a => f a
) = f (d.1.f (state₀ pw)).get! := by
  split; nm m h; simp at h; nm m s h; simp [h]

@[simp]
theorem d_turn_eq {g : Game} : g.d_turn = ¬g.a_turn := rfl

theorem game₀_move {pw a d} : (game₀ pw a d).move =
{ a := a
, d := d
, state := (state₀ pw).push (d.1.f # state₀ pw).get!
, a_turn := True
, ended := False
} := by simp [Game.move, game₀]; split; simp_all; nm m s h; simp [h]

@[simp]
theorem game_mk_move_ended_of_a_turn_iff {a d} {s : State} :
({a := a
, d := d
, state := s
, a_turn := True
, ended := False
} : Game).move.ended ↔ ¬s.state.a_has_move := by
  simp [Game.move]; split
  · nm m h₁; simp [State'.a_has_move] at h₁ ⊢; exact h₁
  · nm m s' h₁; simp; use s'; exact of_a_ap_eq_some h₁

@[simp]
theorem state_push_state {st : State} {s} : (st.push s).state = s := rfl

@[simp, symm]
theorem point_dist_comm {a b : Point} : a.dist b = b.dist a := by
  simp [Point.dist,abs_sub_comm]

theorem a_has_move_iff {s : State'} : s.a_has_move ↔ ∃ (p : Point),
p ∈ s.grid ∧ p ≠ s.a ∧ s.a.dist p ≤ s.pw := by
  simp [State'.a_has_move, State'.a_move, exists_swap]

@[simp]
theorem point_dist_self_eq {a : Point} : a.dist a = 0 := by simp [Point.dist]

@[simp]
theorem point_dist_eq_zero_iff {a b : Point} : a.dist b = 0 ↔ a = b := by
  symm; apply Iff.intro <;> intro h; simp [h]
  simp [Point.dist, Int.add_le_zero_iff_le_neg] at h
  have h₁ : |a.x - b.x| ≤ 0 := by apply h.trans; simp
  have h₂ : |a.y - b.y| ≤ 0 := by apply (Int.le_neg_of_le_neg h).trans; simp
  simp [Int.sub_eq_zero] at h₁ h₂; ext <;> assumption

theorem not_a_hws_0 : ¬a_hws 0 := by
  unfold a_hws Game.a_wins; push_neg; intro a
  use default, 2; simp [game₀_move]
  generalize hm : (default : D_strat).1.f (state₀ 0) = m
  rcases m; simp at hm; nm s; simp
  suffices h : s.pw = 0 by simp [a_has_move_iff, h]
  generalize (default : D_strat) = d at hm
  rcases d with ⟨⟨ms, f, h₁⟩, h₂⟩; dsimp at h₂ hm; subst h₂
  specialize h₁ # state₀ 0; simp [hm] at h₁
  obtain ⟨p, h₁, h₂⟩ := h₁; simp [h₁]