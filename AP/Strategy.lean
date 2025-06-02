import AP.Basic

noncomputable section
open scoped Classical

@[simp]
theorem state₀_state {pw} : (state₀ pw).toState' = state'₀ pw := rfl

@[simp]
theorem state'_reachable_refl {s : State'} : s.reachable s := by
  use {Game.dflt with toState := ⟨s, []⟩}, 0; simp

@[simp]
theorem state'₀_valid {pw} : (state'₀ pw).valid := by
  use pw; simp

@[simp]
theorem state'₀_d_has_move {pw} : (state'₀ pw).d_has_move := by
  apply d_always_has_move; simp

theorem d_ap_state₀_match {α : Type} {f : _ → α} {x pw} {d : DStrat} :
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
, toState := (state₀ pw).push (d.1.f # state₀ pw).get!
, a_turn := True
, ended := False
} := by simp [Game.move, game₀]; split; simp_all; nm m s h; simp [h]

@[simp]
theorem game_mk_move_ended_of_a_turn_iff {a d} {s : State} :
({a := a
, d := d
, toState := s
, a_turn := True
, ended := False
} : Game).move.ended ↔ ¬s.toState'.a_has_move := by
  simp [Game.move]; split
  · nm m h₁; simp [State'.a_has_move] at h₁ ⊢; exact h₁
  · nm m s' h₁; simp; use s'; exact of_a_ap_eq_some h₁

@[simp]
theorem state_push_state {st : State} {s} : (st.push s).toState' = s := rfl

@[simp, symm]
theorem point_dist_comm {a b : Point} : a.dist b = b.dist a := by
  simp [Point.dist,abs_sub_comm]

theorem a_has_move_iff {s : State'} : s.a_has_move ↔ ∃ (p : Point),
p ∈ s.grid ∧ p ≠ s.a_pos ∧ s.a_pos.dist p ≤ s.pw := by
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
  generalize hm : (default : DStrat).1.f (state₀ 0) = m
  rcases m; simp at hm; nm s; simp
  suffices h : s.pw = 0 by simp [a_has_move_iff, h]
  generalize (default : DStrat) = d at hm
  rcases d with ⟨⟨ms, f, h₁⟩, h₂⟩; dsimp at h₂ hm; subst h₂
  specialize h₁ # state₀ 0; simp [hm] at h₁
  obtain ⟨p, h₁, h₂⟩ := h₁; simp [h₁]

def mk_a_strat' (f : State → Point) := λ (s : State) =>
  let s' := {s with a_pos := f s}
  if ¬s.a_has_move then none else some #
  if s.a_move s' then s' else Classical.epsilon s.a_move

def mk_a_strat (f : State → Point) : AStrat := by
  refine' ⟨⟨_, mk_a_strat' f, _⟩, rfl⟩; intro s; dsimp; split
  · nm m h; ext x; change (x ∈ setOf _) ↔ _
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_exists, not_and, not_le]
    rintro p rfl h₁ h₂
    simp only [mk_a_strat', a_has_move_iff, ne_eq, point_dist_comm,
      not_exists, not_and, not_le, ite_eq_left_iff, not_forall,
      Classical.not_imp, not_lt, reduceCtorEq, imp_false] at h
    exact h _ h₁ h₂
  · nm m s' h; change s' ∈ setOf _; simp only [Set.mem_setOf_eq]
    use s'.a_pos; simp [mk_a_strat'] at h; obtain ⟨h₁, h₂⟩ := h
    split_ifs at h₂ with h₃
    · simp [←h₂]; simp [State'.a_move] at h₃; exact h₃
    have h₄ := Classical.epsilon_spec h₁; rw [h₂] at h₄; clear h₂
    obtain ⟨a, rfl, h₄⟩ := h₄; simpa

def mk_d_strat' (f : State → Point) := λ (s : State) =>
  let s' := {s with grid := s.grid.erase # f s}
  if ¬s.d_has_move then none else some #
  if s.d_move s' then s' else Classical.epsilon s.d_move

def mk_d_strat (f : State → Point) : DStrat := by
  refine' ⟨⟨_, mk_d_strat' f, _⟩, rfl⟩; intro s; dsimp; split
  · nm m h; ext x; change (x ∈ setOf _) ↔ _
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_exists, not_and, Decidable.not_not]; rintro p rfl h₁
    simp only [mk_d_strat', State'.d_has_move, not_exists, ite_eq_left_iff,
      not_forall, Decidable.not_not, reduceCtorEq, imp_false] at h
    specialize h {s with grid := s.grid.erase p}
    simp [State'.d_move] at h; apply h p rfl h₁
  · nm m s' h; change s' ∈ setOf _; simp only [Set.mem_setOf_eq]
    obtain ⟨p, hp⟩ := hv # Classical.epsilon λ p => p ∈ s.grid \ s'.grid
    use p; simp [mk_d_strat'] at h; obtain ⟨h₁, h₂⟩ := h
    split_ifs at h₂ with h₃
    · simp [State'.d_move] at h₃; subst h₂; simp at hp ⊢
      have hs : f s ∈ s.grid := by
        contrapose! h₃; intro p h₄ h₅
        replace h₄ := congrArg (p ∈ ·) h₄
        simp [h₅] at h₄; simp [h₃, h₄] at h₅
      have h₄ : p = f s := by
        subst hp; have h : ∀ p, p ∈ s.grid ∧
        (p ≠ f s → p ∉ s.grid) ↔ p = f s := by
          intro p; by_cases h : p ∈ s.grid <;> simp [h]
          contrapose! h; subst h; exact hs
        simp [h]; apply Classical.epsilon_singleton
      subst h₄; obtain ⟨p, h₂, h₃, h₄⟩ := h₃
      replace h₂ := congrArg (p ∈ ·) h₂
      simp [h₃] at h₂; subst h₂; simp [h₃, h₄]
    have h₄ := Classical.epsilon_spec h₁; rw [h₂] at h₄
    have ⟨g, hg⟩ := hv # λ p => s' = {s with grid := s.grid.erase p} ∧
      p ∈ s.grid ∧ p ≠ s.a_pos
    have h₅ : ∀ p, (g p) ↔ p ∈ s.grid \ s'.grid := by
      subst hg; intro p; constructor; rintro ⟨rfl, h₅, h₆⟩; simpa
      intro h₅; obtain ⟨p₁, rfl, h₆, h₇⟩ := h₄; simp at h₅ ⊢
      obtain ⟨h₅, h₈⟩ := h₅; simp [h₅] at h₈; subst h₈; simp [h₆, h₇]
    simp only [State'.d_move, ←hg] at h₄
    obtain hp₁ := Classical.epsilon_spec h₄
    simp [←h₅] at hp; rw [←hp] at hp₁; simp [hg] at hp₁; exact hp₁

@[simp]
theorem not_state'₀_0_a_has_move : ¬(state'₀ 0).a_has_move := by
  simp [a_has_move_iff]

theorem not_a_has_move_of_pw_0 {s : State'} (h : s.pw = 0) : ¬s.a_has_move := by
  simp [a_has_move_iff, h]

theorem game_play_succ' {g : Game} {n} : g.play (n + 1) = g.move.play n := rfl

theorem game_move_eq_of_ended {g : Game} (h : g.ended) : g.move = g := by
  simp [Game.move, h]

theorem game_play_eq_of_ended {g : Game} {n} (h : g.ended) : g.play n = g := by
  induction n; rfl; nm n ih; simp [ih, game_move_eq_of_ended h]

theorem game_move_grid_eq_of_ended {g : Game} (h : g.ended) :
g.move.grid = g.grid := by simp [Game.move, h]

theorem game_move_grid_eq_of_move_ended {g : Game} (h : g.move.ended) :
g.move.grid = g.grid := by
  by_cases h₁ : g.ended; simp [game_move_eq_of_ended h₁]
  revert h; simp [Game.move, h₁]; split <;> simp

theorem game_move_ended_of_ended {g : Game} (h : g.ended) : g.move.ended := by
  simp [Game.move, h]

theorem game_play_ended_of_ended {g : Game} {n} (h : g.ended) : (g.play n).ended := by
  induction n; simpa; nm n ih; simp
  exact game_move_ended_of_ended ih

theorem game_not_ended_of_move_not_ended {g : Game}
(h : ¬g.move.ended) : ¬g.ended := by
  contrapose! h; exact game_move_ended_of_ended h

theorem game_not_ended_of_play_not_ended {g : Game} {n}
(h : ¬(g.play n).ended) : ¬g.ended := by
  contrapose! h; exact game_play_ended_of_ended h

@[simp]
theorem state_push_size_eq {s : State} s' : (s.push s').size = s.size + 1 := by
  simp [State.push, State.size, List.snoc]

theorem game_move_size_eq_of_not_ended {g : Game} (h : ¬g.move.ended) :
g.move.size = g.size + 1 := by
  have h₁ := game_not_ended_of_move_not_ended h; simp [Game.move, h₁]
  split; nm m h₂; contrapose! h; simp [Game.move, h₁, h₂]; simp

#check 0 #exit

theorem game_play_size_eq_of_not_ended {g : Game} {n} (h : ¬(g.play n).ended) :
(g.play n).size = g.size + n := by
  induction n
  · simp
  nm n ih
  simp

#check 0 #exit

theorem exi_valid_state_with_size {n} : ∃ (s : ValidState), s.size = n := by
  obtain ⟨a, ha⟩ := hv # mk_a_strat λ s => ⟨s.size, 0⟩
  obtain ⟨d, hd⟩ := hv # mk_d_strat λ s => ⟨s.size, 1⟩
  refine' ⟨⟨((game₀ 2 a d).play n).toState, _⟩, _⟩
  · apply state_valid_of_game_valid
    simp
  simp

#check 0 #exit

@[simp]
theorem state₀_valid {pw} : (state₀ pw).valid := by
  use game₀ pw default default; simp

instance : Inhabited ValidState := by
  use state₀ 0; simp

-- instance : Inhabited AState := by
--   refine' ⟨⟨⟨(game₀ 0 default default).move.toState', []⟩, _⟩, _⟩