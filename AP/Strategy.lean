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
  simp [Point.dist, abs_sub_comm]

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

theorem game₀_0_play_2_ended {a d} : ((game₀ 0 a d).play 2).ended := by
  simp [game₀_move]
  generalize hm : d.1.f (state₀ 0) = m
  rcases m; simp at hm; nm s; simp
  suffices h : s.pw = 0 by simp [a_has_move_iff, h]
  rcases d with ⟨⟨ms, f, h₁⟩, h₂⟩; dsimp at h₂ hm; subst h₂
  specialize h₁ # state₀ 0; simp [hm] at h₁
  obtain ⟨p, h₁, h₂⟩ := h₁; simp [h₁]

theorem not_a_hws_0 : ¬a_hws 0 := by
  unfold a_hws Game.a_wins; push_neg; intro a
  use default, 2, game₀_0_play_2_ended

@[simp]
def mk_strat (m : State' → State' → Prop) (g : State' → Point → State')
(f : State → Point) (s : State) :=
  let s' := s.toState'
  let s_new := g s' # f s
  let fn := m s'
  if ∀ s₁, ¬fn s₁ then none else some #
  if fn s_new then s_new else Classical.epsilon fn

def mk_a_strat' := mk_strat State'.a_move
  λ s p => {s with a_pos := p}

def mk_d_strat' := mk_strat State'.d_move
  λ s p => {s with grid := s.grid.erase p}

theorem mk_a_strat_valid {f : State → Point} {s : State} :
let set := setOf λ (s₁ : State') =>
  ∃ a₁, s₁ = { pw := s.pw, grid := s.grid, a_pos := a₁ } ∧
  a₁ ∈ s.grid ∧ a₁ ≠ s.a_pos ∧ a₁.dist s.a_pos ≤ s.pw;
match mk_a_strat' f s with
| none => set = ∅
| some s₁ => s₁ ∈ set := by
  dsimp; split
  · nm m h; ext x; change (x ∈ setOf _) ↔ _
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_exists, not_and, not_le]
    rintro p rfl h₁ h₂
    simp only [mk_a_strat'] at h; simp at h
    simp only [State'.a_move, ne_eq, not_exists, not_and, not_le] at h
    exact h _ p rfl h₁ h₂
  · nm m s' h; use s'.a_pos; simp [mk_a_strat'] at h
    obtain ⟨h₁, h₂⟩ := h; split_ifs at h₂ with h₃
    · simp [←h₂]; simp only [State'.a_move, State'.mk.injEq,
      implies_true, imp_self, true_and, ne_eq, exists_eq_left',
      point_dist_comm] at h₃; exact h₃
    have h₄ := Classical.epsilon_spec h₁; rw [h₂] at h₄; clear h₂
    obtain ⟨a, rfl, h₄⟩ := h₄; simpa

theorem mk_d_strat_valid {f : State → Point} {s : State} :
let set := setOf λ (s₁ : State') =>
  ∃ p, s₁ = { pw := s.pw, grid := Set.erase p s.grid, a_pos := s.a_pos } ∧
  p ∈ s.grid ∧ p ≠ s.a_pos;
match mk_d_strat' f s with
| none => set = ∅
| some s₁ => s₁ ∈ set := by
  dsimp; split
  · nm m h; ext x; change (x ∈ setOf _) ↔ _
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_exists, not_and, Decidable.not_not]; rintro p rfl h₁
    simp only [mk_d_strat'] at h; simp at h
    simp only [State'.d_move, ne_eq, not_exists,
      not_and, Decidable.not_not] at h
    specialize h {s with grid := s.grid.erase p}
    simp [State'.d_move] at h; apply h p rfl h₁
  · nm m s' h; obtain ⟨p, hp⟩ := hv # Classical.epsilon
      λ p => p ∈ s.grid \ s'.grid
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

def mk_a_strat (f : State → Point) : AStrat := by
  refine' ⟨⟨_, mk_a_strat' f, _⟩, rfl⟩; apply mk_a_strat_valid

def mk_d_strat (f : State → Point) : DStrat := by
  refine' ⟨⟨_, mk_d_strat' f, _⟩, rfl⟩; apply mk_d_strat_valid

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

theorem game_play_size_eq_of_not_ended {g : Game} {n} (h : ¬(g.play n).ended) :
(g.play n).size = g.size + n := by
  induction n; simp; nm n ih; simp at h ⊢
  rw [game_move_size_eq_of_not_ended h,
    ih # game_not_ended_of_move_not_ended h]; rfl

theorem game_move_size_eq_of_ended {g : Game} (he : g.ended) :
g.move.size = g.size := by simp [Game.move, he]

theorem game_move_state_eq_of_move_ended {g : Game} (he : g.move.ended) :
g.move.toState = g.toState := by
  generalize hg₁ : g.move = g₁ at he ⊢
  simp [Game.move] at hg₁; split_ifs at hg₁ with h₁ h₂; rw [hg₁]
  all_goals split at hg₁ <;> subst hg₁ <;> first | rfl | contradiction

theorem game_play_size_lt_iff_play_ended {g : Game} {n} (h₀ : ¬g.ended) :
(g.play n).size < g.size + n ↔ (g.play n).ended := by
  induction n; constructor <;> intro h <;> simp [h₀] at h
  nm n ih; constructor <;> intro h
  · simp at h ⊢; by_contra he₁
    have he := game_not_ended_of_move_not_ended he₁; simp [he] at ih
    rw [game_move_size_eq_of_not_ended he₁] at h; linarith
  · simp at h ⊢; by_cases he : (g.play n).ended
    · replace ih := ih.mpr he
      suffices (g.play n).move.size = (g.play n).size by linarith
      exact game_move_size_eq_of_ended he
    suffices (g.play n).move.size = g.size + n by linarith
    suffices (g.play n).move.size = (g.play n).size by
      rw [this]; exact game_play_size_eq_of_not_ended he
    rw [game_move_state_eq_of_move_ended h]

@[simp]
theorem state₀_size {pw} : (state₀ pw).size = 0 := rfl

@[simp]
theorem not_game₀_ended {pw a d} : ¬(game₀ pw a d).ended := λ h => h

@[simp]
theorem game_move_a_eq {g : Game} : g.move.a = g.a := by
  rw [Game.move]; split_ifs <;> (try split) <;> rfl

@[simp]
theorem game_move_d_eq {g : Game} : g.move.d = g.d := by
  rw [Game.move]; split_ifs <;> (try split) <;> rfl

@[simp]
theorem game_play_a_eq {g : Game} {n} : (g.play n).a = g.a := by
  induction n <;> simp_all

@[simp]
theorem game_play_d_eq {g : Game} {n} : (g.play n).d = g.d := by
  induction n <;> simp_all

#check 0 #exit

theorem exi_valid_state_with_size_of_pe_ne_0 {pw n}
(h : pw ≠ 0) : ∃ (s : ValidState), s.pw = pw ∧ s.size = n := by
  obtain ⟨fa, hfa⟩ := hv # λ (s : State) => (⟨s.size / 2 + 1, 0⟩ : Point)
  obtain ⟨fd, hfd⟩ := hv # λ (s : State) => (⟨s.size / 2, 1⟩ : Point)
  obtain ⟨a, ha⟩ := hv # mk_a_strat fa
  obtain ⟨d, hd⟩ := hv # mk_d_strat fd
  refine' ⟨⟨((game₀ pw a d).play n).toState, _⟩, _⟩
  · apply state_valid_of_game_valid
    simp
  simp
  rw [game_play_size_eq_of_not_ended]; simp
  apply and_intro # ((game₀ pw a d).play n).toState' =
    { pw := pw
    , grid := Set.univ \ {(x, y) | y = 1 ∧ 0 ≤ x ∧ x < (n + 1) / 2}
    , a_pos := (n / 2, 0)
    }
  induction n
  · simp only [game_play_zero, game₀_state, state₀_state, Nat.cast_zero,
      zero_add, Int.reduceDiv, Int.zero_ediv, not_game₀_ended,
      not_false_eq_true, implies_true, imp_self, and_true]
    ext <;> try rfl
    nm p
    rcases p with ⟨x, y⟩
    simp only [state'₀_grid, Set.mem_univ, implies_true, imp_self, Set.mem_diff,
      Set.mem_setOf_eq, not_and, not_lt, and_self]
  nm n ih
  rcases ih with ⟨ih₁, ih₂⟩
  rw [game_play_succ]
  generalize hg : (game₀ pw a d).play n = g at *
  have ⟨hga, hgd⟩ : g.a = a ∧ g.d = d := by simp [←hg]; exact ⟨rfl, rfl⟩
  subst hga hgd
  apply (by tauto : ∀ P Q, (Q → ¬P) → P → P ∧ ¬Q)
  
  · intro he
    rw [game_move_state_eq_of_move_ended he, ih₁]
    simp only [Nat.cast_add, Nat.cast_one, State'.mk.injEq, implies_true,
      imp_self, point_mk_eq_iff, and_true, true_and, not_and]
    clear * - n
    intro h; contrapose! h
    simp only [ne_eq, Set.ext_iff, Set.mem_diff, Set.mem_univ, implies_true,
      imp_self, Set.mem_setOf_eq, true_and, not_forall]
    have hn := Int.ofNat_zero_le n
    generalize (n : ℤ) = n at *; nm x; clear x
    rw [eq_comm] at h
    use (n / 2, 1); simp
    rw [int_succ_div_2_eq_div_iff hn] at h
    rw [int_even_iff_exi] at h
    obtain ⟨k, rfl⟩ := h
    simp at hn
    simp [hn]
    rw [int_mul_2_succ_div_2_eq hn, add_assoc]
    simp
    rw [int_add_div_eq # by decide]
    simp
  
  · simp [Game.move, ih₂]
    split_ifs with ht
    · have hn : Odd n := by sorry
      
      have h_a_move : g.a_move {g with a_pos := fa g.toState} := by
        simp [hfa, ih₁, State'.a_move]
        rw [←hg] at ih₂ ⊢
        simp [game_play_size_eq_of_not_ended ih₂, Point.dist]
        change 1 ≤ _
        have h₁ : 0 ≤ (pw : ℤ) := by linarith
        rw [le_iff_lt_or_eq] at h₁
        rcases h₁ with h₁ | h₁
        · linarith
        contrapose! h
        exact Int.ofNat_eq_zero.mp h₁.symm
      
      split
      · nm m h₁
        exfalso
        simp at h₁
        apply h₁; clear h₁
        exact ⟨_, h_a_move⟩
      · nm m s h₁
        simp
        simp [ha, mk_a_strat, mk_a_strat', h_a_move] at h₁
        replace h₁ := h₁.2.symm
        convert h₁ <;> clear h₁
        · rw [←hg]; simp
        · simp [ih₁]
          congr
          ext p
          simp
          rcases p with ⟨x, y⟩
          simp
          rintro rfl h₂
          suffices ((n : ℤ) + 1 + 1) / 2 = ((n : ℤ) + 1) / 2 by rw [this]
          rw [int_succ_div_2_eq_div_iff]
          · simpa
          linarith
        · simp [hfa]
          rw [game_play_size_eq_of_not_ended ih₂]

#check 0 #exit

theorem exi_valid_state_with_size_iff_pw_ne_0 {pw} :
(∀ n, ∃ (s : ValidState), s.pw = pw ∧ s.size = n) ↔ pw ≠ 0 := by
  constructor <;> intro h

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