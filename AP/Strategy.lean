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
(match d.ap (state₀ pw) with
| none => x
| some a => f a
) = f (d.ap (state₀ pw)).get! := by
  split; nm m h; simp at h; nm m s h; simp [h]

@[simp]
theorem d_turn_eq {g : Game} : g.d_turn = ¬g.a_turn := rfl

theorem game₀_move {pw a d} : (game₀ pw a d).move =
{ a := a
, d := d
, toState := (state₀ pw).push (d.ap # state₀ pw).get!
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

theorem d_has_move_iff {s : State'} : s.d_has_move ↔ ∃ (p : Point),
p ∈ s.grid ∧ p ≠ s.a_pos := by
  simp [State'.d_has_move, State'.d_move, exists_swap]

@[simp]
theorem point_dist_self_eq {a : Point} : a.dist a = 0 := by simp [Point.dist]

@[simp]
theorem point_dist_eq_zero_iff {a b : Point} : a.dist b = 0 ↔ a = b := by
  refine' ⟨λ h => _, by rintro rfl; simp⟩
  unfold Point.dist at h
  simp at h
  rcases h with ⟨h₁, h₂⟩
  ext <;> apply Int.eq_of_sub_eq_zero <;> assumption

theorem game₀_0_play_2_ended {a d} : ((game₀ 0 a d).play 2).ended := by
  simp [game₀_move]
  generalize hm : d.ap (state₀ 0) = m
  rcases m; simp at hm; nm s; simp
  suffices h : s.pw = 0 by simp [a_has_move_iff, h]
  rcases d with ⟨⟨ms, f, h₁⟩, h₂⟩; dsimp at h₂ hm; subst h₂
  specialize h₁ # state₀ 0; simp [hm] at h₁
  obtain ⟨p, h₁, h₂⟩ := h₁; simp [h₁]

theorem not_a_hws_0 : ¬a_hws 0 := by
  unfold a_hws Game.a_wins; push_neg; intro a
  use default, 2, game₀_0_play_2_ended

def strat_valid (ms : Moves) (f : State → Option State') :=
  ∀ (s : State),
  let g := ms s.toState'
  match f s with
  | none => ∀ s₁, ¬g s₁
  | some s₁ => g s₁

@[simp]
def mk_strat' (ms : Moves)
(f : State → State') : Strat' := λ (s : State) =>
  let s' := s.toState'
  let s_new := f s
  let fn := ms s'
  if ∀ s₁, ¬fn s₁ then none else some #
  if fn s_new then s_new else Classical.epsilon fn

theorem mk_strat_valid {ms f} : strat_valid ms (mk_strat' ms f) := by
  intro s
  simp
  split_ifs with h₁ h₂
  · simp
    apply h₁
  · exact h₂
  · simp at h₁ ⊢
    exact Classical.epsilon_spec h₁

@[simp]
def mk_strat (ms : Moves) (f : State → State') : Strat ms := by
  refine' ⟨⟨_, mk_strat' ms f, _⟩, rfl⟩; exact mk_strat_valid

@[simp]
def mk_strat_p (ms : Moves) (g : State' → Point → State')
(f : State → Point) : Strat' :=
  mk_strat' ms # λ s => g s.toState' # f s

@[simp]
def mk_a_strat' := mk_strat_p State'.a_move
  λ s p => {s with a_pos := p}

@[simp]
def mk_d_strat' := mk_strat_p State'.d_move
  λ s p => {s with grid := s.grid.erase p}

@[simp]
abbrev a_strat_valid := strat_valid AMoves

@[simp]
abbrev d_strat_valid := strat_valid DMoves

@[simp]
theorem AMoves_eq {s : State'} : AMoves s = s.a_move := rfl

@[simp]
theorem DMoves_eq {s : State'} : DMoves s = s.d_move := rfl

theorem mk_a_strat_valid {f : State → Point} :
a_strat_valid (mk_a_strat' f) := mk_strat_valid

theorem mk_d_strat_valid {f : State → Point} :
d_strat_valid (mk_d_strat' f) := mk_strat_valid

def mk_a_strat (f : State → Point) : AStrat := by
  refine' ⟨⟨_, mk_a_strat' f, _⟩, rfl⟩; exact mk_a_strat_valid

def mk_d_strat (f : State → Point) : DStrat := by
  refine' ⟨⟨_, mk_d_strat' f, _⟩, rfl⟩; exact mk_d_strat_valid

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

theorem game_move_size_eq_of_move_not_ended {g : Game} (h : ¬g.move.ended) :
g.move.size = g.size + 1 := by
  have h₁ := game_not_ended_of_move_not_ended h; simp [Game.move, h₁]
  split; nm m h₂; contrapose! h; simp [Game.move, h₁, h₂]; simp

theorem game_play_size_eq_of_not_ended {g : Game} {n} (h : ¬(g.play n).ended) :
(g.play n).size = g.size + n := by
  induction n; simp; nm n ih; simp at h ⊢
  rw [game_move_size_eq_of_move_not_ended h,
    ih # game_not_ended_of_move_not_ended h]; rfl

theorem game_move_size_eq_of_ended {g : Game} (he : g.ended) :
g.move.size = g.size := by simp [Game.move, he]

theorem game_move_toState_eq_of_move_ended {g : Game} (he : g.move.ended) :
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
    rw [game_move_size_eq_of_move_not_ended he₁] at h; linarith
  · simp at h ⊢; by_cases he : (g.play n).ended
    · replace ih := ih.mpr he
      suffices (g.play n).move.size = (g.play n).size by linarith
      exact game_move_size_eq_of_ended he
    suffices (g.play n).move.size = g.size + n by linarith
    suffices (g.play n).move.size = (g.play n).size by
      rw [this]; exact game_play_size_eq_of_not_ended he
    rw [game_move_toState_eq_of_move_ended h]

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

@[simp]
theorem game₀_play_state'_valid {pw a d n} :
((game₀ pw a d).play n).toState'.valid := by
  use pw, game₀ pw a d, n; simp

@[simp]
theorem game₀_d_turn {pw a d} : ¬(game₀ pw a d).a_turn := λ h => h

theorem game_a_has_move_of_a_turn {g : Game}
(ht : g.a_turn) (h : ¬g.move.ended) : g.a_has_move := by
  contrapose! h
  simp [Game.move, ht]
  split; assumption
  split <;> contrapose! h <;> nm m s h₂
  · simp at h
  · exact of_a_ap_eq_some' h₂

theorem game_d_has_move_of_d_turn {g : Game}
(ht : g.d_turn) (h : ¬g.move.ended) : g.d_has_move := by
  contrapose! h
  simp [Game.move, ht]
  split; assumption
  split <;> contrapose! h <;> nm m s h₂
  · simp at h
  · exact of_d_ap_eq_some' h₂

theorem game_move_a_turn_iff_of_not_ended {g : Game}
(h : ¬g.move.ended) : g.move.a_turn ↔ ¬g.a_turn := by
  have h₁ := game_not_ended_of_move_not_ended h
  simp [Game.move, h₁]
  split_ifs <;> split <;> simp_all <;> nm m s h₂ <;> apply h₂
  · exact game_a_has_move_of_a_turn m h
  · exact game_d_has_move_of_d_turn m h

theorem game_play_a_turn_iff_of_not_ended {g : Game} {n}
(h : ¬(g.play n).ended) : (g.play n).a_turn ↔ (g.a_turn ↔ Even n) := by
  induction n
  · simp
  nm n ih
  simp at h ⊢
  specialize ih # game_not_ended_of_move_not_ended h
  rw [game_move_a_turn_iff_of_not_ended h, ih]
  rcases Nat.even_or_odd n with h₁ | h₁
  · rw [←Nat.not_even_iff_odd]
    simp only [h₁]
    simp
  · rw [←Nat.not_odd_iff_even]
    simp only [h₁]
    simp

theorem game₀_play_a_turn_iff_odd {pw a d n}
(h : ¬((game₀ pw a d).play n).ended) :
((game₀ pw a d).play n).a_turn ↔ Odd n := by
  simp [game_play_a_turn_iff_of_not_ended h]

theorem game₀_play_d_turn_iff_even {pw a d n}
(h : ¬((game₀ pw a d).play n).ended) :
¬((game₀ pw a d).play n).a_turn ↔ Even n := by
  simp [game_play_a_turn_iff_of_not_ended h]

theorem exi_valid_state_with_size_of_pw_ne_0 pw n
(h : pw ≠ 0) : ∃ (s : ValidState), s.pw = pw ∧ s.size = n := by
  obtain ⟨fa, hfa⟩ := hv # λ (s : State) => ((s.size / 2 + 1, 0) : Point)
  obtain ⟨fd, hfd⟩ := hv # λ (s : State) => ((s.size / 2, 1) : Point)
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
    rw [game_move_toState_eq_of_move_ended he, ih₁]
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
    
    have hgn : g.size = n :=
      by
        rw [←hg] at ih₂ ⊢
        rw [game_play_size_eq_of_not_ended ih₂]
        simp
    
    have hp : 0 ≤ (n : ℤ) := by simp
    
    have hgpw : g.pw = pw := by rw [←hg]; simp
    
    split_ifs with ht
    
    · have hn : Odd (n : ℤ) :=
        by
          simp
          rw [←hg] at ht
          rw [game₀_play_a_turn_iff_odd] at ht
          · exact ht
          · rwa [hg]
      
      have h_a_move : g.a_move {g with a_pos := fa g.toState} := by
        simp [hfa, ih₁, State'.a_move, hgn, Point.dist]
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
        simp [hgpw] at h₁
        replace h₁ := h₁.2.symm
        convert h₁ <;> clear h₁
        · simp [ih₁]
          congr
          ext p
          simp
          rcases p with ⟨x, y⟩
          simp
          rintro rfl h₂
          suffices ((n : ℤ) + 1 + 1) / 2 = ((n : ℤ) + 1) / 2 by rw [this]
          rw [int_succ_div_2_eq_div_iff]
          · rwa [int_even_succ_iff]
          linarith
        · simp [hfa, hgn]
          rwa [int_succ_div_2_eq_div_succ_iff hp]
        · rw [hfa]
    
    · have hn : Even (n : ℤ) :=
        by
          simp
          rw [←hg] at ht
          rw [game₀_play_d_turn_iff_even] at ht
          · exact ht
          · rwa [hg]
      
      have h_d_move : g.d_move {g with grid := g.grid.erase # fd g.toState} :=
        by
          simp [hfd, ih₁, State'.d_move]
          use ((n : ℤ) / 2, 1)
          simp [hgn]
          intro h₁
          apply le_of_eq
          rwa [int_succ_div_2_eq_div_iff hp]
      
      split
      · nm m h₁
        exfalso
        contrapose h₁
        simp
        apply d_always_has_move
        rw [←hg]
        simp
      · nm m s h₁
        simp
        rw [←int_succ_div_2_eq_div_iff hp] at hn
        simp [hd, mk_d_strat, mk_d_strat', h_d_move] at h₁
        simp [hgpw] at h₁
        replace h₁ := h₁.2.symm
        rw [h₁]; clear h₁; simp; constructor
        · ext p
          rcases p with ⟨x, y⟩
          simp [ih₁, hfd, hgn]
          simp [add_assoc]
          rw [int_add_div_eq # by decide]
          simp [hn]
          constructor
          · rintro ⟨h₁, h₂⟩ rfl h₃
            specialize h₂ rfl h₃
            simp at h₁
            rw [le_iff_lt_or_eq] at h₂
            rw [eq_comm] at h₁
            simp [h₁] at h₂
            exact h₂
          · intro h₁
            constructor
            · rintro rfl rfl
              specialize h₁ rfl (by apply Int.zero_le_ofNat)
              simp [add_assoc] at h₁
            · rintro rfl h₂
              specialize h₁ rfl h₂
              linarith
        · simp [ih₁]
          exact hn.symm

@[simp]
theorem game_size_le_move_size {g : Game} : g.size ≤ g.move.size := by
  by_cases he : g.move.ended
  · rw [game_move_toState_eq_of_move_ended he]
  · simp [game_move_size_eq_of_move_not_ended he]

@[simp]
theorem game_size_le_play_size {g : Game} {n} :
g.size ≤ (g.play n).size := by
  induction n
  · simp
  nm n ih
  simp
  apply ih.trans
  apply game_size_le_move_size

@[simp]
theorem game_play_0_eq {g : Game} : g.play 0 = g := rfl

@[simp]
theorem game_play_1_eq {g : Game} : g.play 1 = g.move := rfl

@[simp]
theorem game_play_add {g : Game} {n m} :
g.play (n + m) = (g.play n).play m := by
  unfold Game.play
  rw [add_comm, Function.iterate_add]
  rfl

theorem game_play_add' {g : Game} {n m} :
g.play (n + m) = (g.play m).play n := by
  rw [add_comm]; simp

@[simp]
theorem game_play_size_le_play_add_size {g : Game} {n m} :
(g.play n).size ≤ (g.play (n + m)).size := by
  simp

theorem game_play_size_le_play_size_of_le {g : Game} {n m}
(h : n ≤ m) : (g.play n).size ≤ (g.play m).size := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp

theorem of_game_play_size_lt_play_size {g : Game} {n m}
(h : (g.play n).size < (g.play m).size) : n < m := by
  rcases Nat.le_total n m with h₁ | h₁ <;>
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₁ <;>
    clear h₁
  · suffices k ≠ 0
      by
        cases k; simp at this
        linarith
    rintro rfl
    simp at h
  · contrapose! h; clear h
    simp

theorem game_move_not_ended_of_a_turn {g : Game}
(he : ¬g.ended) (ht : g.a_turn) (h : g.a_has_move) : ¬g.move.ended := by
  simp [Game.move, he, ht]
  split
  · nm m h₁
    simp at h₁
    contradiction
  simp

theorem game_move_not_ended_of_d_turn {g : Game}
(he : ¬g.ended) (ht : ¬g.a_turn) (h : g.d_has_move) : ¬g.move.ended := by
  simp [Game.move, he, ht]
  split
  · nm m h₁
    simp at h₁
    contradiction
  simp

theorem game_move_valid_not_ended_of_d_turn {g : Game}
(hv : g.valid) (he : ¬g.ended) (ht : ¬g.a_turn) : ¬g.move.ended := by
  have h₁ := d_always_has_move # state'_valid_of_game_valid hv
  exact game_move_not_ended_of_d_turn he ht h₁

@[simp]
theorem game₀_move_not_ended {pw a d} :
¬(game₀ pw a d).move.ended := by
  apply game_move_valid_not_ended_of_d_turn <;> simp

theorem game₀_play_size_eq_of_not_ended {pw a d n}
(h : ¬((game₀ pw a d).play n).ended) :
((game₀ pw a d).play n).size = n := by
  replace h := game_play_size_eq_of_not_ended h
  simp at h
  exact h

theorem game₀_0_play_size_eq_of_le_1 {a d n}
(hn : n ≤ 1) : ((game₀ 0 a d).play n).size = n := by
  apply game₀_play_size_eq_of_not_ended
  cases n; simp
  nm n
  cases n; simp
  nm n
  simp at hn

theorem game_play_size_eq_of_ended {g : Game} {n}
(he : g.ended) : (g.play n).size = g.size := by
  induction n; rfl
  nm n ih
  simp
  rw [←ih]
  apply game_move_size_eq_of_ended
  exact game_play_ended_of_ended he

theorem game_play_ended_of_le {g : Game} {n m}
(he : (g.play n).ended) (h : n ≤ m) : (g.play m).ended := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp
  exact game_play_ended_of_ended he

@[simp]
theorem game₀_0_move_size {a d} : (game₀ 0 a d).move.size = 1 := by
  rw [←game_play_1_eq]
  apply game₀_0_play_size_eq_of_le_1
  rfl

theorem game₀_0_play_2_size {a d} : ((game₀ 0 a d).play 2).size = 1 := by
  generalize hg₀ : game₀ 0 a d = g₀; rw [eq_comm] at hg₀
  generalize hg : g₀.play 2 = g at hg₀; rw [eq_comm] at hg
  have h₁ := @game_play_size_lt_iff_play_ended
    g₀ 2 (by simp [hg₀])
  rw [←hg] at h₁
  have he : g.ended :=
    by
      rw [hg, hg₀]
      exact game₀_0_play_2_ended
  simp [he, hg₀] at h₁
  have h₂ : 0 < g.size :=
    by
      simp [hg]
      have h₂ : 0 < g₀.move.size :=
        by
          simp [hg₀]
      have h₃ : g₀.move.size ≤ g₀.move.move.size :=
        by
          exact game_size_le_move_size
      linarith
  linarith

theorem game₀_0_play_size_eq_of_1_le {a d n}
(hn : 1 ≤ n) : ((game₀ 0 a d).play n).size = 1 := by
  cases n; simp at hn
  nm n
  cases n; simp
  nm n
  clear hn
  rw [add_assoc]
  rw [game_play_add']
  have h₁ := @game_play_size_eq_of_ended
    ((game₀ 0 a d).play 2) n game₀_0_play_2_ended
  rw [h₁]; clear h₁
  exact game₀_0_play_2_size

@[simp]
theorem game₀_0_play_size_eq_min {a d n} :
((game₀ 0 a d).play n).size = min 1 n := by
  by_cases hn : n ≤ 1
  · rw [game₀_0_play_size_eq_of_le_1 hn, Nat.min_eq_right hn]
  · replace hn : 1 ≤ n := by linarith
    rw [game₀_0_play_size_eq_of_1_le hn, Nat.min_eq_left hn]

theorem game₀_0_play_size_le_1 {a d n} :
((game₀ 0 a d).play n).size ≤ 1 := by simp

theorem exi_valid_state_with_size_iff_pw_ne_0 {pw} :
(∀ n, ∃ (s : ValidState), s.pw = pw ∧ s.size = n) ↔ pw ≠ 0 := by
  constructor <;> intro h
  · rintro rfl
    specialize h 2
    obtain ⟨⟨s, ⟨g, ⟨pw, a, d, n, rfl⟩, rfl⟩⟩, h₁, h₂⟩ := h
    simp at h₁ h₂
    subst h₁
    contrapose h₂
    simp
    apply ne_of_congr (· < 2)
    simp
  intro n
  apply exi_valid_state_with_size_of_pw_ne_0
  exact h

theorem exi_valid_state_with_size n : ∃ (s : ValidState), s.size = n := by
  obtain ⟨s, h₁, h₂⟩ := exi_valid_state_with_size_of_pw_ne_0 1 n (by simp)
  exact ⟨_, h₂⟩

@[simp]
theorem state₀_valid {pw} : (state₀ pw).valid := by
  use game₀ pw default default; simp

instance : Inhabited ValidState := by
  use state₀ 0; simp

instance : Inhabited AState := by
  use Classical.choose # exi_valid_state_with_size 1
  generalize_proofs h
  have h₁ := Classical.choose_spec h
  simp [h₁]

instance : Inhabited DState := by
  refine' ⟨⟨state₀ 0, _⟩, _⟩ <;> simp

@[simp]
def Strat.merge' {ms} (P : State → Prop) (a b : Strat ms) (s : State) :=
  (if P s then b else a).ap s

theorem Strat.merge_valid {ms} {P : State → Prop} {a b : Strat ms} :
strat_valid ms (a.merge' P b) := by
  intro s
  simp
  split_ifs with h₁
  · rcases b with ⟨⟨ms, f, h⟩, rfl⟩
    apply h
  · rcases a with ⟨⟨ms, f, h⟩, rfl⟩
    apply h

def Strat.merge {ms} (p : State → Prop) (a b : Strat ms) : Strat ms := by
  refine' ⟨⟨_, a.merge' p b, _⟩, rfl⟩; exact Strat.merge_valid

@[simp]
theorem strat_mk_eq_mk_iff {ms} {a b : Strat ms} :
@Eq (Strat ms) a b ↔ ∀ s, a.ap s = b.ap s := by
  constructor; rintro rfl; simp
  intro h
  rcases a with ⟨⟨ms₁, f₁, h₁⟩, rfl⟩
  rcases b with ⟨⟨ms₂, f₂, h₂⟩, h₃⟩
  dsimp at h₃
  subst h₃
  unfold Strat
  simp at h
  ext <;> simp [h]

theorem a_strat_mk_eq_mk_iff {a b : AStrat} :
@Eq AStrat a b ↔ ∀ s, a.ap s = b.ap s := strat_mk_eq_mk_iff

theorem d_strat_mk_eq_mk_iff {a b : DStrat} :
@Eq DStrat a b ↔ ∀ s, a.ap s = b.ap s := strat_mk_eq_mk_iff

@[ext]
theorem strat_ext {ms} {a b : Strat ms} (h : a.ap = b.ap) : a = b := by
  simp [strat_mk_eq_mk_iff, h]

@[ext]
def a_strat_ext {a₁ a₂ : AStrat} : a₁.ap = a₂.ap → a₁ = a₂ := strat_ext

@[ext]
def d_strat_ext {d₁ d₂ : DStrat} : d₁.ap = d₂.ap → d₁ = d₂ := strat_ext

theorem a_strat_eq_iff {a b : AStrat} :
@Eq AStrat a b ↔ ∀ s, a.ap s = b.ap s := strat_mk_eq_mk_iff

theorem d_strat_eq_iff {a b : DStrat} :
@Eq DStrat a b ↔ ∀ s, a.ap s = b.ap s := strat_mk_eq_mk_iff

theorem strat_merge_self {ms P} {a : Strat ms} : a.merge P a = a := by
  simp [Strat.merge]

theorem strat_merge_swap {ms P} {a b : Strat ms} :
a.merge P b = b.merge (¬P ·) a := by
  simp [Strat.merge]; intro s; split_ifs with h <;> rfl

def mk_strat_const (ms : Moves) (s' : State') : Strat ms :=
  mk_strat ms # λ _ => s'

def Strat.set {ms} (a : Strat ms) (s : State) (s' : State') : Strat ms :=
  a.merge (· = s) # mk_strat_const ms s'

theorem strat_merge_eq_of_neg {ms} {P : State → Prop} {a b : Strat ms} {s}
(h : ¬P s) : (a.merge P b).ap s = a.ap s := by
  simp [Strat.merge, h]

theorem strat_merge_eq_of_pos {ms} {P : State → Prop} {a b : Strat ms} {s}
(h : P s) : (a.merge P b).ap s = b.ap s := by
  simp [Strat.merge, h]

theorem strat_set_ap_eq_of_pos {ms : Moves} {a : Strat ms} {s s'}
(h : ms s.toState' s') : (a.set s s').ap s = some s' := by
  unfold Strat.set
  rw [strat_merge_eq_of_pos] <;> try rfl
  unfold mk_strat_const
  simp
  refine' ⟨⟨_, h⟩, _⟩
  intro h₁
  contradiction

theorem a_state_has_move_iff_has_move' {sa : AState} :
sa.has_move' ↔ sa.a_has_move := by rfl

theorem d_state_has_move_iff_has_move' {sd : DState} :
sd.has_move' ↔ sd.d_has_move := by rfl

@[simp] def mk_a_strat_const (s : State') : AStrat := mk_strat_const AMoves s
@[simp] def mk_d_strat_const (s : State') : DStrat := mk_strat_const DMoves s

@[simp]
theorem game_move_ne_game₀ {pw a d} {g : Game} : g.move ≠ game₀ pw a d := by
  simp only [state₀, game₀, Game.move, State.push]
  split_ifs with h₁
  · rintro rfl
    simp at h₁
  split <;> simp

theorem a_strat_ap_eq_of_not_a_has_move {a : AStrat} {s : State}
(h : ¬s.a_has_move) : a.ap s = none := by simpa

@[simp]
theorem state_push_inj {s₁ s₂ : State} {s'₁ s'₂} :
s₁.push s'₁ = s₂.push s'₂ ↔ s₁ = s₂ ∧ s'₁ = s'₂ := by
  simp [State.push]; aesop

@[simp]
theorem state_push_ne_self {s : State} {s'} : s.push s' ≠ s := by
  apply ne_of_congr State.hist
  simp [State.push]

theorem exi_a_ap_eq_some : ∃ (a₂ : AStrat) (s₂ : State) (sx : State'),
a₂.ap s₂ = some sx := by
  use mk_a_strat # λ _ => (1, 0)
  obtain ⟨s, hs⟩ := hv # state₀ 1
  obtain ⟨s₁, hs₁⟩ := hv {s.toState' with a_pos := (1, 0)}
  dsimp at hs₁
  use s, s₁
  simp [mk_a_strat]
  have h₁ : s.a_move s₁ :=
    by
      subst hs hs₁
      simp [State'.a_move]
      decide
  use ⟨_, h₁⟩
  subst hs₁
  simp [h₁]

theorem game_move_toState_inj {g₁ g₂ : Game}
(h : g₁.move = g₂.move) : g₁.toState = g₂.toState := by
  rcases g₁ with ⟨s₁, a₁, d₁, ht₁, he₁⟩
  rcases g₂ with ⟨s₂, a₂, d₂, ht₂, he₂⟩
  dsimp; simp [Game.move] at h
  split_ifs at h <;> (try split at h) <;> (try split at h) <;>
    simp at h ⊢ <;> tauto

theorem game_move_a_turn_iff_of_not_ended_of_move_ended {g : Game}
(he : g.move.ended) : g.move.a_turn ↔ g.a_turn := by
  simp [Game.move] at he ⊢; split_ifs with h₁ h₂; rfl
  all_goals simp [h₁, h₂] at he; split at he; rfl; simp at he

@[simp]
theorem game₀_a {pw a d} : (game₀ pw a d).a = a := rfl

@[simp]
theorem game₀_d {pw a d} : (game₀ pw a d).d = d := rfl

theorem game_play_eq_play_le_of_ended {g : Game} {n m}
(he : (g.play m).ended) (h : m ≤ n) : g.play n = g.play m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp [game_play_eq_of_ended he]

theorem game_move_eq_of_not_ended_and_move_ended {g : Game}
(h₁ : ¬g.ended) (h₂ : g.move.ended) : g.move = {g with ended := True} := by
  simp [Game.move, h₁] at h₂ ⊢
  split_ifs at h₂ ⊢ with h₃ <;> split <;> simp <;> nm m s h₄ <;>
    simp [h₄] at h₂

theorem game_eq_of_not_ended_and_move_ended {g : Game}
(h₁ : ¬g.ended) (h₂ : g.move.ended) : g = {g.move with ended := False} := by
  simp [game_move_eq_of_not_ended_and_move_ended h₁ h₂]
  rw [←iff_false] at h₁; rw [←h₁]

theorem game_with_not_ended_valid_of_valid {g : Game}
(h : g.valid) : {g with ended := False}.valid := by
  by_cases he : ¬g.ended
  · cases g
    simp at he
    simp [he] at h ⊢
    exact h
  simp at he
  obtain ⟨pw, a, d, n, hg⟩ := h
  
  obtain ⟨g₀, hg₀⟩ := hv # game₀ pw a d
  rw [←hg₀] at hg
  obtain ⟨f, hf⟩ := hv # λ n => (g₀.play n).ended
  have h₁ : ∃ n, f n :=
    by
      subst hf hg hg₀
      exact ⟨_, he⟩
  obtain ⟨m, hm⟩ := hv # nat_find f
  obtain ⟨h₂, h₃⟩ := nat_find_spec' h₁
  rw [←hm] at h₂ h₃
  
  cases m; simp [hf, hg₀] at h₂; nm m
  simp only [Nat.succ_le_iff] at h₃
  
  use pw, a, d, m
  rw [←hg₀]
  
  have he₁ : (g₀.play (m + 1)).ended :=
    by
      rw [hf] at h₂
      exact h₂
  
  replace hg : g = g₀.play (m + 1) :=
    by
      subst hg
      specialize h₃ n # by rwa [hf]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h₃
      apply game_play_eq_play_le_of_ended he₁
      linarith
  clear n
  
  specialize h₃ m
  simp [hf] at h₃
  
  simp at hg he₁
  rw [game_eq_of_not_ended_and_move_ended h₃ he₁]
  simp [hg₀, hg]

theorem game_ext {g₁ g₂ : Game}
(ha : g₁.a = g₂.a) (hd : g₁.d = g₂.d) (hs : g₁.toState = g₂.toState)
(ht : g₁.a_turn ↔ g₂.a_turn) (he : g₁.ended ↔ g₂.ended) : g₁ = g₂ := by
  ext <;> simp_all

theorem game_eq_iff {g₁ g₂ : Game} :
g₁ = g₂ ↔ g₁.a = g₂.a ∧ g₁.d = g₂.d ∧ g₁.toState = g₂.toState ∧
(g₁.a_turn ↔ g₂.a_turn) ∧ (g₁.ended ↔ g₂.ended) := by
  constructor; rintro rfl; simp
  simp [and_imp]; exact game_ext

@[simp]
theorem game_move_valid_iff {g : Game} : g.move.valid ↔ g.valid := by
  refine' ⟨λ h => _, game_move_valid_of_valid⟩
  
  by_cases he : g.ended
  · rw [game_move_eq_of_ended he] at h; exact h

  by_cases he₁ : g.move.ended
  · rw [game_eq_of_not_ended_and_move_ended he he₁]
    exact game_with_not_ended_valid_of_valid h
  
  obtain ⟨pw, a, d, n, h⟩ := h
  cases n <;> simp at h; nm n
  
  obtain ⟨g₁, hg₁⟩ := hv # (game₀ pw a d).play n
  rw [←hg₁] at h
  
  use pw, a, d, n
  
  have h₁ : ¬g₁.move.ended := by rwa [←h]
  have h₂ := game_not_ended_of_move_not_ended h₁
  
  rw [←hg₁]; clear hg₁
  
  apply game_ext
  · replace h := congrArg Game.a h
    simp at h
    exact h
  · replace h := congrArg Game.d h
    simp at h
    exact h
  · exact game_move_toState_inj h
  · replace h := congrArg Game.a_turn h
    rw [game_move_a_turn_iff_of_not_ended he₁,
      game_move_a_turn_iff_of_not_ended h₁] at h
    simp [not_iff_comm'] at h
    exact h
  · tauto

@[simp]
theorem game_play_valid_iff {g : Game} {n} : (g.play n).valid ↔ g.valid := by
  induction n; simp; simpa

@[simp]
theorem a_state_to_game_a {sa : AState} {a d} : (sa.to_game a d).a = a := rfl

@[simp]
theorem a_state_to_game_d {sa : AState} {a d} : (sa.to_game a d).d = d := rfl

@[simp]
theorem a_state_to_game_toState {sa : AState} {a d} :
(sa.to_game a d).toState = sa.toState := rfl

@[simp]
theorem d_state_to_game_a {sd : DState} {a d} : (sd.to_game a d).a = a := rfl

@[simp]
theorem d_state_to_game_d {sd : DState} {a d} : (sd.to_game a d).d = d := rfl

@[simp]
theorem d_state_to_game_toState {sd : DState} {a d} :
(sd.to_game a d).toState = sd.toState := rfl

def Game.set_strats (g : Game) (a : AStrat) (d : DStrat) :=
  {g with a := a, d := d}

def Game.merge (g : Game) (pa pd : State → Prop) (a : AStrat) (d : DStrat) :=
  g.set_strats (g.a.merge pa a) (g.d.merge pd d)

@[simp]
theorem game_merge_toState {g : Game} {pa pd a d} :
(g.merge pa pd a d).toState = g.toState := rfl

@[simp]
theorem game_merge_a {g : Game} {pa pd a d} :
(g.merge pa pd a d).a = g.a.merge pa a := rfl

@[simp]
theorem game_merge_d {g : Game} {pa pd a d} :
(g.merge pa pd a d).d = g.d.merge pd d := rfl

@[simp]
theorem game_merge_a_turn {g : Game} {pa pd a d} :
(g.merge pa pd a d).a_turn ↔ g.a_turn := by rfl

@[simp]
theorem game_merge_ended {g : Game} {pa pd a d} :
(g.merge pa pd a d).ended ↔ g.ended := by rfl

theorem game_merge_move_eq_of_not
{g : Game} {pa pd : State → Prop} {a d}
(ha : ¬pa g.toState) (hd : ¬pd g.toState) :
(g.merge pa pd a d).move = (g.move).merge pa pd a d := by
  simp [Game.move]; split_ifs; rfl
  · rw [strat_merge_eq_of_neg ha]; split <;> rfl
  · rw [strat_merge_eq_of_neg hd]; split <;> rfl

theorem game_merge_play_eq_merge_of_not
{g : Game} {pa pd : State → Prop} {a d n}
(hx : ∀ k < n, ¬pa (g.play k).toState ∧ ¬pd (g.play k).toState) :
(g.merge pa pd a d).play n = (g.play n).merge pa pd a d := by
  induction n; rfl; nm n ih
  specialize ih _
  · intro k hk
    apply hx
    linarith
  simp [ih]
  apply game_merge_move_eq_of_not
  · apply (hx _ _).1; linarith
  · apply (hx _ _).2; linarith

@[simp]
theorem game₀_merge {pw a d} {pa pd a₁ d₁} :
(game₀ pw a d).merge pa pd a₁ d₁ =
game₀ pw (a.merge pa a₁) (d.merge pd d₁) := by rfl

@[simp]
theorem state'₀_eq_state'₀_iff {pw₁ pw₂} :
state'₀ pw₁ = state'₀ pw₂ ↔ pw₁ = pw₂ := by simp [state'₀]

@[simp]
theorem state₀_eq_state₀_iff {pw₁ pw₂} :
state₀ pw₁ = state₀ pw₂ ↔ pw₁ = pw₂ := by simp [state₀]

@[simp]
theorem game₀_eq_game₀_iff {pw₁ pw₂ a₁ a₂ d₁ d₂} :
game₀ pw₁ a₁ d₁ = game₀ pw₂ a₂ d₂ ↔ pw₁ = pw₂ ∧ a₁ = a₂ ∧ d₁ = d₂ := by
  simp [game₀]

@[simp]
theorem strat_merge_const_true {ms} {a b : Strat ms} :
a.merge (λ _ => True) b = b := by simp [Strat.merge]

@[simp]
theorem strat_merge_const_false {ms} {a b : Strat ms} :
a.merge (λ _ => False) b = a := by simp [Strat.merge]

def Game.find_end (g : Game) : ℕ :=
  nat_find # λ n => (g.play n).ended

def Game.find_pre_end (g : Game) : ℕ :=
  nat_find # λ n => let g₁ := g.play n; ¬g₁.ended ∧ g₁.move.ended

theorem game_play_find_end_ended_of_play_ended {g : Game} {n}
(h : (g.play n).ended) : (g.play g.find_end).ended := by
  exact nat_find_spec (⟨_, h⟩ : (∃ n, (g.play n).ended))

theorem game_play_find_pre_end_not_ended_of {g : Game} {n}
(he : ¬g.ended) (h : (g.play n).ended) : ¬(g.play g.find_pre_end).ended := by
  contrapose! he
  induction n using Nat.strong_induction_on; nm n ih
  obtain ⟨m, hm⟩ := hv # g.find_pre_end
  by_cases h₁ : ∃ n, ¬(g.play n).ended ∧ (g.play n).move.ended
  rotate_left
  · unfold Game.find_pre_end nat_find at he
    simp [h₁] at he
    exact he
  have h₂ := nat_find_spec h₁
  rw [←Game.find_pre_end] at h₂
  simp only [←hm] at he h₂
  simp [he] at h₂

theorem game_play_find_pre_end_not_ended_of_play_ended_iff {g : Game} {n}
(h : (g.play n).ended) : (g.play g.find_pre_end).ended ↔ g.ended := by
  refine' ⟨λ he => _, game_play_ended_of_ended⟩
  contrapose! he
  exact game_play_find_pre_end_not_ended_of he h

theorem game₀_play_find_pre_end_not_ended_of_play_ended {pw a d n}
(h : ((game₀ pw a d).play n).ended) :
¬((game₀ pw a d).play (game₀ pw a d).find_pre_end).ended := by
  simp [game_play_find_pre_end_not_ended_of_play_ended_iff h]

theorem game_exi_play_not_ended_and_play_move_ended_iff {g : Game} :
(∃ n, ¬(g.play n).ended ∧ (g.play n).move.ended) ↔
¬g.ended ∧ ∃ n, (g.play n).ended := by
  constructor
  · rintro ⟨n, h₁, h₂⟩
    use game_not_ended_of_play_not_ended h₁
    use n + 1
    simpa
  rintro ⟨h₁, n, h₂⟩
  induction n
  · contradiction
  nm n ih
  simp at h₂
  rw [imp_iff_not_or] at ih
  rcases ih with ih | ih
  · use n
  exact ih

theorem game_play_find_pre_end_move_ended_of_play_ended {g : Game} {n}
(he : (g.play n).ended) : (g.play g.find_pre_end).move.ended := by
  by_cases h₁ : ¬∃ n, ¬(g.play n).ended ∧ (g.play n).move.ended
  · unfold Game.find_pre_end nat_find
    simp [h₁]
    rw [game_exi_play_not_ended_and_play_move_ended_iff] at h₁
    simp at h₁
    rw [imp_cpos] at h₁
    simp at h₁
    exact game_move_ended_of_ended # h₁ _ he
  rw [not_not] at h₁
  exact (nat_find_spec h₁).2

theorem game_play_add_ended_of_ended_left {g : Game} {n m}
(h : (g.play n).ended) : (g.play (n + m)).ended := by
  apply game_play_ended_of_le h; linarith

theorem game_play_add_ended_of_ended_right {g : Game} {n m}
(h : (g.play m).ended) : (g.play (n + m)).ended := by
  apply game_play_ended_of_le h; linarith

theorem game_lt_of_play_not_ended_and_play_ended {g : Game} {n m}
(h₁ : ¬(g.play n).ended) (h₂ : (g.play m).ended) : n < m := by
  contrapose! h₁; exact game_play_ended_of_le h₂ h₁

theorem game_find_pre_end_lt_of {g : Game} {n}
(h₁ : ¬g.ended) (h₂ : (g.play n).ended) : g.find_pre_end < n := by
  have h₃ := game_play_find_pre_end_not_ended_of h₁ h₂
  exact game_lt_of_play_not_ended_and_play_ended h₃ h₂

theorem game_find_pre_end_eq_zero_of_ended {g : Game}
(h : g.ended) : g.find_pre_end = 0 := by
  unfold Game.find_pre_end nat_find
  dsimp
  split_ifs with h₁
  · exfalso
    rw [game_exi_play_not_ended_and_play_move_ended_iff] at h₁
    simp [h] at h₁
  rfl

theorem game_find_pre_end_le_of {g : Game} {n}
(h : (g.play n).ended) : g.find_pre_end ≤ n := by
  by_cases he : g.ended
  · simp [game_find_pre_end_eq_zero_of_ended he]
  apply le_of_lt
  exact game_find_pre_end_lt_of he h

theorem game_a_turn_of_valid_and_move_ended {g : Game}
(h : g.valid) (he : g.move.ended) : g.a_turn := by
  apply (game_move_a_turn_iff_of_not_ended_of_move_ended he).mp
  replace h := game_move_valid_of_valid h
  exact game_a_turn_of_valid_and_ended h he

theorem game_play_eq_play_of_ended {g : Game} {n m}
(h₁ : (g.play n).ended) (h₂ : (g.play m).ended) : g.play n = g.play m := by
  wlog h₃ : n ≤ m with h₄
  · exact (h₄ h₂ h₁ # by linarith).symm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₃
  symm; exact game_play_eq_play_le_of_ended h₁ h₃

theorem game_not_ended_of_valid_and_a_has_move {g : Game}
(h : g.valid) (hm : g.toState.a_has_move) : ¬g.ended := by
  obtain ⟨pw, a, d, n, hg⟩ := h
  obtain ⟨g₀, hg₀⟩ := hv # game₀ pw a d
  rw [←hg₀] at hg
  intro he
  have h : g.valid :=
    by
      simp [hg, hg₀]
  
  obtain ⟨gx, hgx⟩ := hv # g₀.play g₀.find_pre_end
  
  have ht := game_a_turn_of_valid_and_ended h he
  
  have h₁ : ¬gx.ended :=
    by
      subst hgx hg₀ hg
      exact game₀_play_find_pre_end_not_ended_of_play_ended he
  
  have h₂ : gx.move.ended :=
    by
      subst hgx hg
      exact game_play_find_pre_end_move_ended_of_play_ended he
  
  have h₃ : g₀.find_pre_end < n :=
    by
      apply game_find_pre_end_lt_of
      · simp [hg₀]
      rwa [←hg]
  
  have h₄ : gx.valid := by simp [hgx, hg₀]
  
  have h₅ : gx.a_turn :=
    by
      subst hgx
      exact game_a_turn_of_valid_and_move_ended h₄ h₂
  
  have h₆ : gx.toState = g.toState :=
    by
      subst hg hgx
      rw [←game_move_toState_eq_of_move_ended h₂]
      rw [←game_play_succ] at h₂ ⊢
      rw [game_play_eq_play_of_ended h₂ he]
  
  rw [←h₆] at hm
  contrapose! h₂; clear h₂
  
  exact game_move_not_ended_of_a_turn h₁ h₅ hm

theorem game_move_size_le_game_size_succ {g : Game} :
g.move.size ≤ g.size + 1 := by
  by_cases he : g.ended
  · rw [game_move_size_eq_of_ended he]; linarith
  simp [Game.move, he]
  split_ifs <;> split <;> simp

theorem game_play_size_le_game_size_add {g : Game} {n} :
(g.play n).size ≤ g.size + n := by
  induction n; rfl; nm n ih
  trans (g.play n).size + 1
  · simp; exact game_move_size_le_game_size_succ
  linarith

@[simp]
theorem game₀_play_size_le {pw a d n} : ((game₀ pw a d).play n).size ≤ n := by
  have h := @game_play_size_le_game_size_add (game₀ pw a d) n
  simp at h; exact h

@[simp]
theorem a_state_to_game_a_turn {sa : AState} {a d} :
(sa.to_game a d).a_turn := by trivial

@[simp]
theorem a_state_to_game_not_ended {sa : AState} {a d} :
¬(sa.to_game a d).ended := λ h => h

@[simp]
theorem d_state_to_game_not_a_turn {sd : DState} {a d} :
¬(sd.to_game a d).a_turn := λ h => h

@[simp]
theorem d_state_to_game_not_ended {sd : DState} {a d} :
¬(sd.to_game a d).ended := λ h => h

theorem game_a_turn_iff_odd_size_of_valid {g : Game}
(h₁ : g.valid) : g.a_turn ↔ Odd g.size := by
  obtain ⟨pw, a, d, n, hg⟩ := h₁
  induction n generalizing g
  · simp [hg]
  nm n ih
  simp at hg
  specialize ih rfl
  obtain ⟨g₁, hg₁⟩ := hv # (game₀ pw a d).play n
  rw [←hg₁] at hg ih
  clear hg₁
  subst hg
  rename' g₁ => g
  
  by_cases he : g.ended
  · simpa only [game_move_eq_of_ended he]
  
  by_cases he₁ : g.move.ended
  · rw [game_eq_of_not_ended_and_move_ended he he₁] at ih
    simp at ih
    exact ih
  
  rw [game_move_a_turn_iff_of_not_ended he₁, ih]
  rw [game_move_size_eq_of_move_not_ended he₁]
  simp

theorem game_a_turn_of_valid_and_odd_size {g : Game}
(h₁ : g.valid) (h₂ : Odd g.size) : g.a_turn := by
  rwa [game_a_turn_iff_odd_size_of_valid h₁]

theorem game_not_move_ended_of_valid_and_a_has_move {g : Game}
(h₁ : g.valid) (h₂ : g.a_has_move) : ¬g.move.ended := by
  have h₃ := game_not_ended_of_valid_and_a_has_move h₁ h₂
  by_cases ht : ¬g.a_turn
  · exact game_move_valid_not_ended_of_d_turn h₁ h₃ ht
  simp at ht
  simp [Game.move, h₃, ht]
  split
  · nm m h₅
    simp at h₅
    contradiction
  · simp

theorem game_merge_valid_of_not_le_size
{g : Game} {pa pd : State → Prop} {a₁ d₁}
(hx : ∀ (s : State), s.size ≤ g.size → ¬pa s ∧ ¬pd s)
(h : g.valid) : (g.merge pa pd a₁ d₁).valid := by
  obtain ⟨pw, a, d, n, hg⟩ := h
  use pw, a.merge pa a₁, d.merge pd d₁, n
  have h₁ := @game_merge_play_eq_merge_of_not (game₀ pw a d) pa pd
    a₁ d₁ n
  specialize h₁ _
  · clear h₁
    intro k hk
    apply hx; clear hx
    subst hg
    apply game_play_size_le_play_size_of_le
    linarith
  simp at h₁
  simp [←hg] at h₁
  rw [←h₁]

theorem game_merge_valid_of_not_lt_size_of_not_ended
{g : Game} {pa pd : State → Prop} {a₁ d₁}
(hx : ∀ (s : State), s.size < g.size → ¬pa s ∧ ¬pd s)
(h : g.valid) (he : ¬g.ended) : (g.merge pa pd a₁ d₁).valid := by
  obtain ⟨pw, a, d, n, hg⟩ := h
  use pw, a.merge pa a₁, d.merge pd d₁, n
  have h₁ := @game_merge_play_eq_merge_of_not (game₀ pw a d) pa pd
    a₁ d₁ n
  specialize h₁ _
  · clear h₁
    intro k hk
    apply hx; clear hx
    subst hg
    rw [lt_iff_le_and_ne]
    constructor
    · apply game_play_size_le_play_size_of_le
      linarith
    rw [game₀_play_size_eq_of_not_ended he]
    rw [game₀_play_size_eq_of_not_ended]
    · linarith
    contrapose! he
    apply game_play_ended_of_le he
    linarith
  simp at h₁
  simp [←hg] at h₁
  rw [←h₁]

theorem game_move_play {g : Game} {n} : g.move.play n = (g.play n).move :=
  game_play_succ

theorem game_move_toState'_eq_of_of_not_ended_and_a_turn_and_a_has_move
{g : Game} {s'} (he : ¬g.ended) (ht : g.a_turn)
(h₂ : g.a.ap g.toState = some s') : g.move.toState' = s' := by
  simp [Game.move, he, ht]
  split
  · nm m h₃
    simp [h₂] at h₃
  · nm m s₁ h₃
    simp [h₂] at h₃
    exact h₃.symm

theorem game_move_toState'_eq_iff_of_not_ended_and_a_turn_and_a_has_move
{g : Game} {s'} (he : ¬g.ended) (ht : g.a_turn) (h₁ : g.a_has_move) :
g.move.toState' = s' ↔ g.a.ap g.toState = some s' := by
  simp [Game.move, he, ht]
  split
  · nm m h₂
    simp at h₂
    contradiction
  · nm m s₁ h₂
    simp [h₂]

theorem game_move_toState_eq_of_not_ended_and_a_turn_and_a_has_move
{g : Game} (he : ¬g.ended) (ht : g.a_turn) (h₁ : g.a_has_move) :
g.move.toState = g.toState.push g.move.toState' := by
  simp [Game.move, he, ht]
  split
  · nm m h₂
    simp at h₂
    contradiction
  · nm m s h₂
    simp

theorem game_move_toState_eq_of_not_ended_and_d_turn_and_d_has_move
{g : Game} (he : ¬g.ended) (ht : g.d_turn) (h₁ : g.d_has_move) :
g.move.toState = g.toState.push g.move.toState' := by
  simp [Game.move, he, ht]
  split
  · nm m h₂
    simp at h₂
    contradiction
  · nm m s h₂
    simp

theorem game_move_toState'_eq_of_of_not_ended_and_d_turn_and_d_has_move
{g : Game} {s'} (he : ¬g.ended) (ht : ¬g.a_turn)
(h₂ : g.d.ap g.toState = some s') : g.move.toState' = s' := by
  simp [Game.move, he, ht]
  split
  · nm m h₃
    simp [h₂] at h₃
  · nm m s₁ h₃
    simp [h₂] at h₃
    exact h₃.symm

theorem a_state_a_move_to_game_move_of_a_has_move {sa : AState} {a d}
(h : sa.a_has_move) : sa.a_move (sa.to_game a d).move.toState' := by
  simp [Game.move]
  split
  · nm m h₁
    simp at h₁
    contradiction
  nm m s h₁
  exact of_strat_ap_eq_some h₁

theorem d_state_d_move_to_game_move_of_d_has_move {sd : DState} {a d}
(h : sd.d_has_move) : sd.d_move (sd.to_game a d).move.toState' := by
  simp [Game.move]
  split
  · nm m h₁
    simp at h₁
    contradiction
  nm m s h₁
  exact of_strat_ap_eq_some h₁

theorem exi_a_state_move_of_a_move {sa : AState} {s : State'}
(h : sa.a_move s) : ∃ sd, s = sd.toState' ∧ sa.move sd := by
  have ⟨g, h₁, h₂⟩ := sa.h_valid
  have he₁ : ¬g.move.ended :=
    by
      rw [h₂] at h
      apply game_not_move_ended_of_valid_and_a_has_move h₁ ⟨_, h⟩
  have he : ¬g.ended := game_not_ended_of_move_not_ended he₁
  obtain ⟨a₁, ha₁⟩ := hv # g.a.set sa.toState s
  have ⟨g₁, hg₁⟩ := hv # sa.to_game a₁ g.d
  
  have hq : g.valid := by simp [h₁]
  
  have ht : g.a_turn :=
      by
        apply game_a_turn_of_valid_and_odd_size hq
        rw [←h₂]
        exact sa.h_size
  
  have h₃ : g₁ = g.merge
    (· = sa.toState) (λ _ => False)
    (mk_a_strat_const s) default :=
    by
      subst hg₁
      apply game_ext <;> simp
      · exact ha₁
      · exact h₂
      · exact ht
      · exact he
  
  have ht₁ : g₁.a_turn := by simpa [h₃]
  
  refine' ⟨⟨⟨g₁.move.toState, _⟩, _⟩, _⟩
  · apply state_valid_of_game_valid
    simp
    obtain ⟨pw, a, d, n, h₁⟩ := h₁
    use pw, a₁, d, n
    have h₂ : game₀ pw a₁ d =
      (game₀ pw a d).merge (· = sa.toState) (λ _ => False)
      (mk_a_strat_const s) default := by simp [ha₁, h₁]; rfl
    rw [h₂]; clear h₂
    rw [game_merge_play_eq_merge_of_not]
    
    rotate_left
    · intro k hk
      simp
      apply ne_of_congr State.size
      subst h₁
      simp [h₂, game_play_size_eq_of_not_ended he]
      contrapose! hk
      subst hk
      simp
    apply game_ext <;> simp
    · simp [hg₁, ha₁, h₁]; rfl
    · simp [hg₁, h₁]
    · simp [h₃, h₁]
    · simp [←h₁, ht, hg₁]
    · simp [←h₁, he, hg₁]
  · rw [←Nat.not_odd_iff_even]
    rw [←game_a_turn_iff_odd_size_of_valid]
    · rw [game_move_a_turn_iff_of_not_ended]
      · simp [ht₁]
      apply game_move_not_ended_of_a_turn
      · simpa [h₃]
      · exact ht₁
      use s
      convert h
      simp [h₃, h₂]
    · simp
      rw [h₃]
      apply game_merge_valid_of_not_lt_size_of_not_ended
      · intro s hs
        simp
        rintro rfl
        contrapose! hs; clear hs
        rw [h₂]
      · exact hq
      · exact he
  simp
  constructor
  · symm
    rw [hg₁, ha₁]
    apply game_move_toState'_eq_of_of_not_ended_and_a_turn_and_a_has_move
      <;> simp
    exact strat_set_ap_eq_of_pos h
  constructor
  · simp [AState.move', hg₁]
    apply a_state_a_move_to_game_move_of_a_has_move
    exact ⟨_, h⟩
  · simp
    have h₄ := @game_move_toState_eq_of_not_ended_and_a_turn_and_a_has_move g₁
    specialize h₄ _ _ _
    · simpa [h₃]
    · simpa [h₃]
    · simp [h₃, ←h₂]
      exact ⟨_, h⟩
    convert h₄
    simp [hg₁]

theorem game_not_ended_of_valid_and_d_turn {g : Game}
(h : g.valid) (ht : ¬g.a_turn) : ¬g.ended := by
  contrapose! ht; exact game_a_turn_of_valid_and_ended h ht

theorem game_move_not_ended_of_valid_and_d_turn {g : Game}
(h : g.valid) (ht : ¬g.a_turn) : ¬g.move.ended := by
  apply game_move_not_ended_of_d_turn
  · exact game_not_ended_of_valid_and_d_turn h ht
  · exact ht
  · exact d_always_has_move' h

@[simp]
theorem odd_a_state_size {sa : AState} : Odd sa.size := sa.h_size

@[simp]
theorem even_d_state_size {sd : DState} : Even sd.size := sd.h_size

theorem exi_d_state_move_of_d_move {sd : DState} {s : State'}
(h : sd.d_move s) : ∃ sa, s = sa.toState' ∧ sd.move sa := by
  have ⟨g, h₁, h₂⟩ := sd.h_valid
  have he₁ : ¬g.move.ended :=
    by
      apply game_move_not_ended_of_valid_and_d_turn h₁
      rw [game_a_turn_iff_odd_size_of_valid h₁]
      simp [←h₂]
  have he : ¬g.ended := game_not_ended_of_move_not_ended he₁
  obtain ⟨d₁, hd₁⟩ := hv # g.d.set sd.toState s
  have ⟨g₁, hg₁⟩ := hv # sd.to_game g.a d₁
  
  have hq : g.valid := by simp [h₁]
  
  have ht : ¬g.a_turn :=
      by
        rw [game_a_turn_iff_odd_size_of_valid hq]
        simp [←h₂]
  
  have h₃ : g₁ = g.merge
    (λ _ => False) (· = sd.toState)
    default (mk_d_strat_const s) :=
    by
      subst hg₁
      apply game_ext <;> simp
      · exact hd₁
      · exact h₂
      · exact ht
      · exact he
  
  have ht₁ : ¬g₁.a_turn := by simpa [h₃]
  
  refine' ⟨⟨⟨g₁.move.toState, _⟩, _⟩, _⟩
  · apply state_valid_of_game_valid
    simp
    obtain ⟨pw, a, d, n, h₁⟩ := h₁
    use pw, a, d₁, n
    have h₂ : game₀ pw a d₁ =
      (game₀ pw a d).merge (λ _ => False) (· = sd.toState)
      default (mk_d_strat_const s) := by simp [hd₁, h₁]; rfl
    rw [h₂]; clear h₂
    rw [game_merge_play_eq_merge_of_not]
    
    rotate_left
    · intro k hk
      simp
      apply ne_of_congr State.size
      subst h₁
      simp [h₂, game_play_size_eq_of_not_ended he]
      contrapose! hk
      subst hk
      simp
    apply game_ext <;> simp
    · simp [hg₁, h₁]
    · simp [hg₁, hd₁, h₁]; rfl
    · simp [h₃, h₁]
    · simp [←h₁, ht, hg₁]
    · simp [←h₁, he, hg₁]
  · rw [←game_a_turn_iff_odd_size_of_valid]
    · rw [game_move_a_turn_iff_of_not_ended]
      · simp [ht₁]
      apply game_move_not_ended_of_d_turn
      · simpa [h₃]
      · exact ht₁
      use s
      convert h
      simp [h₃, h₂]
    · simp
      rw [h₃]
      apply game_merge_valid_of_not_lt_size_of_not_ended
      · intro s hs
        simp
        rintro rfl
        contrapose! hs; clear hs
        rw [h₂]
      · exact hq
      · exact he
  simp
  constructor
  · symm
    rw [hg₁, hd₁]
    apply game_move_toState'_eq_of_of_not_ended_and_d_turn_and_d_has_move
      <;> simp
    exact strat_set_ap_eq_of_pos h
  constructor
  · simp [AState.move', hg₁]
    apply d_state_d_move_to_game_move_of_d_has_move
    exact ⟨_, h⟩
  · simp
    have h₄ := @game_move_toState_eq_of_not_ended_and_d_turn_and_d_has_move g₁
    specialize h₄ _ _ _
    · simpa [h₃]
    · simpa [h₃]
    · simp [h₃, ←h₂]
      exact ⟨_, h⟩
    convert h₄
    simp [hg₁]

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

theorem exi_a_state_move_of_a_has_move {sa : AState}
(h : sa.a_has_move) : ∃ sd, sa.move sd := by
  obtain ⟨s, h⟩ := h
  obtain ⟨sd, h₁, h₂⟩ := exi_a_state_move_of_a_move h
  exact ⟨_, h₂⟩

theorem exi_d_state_move_of_d_has_move {sd : DState}
(h : sd.d_has_move) : ∃ sa, sd.move sa := by
  obtain ⟨s, h⟩ := h
  obtain ⟨sd, h₁, h₂⟩ := exi_d_state_move_of_d_move h
  exact ⟨_, h₂⟩

def d_state₀ (pw : ℕ) : DState := by
  refine' ⟨⟨state₀ pw, _⟩, _⟩ <;> simp

def a_state₀ (pw : ℕ) : AState :=
  Classical.epsilon (d_state₀ pw).move

@[simp]
theorem d_state₀_toState_eq {pw} : (d_state₀ pw).toState = state₀ pw := rfl

@[simp]
theorem state_mk_size {s' hist} : (⟨s', hist⟩ : State).size = hist.length := rfl

theorem exi_d_state₀_move (pw) : ∃ sa, (d_state₀ pw).move sa := by
  apply exi_d_state_move_of_d_has_move; simp

theorem d_state_size_eq_of_a_state_move {sa : AState} {sd : DState}
(h : sa.move sd) : sd.size = sa.size + 1 := by
  obtain ⟨⟨sa, ha₁⟩, ha₂⟩ := sa
  obtain ⟨⟨sd, hd₁⟩, hd₂⟩ := sd
  obtain ⟨h₁, h₂⟩ := h
  dsimp at ha₂ hd₂ h₂ ⊢
  rw [h₂]
  simp

theorem a_state_size_eq_of_d_state_move {sd : DState} {sa : AState}
(h : sd.move sa) : sa.size = sd.size + 1 := by
  obtain ⟨⟨sa, ha₁⟩, ha₂⟩ := sa
  obtain ⟨⟨sd, hd₁⟩, hd₂⟩ := sd
  obtain ⟨h₁, h₂⟩ := h
  dsimp at ha₂ hd₂ h₂ ⊢
  rw [h₂]
  simp

@[simp]
theorem game₀_move_size {pw a d} : (game₀ pw a d).move.size = 1 := by
  rw [game_move_toState_eq_of_not_ended_and_d_turn_and_d_has_move] <;> simp

theorem game_a_move_move_of {g : Game}
(he : ¬g.move.ended) (ht : g.a_turn) : g.a_move g.move.toState' := by
  have he₁ := game_not_ended_of_move_not_ended he
  revert he; simp [Game.move, he₁, ht]
  split <;> simp
  nm m s h₁
  exact of_a_ap_eq_some h₁

theorem exi_a_state_move : ∃ (sa : AState) (sd : DState), sa.move sd := by
  obtain ⟨⟨s, g, ⟨pw, a, d, n, rfl⟩, rfl⟩, h⟩ := exi_valid_state_with_size 2
  dsimp at h
  generalize hg₀ : game₀ pw a d = g₀ at h; rw [eq_comm] at hg₀
  obtain ⟨g, hg⟩ := hv # g₀.play 2
  have h₁ : g.size = 2 :=
    by
      subst hg₀ hg
      exact game₀_play_size_eq_self_of_any n h
  obtain ⟨sa, hsa⟩ : ∃ (sa : AState), sa.toState = (g₀.play 1).toState :=
    by
      refine' ⟨⟨⟨(g₀.play 1).toState, _⟩, _,⟩, _⟩ <;> simp [hg₀]
      · apply state_valid_of_game_valid
        simp
  use sa
  obtain ⟨sd, hsd⟩ : ∃ (sd : DState), sd.toState = g.toState :=
    by
      refine' ⟨⟨⟨g.toState, _⟩, _,⟩, _⟩ <;> simp [hg]
      · apply state_valid_of_game_valid
        simp [hg₀]
      · simp at hg
        simp [←hg, h₁]
  use sd
  obtain ⟨⟨sa, hsa₁⟩, hsa₂⟩ := sa
  obtain ⟨⟨sd, hsd₁⟩, hsd₂⟩ := sd
  unfold AState.move AState.move'
  dsimp at hsa₂ hsd₂ ⊢
  subst hsa hsd
  have he : ¬g.ended :=
    by
      subst hg hg₀
      rw [←game_play_size_lt_iff_play_ended]
      · rw [h₁]
        simp
      · simp
  have ht : (g₀.play 1).a_turn :=
    by
      rw [game_a_turn_iff_odd_size_of_valid]
      · exact hsa₂
      · simp [hg₀]
  constructor
  · rw [hg]
    nth_rewrite 2 [game_play_succ]
    apply game_a_move_move_of
    · subst hg
      exact he
    · exact ht
  · rw [hg]
    change (g₀.play 1).move.toState = _
    apply game_move_toState_eq_of_not_ended_and_a_turn_and_a_has_move
    · simp [hg₀]
    · exact ht
    · use g.toState'
      rw [hg]
      apply game_a_move_move_of
      · subst hg
        exact he
      · exact ht

theorem exi_d_state_move : ∃ (sd : DState) (sa : AState), sd.move sa :=
  ⟨_, exi_d_state₀_move 1⟩

theorem state_ext {s₁ s₂ : State}
(h₁ : s₁.toState' = s₂.toState') (h₂ : s₁.hist = s₂.hist) : s₁ = s₂ := by
  cases s₁; cases s₂; dsimp at h₁ h₂; rw [h₁, h₂]

@[simp]
theorem a_move_irrefl {s : State'} : ¬s.a_move s := by
  simp [State'.a_move]
  intro p h₁ h₂ h₃
  rw [h₁] at h₃
  simp at h₃

@[simp]
theorem d_move_irrefl {s : State'} : ¬s.d_move s := by
  simp [State'.d_move]
  intro p h₁ h₂
  rw [h₁] at h₂
  simp at h₂

theorem d_move_asymm {s₁ s₂ : State'}
(h : s₁.d_move s₂) : ¬s₂.d_move s₁ := by
  intro h₁
  obtain ⟨p₁, hp₁, hp₂, hp₃⟩ := h
  obtain ⟨p₂, hp₄, hp₅, hp₆⟩ := h₁
  subst hp₁
  contrapose! hp₄
  dsimp
  simp at hp₅ hp₆
  apply ne_of_congr State'.grid
  dsimp
  rw [Set.ext_iff]
  simp
  use p₁
  simpa

theorem game_find_end_le_of_play_ended {g : Game} {n}
(he : (g.play n).ended) : g.find_end ≤ n := by
  contrapose! he; exact nat_find_min he

theorem game_play_eq_play_find_end_of_play_ended {g : Game} {n}
(he : (g.play n).ended) : g.play n = g.play g.find_end := by
  apply game_play_eq_play_le_of_ended
  · exact game_play_find_end_ended_of_play_ended he
  · exact game_find_end_le_of_play_ended he

theorem game_find_end_eq_succ_of_play_ended {g : Game} {n}
(h : ¬g.ended) (he : (g.play n).ended) : g.find_end = g.find_pre_end + 1 := by
  have h₁ := game_play_find_pre_end_not_ended_of h he
  have h₂ := game_play_find_pre_end_move_ended_of_play_ended he
  have h₄ := game_play_find_end_ended_of_play_ended he
  apply le_antisymm
  · apply game_find_end_le_of_play_ended
    simpa
  rw [Nat.succ_le_iff]
  exact game_lt_of_play_not_ended_and_play_ended h₁ h₄

theorem game_play_find_end_eq_move_of_play_ended {g : Game} {n}
(he : (g.play n).ended) : g.play g.find_end = (g.play g.find_pre_end).move := by
  by_cases h : g.ended
  · rw [←game_play_succ]; simp only [game_play_eq_of_ended h]
  rw [game_find_end_eq_succ_of_play_ended h he]; simp

theorem game_play_eq_play_find_pre_end_move_of_play_ended {g : Game} {n}
(he : (g.play n).ended) : g.play n = (g.play g.find_pre_end).move := by
  by_cases h : g.ended
  · rw [←game_play_succ]; simp only [game_play_eq_of_ended h]
  rw [game_play_eq_play_find_end_of_play_ended he]
  rw [←game_play_succ]
  rw [game_find_end_eq_succ_of_play_ended h he]

theorem game_move_toState_eq_of_not_ended_and_move_ended {g : Game}
(h : ¬g.ended) (he : g.move.ended) : g.move.toState = g.toState := by
  rw [game_move_eq_of_not_ended_and_move_ended h he]

theorem game_play_find_pre_end_move_to_state_eq_of_play_ended {g : Game} {n}
(he : (g.play n).ended) :
(g.play g.find_pre_end).move.toState = (g.play g.find_pre_end).toState := by
  by_cases h : g.ended
  · rw [←game_play_succ]
    simp only [game_play_eq_of_ended h]
  apply game_move_toState_eq_of_not_ended_and_move_ended
  · exact game_play_find_pre_end_not_ended_of h he
  · exact game_play_find_pre_end_move_ended_of_play_ended he

theorem game_toState'_ind (g : Game) (P : State' → Prop)
(h₀ : P g.toState')
(ha : ∀ sa sd, sa.a_move sd → P sa → P sd)
(hd : ∀ sd sa, sd.d_move sa → P sd → P sa)
{n} : P (g.play n).toState' := by
  induction n
  · exact h₀
  nm n ih
  simp
  generalize g.play n = g at ih ⊢; nm x; clear x h₀
  simp [Game.move]
  split_ifs with h₁ h₂; exact ih
  all_goals split <;> dsimp <;> (try exact ih); nm m s h₃
  · replace h₃ := of_a_ap_eq_some h₃
    exact ha g.toState' s h₃ ih
  · replace h₃ := of_d_ap_eq_some h₃
    exact hd g.toState' s h₃ ih

@[simp]
theorem a_ap_irrefl {a : AStrat} {s : State} : ¬a.ap s = some s.toState' := by
  intro h
  replace h := of_a_ap_eq_some h
  simp at h

@[simp]
theorem d_ap_irrefl {d : DStrat} {s : State} : ¬d.ap s = some s.toState' := by
  intro h
  replace h := of_d_ap_eq_some h
  simp at h

@[simp]
theorem game_move_toState'_eq_orig_iff_move_ended {g : Game} :
g.move.toState' = g.toState' ↔ g.move.ended := by
  simp [Game.move]
  split_ifs with h₁ h₂; simp [h₁]
  all_goals split <;> simp [h₁]; nm m s h₃; rintro rfl; simp at h₃

theorem game_play_find_pre_end_move_toState_eq_of_ended {g : Game} {n}
(he : (g.play n).ended) :
(g.play g.find_pre_end).move.toState = (g.play g.find_pre_end).toState := by
  apply game_move_toState_eq_of_move_ended
  exact game_play_find_pre_end_move_ended_of_play_ended he

theorem odd_game_size_iff_a_turn_of_valid {g : Game}
(h : g.valid) : Odd g.size ↔ g.a_turn := by
  simp [game_a_turn_iff_odd_size_of_valid h]

theorem even_game_size_iff_d_turn_of_valid {g : Game}
(h : g.valid) : Even g.size ↔ ¬g.a_turn := by
  simp [game_a_turn_iff_odd_size_of_valid h]

@[simp]
theorem odd_game₀_play_size_iff_play_a_turn {pw a d n} :
Odd ((game₀ pw a d).play n).size ↔ ((game₀ pw a d).play n).a_turn := by
  simp [odd_game_size_iff_a_turn_of_valid]

@[simp]
theorem even_game₀_play_size_iff_play_d_turn {pw a d n} :
Even ((game₀ pw a d).play n).size ↔ ¬((game₀ pw a d).play n).a_turn := by
  simp [even_game_size_iff_d_turn_of_valid]

theorem game_find_end_eq_find_pre_end_succ_of {g : Game} {n}
(h₁ : ¬g.ended) (h₂ : (g.play n).ended) : g.find_end = g.find_pre_end + 1 := by
  have h₃ := game_play_find_pre_end_not_ended_of h₁ h₂
  have h₄ := game_play_find_pre_end_move_ended_of_play_ended h₂
  rw [←game_play_succ] at h₄
  generalize g.find_pre_end = m at h₃ h₄ ⊢
  unfold Game.find_end
  apply nat_find_eq_of h₄
  intro k hk
  contrapose! hk
  rw [Nat.succ_le_iff]
  exact game_lt_of_play_not_ended_and_play_ended h₃ hk

theorem game_find_pre_end_succ_eq_find_end_of {g : Game} {n}
(h₁ : ¬g.ended) (h₂ : (g.play n).ended) : g.find_pre_end + 1 = g.find_end := by
  rw [game_find_end_eq_find_pre_end_succ_of h₁ h₂]

theorem game_find_end_eq_zero_of_ended {g : Game}
(he : g.ended) : g.find_end = 0 := by
  unfold Game.find_end; apply nat_find_eq_of he; simp

theorem game_find_end_eq_zero_of_all_not_ended {g : Game}
(h : ∀ n, ¬(g.play n).ended) : g.find_end = 0 := by
  exact nat_find_eq_zero_of h

theorem game_find_pre_end_eq_zero_of_all_not_ended {g : Game}
(h : ∀ n, ¬(g.play n).ended) : g.find_pre_end = 0 := by
  apply nat_find_eq_zero_of
  dsimp
  rintro k ⟨h₁, h₂⟩
  rw [←game_play_succ] at h₂
  exact h _ h₂

theorem game_find_pre_end_le_game_find_end {g : Game} :
g.find_pre_end ≤ g.find_end := by
  by_cases h₁ : g.ended
  · simp [game_find_pre_end_eq_zero_of_ended h₁]
  by_cases h₂ : ∃ n, (g.play n).ended
  · obtain ⟨n, h₂⟩ := h₂
    rw [game_find_end_eq_find_pre_end_succ_of h₁ h₂]
    linarith
  simp at h₂
  simp [game_find_pre_end_eq_zero_of_all_not_ended h₂]

theorem game_play_to_state_eq_of_move_ended {g : Game} {n}
(h : g.move.ended) : (g.play n).toState = g.toState := by
  by_cases h₁ : g.ended
  · rw [game_play_eq_of_ended h₁]
  cases n
  · rfl
  nm n
  rw [game_play_succ']
  rw [game_play_eq_of_ended h]
  exact game_move_toState_eq_of_move_ended h

theorem game_play_not_ended_of_le {g : Game} {n m}
(h₁ : ¬(g.play n).ended) (h₂ : m ≤ n) : ¬(g.play m).ended := by
  contrapose! h₁
  exact game_play_ended_of_le h₁ h₂

@[ext]
theorem valid_state_ext {s₁ s₂ : ValidState}
(h : s₁.toState = s₂.toState) : s₁ = s₂ := by
  cases s₁; cases s₂; simp at h ⊢; exact h

@[ext]
theorem a_state_ext {s₁ s₂ : AState}
(h : s₁.toState = s₂.toState) : s₁ = s₂ := by
  cases s₁; cases s₂; simp at h ⊢
  ext : 1; exact h

@[ext]
theorem d_state_ext {s₁ s₂ : DState}
(h : s₁.toState = s₂.toState) : s₁ = s₂ := by
  cases s₁; cases s₂; simp at h ⊢
  ext : 1; exact h

theorem thm_ap_aux₁ {s : State'}
(h : ∃ p ∈ s.grid, p ≠ s.a_pos) : ∃ s₁, DMoves s s₁ := by
  change ∃ s₁, s.d_move s₁
  obtain ⟨p, h₁, h₂⟩ := h
  use {s with grid := s.grid.erase p}
  use p

theorem mk_a_strat_ap_eq_some_of_pos {f s s'}
(h₁ : s.a_move {s.toState' with a_pos := f s})
(h₂ : (mk_a_strat f).ap s = some s') :
s' = {s.toState' with a_pos := f s} := by
  simp [Strat.ap, mk_a_strat, h₁] at h₂
  exact h₂.2.symm

theorem mk_d_strat_ap_eq_some_of_pos {f s s'}
(h₁ : s.d_move {s.toState' with grid := s.grid.erase # f s})
(h₂ : (mk_d_strat f).ap s = some s') :
s' = {s.toState' with grid := s.grid.erase # f s} := by
  simp [Strat.ap, mk_d_strat, h₁] at h₂
  exact h₂.2.symm

theorem mk_a_strat_ap_eq_some_iff_of_pos {f s s'}
(h₁ : s.a_move {s.toState' with a_pos := f s}) :
(mk_a_strat f).ap s = some s' ↔ s' = {s.toState' with a_pos := f s} := by
  dsimp at h₁ ⊢
  use mk_a_strat_ap_eq_some_of_pos h₁
  rintro rfl
  simp [Strat.ap, mk_a_strat, h₁]
  exact ⟨_, h₁⟩

theorem mk_d_strat_ap_eq_some_iff_of_pos {f s s'}
(h₁ : s.d_move {s.toState' with grid := s.grid.erase # f s}) :
(mk_d_strat f).ap s = some s' ↔
s' = {s.toState' with grid := s.grid.erase # f s} := by
  dsimp at h₁ ⊢
  use mk_d_strat_ap_eq_some_of_pos h₁
  rintro rfl
  simp [Strat.ap, mk_d_strat, h₁]
  exact ⟨_, h₁⟩

theorem a_has_move_of_exi_p (p : Point) {s : State'}
(h : s.a_move {s with a_pos := p}) : s.a_has_move := by
  exact ⟨_, h⟩

theorem d_has_move_of_exi_p (p : Point) {s : State'}
(h : s.d_move {s with grid := s.grid.erase p}) : s.d_has_move := by
  exact ⟨_, h⟩

theorem a_has_move_iff_exi_p {s : State} :
s.a_has_move ↔ ∃ p, s.a_move {s.toState' with a_pos := p} := by
  constructor
  · rintro ⟨s', p, rfl, h⟩
    use p, p
  rintro ⟨p, h⟩
  exact a_has_move_of_exi_p p h

theorem d_has_move_iff_exi_p {s : State} :
s.d_has_move ↔ ∃ p, s.d_move {s.toState' with grid := s.grid.erase p} := by
  constructor
  · rintro ⟨s', p, rfl, h⟩
    use p, p
  rintro ⟨p, h⟩
  exact d_has_move_of_exi_p p h