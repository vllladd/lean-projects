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

theorem game_move_a_turn_iff {g : Game}
(h : ¬g.move.ended) : g.move.a_turn ↔ ¬g.a_turn := by
  have h₁ := game_not_ended_of_move_not_ended h
  simp [Game.move, h₁]
  split_ifs <;> split <;> simp_all <;> nm m s h₂ <;> apply h₂
  · exact game_a_has_move_of_a_turn m h
  · exact game_d_has_move_of_d_turn m h

theorem game_play_a_turn_iff {g : Game} {n}
(h : ¬(g.play n).ended) : (g.play n).a_turn ↔ (g.a_turn ↔ Even n) := by
  induction n
  · simp
  nm n ih
  simp at h ⊢
  specialize ih # game_not_ended_of_move_not_ended h
  rw [game_move_a_turn_iff h, ih]
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
  simp [game_play_a_turn_iff h]

theorem game₀_play_d_turn_iff_even {pw a d n}
(h : ¬((game₀ pw a d).play n).ended) :
¬((game₀ pw a d).play n).a_turn ↔ Even n := by
  simp [game_play_a_turn_iff h]

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
  · rw [game_move_state_eq_of_move_ended he]
  · simp [game_move_size_eq_of_not_ended he]

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

theorem game_move_not_ended_of_not_d_turn {g : Game}
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
  exact game_move_not_ended_of_not_d_turn he ht h₁

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
(h : n ≤ m) (he : (g.play n).ended) : (g.play m).ended := by
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
  (if P s then a else b).ap s

theorem Strat.merge_valid {ms} {P : State → Prop} {a b : Strat ms} :
strat_valid ms (a.merge' P b) := by
  intro s
  simp
  split_ifs with h₁
  · rcases a with ⟨⟨ms, f, h⟩, rfl⟩
    apply h
  · rcases b with ⟨⟨ms, f, h⟩, rfl⟩
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
  (mk_strat_const ms s').merge (· = s) a

theorem strat_merge_eq_of_pos {ms} {P : State → Prop} {a b : Strat ms} {s}
(h : P s) : (a.merge P b).ap s = a.ap s := by
  simp [Strat.merge, h]

theorem strat_merge_eq_of_neg {ms} {P : State → Prop} {a b : Strat ms} {s}
(h : ¬P s) : (a.merge P b).ap s = b.ap s := by
  simp [Strat.merge, h]

theorem strat_set_ap_of_eq {ms : Moves} {a : Strat ms} {s s'}
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

def AState.move (sa : AState) (sd : DState) :=
  sa.move' sd ∧ sa.toState = sd.toState.push sa.toState'

def DState.move (sd : DState) (sa : AState) :=
  sd.move' sa ∧ sd.toState = sa.toState.push sd.toState'

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

theorem not_game_move_inj : ¬∀ (g₁ g₂ : Game), g₁.move = g₂.move → g₁ = g₂ := by
  push_neg
  obtain ⟨g, hg⟩ := hv (game₀ 0 default default).move
  use g, g.move
  have he : ¬g.ended :=
    by
      subst hg
      exact game₀_move_not_ended
  have ht : g.a_turn :=
    by
      subst hg
      simp [game_move_a_turn_iff he]
  have h₁ : ¬g.a_has_move :=
    by
      subst g
      apply not_a_has_move_of_pw_0
      simp
  have h₂ : g.move = {g with ended := True} :=
    by
      simp [Game.move, he, ht]
      rw [a_strat_ap_eq_of_not_a_has_move h₁]
  have h₃ : g.move.move = g.move :=
    by
      apply game_move_eq_of_ended
      rw [h₂]
      trivial
  have h₄ : g.move.ended :=
    by
      rw [h₂]
      trivial
  use h₃.symm
  apply ne_of_congr Game.ended
  simp [he, h₄]

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

theorem not_game_move_toState_toState_inj : ¬∀ (g₁ g₂ : Game),
g₁.move.toState = g₂.move.toState → g₁.toState = g₂.toState := by
  push_neg
  obtain ⟨a₂, s₂, sx, h₁⟩ := exi_a_ap_eq_some
  use ⟨s₂.push sx, default, default, default, True⟩
  use ⟨s₂, a₂, default, True, False⟩
  simp [Game.move, h₁]

theorem not_game_move_toState'_toState_inj : ¬∀ (g₁ g₂ : Game),
g₁.move.toState = g₂.move.toState → g₁.toState = g₂.toState := by
  push_neg
  have h := not_game_move_toState_toState_inj
  push_neg at h
  obtain ⟨g₁, g₂, h₁, h₂⟩ := h
  use g₁, g₂

theorem game_move_toState_inj {g₁ g₂ : Game}
(h : g₁.move = g₂.move) : g₁.toState = g₂.toState := by
  rcases g₁ with ⟨s₁, a₁, d₁, ht₁, he₁⟩
  rcases g₂ with ⟨s₂, a₂, d₂, ht₂, he₂⟩
  dsimp; simp [Game.move] at h
  split_ifs at h <;> (try split at h) <;> (try split at h) <;>
    simp at h ⊢ <;> tauto

theorem game_move_a_turn_iff_of_move_ended {g : Game}
(he : g.move.ended) : g.move.a_turn ↔ g.a_turn := by
  simp [Game.move] at he ⊢; split_ifs with h₁ h₂; rfl
  all_goals simp [h₁, h₂] at he; split at he; rfl; simp at he

@[simp]
theorem game₀_a {pw a d} : (game₀ pw a d).a = a := rfl

@[simp]
theorem game₀_d {pw a d} : (game₀ pw a d).d = d := rfl

def nat_find (P : ℕ → Prop) : ℕ :=
  if h : ∃ x, P x then Nat.find h else 0

theorem nat_find_spec {P : ℕ → Prop} (h : ∃ n, P n) :
P (nat_find P) ∧ ∀ k, P k → nat_find P ≤ k := by
  simp [nat_find, h]
  use Nat.find_spec h
  intro k hk
  use k

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
  obtain ⟨h₂, h₃⟩ := nat_find_spec h₁
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

#check 0 #exit

@[simp]
theorem game_move_valid_iff {g : Game} : g.move.valid ↔ g.valid := by
  refine' ⟨λ h => _, game_move_valid_of_valid⟩
  
  by_cases he : g.ended
  · rw [game_move_eq_of_ended he] at h; exact h

  by_cases he₁ : g.move.ended
  ·
  
  -- obtain ⟨pw, a, d, n, h⟩ := h
  -- cases n <;> simp at h; nm n
  -- 
  -- obtain ⟨g₀, hg₀⟩ := hv # game₀ pw a d
  -- obtain ⟨g₁, hg₁⟩ := hv # g₀.play n
  -- rw [←hg₀, ←hg₁] at h
  
#check 0 #exit

@[simp]
theorem game_move_valid_iff {g : Game} : g.move.valid ↔ g.valid := by
  constructor <;> intro h
  · obtain ⟨pw, a, d, n, h⟩ := h
    cases n; simp at h
    nm n
    simp at h
    replace h : g.move.valid :=
      by
        simp [h]

#check 0 #exit

theorem exi_a_state_move_of_a_move {sa : AState} {s : State'}
(h : sa.a_move s) : ∃ sd, s = sd.toState' ∧ sa.move sd := by
  have ⟨g, hg⟩ := hv # sa.to_game (mk_a_strat_const s) default
  refine' ⟨⟨⟨g.move.toState, _⟩, _⟩, _⟩
  · simp [hg]