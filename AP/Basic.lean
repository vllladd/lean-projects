import AP.Point

namespace AP

def State.choose_d_move (s : State) : Point :=
⟨0, (insert s.a_pos s.taken).max.get!.y + 1⟩

@[simp]
theorem choose_d_move_ne_a_pos {s : State} : s.choose_d_move ≠ s.a_pos := by
  unfold State.choose_d_move
  have h₁ := Finset.insert_nonempty s.a_pos s.taken
  obtain ⟨p, hp⟩ := Finset.max_of_nonempty h₁
  rw [hp]
  simp
  intro h
  rw [←h] at hp
  simp at hp
  have h₂ : ⟨0, p.y + 1⟩ ≤ p := by
    have h₂ : WithBot.some ⟨0, p.y + 1⟩ ≤ WithBot.some p :=
      by simp [←hp]
    simp at h₂
    exact h₂
  cases p
  simp at h₂

@[simp]
theorem choose_d_move_not_mem_taken {s : State} : s.choose_d_move ∉ s.taken := by
  unfold State.choose_d_move
  have h₁ := Finset.insert_nonempty s.a_pos s.taken
  obtain ⟨p, hp⟩ := Finset.max_of_nonempty h₁
  rw [hp]
  simp
  intro h
  simp at hp
  rw [max_eq_iff] at hp
  rcases hp with ⟨h₂, h₃⟩ | ⟨h₂, h₃⟩
  · simp at h₂; subst h₂
    rw [Finset.max_le_iff] at h₃
    specialize h₃ _ h
    generalize s.a_pos = p at h₃
    cases p
    simp at h₃
  · replace h₂ := le_of_eq h₂
    rw [Finset.max_le_iff] at h₂
    specialize h₂ _ h
    cases p
    simp at h₂

theorem choose_d_move_valid {s : State} : s.d_valid_move s.choose_d_move := by
  simp [State.d_move]

def State.a_has_move_comp (s : State) : Bool := [] ≠ do
  let ⟨ax, ay⟩ := s.a_pos
  let ds := List.map (Int.ofNat · - s.pw) #
    List.range # s.pw * 2 + 1
  let x ← ds
  let y ← ds
  let p := ⟨ax + x, ay + y⟩
  guard # s.a_valid_move p
  return p

theorem a_has_move_comp_of {s : State}
(h : s.a_has_move) : s.a_has_move_comp := by
  simp [State.a_has_move_comp, State.a_has_move] at h ⊢
  rcases h with ⟨p, h₁, h₂, h₃⟩
  use Int.toNat # s.pw + p.x - s.a_pos.x
  constructor
  rotate_left
  use Int.toNat # s.pw + p.y - s.a_pos.y
  constructor
  all_goals try
    clear h₁ h₂
    cases s; nm pw grid a_pos
    simp [Point.dist] at h₃ ⊢
    clear grid
    rw [←Int.le_iff_lt_add_one]
    rcases h₃ with ⟨h₁, h₂⟩
    rw [Int.add_sub_assoc, mul_two]
    simp
    replace h₁ := le_of_max_le_left h₁
    replace h₂ := le_of_max_le_left h₂
    linarith
  simp
  constructor
  · cases s; nm pw taken a_pos hist turn
    simp [Point.dist] at h₁ h₃ ⊢; clear h₂
    convert h₁ <;> clear h₁ taken <;> rcases h₃ with ⟨h₁, h₂⟩
    · have h₃ : max (pw + p.x - a_pos.x) 0 = pw + p.x - a_pos.x := by
        apply max_eq_left
        replace h₁ := le_of_max_le_right h₁
        linarith
      rw [h₃]
      ring
    · have h₃ : max (pw + p.y - a_pos.y) 0 = pw + p.y - a_pos.y := by
        apply max_eq_left
        replace h₂ := le_of_max_le_right h₂
        linarith
      rw [h₃]
      ring
  constructor
  · cases s; nm pw taken a_pos hist turn
    clear h₁
    simp at h₂ ⊢
    rw [Point.ext_iff]
    simp
    intro h₄
    contrapose! h₂
    simp [Point.dist] at h₃
    rcases h₃ with ⟨h₅, h₆⟩
    replace h₅ : max (pw + p.x - a_pos.x) 0 = pw + p.x - a_pos.x := by
      apply max_eq_left
      replace h₅ := le_of_max_le_right h₅
      linarith
    replace h₆ : max (pw + p.y - a_pos.y) 0 = pw + p.y - a_pos.y := by
      apply max_eq_left
      replace h₆ := le_of_max_le_right h₆
      linarith
    simp only [h₅, h₆] at h₂ h₄; clear h₅ h₆
    clear taken
    ring_nf at h₂ h₄
    ext <;> linarith
  cases s; nm pw grid a_pos hist turn
  simp at h₁ h₂ h₃ ⊢
  rw [Point.dist.comm]
  convert h₃
  · simp [Point.dist] at h₃
    rcases h₃ with ⟨h₃, h₄⟩
    replace h₃ : max (pw + p.x - a_pos.x) 0 = pw + p.x - a_pos.x := by
      apply max_eq_left
      replace h₃ := le_of_max_le_right h₃
      linarith
    rw [h₃]
    linarith
  · simp [Point.dist] at h₃
    rcases h₃ with ⟨h₃, h₄⟩
    replace h₄ : max (pw + p.y - a_pos.y) 0 = pw + p.y - a_pos.y := by
      apply max_eq_left
      replace h₄ := le_of_max_le_right h₄
      linarith
    rw [h₄]
    linarith

theorem a_has_move_of_comp {s : State}
(h : s.a_has_move_comp) : s.a_has_move := by
  simp [State.a_has_move_comp, State.a_has_move] at h ⊢
  rcases h with ⟨x, hx, y, hy, h₁⟩
  rcases h₁ with ⟨h₁, h₂, h₃⟩
  use ⟨s.a_pos.x + (x - s.pw), s.a_pos.y + (y - s.pw)⟩
  use h₁, h₂
  rw [Point.dist.comm]
  exact h₃

theorem a_has_move_iff_comp {s : State} :
s.a_has_move ↔ s.a_has_move_comp :=
  ⟨a_has_move_comp_of, a_has_move_of_comp⟩

instance {s : State} : Decidable s.a_has_move :=
match h : s.a_has_move_comp with
| true => isTrue # by simpa [a_has_move_iff_comp]
| false => isFalse # by simpa [a_has_move_iff_comp]

#check 0 #exit

-- @[simp]
-- theorem game_play_zero {g : Game} : g.play 0 = g := rfl
-- 
-- @[simp]
-- theorem game_play_succ {n} {g : Game} : g.play (n + 1) = (g.play n).move := by
--   apply Function.iterate_succ_apply'
-- 
-- @[simp]
-- theorem a_moves_ap_iff {s s₁} : AMoves s s₁ ↔ s.a_move s₁ := by apply Iff.refl
-- 
-- @[simp]
-- theorem d_moves_ap_iff {s s₁} : DMoves s s₁ ↔ s.d_move s₁ := by apply Iff.refl
-- 
-- theorem strat_ap_eq_none_iff {f : State' → State' → Prop}
-- {st : Strat # λ s => f s} {s} :
-- st.ap s = none ↔ ∀ s₁, ¬f s.toState' s₁ := by
--   rcases st with ⟨⟨ms, f', h₁⟩, h₂⟩; simp at h₁ h₂ ⊢
--   subst h₂; specialize h₁ s; split at h₁
--   · nm m h
--     simp [h]; intro s₁
--     specialize h₁ s₁; simp at h₁; exact h₁
--   · nm m s₂ h; simp [h]; exact ⟨_, h₁⟩
-- 
-- @[simp]
-- def State'.has_move (ms : Moves) (s : State') := ∃ s₁, ms s s₁
-- 
-- def State'.a_has_move (s : State') := s.has_move AMoves
-- def State'.d_has_move (s : State') := s.has_move DMoves
-- 
-- @[simp]
-- theorem a_strat_ap_eq_none_iff {a : AStrat} {s} :
-- a.ap s = none ↔ ¬s.toState'.a_has_move := by
--   simp [State'.a_has_move]; exact strat_ap_eq_none_iff
-- 
-- @[simp]
-- theorem d_strat_ap_eq_none_iff {a : DStrat} {s} :
-- a.ap s = none ↔ ¬s.toState'.d_has_move := by
--   simp [State'.d_has_move]; exact strat_ap_eq_none_iff
-- 
-- theorem of_strat_ap_eq_some {f : State' → State' → Prop}
-- {st : Strat # λ (s : State') => f s} {s : State} {s₁}
-- (h : st.ap s = some s₁) : f s.toState' s₁ := by
--   rcases st with ⟨⟨ms, f', h₂⟩, h₃⟩; simp at h h₃
--   subst h₃; specialize h₂ s; simp [h] at h₂; exact h₂
-- 
-- theorem of_a_ap_eq_some {a : AStrat} {s s₁} :
-- a.ap s = some s₁ → s.toState'.a_move s₁ := of_strat_ap_eq_some
-- 
-- theorem of_d_ap_eq_some {d : DStrat} {s s₁} :
-- d.ap s = some s₁ → s.toState'.d_move s₁ := of_strat_ap_eq_some
-- 
-- theorem of_a_ap_eq_some' {a : AStrat} {s s₁}
-- (h : a.ap s = some s₁) : s.toState'.a_has_move := ⟨s₁, of_a_ap_eq_some h⟩
-- 
-- theorem of_d_ap_eq_some' {d : DStrat} {s s₁}
-- (h : d.ap s = some s₁) : s.toState'.d_has_move := ⟨s₁, of_d_ap_eq_some h⟩
-- 
-- def State'.reachable (s s₁ : State') :=
--   ∃ (g : Game) (n : ℕ), s = g.toState' ∧ s₁ = (g.play n).toState'
-- 
-- def State'.valid s := ∃ pw, (state'₀ pw).reachable s
-- 
-- @[simp]
-- theorem state'₀_a_pos {pw} : (state'₀ pw).a_pos = ⟨0, 0⟩ := rfl
-- 
-- @[simp]
-- theorem state'₀_grid {pw} : (state'₀ pw).grid = Set.univ := rfl
-- 
-- inductive State'.Reachable' (s₀ : State') : State' → Prop where
-- | h₀ : s₀.Reachable' s₀
-- | ha : ∀ (s s₁ : State'), s₀.Reachable' s → s.a_move s₁ → s₀.Reachable' s₁
-- | hd : ∀ (s s₁ : State'), s₀.Reachable' s → s.d_move s₁ → s₀.Reachable' s₁
-- 
-- theorem of_reachable {P : State' → Prop} {s₀ s : State'}
-- (hs : s₀.reachable s) (hp : P s₀)
-- (ha : ∀ (s s₁ : State'), s.a_move s₁ → P s → P s₁)
-- (hd : ∀ (s s₁ : State'), s.d_move s₁ → P s → P s₁) : P s := by
--   rcases hs with ⟨g₀, n, rfl, rfl⟩; induction n; simpa; nm n ih
--   simp; generalize g₀.play n = g at ih ⊢; simp [Game.move]
--   split_ifs with h₁ h₂; exact ih
--   · split; exact ih; nm m s₂ h; exact ha _ _ (of_strat_ap_eq_some h) ih
--   · split; exact ih; nm m s₂ h; exact hd _ _ (of_strat_ap_eq_some h) ih
-- 
-- theorem Reachable'_of_reachable {s₀ s : State'}
-- (h : s₀.reachable s) : s₀.Reachable' s := by
--   apply of_reachable h <;> clear h s; constructor
--   · intro s s₁ h₁ h₂; apply State'.Reachable'.ha <;> assumption
--   · intro s s₁ h₁ h₂; apply State'.Reachable'.hd <;> assumption
-- 
-- theorem pw_eq_of_Reachable' {s₀ s : State'} (h : s₀.Reachable' s) :
-- s.pw = s₀.pw := by
--   induction h; rfl
--   nm s₁ s₂ h₁ h₂ h₃; rw [←h₃]; rcases h₂ with ⟨a₁, rfl, _⟩; rfl
--   nm s₁ s₂ h₁ h₂ h₃; rw [←h₃]; rcases h₂ with ⟨a₁, rfl, _⟩; rfl
-- 
-- @[simp]
-- theorem reachable_refl {s : State'} : s.reachable s := by
--   use {Game.dflt with toState := ⟨s, []⟩}, 0; simp
-- 
-- @[simp]
-- theorem Reachable'_refl {s : State'} : s.Reachable' s := by constructor
-- 
-- theorem exi_Reachable'_of_valid {s : State'} (h : s.valid) :
-- ∃ pw, (state'₀ pw).Reachable' s := by
--   rcases h with ⟨pw, h⟩; replace h := Reachable'_of_reachable h
--   use pw, h
-- 
-- theorem Reachable'_of_valid {s : State'} (h : s.valid) :
-- (state'₀ s.pw).Reachable' s := by
--   rcases h with ⟨pw, h⟩; replace h := Reachable'_of_reachable h
--   convert h; apply pw_eq_of_Reachable' h
-- 
-- def point_equiv_prod : Point ≃ ℤ × ℤ := by
--   use λ ⟨x, y⟩ => ⟨x, y⟩
--   use λ ⟨x, y⟩ => ⟨x, y⟩
--   all_goals rintro ⟨x₁, y₁⟩; simp
-- 
-- instance : Infinite Point := by
--   rw [Equiv.infinite_iff point_equiv_prod]
--   infer_instance
-- 
-- theorem grid_always_inf {s : State'} (h : s.valid) : s.grid.Infinite := by
--   obtain ⟨pw, h₁⟩ := exi_Reachable'_of_valid h; clear h
--   induction h₁; apply Set.infinite_univ
--   nm s₁ s₂ h₁ h₂ h₃; rcases h₂ with ⟨_, rfl, _⟩; simpa
--   nm s₁ s₂ h₁ h₂ h₃; rcases h₂ with ⟨_, rfl, _⟩; simpa
-- 
-- theorem grid_always_nonempty {s : State'} (h : s.valid) :
-- s.grid.Nonempty := Set.Infinite.nonempty # grid_always_inf h
-- 
-- theorem d_always_has_move {s : State'} (h : s.valid) :
-- ∃ s₁, s.d_move s₁ := by
--   obtain h₁ := grid_always_inf h
--   obtain ⟨p, h₂, h₃⟩ : ∃ p, p ∈ s.grid ∧ p ≠ s.a_pos := by
--     obtain ⟨grid', h₂⟩ := hv # s.grid.erase s.a_pos
--     have h₃ : grid'.Infinite := by simpa [h₂]
--     obtain ⟨p, hp⟩ := h₃.nonempty
--     use p; simp [h₂] at hp; simp [hp]
--   use {s with grid := s.grid.erase p}, p
-- 
-- def Game.valid (g : Game) :=
--   ∃ pw a d n, g = (game₀ pw a d).play n
-- 
-- def State.valid (s : State) :=
--   ∃ (g : Game), g.valid ∧ s = g.toState
-- 
-- theorem state_valid_of_game_valid {g : Game} (h : g.valid) :
-- g.toState.valid := by use g
-- 
-- @[simp]
-- theorem state'₀_pw {pw} : (state'₀ pw).pw = pw := rfl
-- 
-- @[simp]
-- theorem state₀_pw {pw} : (state₀ pw).pw = pw := rfl
-- 
-- @[simp]
-- theorem game₀_pw {pw a d} : (game₀ pw a d).pw = pw := rfl
-- 
-- @[simp]
-- theorem game_mk_pw {a d s p₁ p₂} :
-- ({a := a, d := d, toState := s , a_turn := p₁
-- , ended := p₂} : Game).pw = s.pw := rfl
-- 
-- @[simp]
-- theorem state_push_pw {s : State} {s'} : (s.push s').pw = s'.pw := rfl
-- 
-- @[simp]
-- theorem game_move_pw_eq {g : Game} : g.move.pw = g.pw := by
--   simp [Game.move]; split_ifs with h₁ h₂; rfl
--   · split; rfl; next m s h₃ =>
--     obtain ⟨a₁, rfl, _⟩ := of_a_ap_eq_some h₃; rfl
--   · split; rfl; next m s h₃ =>
--     obtain ⟨a₁, rfl, _⟩ := of_d_ap_eq_some h₃; rfl
-- 
-- theorem invariant_play_of_invariant_move {α : Type} (f : Game → α)
-- {g n} (h₁ : ∀ g, f g.move = f g) : f (g.play n) = f g := by
--   induction n; rfl; simpa [h₁]
-- 
-- @[simp]
-- theorem game_play_pw_eq {g : Game} {n} : (g.play n).pw = g.pw := by
--   apply invariant_play_of_invariant_move λ g => g.pw; simp
-- 
-- @[simp]
-- theorem game_state_pw_play_eq {g : Game} {n} : (g.play n).toState.pw = g.pw :=
--   game_play_pw_eq
-- 
-- theorem state'_valid_of_state_valid {s : State} (h : s.valid) :
-- s.toState'.valid := by
--   obtain ⟨g, ⟨pw, a, d, n, hg⟩, hs⟩ := h
--   use s.pw, game₀ pw a d, n; simp [hs, hg]; rfl
-- 
-- theorem state'_valid_of_game_valid {g : Game} (h : g.valid) :
-- g.toState'.valid := state'_valid_of_state_valid # state_valid_of_game_valid h
-- 
-- theorem d_always_has_move_ex {g : Game} (h : g.valid) :
-- g.d.ap g.toState ≠ none := by
--   simp; exact d_always_has_move # state'_valid_of_game_valid h
-- 
-- theorem d_always_has_move' {g : Game} (h : g.valid) : g.toState'.d_has_move := by
--   have h₁ := d_always_has_move_ex h; simp at h₁; exact h₁
--   
-- @[simp]
-- theorem game₀_state {pw a d} : (game₀ pw a d).toState = state₀ pw := rfl
-- 
-- @[simp]
-- theorem state₀_hist {pw} : (state₀ pw).hist = [] := rfl
-- 
-- @[simp]
-- theorem game_move_valid_of_valid {g : Game} (h : g.valid) : g.move.valid := by
--   obtain ⟨pw, a, d, n, rfl⟩ := h; use pw, a, d, n + 1; simp
-- 
-- @[simp]
-- theorem game₀_valid {pw a d} : (game₀ pw a d).valid := by
--   use pw, a, d, 0; rfl
-- 
-- @[simp]
-- theorem game₀_move_valid {pw a d} : (game₀ pw a d).move.valid := by
--   use pw, a, d, 1; rfl
-- 
-- @[simp]
-- theorem game₀_play_valid {pw a d n} : ((game₀ pw a d).play n).valid := by
--   use pw, a, d, n
-- 
-- theorem of_game_valid {p : Game → Prop} {g : Game} (h₁ : g.valid)
-- (h₂ : ∀ pw a d, p (game₀ pw a d))
-- (h₃ : ∀ g, g.valid → p g → p g.move) : p g := by
--   obtain ⟨pw, a, d, n, rfl⟩ := h₁; induction n; apply h₂
--   simp; apply h₃; simp; assumption
-- 
-- theorem no_move_of_ended {g : Game} (h₁ : g.valid) (h₂ : g.ended) :
-- g.f g.toState = none := by
--   revert h₂; apply of_game_valid h₁; simp [game₀]
--   intro g h₂ h₃ h₄; simp [Game.move] at h₄; split_ifs at h₄ with h₅ h₆
--   · simp [Game.move, h₄]; specialize h₃ h₄
--     split_ifs with h₅ <;> simp [Game.f, h₅] at h₃ ⊢ <;> assumption
--   · split at h₄; nm m h₇; simp [Game.move, h₅, h₆, h₇]; contradiction
--   · split at h₄
--     · nm m h₇; have h₈ := d_always_has_move' h₂
--       simp at h₇; contradiction
--     · nm m s h; contradiction
-- 
-- theorem game_a_turn_of_valid_and_ended {g : Game}
-- (h₁ : g.valid) (h₂ : g.ended) : g.a_turn := by
--   have h₃ := no_move_of_ended h₁ h₂; by_contra h₄; simp [Game.f, h₄] at h₃
--   have h₅ := d_always_has_move' h₁; contradiction
-- 
-- def State.size (s : State) := s.hist.length
-- 
-- structure ValidState extends State where
--   h_valid : toState.valid
-- 
-- structure AState extends ValidState where
--   h_size : Odd toState.size
-- 
-- structure DState extends ValidState where
--   h_size : Even toState.size
-- 
-- theorem a_state_ne_d_state {sa : AState} {sd : DState} :
-- sa.toState ≠ sd.toState := by
--   apply ne_of_congr # λ s => Odd s.size; simp [sa.h_size, sd.h_size]
-- 
-- theorem a_state_or_d_state {s : ValidState} :
-- (∃ (sa : AState), sa.toState = s.toState) ∨
-- (∃ (sd : DState), sd.toState = s.toState) := by
--   by_cases h : Odd s.size
--   · left; exact ⟨⟨s, h⟩, rfl⟩
--   · right; refine' ⟨⟨s, _⟩, rfl⟩; simp at h; exact h
-- 
-- @[simp]
-- def State.to_game (s : State) (a_turn : Prop) (a : AStrat) (d : DStrat) : Game :=
--   { a := a
--   , d := d
--   , toState := s
--   , a_turn := a_turn
--   , ended := False
--   }
-- 
-- def AState.to_game (sa : AState) := sa.toState.to_game True
-- def DState.to_game (sd : DState) := sd.toState.to_game False
-- 
-- def AState.move' (sa : AState) (sd : DState) :=
--   sa.toState'.a_move sd.toState'
-- 
-- def DState.move' (sd : DState) (sa : AState) :=
--   sd.toState'.d_move sa.toState'
-- 
-- def AState.move (sa : AState) (sd : DState) :=
--   sa.move' sd ∧ sd.toState = sa.toState.push sd.toState'
-- 
-- def DState.move (sd : DState) (sa : AState) :=
--   sd.move' sa ∧ sa.toState = sd.toState.push sa.toState'
-- 
-- @[simp] def AState.has_move' (sa : AState) := sa.toState'.a_has_move
-- @[simp] def DState.has_move' (sd : DState) := sd.toState'.d_has_move
-- 
-- def losing' (set : Set AState) : Set AState :=
--   {sa | ∀ sd, sa.move' sd → ∃ sa₂, sd.move' sa₂ ∧ sa₂ ∈ set}
-- 
-- def AState.losing (sa : AState) :=
--   ∃ n, sa ∈ losing'^[n] {sa | ¬sa.has_move'}
-- 
-- def AState.winning (sa : AState) := ¬sa.losing
-- 
-- @[simp]
-- theorem not_a_winning_iff {sa : AState} : ¬sa.winning ↔ sa.losing := by
--   simp [AState.winning]
-- 
-- @[simp]
-- theorem not_a_losing_iff {sa : AState} : ¬sa.losing ↔ sa.winning := by
--   simp [AState.winning]
-- 
-- theorem a_losing_ind {p : AState → Prop} {sa : AState} (h : sa.losing)
-- (h₁ : ∀ sa, ¬sa.has_move' → p sa)
-- (h₂ : ∀ sa, (∀ sd, sa.move' sd → ∃ sa₂, sd.move' sa₂ ∧ p sa₂) → p sa) :
-- p sa := by
--   obtain ⟨n, h⟩ := h; induction n generalizing sa
--   · simp at h; apply h₁; apply h
--   nm n ih; apply h₂; intro s₁ hs₁
--   rw [Function.iterate_succ'] at h; simp [losing'] at h
--   specialize h _ hs₁; obtain ⟨sa₂, h₁, h₂⟩ := h; use sa₂, h₁, ih h₂
-- 
-- theorem of_a_losing {sa : AState} (h : sa.losing) :
-- ∀ sd, sa.move' sd → ∃ sa₂, sd.move' sa₂ ∧ sa₂.losing := by
--   obtain ⟨n, h⟩ := h; cases n
--   · simp at h; intro sd hsd; contrapose! h; use sd.toState'; exact hsd
--   nm n; rw [Function.iterate_succ'] at h; dsimp at h
--   rw [losing'] at h; simp at h; intro sd hsd
--   obtain ⟨sa₂, h₁, h₂⟩ := h _ hsd; use sa₂, h₁, n, h₂
-- 
-- theorem a_winning_of {sa : AState}
-- (h : ∃ sd, sa.move' sd ∧ ∀ sa₂, sd.move' sa₂ → sa₂.winning) : sa.winning := by
--   contrapose! h; simp only [not_a_winning_iff] at h ⊢; exact of_a_losing h