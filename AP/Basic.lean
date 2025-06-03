import AP.Defs

noncomputable section
open scoped Classical

@[ext]
theorem point_ext {a b : Point} (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  cases a; cases b; simp_all

@[simp]
theorem point_mk_eq_iff {x₁ y₁ x₂ y₂} :
@Eq Point (x₁, y₁) (x₂, y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  unfold Point; simp

@[simp]
theorem game_play_zero {g : Game} : g.play 0 = g := rfl

@[simp]
theorem game_play_succ {n} {g : Game} : g.play (n + 1) = (g.play n).move := by
  apply Function.iterate_succ_apply'

@[simp]
theorem a_moves_eq_emp_iff {s} : AMoves s = ∅ ↔ ∀ s₁, ¬s.a_move s₁ := by
  simp [AMoves, Set.eq_empty_iff_forall_notMem]

@[simp]
theorem d_moves_eq_emp_iff {s} : DMoves s = ∅ ↔ ∀ s₁, ¬s.d_move s₁ := by
  simp [DMoves, Set.eq_empty_iff_forall_notMem]

@[simp]
theorem mem_a_moves {s s₁} : s₁ ∈ AMoves s ↔ s.a_move s₁ := by apply Iff.refl

@[simp]
theorem mem_d_moves {s s₁} : s₁ ∈ DMoves s ↔ s.d_move s₁ := by apply Iff.refl

theorem strat_ap_eq_none_iff {f : State' → State' → Prop}
{st : StratT # λ s => setOf # f s} {s} :
st.1.f s = none ↔ ∀ s₁, ¬f s.toState' s₁ := by
  rcases st with ⟨⟨ms, f', h₁⟩, h₂⟩; simp at h₁ h₂ ⊢
  subst h₂; specialize h₁ s; split at h₁
  case _ m h =>
    simp [h]; intro s₁; rw [Set.ext_iff] at h₁
    specialize h₁ s₁; simp at h₁; exact h₁
  case _ m s₂ h => simp [h]; exact ⟨_, h₁⟩

def State'.a_has_move (s : State') := ∃ s₁, s.a_move s₁
def State'.d_has_move (s : State') := ∃ s₁, s.d_move s₁

@[simp]
theorem a_strat_ap_eq_none_iff {a : AStrat} {s} :
a.1.f s = none ↔ ¬s.toState'.a_has_move := by
  simp [State'.a_has_move]; exact strat_ap_eq_none_iff

@[simp]
theorem d_strat_ap_eq_none_iff {a : DStrat} {s} :
a.1.f s = none ↔ ¬s.toState'.d_has_move := by
  simp [State'.d_has_move]; exact strat_ap_eq_none_iff

theorem of_strat_ap_eq_some {f : State' → State' → Prop}
{st : StratT # λ (s : State') => setOf # f s} {s : State} {s₁}
(h : st.1.f s = some s₁) : f s.toState' s₁ := by
  rcases st with ⟨⟨ms, f', h₂⟩, h₃⟩; simp at h h₃
  subst h₃; specialize h₂ s; simp [h] at h₂; exact h₂

theorem of_a_ap_eq_some {a : AStrat} {s s₁} :
a.1.f s = some s₁ → s.toState'.a_move s₁ := of_strat_ap_eq_some

theorem of_d_ap_eq_some {d : DStrat} {s s₁} :
d.1.f s = some s₁ → s.toState'.d_move s₁ := of_strat_ap_eq_some

theorem of_a_ap_eq_some' {a : AStrat} {s s₁}
(h : a.1.f s = some s₁) : s.toState'.a_has_move := ⟨s₁, of_a_ap_eq_some h⟩

theorem of_d_ap_eq_some' {d : DStrat} {s s₁}
(h : d.1.f s = some s₁) : s.toState'.d_has_move := ⟨s₁, of_d_ap_eq_some h⟩

def State'.reachable (s s₁ : State') :=
  ∃ (g : Game) (n : ℕ), s = g.toState' ∧ s₁ = (g.play n).toState'

def State'.valid s := ∃ pw, (state'₀ pw).reachable s

@[simp]
theorem state'₀_a_pos {pw} : (state'₀ pw).a_pos = (0, 0) := rfl

@[simp]
theorem state'₀_grid {pw} : (state'₀ pw).grid = Set.univ := rfl

inductive State'.Reachable' (s₀ : State') : State' → Prop where
| h₀ : s₀.Reachable' s₀
| ha : ∀ (s s₁ : State'), s₀.Reachable' s → s.a_move s₁ → s₀.Reachable' s₁
| hd : ∀ (s s₁ : State'), s₀.Reachable' s → s.d_move s₁ → s₀.Reachable' s₁

theorem of_reachable {P : State' → Prop} {s₀ s : State'}
(hs : s₀.reachable s) (hp : P s₀)
(ha : ∀ (s s₁ : State'), s.a_move s₁ → P s → P s₁)
(hd : ∀ (s s₁ : State'), s.d_move s₁ → P s → P s₁) : P s := by
  rcases hs with ⟨g₀, n, rfl, rfl⟩; induction n; simpa; nm n ih
  simp; generalize g₀.play n = g at ih ⊢; simp [Game.move]
  split_ifs with h₁ h₂; exact ih
  · split; exact ih; nm m s₂ h; exact ha _ _ (of_strat_ap_eq_some h) ih
  · split; exact ih; nm m s₂ h; exact hd _ _ (of_strat_ap_eq_some h) ih

theorem Reachable'_of_reachable {s₀ s : State'}
(h : s₀.reachable s) : s₀.Reachable' s := by
  apply of_reachable h <;> clear h s; constructor
  · intro s s₁ h₁ h₂; apply State'.Reachable'.ha <;> assumption
  · intro s s₁ h₁ h₂; apply State'.Reachable'.hd <;> assumption

theorem pw_eq_of_Reachable' {s₀ s : State'} (h : s₀.Reachable' s) :
s.pw = s₀.pw := by
  induction h; rfl
  nm s₁ s₂ h₁ h₂ h₃; rw [←h₃]; rcases h₂ with ⟨a₁, rfl, _⟩; rfl
  nm s₁ s₂ h₁ h₂ h₃; rw [←h₃]; rcases h₂ with ⟨a₁, rfl, _⟩; rfl

@[simp]
theorem reachable_refl {s : State'} : s.reachable s := by
  use {Game.dflt with toState := ⟨s, []⟩}, 0; simp

@[simp]
theorem Reachable'_refl {s : State'} : s.Reachable' s := by constructor

-- theorem reachable_of_Reachable' {s₀ s : State'}
-- (h : s₀.Reachable' s) : s₀.reachable s := by
--   induction h
--   · simp
--   · nm s₁ s₂ h₁ h₂ h₃

-- #check 0 #exit

theorem exi_Reachable'_of_valid {s : State'} (h : s.valid) :
∃ pw, (state'₀ pw).Reachable' s := by
  rcases h with ⟨pw, h⟩; replace h := Reachable'_of_reachable h
  use pw, h

theorem Reachable'_of_valid {s : State'} (h : s.valid) :
(state'₀ s.pw).Reachable' s := by
  rcases h with ⟨pw, h⟩; replace h := Reachable'_of_reachable h
  convert h; apply pw_eq_of_Reachable' h

def point_equiv_prod : Point ≃ Prod ℤ ℤ := by apply Equiv.refl

instance : Infinite Point := by unfold Point; infer_instance

theorem grid_always_inf {s : State'} (h : s.valid) : s.grid.Infinite := by
  obtain ⟨pw, h₁⟩ := exi_Reachable'_of_valid h; clear h
  induction h₁; apply Set.infinite_univ
  nm s₁ s₂ h₁ h₂ h₃; rcases h₂ with ⟨_, rfl, _⟩; simpa
  nm s₁ s₂ h₁ h₂ h₃; rcases h₂ with ⟨_, rfl, _⟩; simpa

theorem grid_always_nonempty {s : State'} (h : s.valid) :
s.grid.Nonempty := Set.Infinite.nonempty # grid_always_inf h

theorem d_always_has_move {s : State'} (h : s.valid) :
∃ s₁, s.d_move s₁ := by
  obtain h₁ := grid_always_inf h
  obtain ⟨p, h₂, h₃⟩ : ∃ p, p ∈ s.grid ∧ p ≠ s.a_pos := by
    obtain ⟨grid', h₂⟩ := hv # s.grid.erase s.a_pos
    have h₃ : grid'.Infinite := by simpa [h₂]
    obtain ⟨p, hp⟩ := h₃.nonempty
    use p; simp [h₂] at hp; simp [hp]
  use {s with grid := s.grid.erase p}, p

def Game.valid (g : Game) :=
  ∃ pw a d n, g = (game₀ pw a d).play n

def State.valid (s : State) :=
  ∃ (g : Game), g.valid ∧ s = g.toState

theorem state_valid_of_game_valid {g : Game} (h : g.valid) :
g.toState.valid := by use g

@[simp]
theorem state'₀_pw {pw} : (state'₀ pw).pw = pw := rfl

@[simp]
theorem state₀_pw {pw} : (state₀ pw).pw = pw := rfl

@[simp]
theorem game₀_pw {pw a d} : (game₀ pw a d).pw = pw := rfl

@[simp]
theorem game_mk_pw {a d s p₁ p₂} :
({a := a, d := d, toState := s , a_turn := p₁
, ended := p₂} : Game).pw = s.pw := rfl

@[simp]
theorem state_push_pw {s : State} {s'} : (s.push s').pw = s'.pw := rfl

@[simp]
theorem game_move_pw_eq {g : Game} : g.move.pw = g.pw := by
  simp [Game.move]; split_ifs with h₁ h₂; rfl
  · split; rfl; next m s h₃ =>
    obtain ⟨a₁, rfl, _⟩ := of_a_ap_eq_some h₃; rfl
  · split; rfl; next m s h₃ =>
    obtain ⟨a₁, rfl, _⟩ := of_d_ap_eq_some h₃; rfl

theorem invariant_play_of_invariant_move {α : Type} (f : Game → α)
{g n} (h₁ : ∀ g, f g.move = f g) : f (g.play n) = f g := by
  induction n; rfl; simpa [h₁]

@[simp]
theorem game_play_pw_eq {g : Game} {n} : (g.play n).pw = g.pw := by
  apply invariant_play_of_invariant_move λ g => g.pw; simp

@[simp]
theorem game_state_pw_play_eq {g : Game} {n} : (g.play n).toState.pw = g.pw :=
  game_play_pw_eq

theorem state'_valid_of_state_valid {s : State} (h : s.valid) :
s.toState'.valid := by
  obtain ⟨g, ⟨pw, a, d, n, hg⟩, hs⟩ := h
  use s.pw, game₀ pw a d, n; simp [hs, hg]; rfl

theorem state'_valid_of_game_valid {g : Game} (h : g.valid) :
g.toState'.valid := state'_valid_of_state_valid # state_valid_of_game_valid h

theorem d_always_has_move_ex {g : Game} (h : g.valid) :
g.d.1.f g.toState ≠ none := by
  simp; exact d_always_has_move # state'_valid_of_game_valid h

theorem d_always_has_move' {g : Game} (h : g.valid) : g.toState'.d_has_move := by
  have h₁ := d_always_has_move_ex h; simp at h₁; exact h₁
  
@[simp]
theorem game₀_state {pw a d} : (game₀ pw a d).toState = state₀ pw := rfl

@[simp]
theorem state₀_hist {pw} : (state₀ pw).hist = [] := rfl

@[simp]
theorem game_valid_move_of_valid {g : Game} (h : g.valid) : g.move.valid := by
  obtain ⟨pw, a, d, n, rfl⟩ := h; use pw, a, d, n + 1; simp

@[simp]
theorem game₀_valid {pw a d} : (game₀ pw a d).valid := by
  use pw, a, d, 0; rfl

@[simp]
theorem game₀_move_valid {pw a d} : (game₀ pw a d).move.valid := by
  use pw, a, d, 1; rfl

@[simp]
theorem game₀_play_valid {pw a d n} : ((game₀ pw a d).play n).valid := by
  use pw, a, d, n

theorem of_game_valid {p : Game → Prop} {g : Game} (h₁ : g.valid)
(h₂ : ∀ pw a d, p (game₀ pw a d))
(h₃ : ∀ g, g.valid → p g → p g.move) : p g := by
  obtain ⟨pw, a, d, n, rfl⟩ := h₁; induction n; apply h₂
  simp; apply h₃; simp; assumption

theorem no_move_of_ended {g : Game} (h₁ : g.valid) (h₂ : g.ended) :
g.f g.toState = none := by
  revert h₂; apply of_game_valid h₁; simp [game₀]
  intro g h₂ h₃ h₄; simp [Game.move] at h₄; split_ifs at h₄ with h₅ h₆
  · simp [Game.move, h₄]; specialize h₃ h₄
    split_ifs with h₅ <;> simp [Game.f, h₅] at h₃ ⊢ <;> assumption
  · split at h₄; nm m h₇; simp [Game.move, h₅, h₆, h₇]; contradiction
  · split at h₄
    · nm m h₇; have h₈ := d_always_has_move' h₂
      simp at h₇; contradiction
    · nm m s h; contradiction

theorem a_turn_of_ended {g : Game} (h₁ : g.valid) (h₂ : g.ended) : g.a_turn := by
  have h₃ := no_move_of_ended h₁ h₂; by_contra h₄; simp [Game.f, h₄] at h₃
  have h₅ := d_always_has_move' h₁; contradiction

def State.size (s : State) := s.hist.length

structure ValidState extends State where
  h_valid : toState.valid

structure AState extends ValidState where
  h_size : Odd toState.size

structure DState extends ValidState where
  h_size : Even toState.size

theorem a_state_ne_d_state {sa : AState} {sd : DState} :
sa.toState ≠ sd.toState := by
  apply ne_of_congr # λ s => Odd s.size; simp [sa.h_size, sd.h_size]

theorem a_state_or_d_state {s : ValidState} :
(∃ (sa : AState), sa.toState = s.toState) ∨
(∃ (sd : DState), sd.toState = s.toState) := by
  by_cases h : Odd s.size
  · left; exact ⟨⟨s, h⟩, rfl⟩
  · right; refine' ⟨⟨s, _⟩, rfl⟩; simp at h; exact h

def AState.to_game (sa : AState) (a : AStrat) (d : DStrat) : Game :=
  { a := a
  , d := d
  , toState := sa.toState
  , a_turn := True
  , ended := False
  }

abbrev AState.move (sa : AState) (sd : DState) := sa.toState'.a_move sd.toState'
abbrev DState.move (sd : DState) (sa : AState) := sd.toState'.d_move sa.toState'

abbrev AState.has_move (sa : AState) := sa.toState'.a_has_move
abbrev DState.has_move (sd : DState) := sd.toState'.d_has_move

def losing' (set : Set AState) : Set AState :=
  {sa | ∀ sd, sa.move sd → ∃ sa₂, sd.move sa₂ ∧ sa₂ ∈ set}

def AState.losing (sa : AState) :=
  ∃ n, sa ∈ losing'^[n] {sa | ¬sa.has_move}

def AState.winning (sa : AState) := ¬sa.losing

@[simp]
theorem not_a_winning_iff {sa : AState} : ¬sa.winning ↔ sa.losing := by
  simp [AState.winning]

@[simp]
theorem not_a_losing_iff {sa : AState} : ¬sa.losing ↔ sa.winning := by
  simp [AState.winning]

theorem a_losing_ind {p : AState → Prop} {sa : AState} (h : sa.losing)
(h₁ : ∀ sa, ¬sa.has_move → p sa)
(h₂ : ∀ sa, (∀ sd, sa.move sd → ∃ sa₂, sd.move sa₂ ∧ p sa₂) → p sa) :
p sa := by
  obtain ⟨n, h⟩ := h; induction n generalizing sa
  · simp at h; apply h₁; apply h
  nm n ih; apply h₂; intro s₁ hs₁
  rw [Function.iterate_succ'] at h; simp [losing'] at h
  specialize h _ hs₁; obtain ⟨sa₂, h₁, h₂⟩ := h; use sa₂, h₁, ih h₂

theorem of_a_losing {sa : AState} (h : sa.losing) :
∀ sd, sa.move sd → ∃ sa₂, sd.move sa₂ ∧ sa₂.losing := by
  obtain ⟨n, h⟩ := h; cases n
  · simp at h; intro sd hsd; contrapose! h; use sd.toState'
  nm n; rw [Function.iterate_succ'] at h; dsimp at h
  rw [losing'] at h; simp at h; intro sd hsd
  obtain ⟨sa₂, h₁, h₂⟩ := h _ hsd; use sa₂, h₁, n

theorem a_winning_of {sa : AState}
(h : ∃ sd, sa.move sd ∧ ∀ sa₂, sd.move sa₂ → sa₂.winning) : sa.winning := by
  contrapose! h; simp only [not_a_winning_iff] at h ⊢; exact of_a_losing h