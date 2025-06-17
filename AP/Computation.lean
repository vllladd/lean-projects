import AP.Strategy

structure CompState where
  pw : ℕ
  grid : Ordset Point
  a_pos : Point

structure CompGame where
  fa : List CompState → CompState → Point
  fd : List CompState → CompState → Point
  hist : List CompState
  s : CompState
  a_turn : Bool
  ended : Bool

def CompState.check_a_move (s : CompState) (p : Point) : Bool :=
  decide # p ∉ s.grid ∧ p ≠ s.a_pos ∧ s.a_pos.dist p ≤ s.pw

def CompState.check_d_move (s : CompState) (p : Point) : Bool :=
  decide # p ∉ s.grid ∧ p ≠ s.a_pos

def CompState.a_has_move (s : CompState) : Bool := [] ≠ do
  let ⟨ax, ay⟩ := s.a_pos
  let ds := List.map (Int.ofNat · - s.pw) #
    List.range # s.pw * 2 + 1
  let x ← ds
  let y ← ds
  let p := ⟨ax + x, ay + y⟩
  guard # s.check_a_move p
  return p

def CompGame.push (g : CompGame) (s : CompState) : CompGame :=
  {g with hist := g.s :: g.hist, s := s, a_turn := ¬g.a_turn}

def CompGame.move (g : CompGame) : Option CompGame :=
  if g.ended then pure g else do
  if g.a_turn then do
    let p := g.fa g.hist g.s
    if g.s.check_a_move p then
      return g.push {g.s with a_pos := p}
    else do
      guard # ¬g.s.a_has_move
      return {g with ended := true}
  else do
    let p := g.fd g.hist g.s
    guard # g.s.check_d_move p
    return g.push {g.s with grid := insert p g.s.grid}

def CompGame.play (g : CompGame) : ℕ → Option CompGame
| 0 => pure g
| n + 1 => do
  let g ← g.move
  g.play n

def CompState.to_state' (s : CompState) : State' :=
  { pw := s.pw
  , grid := setOf (· ∉ s.grid)
  , a_pos := s.a_pos
  }

def comp_hist_to_hist (hist : List CompState) : List State' :=
  (hist.map (·.to_state')).reverse

def CompGame.to_state (g : CompGame) : State :=
  { toState' := g.s.to_state'
  , hist := comp_hist_to_hist g.hist
  }

def Game.congr_comp (g : Game) (cg : CompGame) :=
  g.toState = cg.to_state ∧
  g.a_turn = cg.a_turn ∧
  g.ended = cg.ended

def Game.congr_mcomp (g : Game) (mcg : Option CompGame) :=
  ∀ cg, mcg = some cg → g.congr_comp cg

@[simp]
theorem game_congr_mcomp_none {g : Game} : g.congr_mcomp none := by
  simp [Game.congr_mcomp]

@[simp]
theorem game_congr_mcomp_some {g : Game} {cg} :
g.congr_mcomp (some cg) ↔ g.congr_comp cg := by
  simp [Game.congr_mcomp]

class GameToComp (g : Game) where
  mcg : Option CompGame
  h : g.congr_mcomp mcg

def strat_fn_to_comp (f : State → Point) : List CompState -> CompState -> Point :=
  λ h s => f ⟨s.to_state', comp_hist_to_hist h⟩

instance {pw fa fd} : GameToComp # game₀ pw (mk_a_strat fa) (mk_d_strat fd) := by
  use pure #
    { fa := strat_fn_to_comp fa
    , fd := strat_fn_to_comp fd
    , hist := []
    , s := {pw := pw, grid := ∅, a_pos := point₀}
    , a_turn := false
    , ended := false
    }
  simp [CompGame.to_state, CompState.to_state', Game.congr_comp]
  apply state_ext <;> rfl

@[simp]
theorem comp_game_play_0 {cg : CompGame} : cg.play 0 = some cg := rfl

theorem comp_game_play_succ' {cg : CompGame} {n} :
cg.play (n + 1) = (cg.move >>= (·.play n)) := rfl

@[simp]
theorem comp_game_play_succ {cg : CompGame} {n} :
cg.play (n + 1) = (cg.play n >>= (·.move)) := by
  induction n generalizing cg
  · simp [comp_game_play_succ']
  nm n ih
  generalize h₁ : cg.move = cg₁
  cases cg₁
  · simp [comp_game_play_succ', h₁]
  nm cg₁
  specialize @ih cg₁
  simp [comp_game_play_succ', h₁]
  exact ih

@[simp]
theorem comp_state_to_state'_pw {s : CompState} :
s.to_state'.pw = s.pw := rfl

@[simp]
theorem comp_state_to_state'_a_pos {s : CompState} :
s.to_state'.a_pos = s.a_pos := rfl

@[simp]
theorem unit_mem_guard_list_iff {P : Prop} [Decidable P] :
() ∈ (guard P : List Unit) ↔ P := by
  by_cases h : P <;> simp [h]
  simp [List.instAlternative]

@[simp]
theorem mem_compt_state_to_state'_grid_iff {s : CompState} {p} :
p ∈ s.to_state'.grid ↔ ¬p ∈ s.grid := by rfl

theorem of_comp_state_to_state'_a_has_move {s : CompState}
(h : s.to_state'.a_has_move) : s.a_has_move := by
  simp [CompState.a_has_move, a_has_move_iff] at h ⊢
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
  simp [CompState.check_a_move]
  constructor
  · cases s; nm pw grid a_pos
    simp [Point.dist] at h₁ h₃ ⊢; clear h₂
    convert h₁ <;> clear h₁ grid <;> rcases h₃ with ⟨h₁, h₂⟩
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
  · cases s; nm pw grid a_pos
    clear h₁
    simp at h₂ ⊢
    rw [point_mk_eq_iff]
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
    clear grid
    ring_nf at h₂ h₄
    ext <;> linarith
  cases s; nm pw grid a_pos
  simp at h₁ h₂ h₃ ⊢
  rw [point_dist_comm]
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

theorem comp_state_to_state'_a_has_move_of {s : CompState}
(h : s.a_has_move) : s.to_state'.a_has_move := by
  simp [CompState.a_has_move, a_has_move_iff] at h ⊢
  rcases h with ⟨x, hx, y, hy, h₁⟩
  simp [CompState.check_a_move] at h₁
  rcases h₁ with ⟨h₁, h₂, h₃⟩
  use ⟨s.a_pos.x + (x - s.pw), s.a_pos.y + (y - s.pw)⟩
  use h₁, h₂
  rw [point_dist_comm]
  exact h₃

@[simp]
theorem comp_state_to_state'_a_has_move_iff {s : CompState} :
s.to_state'.a_has_move ↔ s.a_has_move :=
  ⟨of_comp_state_to_state'_a_has_move, comp_state_to_state'_a_has_move_of⟩

theorem comp_game_to_state_toState'_eq {cg : CompGame} :
cg.to_state.toState' = cg.s.to_state' := by rfl

theorem comp_state_a_has_move_of_check_a_move {s : CompState} {p}
(h : s.check_a_move p) : s.a_has_move := by
  apply of_comp_state_to_state'_a_has_move
  simp [CompState.check_a_move] at h
  rw [CompState.to_state', a_has_move_iff]
  use p
  simpa

theorem comp_game_to_state_a_has_move_of_check_a_move {cg : CompGame} {p}
(h : cg.s.check_a_move p) : cg.to_state.a_has_move := by
  simp [comp_game_to_state_toState'_eq]
  exact comp_state_a_has_move_of_check_a_move h

@[simp]
theorem comp_game_state_a_has_move_iff {cg : CompGame} :
cg.s.a_has_move ↔ cg.to_state.a_has_move := by
  rw [comp_game_to_state_toState'_eq]
  exact comp_state_to_state'_a_has_move_iff.symm

@[simp]
theorem comp_game_push_to_state {cg : CompGame} {s} :
(cg.push s).to_state = cg.to_state.push s.to_state' := by
  apply state_ext; rfl
  simp [CompGame.push, CompGame.to_state, State.push,
    comp_hist_to_hist, List.snoc]

#check 0 #exit

theorem eq_of_comp_game_check_a_move_and_a_ap_eq {g : Game} {cg p s'}
(h₁ : g.congr_comp cg)
(h₂ : cg.s.check_a_move p)
(h₃ : g.a.ap cg.to_state = some s') :
s' = {cg.to_state.toState' with a_pos := p} := by
  dsimp
  rcases h₁ with ⟨h₁, h₄, h₅⟩

#check 0 #exit

theorem game_move_congr_mcomp_of {g : Game} {mcg : Option CompGame}
(h : g.congr_mcomp mcg) : g.move.congr_mcomp (mcg >>= (·.move)) := by
  dsimp
  intro cg₁ h₁
  cases mcg
  · simp at h₁
  nm cg
  simp at h h₁
  
  have h₂ := h
  rcases h₂ with ⟨h₂, h₃, h₄⟩
  
  simp [Game.move]
  split_ifs with he ht <;> simp [he] at h₄ <;>
    simp [CompGame.move, h₄] at h₁
  · rwa [←h₁]
  all_goals simp [ht] at h₃; simp [h₃] at h₁; split
  · nm m h₅
    simp at h₅
    split_ifs at h₁ with h₆
    · simp at h₁
      simp [h₂] at h₅
      exfalso
      apply h₅
      exact comp_game_to_state_a_has_move_of_check_a_move h₆
    · have h₇ : ¬cg.s.a_has_move := by simpa [←h₂]
      simp [h₇] at h₁
      subst h₁
      constructor; rw [h₂]; rfl; simpa
  · nm m s h₅
    split_ifs at h₁ with h₆
    · simp at h₁
      subst cg₁
      constructor
      · simp [h₂]
        sorry
      · sorry
    · sorry
  · sorry
  · sorry

#check 0 #exit

theorem game_play_congr_mcomp_of {g : Game} {mcg : Option CompGame} {n}
(h : g.congr_mcomp mcg) : (g.play n).congr_mcomp (mcg >>= (·.play n)) := by
  intro cg₁ h₁
  dsimp at h₁
  
  cases mcg
  · simp at h₁
  nm cg
  simp at h h₁
  
  induction n generalizing g cg
  · simp at h₁ ⊢
    rwa [←h₁]
  
  nm n ih
  simp
  generalize h₂ : cg.move = cg₂
  cases cg₂
  · rw [comp_game_play_succ'] at h₁
    simp [h₂] at h₁
  nm cg₂
  
  specialize @ih g.move cg₂ _ _
  · rw [←h₁, comp_game_play_succ', h₂]
    simp
  · have h₃ := @game_move_congr_mcomp_of g cg
    specialize h₃ _
    · simpa
    simp [h₂] at h₃
    exact h₃
  
  rw [comp_game_play_succ'] at h₁
  simp [h₂] at h₁
  rw [←game_play_succ', game_play_succ] at ih
  exact ih

#check 0 #exit

instance {g : Game} [h : GameToComp g] {n} : GameToComp # g.play n := by
  use h.cg >>= (·.play n)
  simp