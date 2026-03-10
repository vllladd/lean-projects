import Projects.AP.FreshA

namespace AP.Alt₁

@[ext]
structure Point : Type where
  x : ℤ
  y : ℤ
deriving Nonempty

def center : Point := ⟨0, 0⟩

def dist (p₁ p₂ : Point) : ℕ :=
  max |p₁.x - p₂.x| |p₁.y - p₂.y| |>.toNat

@[ext]
structure Board : Type where
  squares : Set Point
  A : Point

def board₀ : Board :=
  ⟨Set.univ, center⟩

abbrev AMove : Type := Point
abbrev DMove : Type := Option Point

def AMoveValid (pw : ℕ) (b : Board) (p : AMove) : Prop :=
  p ≠ b.A ∧ dist p b.A ≤ pw ∧ p ∈ b.squares

def DMoveValid (b : Board) : DMove → Prop
  | .none => true
  | .some p => p ≠ b.A ∧ p ∈ b.squares

structure ValidAMove (pw : ℕ) (b : Board) : Type where
  m : AMove
  h : AMoveValid pw b m

structure ValidDMove (b : Board) : Type where
  m : DMove
  h : DMoveValid b m

def AHasValidMove (pw : ℕ) (b : Board) : Prop :=
  ∃ (m : AMove), AMoveValid pw b m

@[ext]
structure State : Type where
  board : Board
  history : List Board
  act : Prop

def initState (b : Board) : State where
  board := b
  history := []
  act := True

def state₀ : State :=
  initState board₀

def State.finish (s : State) : State :=
  {s with act := False}

structure A (pw : ℕ) : Type where
  f : Π (s : State), s.act → AHasValidMove pw s.board → ValidAMove pw s.board

structure D : Type where
  f : Π (s : State), s.act → ValidDMove s.board

def applyMove (s : State) (b : Board) : State :=
  {s with board := b, history := s.history ++ [s.board]}

def applyAMoveB (b : Board) (m : AMove) : Board :=
  {b with A := m}

def applyDMoveB (b : Board) : DMove → Board
| .none => b
| .some p => {b with squares := b.squares \ {p}}

def applyAMove (s : State) (m : AMove) : State :=
  applyMove s # applyAMoveB s.board m

def applyDMove (s : State) (m : DMove) : State :=
  applyMove s # applyDMoveB s.board m

@[ext]
structure Game (pw : ℕ) : Type where
  a : A pw
  d : D
  s : State

def init_game {pw : ℕ} (a : A pw) (d : D) (s : State) : Game pw where
  a := a
  d := d
  s := s

def Game.act {pw : ℕ} (g : Game pw) : Prop :=
  g.s.act

def Game.setState {pw : ℕ} (g : Game pw) (s₁ : State) : Game pw :=
  {g with s := s₁}

def Game.finish {pw : ℕ} (g : Game pw) : Game pw :=
  g.setState g.s.finish

def playAMoveAt' {pw pw₁ : ℕ} (a₁ : A pw₁) (g : Game pw)
(hs : g.s.act) (h : AHasValidMove pw₁ g.s.board) : Game pw :=
  g.setState # applyAMove g.s # a₁.f g.s hs h |>.m

open Classical in noncomputable
def playAMoveAt {pw : ℕ} (g : Game pw) : Game pw :=
  if h : g.act ∧ AHasValidMove pw g.s.board
  then playAMoveAt' g.a g h.1 h.2
  else g.finish

def playDMoveAt {pw : ℕ} (g : Game pw) (hs : g.s.act) : Game pw :=
  g.setState # applyDMove g.s # g.d.f g.s hs |>.m

open Classical in noncomputable
def Game.playMove {pw : ℕ} (g : Game pw) : Game pw :=
  if hs : g.act
  then playAMoveAt # playDMoveAt g hs
  else g

noncomputable
def Game.play {pw : ℕ} (g : Game pw) (n : ℕ) : Game pw :=
  Game.playMove^[n] g

def Game.AWins {pw : ℕ} (g : Game pw) : Prop :=
  ∀ (n : ℕ), (g.play n).act

def AHwsAt (pw : ℕ) (s : State) : Prop :=
  ∃ (a : A pw), ∀ (d : D), init_game a d s |>.AWins

def AHws (pw : ℕ) : Prop :=
  AHwsAt pw state₀

-----

@[simp]
def Point.toAlt : Point → PointZ
| ⟨x, y⟩ => ⟨x, y⟩

@[simp]
def Point.ofAlt : PointZ → Point
| ⟨x, y⟩ => ⟨x, y⟩

def Board.ofAlt (s : AP.State) : Board where
  squares := Set.univ \ s.taken.toSet.image .ofAlt
  A := .ofAlt s.aPos

open Classical in noncomputable
def Board.diff (b₁ b₂ : Board) : Point :=
  if b₁.A ≠ b₂.A then b₁.A else
  Classical.epsilon λ p => p ∈ b₂.squares ∧ p ∉ b₁.squares

@[simp] noncomputable
def histToAlt' (bs : List Board) : List PointZ :=
  match bs with
  | [] => []
  | [b] => [b.A.toAlt]
  | b₁ :: b₂ :: bs => (b₁.diff b₂).toAlt :: histToAlt' (b₂ :: bs)

noncomputable
def State.histToAlt (s : State) : List PointZ :=
  histToAlt' # s.board :: s.history.reverse

def histOfAltFn (s : AP.State) (ps : List PointZ) : Board :=
  .ofAlt # sys.trs s.init ps.tail |>.1

def histOfAlt (s : AP.State) : List Board :=
  s.hist.reverse.inits.init.tail.map # histOfAltFn s.init

noncomputable
def State.toAlt (s : State) (pw : ℕ) : AP.State where
  pw := pw
  taken := Set'.ofSet # Set.univ \ s.board.squares |>.image (·.toAlt)
  aPos := s.board.A.toAlt
  aTurn := Odd s.history.length
  hist := s.histToAlt

def State.ofAlt (s : AP.State) (act : Prop) : State where
  board := Board.ofAlt s
  history := histOfAlt s
  act := act

-- def A.alt {pw} (a : A pw) : AStrat where
--   f s := Π (s : State), s.act → AHasValidMove pw s.board → ValidAMove pw s.board

-- #check 0 #exit

-----

@[simp]
theorem ofAlt_dist {p₁ p₂ : PointZ} :
dist (.ofAlt p₁) (.ofAlt p₂) = (p₁.dist p₂).toNat := by
  rcases p₁, p₂ with ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩; simp [dist]

@[simp]
theorem State.pw_toAlt {s : State} {pw} : (s.toAlt pw).pw = pw := rfl

@[simp]
theorem State.taken_toAlt {s : State} {pw} : (s.toAlt pw).taken =
Set'.ofSet (Set.univ \ s.board.squares |>.image (·.toAlt)) := rfl

@[simp]
theorem State.aPos_toAlt {s : State} {pw} : (s.toAlt pw).aPos = s.board.A.toAlt := rfl

@[simp]
theorem State.aTurn_toAlt {s : State} {pw} : (s.toAlt pw).aTurn =
decide (Odd s.history.length) := rfl

@[simp]
theorem State.hist_toAlt {s : State} {pw} : (s.toAlt pw).hist = s.histToAlt := rfl

@[simp]
theorem State.board_ofAlt {s act} : (State.ofAlt s act).board = Board.ofAlt s := rfl

@[simp]
theorem State.history_ofAlt {s act} : (State.ofAlt s act).history = histOfAlt s := rfl

@[simp]
theorem State.act_ofAlt {s act} : (State.ofAlt s act).act ↔ act := by rfl

@[simp]
theorem histToAlt_mk {b hist act} :
State.histToAlt ⟨b, hist, act⟩ = histToAlt' (b :: hist.reverse) := rfl

@[simp]
theorem toAlt_state₀ {pw} : state₀.toAlt pw = AP.initState pw 0 := by
  simp [state₀, board₀, initState, center]; ext :1 <;> simp

@[simp]
theorem Point.toAlt_ofAlt {p} : (Point.ofAlt p).toAlt = p := rfl

@[simp]
theorem Point.ofAlt_toAlt {p} : Point.ofAlt p.toAlt = p := rfl

@[simp]
theorem Board.squares_ofAlt {s} : (Board.ofAlt s).squares =
Set.univ \ s.taken.toSet.image .ofAlt := rfl

@[simp]
theorem Board.a_ofAlt {s} : (Board.ofAlt s).A = .ofAlt s.aPos := rfl

@[simp]
theorem length_histOfAlt {s} : (histOfAlt s).length = s.hist.length - 1 := by
  simp [histOfAlt]

@[simp]
theorem Board.ofAlt_init {s : AP.State} : Board.ofAlt s.init = ⟨Set.univ, .ofAlt s.aPos₀⟩ := by
  ext:1 <;> simp

@[simp]
theorem histOfAlt_init {s : AP.State} : histOfAlt s.init = [] := rfl

-- #check 0 #exit

-- @[simp]
-- theorem histToAlt_cons_histOfAlt {s} [hs : sys.WF s] :
-- histToAlt' (.ofAlt s :: (histOfAlt s).reverse) = s.hist := by
--   choose ps h using State.wf_iff.mp hs
--   
--   simp [histOfAlt]
--   rw [hist_eq_of_trs h]
--   
--   simp
--   
--   rw [List.tail_map, List.tail_init]
--   simp
--   
--   rw [List.init_map]
--   simp
--   
--   simp [histOfAltFn]
--   
--   sorry

-- #check 0 #exit

-- @[simp]
-- theorem State,histToAlt_ofAlt {s act} [hs : sys.WF s] :
-- (State.ofAlt s act).histToAlt = s.hist := by
--   simp [ofAlt]
-- 
-- @[simp]
-- theorem State.toAlt_ofAlt {s : AP.State} {act pw} [hs : sys.WF s] :
-- (State.ofAlt s act).toAlt pw = s.setPw pw := by
--   ext:1 <;> simp [Set.image_image]
--   ·
--     simp [ofAlt]
--   ·
--     sorry