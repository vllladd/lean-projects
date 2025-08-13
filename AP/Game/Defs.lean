import AP.System.Main

open Util.Data

universe u

structure GameParams : Type (u + 1) where
  Player : Type u
  State : Type u
  Move : Player → Type u
  PState : Player → Type u
  PMove : Player → Player → Type u
  Score : Type u

  h_inhabited_player : Inhabited Player
  h_hashable_player : Hashable Player
  h_linearOrder_player : LinearOrder Player
  h_inhabited_move : ∀ p, Inhabited # Move p
  h_linearOrder_score : LinearOrder Score
  h_move_rfl : ∀ p, PMove p p = Move p

namespace GameParams

section instances

variable {T : GameParams}

instance : Inhabited T.Player :=
  T.h_inhabited_player

instance : Hashable T.Player :=
  T.h_hashable_player

instance {p} : Inhabited # T.Move p :=
  T.h_inhabited_move p

instance : LinearOrder T.Player :=
  T.h_linearOrder_player

instance : LinearOrder T.Score :=
  T.h_linearOrder_score

end instances

variable (T : GameParams)

def Trans : Type u :=
  Σ (p : T.Player), T.Move p

def PTrans (p : T.Player) : Type u :=
  Σ (p' : T.Player), T.PMove p p'

def GRules : Type u :=
  (p : T.Player) → T.State → T.Move p → Option (T.Player × T.State)

abbrev Hist : Type u :=
  DMap T.Player # λ p => List (T.PTrans p)

@[ext]
structure GState : Type u where
  player : T.Player
  state : T.State
  hist : T.Hist

def initState
(ps : Util.Data.Set T.Player) (p : T.Player) (s : T.State) : T.GState :=
  { player := p
  , state := s
  , hist := ps.toDMap # λ _ => []
  }

def GPMove : Type u :=
  (p : T.Player) → (s : T.GState) → T.Move s.player → T.PMove p s.player

def updateHist (pmove : T.GPMove)
(s : T.GState) (t : T.Move s.player) : T.Hist :=
  s.hist.map # @λ p ts => ⟨s.player, pmove p s t⟩ :: ts

def sys_tr (rules : T.GRules) (pmove : T.GPMove)
(s : T.GState) (t : T.Trans) : Option T.GState :=
  if h : s.player = t.1 then do
    let (p₁, s₁) ← rules t.1 s.state t.2
    some #
      { player := p₁
      , state := s₁
      , hist := T.updateHist pmove s # h ▸ t.2
      }
  else none

abbrev StratFn (p : T.Player) : Type u :=
  T.PState p → List (T.PTrans p) → T.Move p

abbrev Outcome : Type u :=
  Map T.Player T.Score

end GameParams

@[ext]
structure Game (T : GameParams) : Type u where
  rules : T.GRules
  pstate : (p : T.Player) → T.State → T.PState p
  pmove : T.GPMove
  choose_move : (p : T.Player) → T.PState p → T.Move p
  outcome : T.GState → T.Outcome
  
  sys : System T.GState T.Trans
  
  h_sys_init_nemp : sys.initial ≠ ∅
  h_sys_init_valid : ∀ s [sys.Initial s], ∃ ps p s',
    T.initState ps p s' = s ∧ s.hist ≠ ∅
  h_rules_player_mem : ∀ {s : T.GState} [sys.WF s] {t : T.Trans} {r},
    rules t.1 s.state t.2 = some r → r.1 ∈ s.hist
  h_sys_tr : sys.tr = T.sys_tr rules pmove
  h_choose_move : ∀ (s : T.GState),
    let p := s.player
    let t := choose_move p (pstate p s.state)
    (∃ t, (rules p s.state t).isSome) → (rules p s.state t).isSome
  h_mem_outcome : ∀ {s : T.GState} [sys.WF s],
    ¬sys.hasTr s → ∀ p, p ∈ outcome s ↔ p ∈ s.hist
  h_outcome_no_hist : ∀ {s₁ s₂ : T.GState} [sys.WF s₁] [sys.WF s₂],
    ¬sys.hasTr s₁ → ¬sys.hasTr s₂ → s₁.player = s₂.player → s₁.state = s₂.state →
    ∀ p x y, (outcome s₁).get? p = some x → (outcome s₂).get? p = some y → x = y

namespace Game

variable {T : GameParams.{u}} (game : Game T)

def updateHist (s : T.GState) (t : T.Trans) : T.Hist :=
  if h : s.player = t.1
  then T.updateHist game.pmove s # h ▸ t.2
  else s.hist

def runStratFn {s : T.GState} (f : T.StratFn s.player) : T.Trans :=
  let p := s.player; Sigma.mk p #
  f (game.pstate p s.state) (s.hist.get! p)

def stratCnd {p : T.Player} (f : T.StratFn p) : Prop :=
  ∀ (s : T.GState), s.player = p → game.sys.hasTr s → game.sys.validTr s
  ⟨p, f (game.pstate p s.state) (s.hist.get! p)⟩

structure Strat (p : T.Player) : Type u where
  f : T.StratFn p
  h : game.stratCnd f

def instFn (strats : ∀ p, game.Strat p) (s : T.GState) : T.Trans :=
  game.runStratFn (strats s.player).f

structure Inst : Type u where
  strats : ∀ p, game.Strat p
  s₀ : T.GState
  s : T.GState
  h_init : game.sys.Initial s₀
  h_sim : ∃ n, game.sys.simulate (game.instFn strats) s₀ n = (s, 0)