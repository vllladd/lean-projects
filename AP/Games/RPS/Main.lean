import AP.Game.Main

namespace GameRPS

abbrev Player := Fin 2
abbrev Item := Fin 3

abbrev playerA : Player := 0
abbrev playerB : Player := 1

structure State where
  items : Map Player Item

def State.init : State := ⟨∅⟩

abbrev Params : GameParams :=
  { Player := Player
  , State := State
  , Move := λ _ => Item
  , PState := λ _ => Unit
  , PMove := λ a b => if a = b then Item else Unit
  , Outcome := Bool

  , h_inh_player := inferInstance
  , h_inh_move := λ _ => inferInstance
  , h_pl_fin := inferInstance
  , h_pl_lin := inferInstance
  , h_out_lin := inferInstance
  , h_move_rfl := by simp
  }

def rules : Params.GRules := λ p s t => do
  guard # s.items.get? p = none
  let s' := ⟨s.items.insert p t⟩
  return Prod.mk p.next # match s.items.get? 0 with
    | none => s'
    | some t' => if t ≠ t' then s' else State.init

def pmove : Params.GPMove := λ p _ t => by
  dsimp [GameParams.PTrans]
  split_ifs; exact t; exact ()

def RPS : Game Params :=
  { rules := rules
  , pstate := λ _ _ => ()
  , pmove := pmove
  
  , outcome := λ _ s p =>
      let items := s.items
      match items.get? p, items.get? p.next with
      | some x, some y => x = y.next
      | _, _ => false
  
  , sys :=
    { initial := {Params.initState playerA State.init}
    , tr := Params.sys_tr rules pmove
    }
  
  , h_sys_init_nemp := by simp
  , h_sys_init_valid := by
      simp [System.initial_iff]
  , h_sys_tr := rfl
  }

-----

theorem stratCnd {p} {f : Params.StratFn p} : RPS.stratCnd f := by
  rintro s h₁ ⟨⟨p, t⟩, h₂⟩
  rw [Game.valid_tr_iff] at h₂ ⊢
  use h₁; dsimp
  rcases h₂ with ⟨rfl, r, h₂⟩
  dsimp at h₂
  simp [RPS, rules] at h₂ ⊢
  replace h₂ := h₂.1
  rwa [←h₁]

-----

def Rock     : Fin 3 := 0
def Paper    : Fin 3 := 1
def Scissors : Fin 3 := 2

example :
let run (x y : Item) : List ℕ :=
  let aStrat : RPS.Strat playerA := ⟨λ _ _ => x, stratCnd⟩
  let bStrat : RPS.Strat playerB := ⟨λ _ _ => y, stratCnd⟩
  let state₀ := Params.initState playerA State.init
  let inst : RPS.Inst :=
    { strats := λ p => match p with
        | 0 => aStrat
        | 1 => bStrat
    , s₀ := state₀
    , s := state₀
    , h_init := ⟨rfl⟩
    , h_sim := ⟨0, rfl⟩
    }
  match inst.outcome 3 with
  | none => [0, 0]
  | some r => [r 0, r 1].map # λ (b : Bool) => ite b 1 0
let tests : List # Item × Item × List ℕ :=
  [ (Rock,     Rock,     [0, 0])
  , (Rock,     Paper,    [0, 1])
  , (Rock,     Scissors, [1, 0])
  , (Paper,    Rock,     [1, 0])
  , (Paper,    Paper,    [0, 0])
  , (Paper,    Scissors, [0, 1])
  , (Scissors, Rock,     [0, 1])
  , (Scissors, Paper,    [1, 0])
  , (Scissors, Scissors, [0, 0])
  ]
tests.all # λ ⟨x, y, r⟩ => run x y = r := rfl