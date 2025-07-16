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
      ∃ x y, let items := s.items
      items.get? p = some x ∧
      items.get? p.next = some y ∧
      y < x
  
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

def aStrat : RPS.Strat playerA :=
  { f := λ _ _ => 1
  , h := stratCnd
  }

def bStrat : RPS.Strat playerB :=
  { f := λ _ _ => 0
  , h := stratCnd
  }

def state₀ := Params.initState playerA State.init

def inst : RPS.Inst :=
  { strats := λ p => match p with
      | 0 => aStrat
      | 1 => bStrat
  , s₀ := state₀
  , s := state₀
    
  , h_init := ⟨rfl⟩
  , h_sim := ⟨0, rfl⟩
  }