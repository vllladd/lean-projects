import AP.Game.Main

namespace GameRPS

abbrev Player := Fin 2
abbrev Item := Fin 3

abbrev PlayerA : Player := 0
abbrev PlayerB : Player := 1

structure State where
  items : Map Player Item

def State.init : State := ⟨∅⟩

abbrev Params : GameParams :=
  { Player := Player
  , State := State
  , Move := λ _ => Item
  , PSTate := λ _ => Unit
  , PMove := λ a b => if a = b then Item else Unit
  , Outcome := Bool

  , h_inh_move := λ _ => inferInstance
  , h_pl_lin := inferInstance
  , h_out_lin := inferInstance
  , h_move_rfl := by simp
  }

def rules : Params.Rules := λ p s t => do
  guard # s.items.get? p = none
  let s' := ⟨s.items.insert p t⟩
  return Prod.mk p.next # match s.items.get? 0 with
    | none => s'
    | some t' => if t ≠ t' then s' else State.init

def RPS : Game Params :=
  { sys :=
    { initial := {Params.initState PlayerA State.init}
    , tr := Params.sys_tr rules
    }
  
  , rules := rules
  , pstate := λ _ _ => ()
  , pmove := λ p _ ⟨p', t⟩ _ => by
      dsimp [Params]; split_ifs; exact t; exact ()
  
  , outcome := λ r => match r with
      | .inr _ => λ _ => false
      | .inl s => λ p =>
        let items := s.state.items
        items.get! p.next < items.get! p
  
  , h_sys_initial := by simp
  , h_sys_tr := rfl
  }