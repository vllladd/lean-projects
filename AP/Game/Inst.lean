import AP.Game.Basic

namespace Game.Inst

variable {T : GameParams} {game : Game T} (inst : game.Inst)

def f : T.GState → T.Trans :=
  game.instFn inst.strats

@[simp]
theorem fst_f {s} : (inst.f s).fst = s.player := rfl

theorem simFn_f : game.sys.SimFn inst.f := by
  rw [System.sim_fn_iff]
  intro s h₁
  unfold f
  rcases inst with ⟨f, s₀, s', h₂, h₃⟩
  dsimp
  clear! s₀
  unfold Game.instFn Game.runStratFn
  simp
  have h₂ := (f s.player).2
  unfold Game.stratCnd at h₂
  exact h₂ _ rfl h₁

instance : game.sys.SimFn inst.f := inst.simFn_f

def step : Option game.Inst :=
  match h : game.sys.tr inst.s (inst.f inst.s) with
  | none => none
  | some s' => some #
    { inst with
      s := s'
    , h_sim := by
        obtain ⟨n, h₁⟩ := inst.h_sim
        use n + 1
        unfold Inst.f at h
        rw [System.simulate_add, h₁]
        simp [h]
    }

def run (n : ℕ) : game.Inst × ℕ :=
  match h : game.sys.simulate inst.f inst.s n with
  | (s', m) => ((·, m)) #
  { inst with
    s := s'
  , h_sim := by
      obtain ⟨k, h₁⟩ := inst.h_sim
      have ⟨n, hn⟩ := Nat.exists_eq_add_of_le #
        System.snd_le_of_simulate_eq h
      subst hn
      use k + n
      rw [System.simulate_add, h₁]
      simp
      rw [System.simulate_add_eq_left_iff] at h
      exact h.1
  }

def score (n : ℕ) : Option (T.Player → T.Score) :=
  let (inst', m) := inst.run n
  let s := inst'.s
  if m = 0 then none else some # game.score s.player s.state

end Game.Inst
namespace Game

variable {T : GameParams} {game : Game T}

def dfltStrat (p) : game.Strat p := by
  use λ s _ => game.choose_move p s
  rintro s rfl h₁
  rw [has_tr_iff_exi_rules_ap_isSome] at h₁
  rw [valid_tr_iff]
  use rfl
  dsimp
  obtain ⟨t, h₁⟩ := h₁
  have h₂ := game.h_choose_move s
  simp at h₂
  specialize h₂ _ h₁
  rwa [←Option.isSome_iff_exists]

instance {p} : Inhabited # game.Strat p := ⟨dfltStrat p⟩

def dfltInst (s) [hs : game.sys.Initial s] : game.Inst :=
  { strats := dfltStrat
  , s₀ := s
  , s := s
  , h_init := hs
  , h_sim := ⟨0, rfl⟩
  }

instance : Nonempty game.Inst := by
  classical
  have h₁ := game.h_sys_init_nemp
  simp [Set.eq_empty_iff] at h₁
  obtain ⟨s, h₁⟩ := h₁
  rw [←System.initial_iff] at h₁
  exact ⟨game.dfltInst s⟩