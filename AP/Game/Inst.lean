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

def step : Option game.Inst := do
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