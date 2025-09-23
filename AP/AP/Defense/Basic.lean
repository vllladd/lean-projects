import AP.AP.Defense.Defs

namespace AP.Defense

variable {dse dse₁ dse₂ : Defense}

instance : Inhabited Defense :=
  ⟨{cnd := λ _ => True, ps := ∅, f := λ _ => none}⟩

@[simp]
theorem default_def : (default : Defense) =
{cnd := λ _ => True, ps := ∅, f := λ _ => none} := rfl

@[simp] instance : WF default where
  valid_tr := by simp
  not_mem_ps := by simp

theorem valid_tr [H : dse.ValidTr] {s} [DState s] {p} :
dse.f s = some p → sys.validTr s p := H.1

@[simp]
instance [H : dse.ValidTr] {d : DStrat} [Hd : d.WF] : (dse.st d).WF := by
  unfold st; rw [DStrat.wf_iff]; intro s hs
  dsimp; cases h : dse.f s <;> simp; exact dse.valid_tr h

theorem st_comm {d}
(h : ∀ {s p₁ p₂}, dse₁.f s = some p₁ → dse₂.f s = some p₂ → p₁ = p₂) :
dse₁.st (dse₂.st d) = dse₂.st (dse₁.st d) := by
  ext s :2; simp [st]; cases h₁ : dse₁.f s <;>
  cases h₂ : dse₂.f s <;> simp; exact h h₁ h₂

theorem simulate_st_comm {s₀ n} {a : AStrat} {d : DStrat}
[hs₀ : sys.WF s₀] [Ha : a.WF] [Hd : d.WF] [H₁ : dse₁.WF] [H₂ : dse₂.WF]
(h : ∀ {s}, sys.Reachable s₀ s → ∀ {p₁ p₂},
dse₁.f s = some p₁ → dse₂.f s = some p₂ → p₁ = p₂) :
sys.simulate (Strat.f ⟨a, dse₁.st (dse₂.st d)⟩) s₀ n =
sys.simulate (Strat.f ⟨a, dse₂.st (dse₁.st d)⟩) s₀ n := by
  apply simulate_congr <;> simp
  intro k hk s hs h₁ h₂ h₃
  simp [st]
  cases H₃ : dse₁.f s <;> cases H₄ : dse₂.f s <;> simp
  nm s₁ s₂
  have H₅ := sys.reachable_of_simulate_full h₁
  exact h H₅ H₃ H₄