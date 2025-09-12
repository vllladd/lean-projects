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

theorem valid_tr [H : dse.ValidTr] {s} [sys.WF s] {p} :
dse.f s = some p → sys.validTr s p := H.1

@[simp]
instance [H : dse.ValidTr] {d : DStrat} [Hd : d.WF] : (dse.st d).WF := by
  unfold st; rw [DStrat.wf_iff]; intro s hs
  dsimp; cases h : dse.f s <;> simp; exact dse.valid_tr h

theorem st_comm_of {d}
(h : ∀ {s p₁ p₂}, dse₁.f s = some p₁ → dse₂.f s = some p₂ → p₁ = p₂) :
dse₁.st (dse₂.st d) = dse₂.st (dse₁.st d) := by
  ext s :2; simp [st]; cases h₁ : dse₁.f s <;> cases h₂ : dse₂.f s <;> simp
  nm s₁ s₂; exact h h₁ h₂