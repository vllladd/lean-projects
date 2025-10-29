import AP.AP.Defense.Edge.Symmetry

namespace AP.Edge

variable {e e₁ e₂ : Edge}

def cnd (e : Edge) (s : State) : Prop :=
  let pa := s.aPos
  let p₀ := e.getBorderPoint₀ pa
  let get := e.getBorderPoints pa
  match e.dist pa with
  | 5 => p₀ ∈ s.taken
  | 4 => p₀ ∈ s.taken ∧ (get 1).any (· ∈ s.taken)
  | 3 => 2 ≤ (p₀ :: get 1).countP (· ∈ s.taken)
  | 2 => False
  | 1 => (p₀ :: get 1).all (· ∈ s.taken)
  | d => 0 < d

instance {e : Edge} {s} : Decidable # e.cnd s := by
  simp [Edge.cnd]; split <;> all_goals infer_instance

-- #check 0 #exit

theorem wf_defense_of_down (H : e.dir = .down) : e.defense.WF := by
  sorry

-- #check 0 #exit

theorem wf_defense : e.defense.WF := by
  use e.validTr_defense
  intro s hs h a ha d hd n
  cases H : e.dir
  ·
    -- obtain ⟨h₁, h₂⟩ := e.flipV.wf_defense_of_down (by simp [H])
    -- have H₁ : Fact # e.flipV.dir = .down; simp [H]
    -- specialize @h₂ (flipV.fs s) _ _ (a.sym flipV) _ (d.sym flipV) _ n
    -- · simp [Edge.defense] at h ⊢; exact h
    -- simp at h₂ ⊢
    -- have h₃ := congrArg (·.sym rot180) e.flipV.defense_flipV_of_up
    -- simp at h₃
    -- rw [←h₃] at h₂; clear h₃
    -- sorry
    sorry
  ·
    -- obtain ⟨h₁, h₂⟩ := e.rotRight.wf_defense_of_up (by simp [H])
    -- have H₁ : Fact e.rotRight.hor; simp [H]
    -- have h₃ := e.rotRight.defense_rotRight_of_hor
    -- specialize @h₂ s _ _
    sorry
  ·
    -- obtain ⟨h₁, h₂⟩ := e.rotRight.wf_defense_of_up (by simp [H])
    -- have H₁ : Fact e.rotRight.hor; simp [H]
    -- specialize @h₂ (rotRight.fs s) _ _ (a.sym rotRight) _ (d.sym rotRight) _ n
    -- · simp [Edge.defense] at h ⊢; exact h
    -- convert h₂ using 2
    -- · symm
    sorry
  · apply wf_defense_of_down H |>.2 h

-- #check 0 #exit

@[simp] instance : e.defense.WF := wf_defense