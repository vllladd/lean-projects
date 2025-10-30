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

theorem wf_defense_of_down (h : e.dir = .down) : e.defense.WF := by
  sorry

-- #check 0 #exit

theorem wf_defense_of_up (h : e.dir = .up) : e.defense.WF := by
  have H : Fact # e.dir = .up; use h
  have h₁ := congrArg (·.sym rot180) e.defense_flipV_of_up
  simp at h₁
  rw [←h₁]; clear h₁
  have h₁ : e.flipV.defense.WF
  · apply wf_defense_of_down; simp
  infer_instance

theorem wf_defense : e.defense.WF := by
  cases h : e.dir
  · exact wf_defense_of_up h
  · have h₁ : e.rotLeft.defense.WF
    · apply wf_defense_of_down; simp [h]
    
    have h₂ : e.rotLeft.rotRight.defense = e.rotLeft.defense.sym rotRight
    · have H : Fact # e.rotLeft.hor; simp [h]
      exact defense_rotRight_of_hor
    simp at h₂
    rw [h₂]
    simpa
  · have h₁ : e.rotLeft.defense.WF
    · apply wf_defense_of_up; simp [h]
    
    have h₂ : e.rotLeft.rotRight.defense = e.rotLeft.defense.sym rotRight
    · have H : Fact # e.rotLeft.hor; simp [h]
      exact defense_rotRight_of_hor
    simp at h₂
    rw [h₂]
    simpa
  · exact wf_defense_of_down h

@[simp] instance : e.defense.WF := wf_defense