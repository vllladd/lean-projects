import AP.AP.Defense.Edge.Symmetry

namespace AP.Edge

variable {e e₁ e₂ : Edge}

def cnd₀ (s : State) : Prop :=
  let pa := s.aPos
  let p₀ := edge₀.getBorderPoint₀ pa
  let get := edge₀.getBorderPoints pa
  match edge₀.dist pa with
  | 5 => p₀ ∈ s.taken
  | 4 => p₀ ∈ s.taken ∧ (get 1).any (· ∈ s.taken)
  | 3 => 2 ≤ (p₀ :: get 1).countP (· ∈ s.taken)
  | 2 => False
  | 1 => (p₀ :: get 1).all (· ∈ s.taken)
  | d => 0 < d

theorem aPos_y_lt_zero_of_cnd₀ {s} (h : cnd₀ s) : s.aPos.y < 0 := by
  simp [cnd₀, getBorderPoints, getBorderPoint₀, getBorderPoint, dist] at h ⊢
  split at h <;> linarith

theorem cnd₀_of_aPos_y_le_neg_6 {s} (h : s.aPos.y ≤ -6) : cnd₀ s := by
  simp [cnd₀, getBorderPoints, getBorderPoint₀, getBorderPoint, dist] at h ⊢
  split <;> linarith

-- #check 0 #exit

theorem cnd₀_simulate_of_aState {s} {a : AStrat} {d : DStrat} {n}
[hs : AState s] [ha : a.WF] [hd : d.WF] (h : cnd₀ s) :
cnd₀ # sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s n |>.1 := by
  induction n using Nat.strong_induction_on
  nm n ih
  cases n; exact h; nm n
  simp; split; exact h; nm x s₁ h₁; clear x
  sorry

-- #check 0 #exit

theorem edge₀_simulate_aPos_y_lt_zero_of_aState {s} {a : AStrat} {d : DStrat} {n}
[hs : AState s] [ha : a.WF] [hd : d.WF] (h : s.aPos.y ≤ -6) :
sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s n |>.1.aPos.y < 0 :=
  aPos_y_lt_zero_of_cnd₀ # cnd₀_simulate_of_aState # cnd₀_of_aPos_y_le_neg_6 h

theorem edge₀_simulate_aPos_y_lt_zero {s} {a : AStrat} {d : DStrat} {n}
[hs : sys.WF s] [ha : a.WF] [hd : d.WF] (h : s.aPos.y ≤ -6) :
sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s n |>.1.aPos.y < 0 := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs
  · exact edge₀_simulate_aPos_y_lt_zero_of_aState h
  cases n; simp; linarith; nm n
  simp; split; simp; linarith; nm x s₁ h₁; clear x
  have hs₁ := AState.of_tr h₁
  apply edge₀_simulate_aPos_y_lt_zero_of_aState
  rwa [DState.aPos_eq_of_tr h₁]

theorem wf_defense_edge₀ : edge₀.defense.WF := by
  use validTr_defense
  intro s hs h a ha d hd n
  simp [defense, points, memPoints]
  apply edge₀_simulate_aPos_y_lt_zero
  simp [defense, dist] at h
  linarith

theorem wf_defense_of_down (h : e.dir = .down) : e.defense.WF := by
  have h₁ : edge₀.translate ⟨0, e.offset⟩ = e
  · ext <;> simp [h]
  rw [←h₁]
  have H : Fact # edge₀.dir = .down; simp
  rw [defense_translate_of_down]
  have h₂ := wf_defense_edge₀
  infer_instance

theorem wf_defense_of_left (h : e.dir = .left) : e.defense.WF := by
  have h₁ : e.rotLeft.defense.WF
  · apply wf_defense_of_down; simp [h]
  have h₂ : e.rotLeft.rotRight.defense = e.rotLeft.defense.sym rotRight
  · have H : Fact # e.rotLeft.hor; simp [h]
    exact defense_rotRight
  simp at h₂
  rw [h₂]
  simpa

theorem wf_defense_of_up (h : e.dir = .up) : e.defense.WF := by
  have h₁ : e.rotLeft.defense.WF
  · apply wf_defense_of_left; simp [h]
  have h₂ : e.rotLeft.rotRight.defense = e.rotLeft.defense.sym rotRight
  · have H : Fact # e.rotLeft.vert; simp [h]
    exact defense_rotRight
  simp at h₂
  rw [h₂]
  simpa

theorem wf_defense_of_right (h : e.dir = .right) : e.defense.WF := by
  have h₁ : e.rotLeft.defense.WF
  · apply wf_defense_of_up; simp [h]
  have h₂ : e.rotLeft.rotRight.defense = e.rotLeft.defense.sym rotRight
  · have H : Fact # e.rotLeft.hor; simp [h]
    exact defense_rotRight
  simp at h₂
  rw [h₂]
  simpa

theorem wf_defense : e.defense.WF := by
  cases h : e.dir
  · exact wf_defense_of_up h
  · exact wf_defense_of_left h
  · exact wf_defense_of_right h
  · exact wf_defense_of_down h

@[simp] instance : e.defense.WF := wf_defense