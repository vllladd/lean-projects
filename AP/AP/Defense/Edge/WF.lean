import AP.AP.Defense.Edge.Symmetry

namespace AP.Edge

variable {e e₁ e₂ : Edge}
variable {s : State} [hpw : Fact # s.pw = 1]
omit hpw

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

theorem aPos_y_lt_zero_of_cnd₀ (h : cnd₀ s) : s.aPos.y < 0 := by
  simp [cnd₀, getBorderPoints, getBorderPoint₀, getBorderPoint] at h ⊢
  split at h <;> linarith

theorem cnd₀_of_aPos_y_le_neg_6 (h : s.aPos.y ≤ -6) : cnd₀ s := by
  simp [cnd₀, getBorderPoints, getBorderPoint₀, getBorderPoint] at h ⊢
  split <;> linarith

include hpw in
theorem cnd₀_simulatemul_two_full_of_aState {s₁} {a : AStrat} {d : DStrat} {n}
[hs : AState s] [ha : a.WF] [hd : d.WF] (h₁ : cnd₀ s)
(h₂ : sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s (n * 2) = (s₁, 0)) : cnd₀ s₁ := by
  induction n
  · sorry
  · sorry

-- #check 0 #exit

include hpw in
theorem aPos_y_lt_zero_of_tr_aState_cnd₀ {s' p} [hs : AState s]
(h₁ : cnd₀ s) (h₂ : sys.tr s p = some s') : s'.aPos.y < 0 := by
  replace hpw := hpw.1
  rw [hs.tr_eq_some_iff] at h₂
  rcases h₂ with ⟨⟨h₂, h₃, h₄⟩, rfl⟩
  dsimp
  simp [Point.dist, hpw] at h₄
  rcases h₄ with ⟨hx, h₄⟩
  simp [abs_le] at h₄
  rcases h₄ with ⟨-, h₄⟩
  have h₅ := aPos_y_lt_zero_of_cnd₀ h₁
  rw [lt_iff_le_and_ne]
  split_ands; linarith
  intro h₆
  simp [h₆] at h₄
  rw [add_comm, ←neg_le_iff_add_nonneg] at h₄
  replace h₄ : s.aPos.y = -1; omega; clear h₅
  clear hpw h₂
  simp [cnd₀, h₄, getBorderPoints, getBorderPoint₀, getBorderPoint] at h₁
  rcases h₁ with ⟨H₁, H₂, H₃⟩
  apply h₃; clear h₃
  replace hx : p.x ∈ (s.aPos.x + ·) '' {-1, 0, 1}
  · simp; simp [abs_le] at hx; omega
  simp at hx
  rcases p with ⟨x, y⟩
  dsimp at *
  subst h₆
  rcases hx with hx | hx | hx
  · convert H₂; linarith
  · convert H₁; linarith
  · convert H₃; linarith

include hpw in
theorem edge₀_simulate_full_aPos_y_lt_zero_of_aState {s₁} {a : AStrat} {d : DStrat} {n}
[hs : AState s] [ha : a.WF] [hd : d.WF] (h₁ : s.aPos.y ≤ -6)
(h₂ : sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s n = (s₁, 0)) : s₁.aPos.y < 0 := by
  have H := cnd₀_of_aPos_y_le_neg_6 h₁
  induction n using Nat.mod_2_ind <;> nm n
  · apply aPos_y_lt_zero_of_cnd₀
    apply cnd₀_simulatemul_two_full_of_aState H h₂
  rw [sys.simulate_succ_full'] at h₂
  choose s' h₂ h₃ using h₂
  have h₄ := cnd₀_simulatemul_two_full_of_aState H h₂
  have hs' := AState.of_simulate_mul_two_eq_full h₂
  have h₅ : s'.pw = s.pw
  · apply pw_eq_of_reachable
    exact sys.reachable_of_simulate_eq h₂
  rw [←h₅] at hpw
  exact aPos_y_lt_zero_of_tr_aState_cnd₀ h₄ h₃

include hpw in
theorem edge₀_simulate_aPos_y_lt_zero_of_aState {a : AStrat} {d : DStrat} {n}
[hs : AState s] [ha : a.WF] [hd : d.WF] (h : s.aPos.y ≤ -6) :
sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s n |>.1.aPos.y < 0 := by
  apply sys.fst_simulate_ind (p := (·.aPos.y < 0)) _ n; clear n; intro n s' h₁
  exact edge₀_simulate_full_aPos_y_lt_zero_of_aState h h₁

include hpw in
theorem edge₀_simulate_aPos_y_lt_zero {a : AStrat} {d : DStrat} {n}
[hs : sys.WF s] [ha : a.WF] [hd : d.WF] (h : s.aPos.y ≤ -6) :
sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s n |>.1.aPos.y < 0 := by
  replace hs := s.aState_or_dState
  rcases hs with hs | hs
  · exact edge₀_simulate_aPos_y_lt_zero_of_aState h
  cases n; simp; linarith; nm n
  simp [System.simulate]; split; simp; linarith; nm x s₁ h₁; clear x
  have hs₁ := AState.of_tr h₁
  rw [←pw_eq_of_tr h₁] at hpw
  apply edge₀_simulate_aPos_y_lt_zero_of_aState
  rwa [DState.aPos_eq_of_tr h₁]

theorem wf_defense_edge₀ : edge₀.defense.WF := by
  use validTr_defense
  intro s hs h a ha d hd n
  have hpw : Fact # s.pw = 1; use h.1
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