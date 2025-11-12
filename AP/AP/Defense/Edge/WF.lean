import AP.AP.Defense.Edge.Cnd

namespace AP.Edge

variable {e e₁ e₂ : Edge}
variable {s : State} [hpw : Fact # s.pw = 1]
omit hpw

theorem cndComp₀_of_ptsArr_subset_aux₁ {arr₁ arr₂ : Array Bool} {d : ℕ}
(h₁ : cndComp₀ arr₁ 0 d) (h₂ : arr₁.size = 5) (h₃ : arr₂.size = 5)
(h₄ : ∀ i < arr₁.size, arr₁[i]? = some true → arr₂[i]? = some true) :
cndComp₀ arr₂ 0 d := by
  rw [cndComp₀_eq_cndComp₀_min_6] at h₁ ⊢
  generalize hn : min 6 d = n at h₁ ⊢
  replace hn : n ≤ 6; simp [←hn]
  generalize hm : (⟨n, by omega⟩ : Fin 7) = m
  rw [show n = m.1 by simp [←hm]] at h₁ ⊢
  clear! n d
  revert arr₁
  revert arr₂
  revert m
  native_decide

theorem cndComp₀_of_ptsArr_subset_aux₂ {arr₁ arr₂ : Array Bool} {d : ℕ}
(h₁ : cndComp₀ arr₁ 0 d) (h₂ : arr₁.size ≤ 5) (h₃ : arr₂.size ≤ 5)
(h₄ : ∀ i < arr₁.size, arr₁[i]? = some true → arr₂[i]? = some true) :
cndComp₀ arr₂ 0 d := by
  rw [cndComp₀_eq_cndComp₀_append (n := 5 - arr₁.size)] at h₁
  rw [cndComp₀_eq_cndComp₀_append (n := 5 - arr₂.size)]
  obtain ⟨k₁, h₅⟩ := Nat.exists_eq_add_of_le h₂
  obtain ⟨k₂, h₆⟩ := Nat.exists_eq_add_of_le h₃
  apply cndComp₀_of_ptsArr_subset_aux₁ h₁ (by simp [h₅]) (by simp [h₆])
  simp [h₅]
  intro i hi h₇
  rw [List.getElem?_append] at h₇ ⊢
  split_ifs at h₇ with h₈
  rotate_left
  · push_neg at h₈
    simp [List.getElem?_eq_some_iff] at h₇
  simp only [Array.length_toList, Array.getElem?_toList] at *
  split_ifs with h₉
  · apply h₄ <;> assumption
  push_neg at h₉
  exfalso
  specialize h₄ i h₈ h₇
  rw [Array.getElem?_eq_some_iff] at h₄
  choose H h₄ using h₄
  linarith

theorem cndComp₀_of_ptsArr_subset {arr₁ arr₂ : Array Bool} {offset d : ℕ}
(h₁ : cndComp₀ arr₁ offset d)
(h₃ : ∀ i < arr₁.size, arr₁[i]? = some true → arr₂[i]? = some true) :
cndComp₀ arr₂ offset d := by
  rw [cndComp₀_eq_cndComp₀_extract] at h₁ ⊢
  apply cndComp₀_of_ptsArr_subset_aux₂ h₁ (by grind) (by grind)
  intro i h₄ h₅
  simp at h₄
  rw [←Nat.add_lt_iff_lt_sub_right, lt_min_iff] at h₄
  have h₆ : i < arr₁.size
  · linarith
  have h₇ : i < 5
  · linarith
  clear h₄
  rw [Array.getElem?_extract_add h₇] at h₅ ⊢
  have h₈ : offset + i < arr₁.size
  · rw [Array.getElem?_eq_some_iff] at h₅
    exact h₅.1
  exact h₃ _ h₈ h₅

theorem cnd₀_of_taken_subset {s s'} (h₁ : cnd₀ s) (h₃ : s'.aPos = s.aPos)
(h₂ : s.taken ⊆ s'.taken) : cnd₀ s' := by
  rw [cnd₀_iff_cndComp₀] at h₁ ⊢
  rw [h₃]
  apply cndComp₀_of_ptsArr_subset h₁
  simp
  rintro i - h₄
  simp [ptsArr] at h₄ ⊢
  choose k hk h₄ using h₄
  use k, hk
  simp [getBorderPoint] at h₄ ⊢
  apply h₂
  rwa [h₃]

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

theorem cnd₀_of_tr_tr_aState {sa sd sa' pa pd} [hsa : AState sa]
[hpw : Fact # sa.pw = 1] (h₀ : cnd₀ sa) (h₁ : sys.tr sa pa = some sd)
(h₂ : sys.tr sd pd = some sa') (h₃ : edge₀.f sd = some pd) : cnd₀ sa' := by
  have hsd := DState.of_tr h₁
  have hsa' := AState.of_tr h₂
  sorry

-- #check 0 #exit

theorem cnd₀_of_tr_tr_st_aState {sa sd sa' p} {d : DStrat} [hsa : AState sa]
[hpw : Fact # sa.pw = 1] (h₀ : cnd₀ sa) (h₁ : sys.tr sa p = some sd)
(h₂ : sys.tr sd (edge₀.defense.st d |>.f sd) = some sa') : cnd₀ sa' := by
  have hsd := DState.of_tr h₁
  have hsa' := AState.of_tr h₂
  by_cases h₃ : cnd₀ sd
  · apply cnd₀_of_taken_subset h₃ # DState.aPos_eq_of_tr h₂
    simp [DState.taken_eq_of_tr h₂]
  have h₄ := aPos_y_lt_zero_of_cnd₀ h₀
  have h₅ := aPos_y_lt_zero_of_tr_aState_cnd₀ h₀ h₁
  rw [cnd₀_iff_f_edge₀_eq_none_of_neg_aPos_y h₅] at h₃
  simp [Option.ne_none_iff_exists'] at h₃
  choose pd h₃ using h₃
  simp [Defense.st, defense, h₃] at h₂
  exact cnd₀_of_tr_tr_aState h₀ h₁ h₂ h₃

include hpw in
theorem cnd₀_simulatemul_two_full_of_aState {s₁} {a : AStrat} {d : DStrat} {n}
[hs : AState s] (h₁ : cnd₀ s)
(h₂ : sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s (n * 2) = (s₁, 0)) : cnd₀ s₁ := by
  induction n generalizing s₁
  · simp at h₂; rwa [←h₂]
  nm n ih
  rw [Nat.succ_mul, sys.simulate_add_full] at h₂
  simp at h₂
  choose sa h₂ sd h₃ h₄ using h₂
  have hsa := AState.of_simulate_mul_two_eq_full h₂
  have hsd := DState.of_tr h₃
  have hs₁ := AState.of_tr h₄
  have hpw₁ : sa.pw = 1
  · convert hpw.1 using 1
    exact pw_eq_of_reachable # sys.reachable_of_simulate_eq h₂
  specialize ih h₂
  simp at h₃ h₄
  exact cnd₀_of_tr_tr_st_aState (hpw := ⟨hpw₁⟩) ih h₃ h₄

include hpw in
theorem edge₀_simulate_full_aPos_y_lt_zero_of_aState {s₁} {a : AStrat} {d : DStrat} {n}
[hs : AState s] (h₁ : s.aPos.y ≤ -6)
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
[hs : AState s] (h : s.aPos.y ≤ -6) :
sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s n |>.1.aPos.y < 0 := by
  apply sys.fst_simulate_ind (p := (·.aPos.y < 0)) _ n; clear n; intro n s' h₁
  exact edge₀_simulate_full_aPos_y_lt_zero_of_aState h h₁

include hpw in
theorem edge₀_simulate_aPos_y_lt_zero {a : AStrat} {d : DStrat} {n}
[hs : sys.WF s] (h : s.aPos.y ≤ -6) :
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