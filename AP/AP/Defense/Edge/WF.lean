import AP.AP.Defense.Edge.Cnd

namespace Array

variable {α : Type*} {xs ys : Array α}

theorem set_eq_set! {i x h} : xs.set i x h = xs.set! i x := by
  unfold Array.set! Array.setIfInBounds; simp [h]

-- #check 0 #exit

end Array

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
  
  obtain ⟨m, hpa⟩ := exi_aMove₀_of_tr_eq_some h₁
  
  obtain ⟨y, hy⟩ : ∃ (y : Fin 7), sa.aPos.y = -y
  · obtain ⟨y, hy⟩ := exi_fin_y_of_f_eq_some h₃
    by_cases H₁ : y = 0
    · subst H₁
      simp at hy
      simp [f, f', hy] at h₃
    rw [AState.aPos_eq_of_tr h₁] at hy
    have H₂ := aMove₀_dist_eq_one sa.aPos m
    rw [hpa] at H₂
    rw [Point.dist] at H₂
    replace H₂ := le_of_eq H₂
    rw [max_le_iff] at H₂
    replace H₂ := H₂.2
    rw [abs_le] at H₂
    rcases H₂ with ⟨H₂, H₃⟩
    use ⟨(-sa.aPos.y).toNat, by omega⟩
    simp
    rw [show (0 : ℤ)= -0 by simp]
    rw [Int.neg_max_neg]
    simp
    omega

  generalize hxs : ptsArr sa (-3) 7 = xs
  rw [cnd₀_iff_cndComp₀] at h₀
  have h : ptsArr sa (-2) 5 = xs.extract 1 6
  · simp [←hxs]
  rw [h] at h₀; clear h
  obtain hpd := f₀_eq_of_f_eq_some h₃
  generalize h₄ : (1 + pa.x - sa.aPos.x).toNat = offset
  generalize hys : xs.extract offset (offset + 5) = ys
  
  have H₁ : ptsArr sd (-2) 5 = ys
  · subst hxs h₄ hpa hys
    simp only [Int.reduceNeg, extract_ptsArr, Int.ofNat_toNat, Int.sub_nonneg, le_one_add_aMove₀_x,
      sup_of_le_left]
    rw [min_eq_right]
    rotate_left
    · simp only [Nat.reduceLeDiff, Int.toNat_le, Nat.cast_ofNat, tsub_le_iff_right,
      one_add_aMove₀_le_two_add_x]
    simp only [Int.reduceNeg, add_tsub_cancel_left]
    ring_nf
    rw [ptsArr_eq_of_taken_eq # hsa.taken_eq_of_tr h₁, hsa.aPos_eq_of_tr h₁]
    ring_nf
  rw [H₁, hsa.aPos_eq_of_tr h₁] at hpd
  rw [cnd₀_iff_cndComp₀]
  
  have h₅ : offset + 5 ≤ xs.size
  · subst h₄ hxs hpa; simp
  
  have h₆ : ys.size = 5
  · subst hys
    simp
    rw [min_eq_left h₅]
    simp
  
  generalize hk : f₀ ys 0 (-pa.y).toNat = k at hpd
  
  have h₇ : k < 5
  · simp [←hk]
  
  have h : ptsArr sa' (-2) 5 = ys.set k true
  ·
    rw [ptsArr_eq_of_aPos_eq_and_taken_eq_insert]
    rotate_left
    · exact hsd.aPos_eq_of_tr h₂
    · exact hsd.taken_eq_of_tr h₂
    · subst hpd
      simp [getBorderPoint]
      use k - 2
      split_ands
      · rw [abs_le]
        omega
      rw [AState.aPos_eq_of_tr h₁]
      ring_nf
    rw! [AState.aPos_eq_of_tr h₁]
    subst hpd
    simp
    ring_nf
    simp
    rw! [H₁]
  rw [h]; clear h
  
  have H₂ : xs.size = 7
  · simp [←hxs]
  
  rw [DState.aPos_eq_of_tr h₂, AState.aPos_eq_of_tr h₁]
  
  have H : y = 2 ∧ m = 0 ∧
    [  xs[0]!
    , !xs[1]!
    ,  xs[2]!
    , !xs[3]!
    ,  xs[4]!
    ,  xs[5]!
    ,  xs[6]!
    ].all id
  · sorry
  
  rw [Array.set_eq_set!]
  simp only [Int.reduceNeg, aMove₀] at *
  clear h₁ h₂ hxs h₇ h₅ H₁ h₆ h₃
  subst hpa hpd hys h₄ hk
  clear hpw hsa hsd hsa'
  simp only [hy, neg_neg, Int.toNat_natCast, Point.x_add, Point.y_add, neg_add_rev,
    Array.set!_eq_setIfInBounds] at *
  clear hy
  ring_nf at *
  clear sa sd sa'
  
  revert y m h₀
  revert xs
  -- native_decide
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
theorem cnd₀_simulate_mul_two_full_of_aState {s₁} {a : AStrat} {d : DStrat} {n}
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
    apply cnd₀_simulate_mul_two_full_of_aState H h₂
  rw [sys.simulate_succ_full'] at h₂
  choose s' h₂ h₃ using h₂
  have h₄ := cnd₀_simulate_mul_two_full_of_aState H h₂
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