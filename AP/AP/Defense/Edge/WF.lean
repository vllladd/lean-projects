import AP.AP.Defense.Edge.Symmetry

namespace AP.Edge

variable {e e₁ e₂ : Edge}
variable {s : State} [hpw : Fact # s.pw = 1]
omit hpw

def cndCase2 (s : State) (p₀ : PointZ) (get : ℕ → List PointZ) : Prop :=
  p₀ ∈ s.taken ∧
  let p := do
    let ps₁ := get 2
    let ps₂ := get 1
    let p ← ps₁ |>.find? (· ∈ s.taken)
    ps₂ |>.find? # λ (p' : PointZ) => p'.dist p ≠ 1
  match p with
  | none => True
  | some p => p ∈ s.taken

def cnd₀ (s : State) : Prop :=
  let pa := s.aPos
  let p₀ := edge₀.getBorderPoint₀ pa
  let get := edge₀.getBorderPoints pa
  match edge₀.dist pa with
  | 5 => p₀ ∈ s.taken
  | 4 => p₀ ∈ s.taken ∧ (get 1).any (· ∈ s.taken)
  | 3 => (get 1).all (· ∈ s.taken)
  | 2 => cndCase2 s p₀ get
  | 1 => (p₀ :: get 1).all (· ∈ s.taken)
  | d => 0 < d

def cndComp₀ (arr : Array Bool) (offset : ℕ) (d : ℕ) : Bool :=
  let f (i : ℕ) := arr[offset + i]?.iget
  match d with
  | 5 => f 2
  | 4 => f 2 ∧ (f 1 ∨ f 3)
  | 3 => f 1 ∧ f 3
  | 2 => false
  | 1 => f 1 ∧ f 2 ∧ f 3
  | d => d ≠ 0

-- #check 0 #exit

def ptsArr (s : State) (start : ℤ) (len : ℕ) : Array Bool :=
  ⟨List.range len |>.map # λ i => edge₀.getBorderPoint s.aPos (start + i) ∈ s.taken⟩

theorem cndCase2_iff_fCase2_eq_none {s p₀ get} :
cndCase2 s p₀ get ↔ fCase2 s p₀ get = none := by
  unfold cndCase2 fCase2
  split_ifs with h₁
  rotate_left; simp [h₁]
  
  suffices h : ∀ (ps₁ ps₂ : List PointZ),
    (have p := do
      let p ← List.find? (fun x ↦ decide (x ∈ s.taken)) ps₁
      List.find? (fun p' ↦ decide (Point.dist p' p ≠ 1)) ps₂;
    match p with
    | none => True
    | some p => p ∈ s.taken) ↔
  (do
    let p ← List.find? (fun x ↦ decide (x ∈ s.taken)) ps₁
    let p' ← List.find? (fun p' ↦ decide (Point.dist p' p ≠ 1)) ps₂
    guard (p' ∉ s.taken)
    pure p') =
    none
  · simp [h₁] at h ⊢; apply h
  intro ps₁ ps₂
  
  generalize ps₁.find? (fun x ↦ decide (x ∈ s.taken)) = p₁
  rcases p₁ with ⟨⟩ | p₁ <;> simp
  
  generalize ps₂.find? (λ p' => !decide (p'.dist p₁ = 1)) = p₂
  rcases p₂ with ⟨⟩ | p₂ <;> simp

-- #check 0 #exit

theorem cnd₀_iff_f_edge₀_eq_none_of_neg_y_aPos {s} [hs : sys.WF s] (h₀ : s.aPos.y < 0) :
cnd₀ s ↔ edge₀.f s = none := by
  simp [cnd₀, f, f', dist_edge₀, getBorderPoint₀, getBorderPoints, getBorderPoint]
  split <;> nm x h₁ <;> rw [neg_eq_iff_eq_neg] at h₁ <;> simp [h₁]
  · simp only [Point.ext_iff, true_and]; omega
  · rcases h : s.aPos with ⟨x, y⟩
    simp [h] at h₁
    simp [Point.ext_iff, Point.forall_iff]
    constructor
    · rintro ⟨h₂, h₃⟩ a b
      split_ifs; simp [h₂]
    · intro h₂
      split_ifs at h₂ with h₄ <;> simp at h₂
      · rcases h₄ with h₄ | h₄
        all_goals
          simp [h₄]
          by_contra! h₅
          simp [h₅] at h₂
          subst h₂
          simp at h₁
      · simp at h₄
        simp_all only [Int.reduceNeg, not_false_eq_true, true_and, false_and, or_false, or_self,
          and_false]
        subst h₁
        rcases h₄ with ⟨h₃, h₄⟩
        simp [←sub_eq_add_neg] at h₂ h₃
        have h₅ := h₂ x 0
        have h₆ := h₂ (x - 1) 0
        simp at h₅
        simp [h₃, h₅] at h₆
  · rcases h : s.aPos with ⟨x, y⟩
    simp [h] at h₁; subst h₁
    simp [Point.ext_iff, ←sub_eq_add_neg, Point.forall_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      simp [h₁, h₂]
    · intro h₁
      have h₂ := h₁ (x - 1) 0
      split_ands
      · by_contra! h₃
        simp [h₃] at h₂
      · by_contra! h₃
        have h₄ := h₁ (x + 1) 0
        simp [h₃] at h₄
        tauto
  · clear x
    rw [cndCase2_iff_fCase2_eq_none]
    generalize h₂ : fCase2 s { x := s.aPos.x, y := 0 } (edge₀.getBorderPoints s.aPos) = m
    rcases m with ⟨⟩ | p
    · simp
    simp
    split_ands
    · rintro rfl
      simp [fCase2] at h₂
      split_ifs at h₂ with h₃ <;> simp at h₂
      rotate_left
      · simp [Point.ext_iff] at h₂
        simp [←h₂] at h₁
      choose p h₂ h₄ using h₂
      clear h₂
      simp [List.find?_eq_some_iff_append] at h₄
      obtain ⟨h₄, xs, ⟨x, h₇⟩, h₈⟩ := h₄
      simp [getBorderPoints, getBorderPoint] at h₇
      cases xs <;> simp at h₇
      · rw [←h₇.1] at h₁
        simp at h₁
      nm p₂ xs
      cases xs <;> simp at h₇
      simp at h₈
      rcases h₇ with ⟨rfl, h₇, rfl⟩
      rw [←h₇] at h₁
      simp at h₁
    · simp [fCase2] at h₂
      split_ifs at h₂ with h₃ <;> simp at h₂
      rotate_left
      · rwa [←h₂]
      choose p₁ h₂ h₄ h₅ using h₂
      exact h₅
  · clear x
    rcases h : s.aPos with ⟨x, y⟩
    simp [h] at h₁; subst h₁
    simp [Point.ext_iff, Point.forall_iff]
    grind only [cases Or]
  · split <;> simp_all [neg_eq_iff_eq_neg]

-- #check 0 #exit

theorem aPos_y_lt_zero_of_cnd₀ (h : cnd₀ s) : s.aPos.y < 0 := by
  simp [cnd₀, getBorderPoints, getBorderPoint₀, getBorderPoint] at h ⊢
  split at h <;> linarith

theorem cnd₀_of_aPos_y_le_neg_6 (h : s.aPos.y ≤ -6) : cnd₀ s := by
  simp [cnd₀, getBorderPoints, getBorderPoint₀, getBorderPoint] at h ⊢
  split <;> linarith

theorem cnd₀_of_taken_subset {s s'} (h₁ : cnd₀ s) (h₃ : s'.aPos = s.aPos)
(h₂ : s.taken ⊆ s'.taken) : cnd₀ s' := by
  simp [cnd₀, h₃] at h₁ ⊢
  replace h₂ := λ {x} => h₂ x
  split at h₁ <;> nm x h₄
  · exact h₂ h₁
  · choose h₁ p h₅ h₆ using h₁
    use h₂ h₁, p, h₅, h₂ h₆
  · intro p h₅
    specialize h₁ p h₅
    exact h₂ h₁
  · simp [cndCase2] at h₁ ⊢
    rcases h₁ with ⟨h₁, h₅⟩
    use h₂ h₁
    sorry
  · choose h₁ h₅ using h₁
    use h₂ h₁
    intro p h₆
    specialize h₅ p h₆
    use h₂ h₅
  · exact h₁

-- #check 0 #exit

theorem cnd₀_eq_cndComp₀ {s} : cnd₀ s = cndComp₀ (ptsArr s (-2) 5) 0 (-s.aPos.y).toNat := by
  unfold ptsArr
  by_cases h : 0 ≤ s.aPos.y
  · have h₁ : ¬cnd₀ s
    · contrapose! h
      exact aPos_y_lt_zero_of_cnd₀ h
    simp [h₁]
    replace h : -s.aPos.y ≤ 0; linarith
    rw [←Int.toNat_eq_zero] at h
    simp [cndComp₀, h]
  push_neg at h
  simp [cnd₀, cndComp₀, getBorderPoints, getBorderPoint₀]
  split <;> nm H h₁ <;> simp [h₁]
  · sorry
  · tauto
  · nm x h₂ h₃ h₄; clear x
    simp at H h₁ h₂ h₃ h₄
    split <;> try omega
    simp

-- #check 0 #exit

theorem cnd₀_of_tr_tr_aState {sa sd sa' p} {d : DStrat} [hsa : AState sa] [hd : d.WF]
(hpw : sa.pw = 1) (h₀ : cnd₀ sa) (h₁ : sys.tr sa p = some sd)
(h₂ : sys.tr sd (edge₀.defense.st d |>.f sd) = some sa') : cnd₀ sa' := by
  have hsd := DState.of_tr h₁
  have hsa' := AState.of_tr h₂
  by_cases h₃ : cnd₀ sd
  · apply cnd₀_of_taken_subset h₃ # DState.aPos_eq_of_tr h₂
    rw [DState.taken_eq_of_tr h₂]
    sorry
  sorry

-- #check 0 #exit

include hpw in
theorem cnd₀_simulatemul_two_full_of_aState {s₁} {a : AStrat} {d : DStrat} {n}
[hs : AState s] [hd : d.WF] (h₁ : cnd₀ s)
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
  exact cnd₀_of_tr_tr_aState hpw₁ ih h₃ h₄

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
[hs : AState s] [hd : d.WF] (h₁ : s.aPos.y ≤ -6)
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
[hs : AState s] [hd : d.WF] (h : s.aPos.y ≤ -6) :
sys.simulate (Strat.f ⟨a, edge₀.defense.st d⟩) s n |>.1.aPos.y < 0 := by
  apply sys.fst_simulate_ind (p := (·.aPos.y < 0)) _ n; clear n; intro n s' h₁
  exact edge₀_simulate_full_aPos_y_lt_zero_of_aState h h₁

include hpw in
theorem edge₀_simulate_aPos_y_lt_zero {a : AStrat} {d : DStrat} {n}
[hs : sys.WF s] [hd : d.WF] (h : s.aPos.y ≤ -6) :
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