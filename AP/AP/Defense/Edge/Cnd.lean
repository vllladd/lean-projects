import AP.AP.Defense.Edge.Symmetry

namespace AP.Edge

def cnd₀ (s : State) : Prop :=
  let pa := s.aPos
  let p₀ := edge₀.getBorderPoint₀ pa
  let get1 := edge₀.getBorderPoint pa
  let get := edge₀.getBorderPoints pa
  match edge₀.dist pa with
  | 5 => p₀ ∈ s.taken
  | 4 => p₀ ∈ s.taken ∧ (get 1).any (· ∈ s.taken)
  | 3 => (get 1).all (· ∈ s.taken)
  | 2 => (get1 (-2) ∈ s.taken ∨ get1 (-1) ∈ s.taken) ∧
    (get1 1 ∈ s.taken ∨ get1 2 ∈ s.taken)
  | 1 => (p₀ :: get 1).all (· ∈ s.taken)
  | d => 0 < d

def cndComp₀ (arr : Array Bool) (offset : ℕ) (d : ℕ) : Bool :=
  let f (i : ℕ) := arr[offset + i]?.getD false
  match d with
  | 5 => f 2
  | 4 => f 2 ∧ (f 1 ∨ f 3)
  | 3 => f 1 ∧ f 3
  | 2 => (f 0 ∨ f 1) ∧ (f 3 ∨ f 4)
  | 1 => f 1 ∧ f 2 ∧ f 3
  | d => d ≠ 0

def f₀ (arr : Array Bool) (offset : ℕ) (d : ℕ) : ℕ :=
  let f (i : ℕ) := arr[offset + i]?.getD false
  match d with
  | 5 => 2
  | 4 => if !f 2 then 2 else if !f 1 then 1 else 3
  | 3 => if !f 1 then 1 else 3
  | 2 => if !f 0 && !f 1 then 1 else 3
  | 1 => if !f 2 then 2 else if !f 1 then 1 else 3
  | _ => 0

def ptsArr (s : State) (start : ℤ) (len : ℕ) : Array Bool :=
  ⟨List.range len |>.map # λ i => edge₀.getBorderPoint s.aPos (start + i) ∈ s.taken⟩

def aMove₀' (m : Fin 8) : PointZ :=
  match m with
  | 0 => ⟨-1, -1⟩
  | 1 => ⟨0, -1⟩
  | 2 => ⟨1, -1⟩
  | 3 => ⟨-1, 0⟩
  | 4 => ⟨1, 0⟩
  | 5 => ⟨-1, 1⟩
  | 6 => ⟨0, 1⟩
  | 7 => ⟨1, 1⟩

def aMove₀ (p : PointZ) (m : Fin 8) : PointZ :=
  p + aMove₀' m

-- #check 0 #exit

-----

variable {e e₁ e₂ : Edge}
variable {s : State} [hpw : Fact # s.pw = 1]
omit hpw

@[simp]
theorem size_ptsArr {s offset n} : (ptsArr s offset n).size = n := by
  simp [ptsArr]

theorem cnd₀_iff_f_edge₀_eq_none_of_neg_aPos_y {s} (h₀ : s.aPos.y < 0) :
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
    generalize s.aPos = p at *
    rcases p with ⟨x, y⟩
    subst h₁
    simp_all only [Int.reduceNeg, Int.neg_neg_iff_pos, Nat.ofNat_pos]
    apply Iff.intro
    · intro a a_1 a_2 a_3
      obtain ⟨left, right⟩ := a
      cases left with
      | inl h =>
        cases right with
        | inl h_1 => simp_all only [Int.reduceNeg, not_true_eq_false, false_and, ↓reduceIte,
          reduceCtorEq]
        | inr h_2 => simp_all only [Int.reduceNeg, not_true_eq_false, false_and, ↓reduceIte,
          and_false, reduceCtorEq]
      | inr h_1 =>
        cases right with
        | inl h => simp_all only [Int.reduceNeg, not_true_eq_false, and_false, ↓reduceIte,
          false_and, reduceCtorEq]
        | inr h_2 => simp_all only [Int.reduceNeg, not_true_eq_false, and_false, ↓reduceIte,
          reduceCtorEq]
    · intro a
      apply And.intro
      · split at a
        next h =>
          simp_all only [Int.reduceNeg, Point.mk.injEq, add_eq_left, neg_eq_zero, one_ne_zero,
            zero_eq_neg,
            OfNat.ofNat_ne_zero, and_self, not_false_eq_true, not_true_eq_false, and_false]
        next h =>
          split at a
          next h_1 =>
            simp_all only [Int.reduceNeg, not_and, Decidable.not_not, Point.mk.injEq, add_eq_left,
              one_ne_zero,
              zero_eq_neg, OfNat.ofNat_ne_zero, and_self, not_false_eq_true, not_true_eq_false,
                false_and]
          next
            h_1 =>
            simp_all only [Int.reduceNeg, not_and, Decidable.not_not, reduceCtorEq,
              IsEmpty.forall_iff, implies_true]
            tauto
      · split at a
        next h =>
          simp_all only [Int.reduceNeg, Point.mk.injEq, add_eq_left, neg_eq_zero, one_ne_zero,
            zero_eq_neg,
            OfNat.ofNat_ne_zero, and_self, not_false_eq_true, not_true_eq_false, and_false]
        next h =>
          split at a
          next h_1 =>
            simp_all only [Int.reduceNeg, not_and, Decidable.not_not, Point.mk.injEq, add_eq_left,
              one_ne_zero,
              zero_eq_neg, OfNat.ofNat_ne_zero, and_self, not_false_eq_true, not_true_eq_false,
                false_and]
          next
            h_1 =>
            simp_all only [Int.reduceNeg, not_and, Decidable.not_not, reduceCtorEq,
              IsEmpty.forall_iff, implies_true]
            tauto
  · clear x
    rcases h : s.aPos with ⟨x, y⟩
    simp [h] at h₁; subst h₁
    simp [Point.ext_iff, Point.forall_iff]
    grind only [cases Or]
  · split <;> simp_all [neg_eq_iff_eq_neg]

theorem aPos_y_lt_zero_of_cnd₀ (h : cnd₀ s) : s.aPos.y < 0 := by
  simp [cnd₀, getBorderPoints, getBorderPoint₀, getBorderPoint] at h ⊢
  split at h <;> linarith

theorem cnd₀_of_aPos_y_le_neg_6 (h : s.aPos.y ≤ -6) : cnd₀ s := by
  simp [cnd₀, getBorderPoints, getBorderPoint₀, getBorderPoint] at h ⊢
  split <;> linarith

theorem cnd₀_iff_cndComp₀ {s} : cnd₀ s ↔ cndComp₀ (ptsArr s (-2) 5) 0 (-s.aPos.y).toNat := by
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
  · rw [neg_eq_iff_eq_neg] at h₁
    simp [getBorderPoint]
    tauto
  nm h₂ h₃ h₄ h₅
  simp [h]
  split <;> nm x h₆
  any_goals
    replace h₇ : (-s.aPos.y).toNat = (((-s.aPos.y).toNat : ℕ) : ℤ); simp
    nth_rw 2 [h₆] at h₇
    rw [Int.toNat_eq_max, max_eq_left # by linarith, neg_eq_iff_eq_neg] at h₇
    simp [h₇] at *
  simpa

theorem cndComp₀_eq_cndComp₀_extract {arr : Array Bool} {offset d : ℕ} :
cndComp₀ arr offset d = cndComp₀ (arr.extract offset # offset + 5) 0 d := by
  simp only [cndComp₀, Bool.decide_and, Bool.decide_eq_true, Bool.decide_or, add_zero, ne_eq,
    decide_not, zero_add]; iterate rw [Array.getElem?_extract_add # by norm_num];; rfl

theorem cndComp₀_eq_cndComp₀_append {arr : Array Bool} {offset d n : ℕ} :
cndComp₀ arr offset d = cndComp₀ ⟨arr.1 ++ List.replicate n false⟩ offset d := by
  rcases arr with ⟨xs⟩
  simp only [cndComp₀, List.getElem?_toArray, Bool.decide_and, Bool.decide_eq_true, Bool.decide_or,
    ne_eq, decide_not, List.getD_getElem?_append_replicate]

theorem cndComp₀_eq_cndComp₀_min_6 {arr : Array Bool} {offset d : ℕ} :
cndComp₀ arr offset d = cndComp₀ arr offset (min 6 d) := by
  simp only [cndComp₀, Bool.decide_and, Bool.decide_eq_true, Bool.decide_or, ne_eq, decide_not]
  by_cases h : 6 ≤ d
  · rw [min_eq_left h]
    split <;> simp at h
    simp
    positivity
  push_neg at h
  rw [min_eq_right_of_lt h]

@[simp]
theorem ptsArr_eq_empty_iff {s z n} : ptsArr s z n = #[] ↔ n = 0 := by
  simp [ptsArr]

@[simp]
theorem ptsArr_zero {s z} : ptsArr s z 0 = #[] := rfl

theorem getBorderPoint_add {p n m} :
edge₀.getBorderPoint p (n + m) = edge₀.getBorderPoint p n + ⟨m, 0⟩ := by
  simp [getBorderPoint, add_assoc]

@[simp]
theorem extract_ptsArr {s z n i j} :
(ptsArr s z n).extract i j = ptsArr s (z + i) (min n j - i) := by
  rw [←Nat.sub_min_sub_right]
  by_cases h : j < i
  · rw [Array.extract_eq_empty_of_le # by omega]
    simp
    omega
  push_neg at h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  by_cases h : n < i
  · rw [show n - i = 0 by omega]
    simp; omega
  push_neg at h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  simp
  by_cases h : n < j
  · rw [min_eq_left_of_lt h]
    simp [ptsArr, add_assoc]
    simp [List.range_add]
    omega
  push_neg at h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h; clear h
  simp [ptsArr, add_assoc]
  simp [List.range_add]

theorem exi_aMove₀_of_dist_eq_one {p p' : PointZ} (h : p'.dist p = 1) :
∃ (m : Fin 8), aMove₀ p m = p' := by
  rcases p, p' with ⟨⟨x, y⟩, ⟨x', y'⟩⟩
  simp [Point.dist] at h
  simp_rw [max_eq_ite, abs_eq_ite] at h
  unfold aMove₀ aMove₀'
  split_ifs at h <;> nm h₁ h₂ h₃ <;> simp at *
  · by_cases h₄ : y' = y
    · use 4; simp; omega
    · use 7; simp; omega
  · use 6; simp; omega
  · by_cases h₄ : y' = y
    · use 3; simp; omega
    · use 5; simp; omega
  · use 5; simp; omega
  · use 2; simp; omega
  · use 1; simp; omega
  · use 0; simp; omega
  · omega

include hpw in
theorem exi_aMove₀_of_tr_eq_some {s' p} [hs : AState s]
(h : sys.tr s p = some s') : ∃ (m : Fin 8), aMove₀ s.aPos m = p := by
  rw [hs.tr_eq_some_iff] at h
  obtain ⟨⟨h₁, h₂, h₃⟩, rfl⟩ := h
  simp [hpw.1, ne_symm' h₁] at h₃
  exact exi_aMove₀_of_dist_eq_one h₃

theorem f₀_eq_of_f_eq_some {p} (h : edge₀.f s = some p) :
⟨s.aPos.x - 2 + f₀ (ptsArr s (-2) 5) 0 (-s.aPos.y).toNat, 0⟩ = p := by
  ext <;> dsimp
  rotate_left
  · symm
    obtain ⟨-, -, -, z, -, rfl⟩ := of_eq_some h
    simp [getBorderPoint]
  generalize ha : ptsArr s (-2) 5 = arr
  have H₁ : arr.size = 5; simp [←ha]
  have H₂ : ∀ {i : ℕ} (hi : i < 5 := by norm_num), arr[i]?.getD false =
    decide (edge₀.getBorderPoint s.aPos (i - 2) ∈ s.taken)
  · subst ha
    intro i hi
    rw [Array.getElem?_eq_getElem hi]
    simp [ptsArr]
    ring_nf
  simp only [f, f', dist_edge₀, getBorderPoint₀, decide_not, getBorderPoints, Nat.cast_one,
    Int.reduceNeg, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq,
    List.find?_cons', Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, ite_not,
    List.find?_nil, Bool.not_or, Bool.and_eq_true, ne_eq, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff', Option.guard_eq_some', Option.some.injEq, exists_const, ↓existsAndEq,
    and_true] at h
  simp only [f₀, zero_add, Nat.reduceLT, H₂, Nat.cast_ofNat, sub_self, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, Nat.one_lt_ofNat, Nat.cast_one, Int.reduceSub,
    Int.reduceNeg, ite_not, add_zero, Nat.ofNat_pos, CharP.cast_eq_zero, zero_sub, Bool.and_eq_true]
  split at h <;> nm x h₁ <;> try rw [neg_eq_iff_eq_neg] at h₁; simp [h₁]; clear H₂
  · simp [getBorderPoint] at h; rw [←h.1]
  · subst ha
    simp_all only [Int.reduceNeg, size_ptsArr]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    split
    next h =>
      simp_all only [Int.reduceNeg, ↓reduceIte]
      split
      next h_1 => simp_all only [Int.reduceNeg, true_or, ↓reduceIte, List.find?_nil, reduceCtorEq]
      next h_1 =>
        simp_all only [Int.reduceNeg, false_or]
        split at left
        next h_2 => simp_all only [Int.reduceNeg, List.find?_nil, reduceCtorEq]
        next
          h_2 =>
          simp_all only [Int.reduceNeg, decide_false, Bool.not_false, List.find?_cons_of_pos,
            Option.some.injEq,
            not_false_eq_true]
          subst left
          simp [getBorderPoint]
          ring_nf
    next h =>
      simp_all only [Int.reduceNeg, ↓reduceIte, Option.some.injEq, not_false_eq_true,
        sub_add_cancel]
      subst left
      simp [getBorderPoint]
  · subst ha
    simp_all only [Int.reduceNeg, size_ptsArr]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    split
    next h =>
      simp_all only [Int.reduceNeg, ↓reduceIte, Option.ite_none_left_eq_some, Option.some.injEq]
      obtain ⟨left, right_1⟩ := left
      subst right_1
      simp_all only [Int.reduceNeg, not_false_eq_true]
      simp [getBorderPoint]; ring_nf
    next h =>
      simp_all only [Int.reduceNeg, ↓reduceIte, Option.some.injEq, not_false_eq_true]
      subst left
      simp [getBorderPoint]; ring_nf
  · subst ha
    simp_all only [Int.reduceNeg, size_ptsArr]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    split
    next h =>
      simp_all only [Int.reduceNeg, not_false_eq_true, and_self, ↓reduceIte, Option.some.injEq,
        and_true]
      subst left
      simp [getBorderPoint]; ring_nf
    next
      h =>
      simp_all only [Int.reduceNeg, ↓reduceIte, Option.ite_none_right_eq_some, Option.some.injEq,
        not_and, Decidable.not_not]
      obtain ⟨left, right_1⟩ := left
      obtain ⟨left, right_2⟩ := left
      subst right_1
      simp_all only [Int.reduceNeg, not_false_eq_true]
      simp [getBorderPoint]; ring_nf
  · subst ha
    simp_all only [Int.reduceNeg, size_ptsArr]
    obtain ⟨left, right⟩ := h
    obtain ⟨left_1, right⟩ := right
    split
    next h =>
      simp_all only [Int.reduceNeg, ↓reduceIte]
      split
      next h_1 =>
        simp_all only [Int.reduceNeg, ↓reduceIte, Option.ite_none_left_eq_some, Option.some.injEq]
        obtain ⟨left, right_1⟩ := left
        subst right_1
        simp_all only [Int.reduceNeg, not_false_eq_true]
        simp [getBorderPoint]; ring_nf
      next h_1 =>
        simp_all only [Int.reduceNeg, ↓reduceIte, Option.some.injEq, not_false_eq_true]
        subst left
        simp [getBorderPoint]; ring_nf
    next h =>
      simp_all only [Int.reduceNeg, ↓reduceIte, Option.some.injEq, not_false_eq_true,
        sub_add_cancel]
      subst left
      simp [getBorderPoint]
  · simp at h

theorem aMove₀_dist_eq_one (p m) : (aMove₀ p m).dist p = 1 := by
  unfold aMove₀ aMove₀'; split <;> simp [Point.dist]

@[simp]
theorem le_one_add_aMove₀_x {p m} : p.x ≤ 1 + (aMove₀ p m).x := by
  unfold aMove₀ aMove₀'; split <;> simp <;> omega

@[simp]
theorem one_add_aMove₀_le_two_add_x {p m} : 1 + (aMove₀ p m).x ≤ 2 + p.x := by
  unfold aMove₀ aMove₀'; split <;> simp <;> omega

@[simp]
theorem f₀_lt_5 {arr offset d} : f₀ arr offset d < 5 := by
  simp only [f₀, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.ite_eq_false_iff, add_zero,
    Bool.and_eq_true]
  split <;> (try split_ifs) <;> simp

theorem ptsArr_eq_of_taken_eq {s s' : State} {z n} (h : s'.taken = s.taken) :
ptsArr s' z n = ptsArr s (z + s'.aPos.x - s.aPos.x) n := by
  unfold ptsArr
  simp only [h, getBorderPoint, dir_edge₀, instFactTrue_aP, dir_eq_of_down, offset_edge₀,
    List.pure_def, List.bind_eq_flatMap, List.flatMap_fn_singletonc, List.map_map,
    Function.comp_def', Array.mk.injEq, List.map_inj_left, List.mem_range, decide_eq_decide]
  ring_nf; simp

theorem ptsArr_eq_of_aPos_eq_and_taken_eq_insert.proof₁ {s s' : State} {p}
(h₁ : s'.taken = s.taken.insert p) (h₃ : ∃ (z : ℤ), |z| ≤ 2 ∧ edge₀.getBorderPoint s.aPos z = p) :
(p.x - s.aPos.x + 2).toNat < (ptsArr s (-2) 5).size := by
  obtain ⟨z, h₃, h₄⟩ := h₃
  simp [getBorderPoint] at h₄
  subst h₄
  simp
  rw [abs_le] at h₃
  omega

theorem ptsArr_eq_of_aPos_eq_and_taken_eq_insert {s s' : State} {p}
(h₂ : s'.aPos = s.aPos) (h₁ : s'.taken = s.taken.insert p)
(h₃ : ∃ (z : ℤ), |z| ≤ 2 ∧ edge₀.getBorderPoint s.aPos z = p) :
ptsArr s' (-2) 5 = (ptsArr s (-2) 5).set (p.x - s.aPos.x + 2).toNat true
(ptsArr_eq_of_aPos_eq_and_taken_eq_insert.proof₁ h₁ h₃) := by
  unfold ptsArr
  obtain ⟨z, h₃, h₄⟩ := h₃
  simp [getBorderPoint] at h₄ ⊢
  subst h₄
  simp only [h₁, h₂, Int.reduceNeg, Set'.mem_insert, Point.mk.injEq, add_right_inj, and_true,
    Bool.decide_or, add_sub_cancel_left]; clear h₁ h₂
  simp [List.range_succ]
  replace h₃ : z ∈ ({-2, -1, 0, 1, 2} : Set ℤ)
  · rw [abs_le] at h₃
    simp
    omega
  simp at h₃
  rcases h₃ with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem exi_fin_y_of_f_eq_some {p} (h : edge₀.f s = some p) : ∃ (y : Fin 6), s.aPos.y = -y := by
  simp only [f, f', dist_edge₀, decide_not, List.any_eq_true, decide_eq_true_eq, Int.reduceNeg,
    Bool.not_or, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    ne_eq, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff', Option.guard_eq_some',
    Option.some.injEq, exists_const, ↓existsAndEq, and_true] at h
  split at h <;> nm x h₁ <;> clear x <;> rw [neg_eq_iff_eq_neg] at h₁ <;> try rw [h₁]
  · use 5; simp
  · use 4; simp
  · use 3; simp
  · use 2; simp
  · use 1; simp
  · simp at h