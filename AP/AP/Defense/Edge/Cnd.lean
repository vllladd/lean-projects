import AP.AP.Defense.Edge.Symmetry

namespace AP.Edge

variable {e e₁ e₂ : Edge}
variable {s : State} [hpw : Fact # s.pw = 1]
omit hpw

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

def ptsArr (s : State) (start : ℤ) (len : ℕ) : Array Bool :=
  ⟨List.range len |>.map # λ i => edge₀.getBorderPoint s.aPos (start + i) ∈ s.taken⟩

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