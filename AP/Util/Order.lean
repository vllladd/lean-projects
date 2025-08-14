import AP.Util.SetTheory

theorem max_right_eq_of_max_eq_and_ne {α : Type*} [LinearOrder α] {a b c : α}
(h₁ : max a b = c) (h₂ : a ≠ c) : b = c := by
  simp [max_eq_iff, h₂] at h₁; exact h₁.1

instance  (priority := low) leOfOrd' {α : Type*} [Ord α] : LE α :=
  LE.mk # λ a b => (compare a b).isLE

instance  (priority := low) ltOfOrd' {α : Type*} [Ord α] : LT α :=
  LT.mk # λ a b => (compare a b).isLT

instance (priority := low) minOfOrd' {α : Type*} [Ord α] : Min α :=
  Min.mk # λ a b => if (compare a b).isLE then a else b

instance (priority := low) maxOfOrd' {α : Type*} [Ord α] : Max α :=
  Max.mk # λ a b => if (compare a b).isLE then b else a

theorem Ord.le_def {α : Type*} [ha : Ord α] {a b : α} :
@LE.le α leOfOrd' a b ↔ (compare a b).isLE := by rfl

theorem Ord.lt_def {α : Type*} [ha : Ord α] {a b : α} :
@LT.lt α ltOfOrd' a b ↔ (compare a b).isLT := by rfl

instance {α : Type*} [ha : Ord α] : DecidableRel (@LT.lt α ltOfOrd') := by
  intro a b
  rw [Ord.lt_def]
  infer_instance

theorem compare_eq {α : Type*} [ha : LinearOrder α] {a b : α} :
compare a b = if a < b then Ordering.lt
else if a = b then Ordering.eq else Ordering.gt := by
  rw [ha.compare_eq_compareOfLessAndEq]; rfl

def Preorder.ofOrd {α : Type*} [ha : Ord α]
(h_refl : ∀ (a : α), a ≤ a)
(h_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c)
(h_lt : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬(b ≤ a)) :
Preorder α :=
  ⟨h_refl, h_trans, h_lt⟩

def PartialOrder.ofOrd {α : Type*} [ha : Ord α]
(h_refl : ∀ (a : α), a ≤ a)
(h_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c)
(h_lt : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬(b ≤ a))
(h_ant : ∀ (a b : α), a ≤ b → b ≤ a → a = b) :
PartialOrder α :=
  letI := Preorder.ofOrd h_refl h_trans h_lt
  ⟨h_ant⟩

def LinearOrder.ofOrd {α : Type*} [ha : Ord α]
(h_refl : ∀ (a : α), a ≤ a)
(h_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c)
(h_lt : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬(b ≤ a))
(h_ant : ∀ (a b : α), a ≤ b → b ≤ a → a = b)
(h_tot : ∀ (a b : α), a ≤ b ∨ b ≤ a) :
LinearOrder α := by
  letI := PartialOrder.ofOrd h_refl h_trans h_lt h_ant
  have h_eq : ∀ (a b : α), a = b ↔ (compare a b).isEq :=
    by
      intro a b
      cases h : compare a b <;> simp
      · rintro rfl
        replace h : a < a :=
          by
            rw [Ord.lt_def]
            rw [h]; rfl
        rw [h_lt] at h
        simp at h
      · have h₁ : a ≤ b :=
          by
            rw [Ord.le_def]; simp [h]
        apply h_ant
        · exact h₁
        by_contra h₂
        have h₃ := And.intro h₁ h₂
        rw [←h_lt] at h₃
        rw [Ord.lt_def] at h₃
        simp [h] at h₃
      rintro rfl
      specialize h_refl a
      rw [Ord.le_def] at h_refl
      simp [h] at h_refl
  letI : DecidableEq α := by
    intro a b
    rw [h_eq]
    infer_instance
  refine' ⟨h_tot, _, _, _, _, _, _⟩
  any_goals try first | infer_instance | intro a b; rfl
  intro a b
  unfold compareOfLessAndEq
  simp_rw [Ord.lt_def, h_eq]
  generalize compare a b = o
  cases o <;> rfl

def equiv_toLinearOrder_aux {α β : Type*}
[ha : LinearOrder α] (e : α ≃ β) : LinearOrder β := by
  let f := e.1
  let g := e.2
  have inj := e.bijective_invFun.1
  have gf : ∀ x, g (f x) = x := e.left_inv
  have eq_iff : ∀ x y, x = y ↔ g x = g y :=
    by
      intro x y
      constructor
      · rintro rfl; rfl
      · apply inj
  let h_ord : Ord β := ⟨λ x y => compare (g x) (g y)⟩
  apply LinearOrder.ofOrd
  · intro a
    rw [Ord.le_def]
    simp [h_ord, compare_eq]
  · intro a b c h₁ h₂
    rw [Ord.le_def] at h₁ h₂ ⊢
    simp [h_ord, compare_eq] at h₁ h₂ ⊢
    split_ifs at h₁ <;> simp at h₁ <;>
      split_ifs at h₂ <;> simp at h₂ <;>
      split_ifs <;> simp <;> nm h₃ h₄ h₅ h₆
    · apply h₅; exact gt_trans h₄ h₃
    · nm h₇
      simp [h₄] at h₃ h₇
      contradiction
    · nm h₇
      apply h₅
      simpa [h₃]
    · nm h₇ h₈
      simp [h₄, h₈] at h₆
  · intro a b
    simp_rw [Ord.le_def, Ord.lt_def]
    simp [h_ord, compare_eq]
    split_ifs <;> simp_all
    nm h₁ h₂ h₃;
    contrapose! h₂
    exact le_of_lt h₃
  · intro a b
    simp_rw [Ord.le_def]
    simp [h_ord, compare_eq]
    split_ifs <;> simp
    · nm h₁ h₂
      contrapose! h₁
      exact le_of_lt h₂
    · nm h₁ h₂ h₃
      exact inj h₃.symm
    · nm h₁ h₂ h₃
      exact inj h₂
    · nm h₁ h₂ h₃ h₄
      exact inj h₂
  · intro a b
    simp_rw [Ord.le_def]
    simp [h_ord, compare_eq]
    split_ifs <;> simp
    nm h₁ h₂ h₃ h₄
    apply h₁
    simp at h₃
    exact lt_of_le_of_ne h₃ h₂

def Equiv.toLinearOrder {α β : Type*}
[ha : LinearOrder α] (e : α ≃ β) : LinearOrder β := by
  let f := e.1
  let g := e.2
  have inj := e.bijective_invFun.1
  have gf : ∀ x, g (f x) = x := e.left_inv
  have eq_iff : ∀ x y, x = y ↔ g x = g y :=
    by
      intro x y
      constructor
      · rintro rfl; rfl
      · apply inj
  let h_ord : Ord β := ⟨λ x y => compare (g x) (g y)⟩
  let h₂ : Min β := ⟨λ x y => f # min (g x) (g y)⟩
  let h₃ : Max β := ⟨λ x y => f # max (g x) (g y)⟩
  let h₄ : LE β := ⟨λ x y => g x ≤ g y⟩
  let h₅ : LT β := ⟨λ x y => g x < g y⟩
  let h₆ : Preorder β :=
    by
      constructor
      · intro a
        rfl
      · intro a b c ha hb
        exact ha.trans hb
      · intro a b
        exact lt_iff_le_not_ge
  let h₇ : PartialOrder β :=
    by
      constructor
      intro a b
      intro ha hb
      exact inj # le_antisymm ha hb
  constructor
  · intro a b
    apply le_total
  · intro a b; apply inj
    change g (f # g a ⊓ g b) = g (if g a ≤ g b then a else b)
    rw [gf, apply_ite (f := g)]
    apply min_def
  · intro a b; apply inj
    change g (f # g a ⊔ g b) = g (if g a ≤ g b then b else a)
    rw [gf, apply_ite (f := g)]
    apply max_def
  · intro a b
    unfold compareOfLessAndEq
    simp only [eq_iff]
    apply LinearOrder.compare_eq_compareOfLessAndEq
  · intro a b
    rw [eq_iff]
    infer_instance
  · intro a b
    change Decidable # g a < g b
    infer_instance

example : @equiv_toLinearOrder_aux = @Equiv.toLinearOrder := by
  unfold equiv_toLinearOrder_aux Equiv.toLinearOrder
  ext α β ha e x y
  let g := e.invFun
  let h_ord : Ord β := ⟨λ x y => compare (g x) (g y)⟩
  rw [Ord.le_def]
  dsimp
  rw [compare_eq]
  split_ifs with h₁ h₂ <;> simp
  · exact le_of_lt h₁
  · simp [h₂]
  · contrapose! h₂
    simp at h₁
    exact le_antisymm h₂ h₁

theorem false_of_lt_and_lt {α : Type*} [ha : LinearOrder α] {a b : α}
(h₁ : a < b) (h₂ : b < a) : False := by
  have h₃ := h₁.trans h₂
  rw [lt_self_iff_false] at h₃
  exact h₃

@[simp]
theorem not_lt_and_lt {α : Type*} [ha : LinearOrder α] {a b : α} : ¬(a < b ∧ b < a) := by
  rintro ⟨h₁, h₂⟩; exact false_of_lt_and_lt h₁ h₂

theorem max_eq_ite {α : Type*} [ha : LinearOrder α] {a b : α} :
max a b = if b ≤ a then a else b := max_def' _ _

theorem abs_add_le_max_add_max {α : Type*}
[ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : IsOrderedAddMonoid α]
{a b : α} : |a + b| ≤ max |a| b + max a |b| := by
  apply (abs_add _ _).trans; apply add_le_add <;> simp