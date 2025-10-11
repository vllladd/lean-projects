import AP.Util.Real
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
(a b x y : α) : |a + b| ≤ max |a| x + max y |b| := by
  apply (abs_add _ _).trans; apply add_le_add <;> simp

class InjectiveOfNat (α : Type*) [ha : Semiring α] : Prop where
  h : Function.Injective (λ (n : ℕ) => (OfNat.ofNat n : α))

instance : InjectiveOfNat ℕ := by
  constructor; intro n m h; dsimp at h
  by_contra! h₁
  wlog hm : m < n with ih
  · simp at hm; apply ih h.symm (ne_symm' h₁) # Nat.lt_of_le_of_ne hm h₁
  clear h₁
  cases n; simp at hm; nm n
  cases n
  · simp at hm
    subst hm
    cases h
  nm n
  change n + 2 = _ at h
  iterate 2 cases m; cases h; nm m
  change _ = m + 2 at h
  simp at h
  simp [h] at hm

instance : InjectiveOfNat ℤ := by
  constructor; intro n m h; dsimp at h
  by_contra! h₁
  wlog hm : m < n with ih
  · simp at hm; apply ih h.symm (ne_symm' h₁) # Nat.lt_of_le_of_ne hm h₁
  clear h₁
  cases n; simp at hm; nm n
  cases n
  · simp at hm
    subst hm
    cases h
  nm n
  change (n : ℤ) + 2 = _ at h
  iterate 2 cases m; cases h; nm m
  change _ = (m : ℤ) + 2 at h
  simp at h
  simp [h] at hm

instance : InjectiveOfNat ℝ := by
  constructor; intro n m h; simp [Real.ofNat_eq] at h; exact h

@[simp]
theorem add_self_eq_zero_iff {α : Type*}
[ha₂ : Ring α] [ha₄ : NoZeroDivisors α] [ha₅ : InjectiveOfNat α]
{a : α} : a + a = 0 ↔ a = 0 := by
  rw [←mul_two, mul_eq_zero]; simp; intro h
  change OfNat.ofNat 2 = OfNat.ofNat 0 at h
  replace h := ha₅.h h; simp at h

class LocallyFiniteOrderList (α : Type*) extends LinearOrder α where
  listIcc : α → α → List α
  sorted_listIcc : ∀ {a b}, (listIcc a b).Sorted (· < ·)
  mem_listIcc : ∀ {a b x}, x ∈ listIcc a b ↔ a ≤ x ∧ x ≤ b

instance : LocallyFiniteOrderList ℕ := by
  use λ a b => List.range (b + 1 - a) |>.map (a + ·)
  · intro a b; simp; apply List.sorted_lt_range
  · intro a b x; simp; exact ⟨by omega, λ _ => ⟨x - a, by omega⟩⟩

instance : LocallyFiniteOrderList ℤ := by
  use λ a b => List.range (b + 1 - a).toNat |>.map (a + ·)
  · intro a b; simp; apply List.sorted_lt_range
  · intro a b x; simp; exact ⟨by omega, λ _ => ⟨x - a |>.toNat, by omega⟩⟩

namespace List

variable {α : Type*} [ha : LocallyFiniteOrderList α]

def icc : α → α → List α := ha.listIcc

@[simp]
theorem sorted_lt_icc {a b : α} :
(icc a b).Sorted (· < ·) := ha.sorted_listIcc

@[simp]
theorem sorted_le_icc {a b : α} :
(icc a b).Sorted (· ≤ ·) := sorted_le_of_sorted_lt ha.sorted_listIcc

@[simp]
theorem mem_icc {a b x : α} :
x ∈ icc a b ↔ a ≤ x ∧ x ≤ b := ha.mem_listIcc

@[simp]
theorem icc_eq_nil_iff {a b : α} : icc a b = [] ↔ b < a := by
  simp [eq_nil_iff_forall_not_mem]; constructor
  · intro h; by_contra! h₁; specialize h _ h₁; simp at h
  · intro h₁ c h₂; exact lt_of_lt_of_le h₁ h₂

end List

variable {α : Type*}
variable [ha₁ : LinearOrder α] [ha₂ : Ring α]
variable [ha₃ : IsOrderedAddMonoid α] [ha₄ : ZeroLEOneClass α] [ha₅ : NeZero (1 : α)]

@[simp]
theorem min_sub_one_lt_left {a b : α} : min a b - 1 < a :=
  lt_of_le_of_lt' (min_le_left _ _) (sub_one_lt _)

@[simp]
theorem min_sub_one_lt_right {a b : α} : min a b - 1 < b :=
  lt_of_le_of_lt' (min_le_right _ _) (sub_one_lt _)

@[simp]
theorem left_lt_max_add_one {a b : α} : a < max a b + 1 :=
  lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)

@[simp]
theorem right_lt_max_add_one {a b : α} : b < max a b + 1 :=
  lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)

theorem min_eq_ite {α : Type*} [ha : LinearOrder α] {x y : α} :
min x y = if x ≤ y then x else y := by
  split_ifs with h₁; exact min_eq_left h₁; push_neg at h₁; exact min_eq_right_of_lt h₁

theorem abs_eq_ite {α : Type*} [ha₁ : LinearOrder α]
[hs₂ : AddGroup α] [ha₃ : AddLeftMono α] {x : α} :
|x| = if 0 ≤ x then x else -x := by
  split_ifs with h; exact abs_of_nonneg h; simp at h; exact abs_of_neg h

theorem bddBelow_range_of_forall_le {ι α : Type*} [ha : LinearOrder α]
{f : ι → α} (x) (h : ∀ i, x ≤ f i) : BddBelow (Set.range f) := by
  use x; simpa [lowerBounds]

theorem bddAbove_range_of_forall_le {ι α : Type*} [ha : LinearOrder α]
{f : ι → α} (x) (h : ∀ i, f i ≤ x) : BddAbove (Set.range f) := by
  use x; simpa [upperBounds]

theorem bddBelow_range {ι α : Type*} [ha : LinearOrder α] {f : ι → α} :
BddBelow (Set.range f) ↔ ∃ x, ∀ i, x ≤ f i := by
  constructor
  · intro h; rcases h with ⟨x, h⟩; simp [lowerBounds] at h; use x
  · rintro ⟨x, h⟩; exact bddBelow_range_of_forall_le x h

theorem bddAbove_range {ι α : Type*} [ha : LinearOrder α] {f : ι → α} :
BddAbove (Set.range f) ↔ ∃ x, ∀ i, f i ≤ x := by
  constructor
  · intro h; rcases h with ⟨x, h⟩; simp [upperBounds] at h; use x
  · rintro ⟨x, h⟩; exact bddAbove_range_of_forall_le x h

theorem bddBelow_range_neg {ι α : Type*} [ha₁ : LinearOrder α] [ha₂ : Ring α]
[ha₃ : AddLeftMono α] [ha₄ : AddRightMono α] {f : ι → α} :
BddBelow (Set.range (-f)) ↔ BddAbove (Set.range f) := by
  simp [bddBelow_range, bddAbove_range]
  constructor <;> rintro ⟨x, hx⟩ <;> use -x <;> intro i <;> specialize hx i
  · rwa [←neg_neg # f i, neg_le_neg_iff]
  · rwa [neg_le_neg_iff]

theorem bddAbove_range_neg {ι α : Type*} [ha₁ : LinearOrder α] [ha₂ : Ring α]
[ha₃ : AddLeftMono α] [ha₄ : AddRightMono α] {f : ι → α} :
BddAbove (Set.range (-f)) ↔ BddBelow (Set.range f) := by
  nth_rw 2 [←neg_neg f]; rw [bddBelow_range_neg]

theorem le_of_le_min_left {α : Type*} [ha₁ : LinearOrder α]
{a b c : α} (h : a ≤ min b c) : a ≤ b := by
  rw [le_inf_iff] at h; exact h.1

theorem le_of_le_min_right {α : Type*} [ha₁ : LinearOrder α]
{a b c : α} (h : a ≤ min b c) : a ≤ c := by
  rw [le_inf_iff] at h; exact h.2

section

variable {α : Type*} [ha₁ : DecidableEq α] [ha₂ : Fintype α]

noncomputable
def fintypeIdx (x : α) : ℕ :=
  Finset.univ.toList.idxOf x

@[simp]
theorem fintypeIdx_eq_iff {x y : α} : fintypeIdx x = fintypeIdx y ↔ x = y := by
  symm; constructor; rintro rfl; rfl; intro h; unfold fintypeIdx at h
  rwa [List.idxOf_inj] at h <;> simp

open Classical in noncomputable
def fintypeToLinearOrder : LinearOrder α where
  le a b := fintypeIdx a ≤ fintypeIdx b
  le_refl a := by rfl
  le_trans a b c h₁ h₂ := h₁.trans h₂
  le_antisymm a b h₁ h₂ := by
    have h₃ := le_antisymm h₁ h₂
    simp at h₃; exact h₃
  le_total a b := by apply le_total
  toDecidableLE := by infer_instance

end

theorem abs_sub_lt_iff' {x y z : ℝ} : |x - y| < z ↔ y - z < x ∧ x < y + z := by
  rw [abs_sub_lt_iff]; constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith