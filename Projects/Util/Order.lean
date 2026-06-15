import Projects.Util.Real
import Projects.Util.SetTheory

import Mathlib.SetTheory.Cardinal.Order

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

@[reducible]
def Preorder.ofOrd {α : Type*} [ha : Ord α]
(h_refl : ∀ (a : α), a ≤ a)
(h_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c)
(h_lt : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬(b ≤ a)) :
Preorder α :=
  ⟨h_refl, h_trans, h_lt⟩

@[reducible]
def PartialOrder.ofOrd {α : Type*} [ha : Ord α]
(h_refl : ∀ (a : α), a ≤ a)
(h_trans : ∀ (a b c : α), a ≤ b → b ≤ c → a ≤ c)
(h_lt : ∀ (a b : α), a < b ↔ a ≤ b ∧ ¬(b ≤ a))
(h_ant : ∀ (a b : α), a ≤ b → b ≤ a → a = b) :
PartialOrder α :=
  letI := Preorder.ofOrd h_refl h_trans h_lt
  ⟨h_ant⟩

@[reducible]
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

theorem isLe_compare_iff_le {α : Type*} [ha : LinearOrder α] {x y : α} :
(compare x y).isLE = true ↔ x ≤ y := by
  rw [←Ord.le_def]
  cases ha
  nm hpo min' max' ord' h_tot dec_le dec_eq dec_lt h_min h_max h₁
  cases hpo
  nm hp h₂
  cases hp
  nm le lt h_refl h_trans h₃
  rcases le with ⟨le⟩
  rcases lt with ⟨lt⟩
  change ∀ a b, le a b → le b a → a = b at h₂
  change ∀ a b, lt a b ↔ le a b ∧ ¬le b a at h₃
  congr!
  clear x y
  unfold leOfOrd' instDistribLatticeOfLinearOrder Lattice.toSemilatticeInf Preorder.toLE
    PartialOrder.toPreorder SemilatticeInf.toPartialOrder SemilatticeSup.toPartialOrder
    Lattice.toSemilatticeSup LinearOrder.toLattice
  dsimp
  congr!; nm x y
  rw [h₁]
  unfold compareOfLessAndEq
  split_ifs with H₁ H₂
  · simp
    change lt x y at H₁
    rw [h₃] at H₁
    exact H₁.1
  · subst H₂
    simp
    apply h_refl
  · change ¬lt x y at H₁
    simp
    contrapose! H₁
    rw [h₃]
    use H₁
    contrapose! H₂
    exact h₂ x y H₁ H₂

theorem isLt_compare_iff_lt {α : Type*} [ha : LinearOrder α] {x y : α} :
(compare x y).isLT = true ↔ x < y := by
  rw [←Ord.lt_def]
  cases ha
  nm hpo min' max' ord' h_tot dec_le dec_eq dec_lt h_min h_max h₁
  cases hpo
  nm hp h₂
  cases hp
  nm le lt h_refl h_trans h₃
  rcases le with ⟨le⟩
  rcases lt with ⟨lt⟩
  change ∀ a b, le a b → le b a → a = b at h₂
  change ∀ a b, lt a b ↔ le a b ∧ ¬le b a at h₃
  congr!
  clear x y
  unfold ltOfOrd' instDistribLatticeOfLinearOrder Lattice.toSemilatticeInf Preorder.toLT
    PartialOrder.toPreorder SemilatticeInf.toPartialOrder SemilatticeSup.toPartialOrder
    Lattice.toSemilatticeSup LinearOrder.toLattice
  dsimp
  congr!; nm x y
  rw [h₁]
  unfold compareOfLessAndEq
  split_ifs with H₁ H₂
  · simp
    exact H₁
  · subst H₂
    simp
    exact H₁
  · change ¬lt x y at H₁
    simp
    exact H₁

theorem instDistribLatticeOfLinearOrder_toSemilatticeInf_toLE_eq {α : Type*} [ha : LinearOrder α] :
(@instDistribLatticeOfLinearOrder α ha).toSemilatticeInf.toLE = ha.toLE := rfl

@[reducible]
def equivToLinearOrderAux {α β : Type*}
[ha : LinearOrder α] (e : α ≃ β) : LinearOrder β := by
  let f := e.1
  let g := e.2
  have inj := e.bijective_invFun.1
  have gf : ∀ x, g (f x) = x := e.left_inv
  have eq_iff : ∀ x y, x = y ↔ g x = g y
  · intro x y; constructor
    · rintro rfl; rfl
    · apply inj
  let h_ord : Ord β := ⟨λ x y => compare (g x) (g y)⟩
  apply LinearOrder.ofOrd
  · intro a
    rw [Ord.le_def]
    subst h_ord
    simp
  · intro a b c h₁ h₂
    rw [Ord.le_def] at h₁ h₂ ⊢
    subst h_ord
    simp at h₁ h₂ ⊢
    simp only [isLe_compare_iff_le] at h₁ h₂ ⊢
    exact h₁.trans h₂
  · intro a b
    simp_rw [Ord.le_def, Ord.lt_def]
    subst h_ord
    simp [-Ordering.isLT_iff_eq_lt, isLe_compare_iff_le, isLt_compare_iff_lt]
    exact le_of_lt
  · intro a b
    simp_rw [Ord.le_def]
    subst h_ord
    simp [isLe_compare_iff_le, eq_iff]
  · intro a b
    simp_rw [Ord.le_def]
    subst h_ord
    simp [isLe_compare_iff_le]

theorem min_def₁ {α : Type*} [ha : LinearOrder α] :
min (α := α) = λ x y => if x ≤ y then x else y := by
  grind

theorem max_def₁ {α : Type*} [ha : LinearOrder α] :
max (α := α) = λ x y => if x ≤ y then y else x := by
  grind

@[reducible]
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
      intro a b ha hb
      exact inj # le_antisymm ha hb
  constructor
  · intro a b
    apply le_total
  · intro a b; apply inj
    change g (f # g a ⊓ g b) = g (if g a ≤ g b then a else b)
    rw [gf, apply_ite (f := g)]
    simp [min_def₁]
  · intro a b; apply inj
    change g (f # g a ⊔ g b) = g (if g a ≤ g b then b else a)
    rw [gf, apply_ite (f := g)]
    simp [max_def₁]
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

theorem equivToLinearOrderAux_eq : @equivToLinearOrderAux = @Equiv.toLinearOrder := by
  unfold equivToLinearOrderAux Equiv.toLinearOrder; ext
  change _ = _ ↔ _; simp; rw [isLe_compare_iff_le]; rfl

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
  apply (abs_add_le _ _).trans; apply add_le_add <;> simp

theorem nonneg_of_abs_le {α : Type*} {a b : α}
[ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : IsOrderedAddMonoid α]
(h : |a| ≤ b) : 0 ≤ b := h.trans' # abs_nonneg _

theorem pos_of_abs_lt {α : Type*} {a b : α}
[ha₁ : LinearOrder α] [ha₂ : Ring α] [ha₃ : IsOrderedAddMonoid α]
(h : |a| < b) : 0 < b := lt_of_le_of_lt (abs_nonneg _) h

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
  sortedLT_listIcc : ∀ {a b}, listIcc a b |>.SortedLT
  mem_listIcc : ∀ {a b x}, x ∈ listIcc a b ↔ a ≤ x ∧ x ≤ b

instance : LocallyFiniteOrderList ℕ := by
  use λ a b => List.range (b + 1 - a) |>.map (a + ·)
  · intro a b; simp [List.sortedLT_iff_pairwise]; apply List.pairwise_lt_range
  · intro a b x; simp; exact ⟨by omega, λ _ => ⟨x - a, by omega⟩⟩

instance : LocallyFiniteOrderList ℤ := by
  use λ a b => List.range (b + 1 - a).toNat |>.map (a + ·)
  · intro a b; simp [List.sortedLT_iff_pairwise]; apply List.pairwise_lt_range
  · intro a b x; simp; exact ⟨by omega, λ _ => ⟨x - a |>.toNat, by omega⟩⟩

namespace List

variable {α : Type*} [ha : LocallyFiniteOrderList α]

def icc : α → α → List α :=
  ha.listIcc

@[simp]
theorem sortedLT_icc {a b : α} : (icc a b).SortedLT :=
  ha.sortedLT_listIcc

@[simp]
theorem sortedLE_icc {a b : α} : (icc a b).SortedLE :=
  sortedLT_icc.sortedLE

@[simp]
theorem mem_icc {a b x : α} :
x ∈ icc a b ↔ a ≤ x ∧ x ≤ b := ha.mem_listIcc

@[simp]
theorem icc_eq_nil_iff {a b : α} : icc a b = [] ↔ b < a := by
  simp [eq_nil_iff_forall_not_mem]; constructor
  · intro h; by_contra! h₁; specialize h _ h₁; simp at h
  · intro h₁ c h₂; exact lt_of_lt_of_le h₁ h₂

@[simp]
theorem nodup_icc {x y : α} : (icc x y).Nodup :=
  sortedLT_icc.nodup

@[simp]
theorem length_icc_int_nat {z : ℤ} {a b : ℕ} :
(icc (z - a) (z + b)).length = a + b + 1 := by
  unfold instLocallyFiniteOrderListInt; simp [icc]; omega

theorem icc_eq_range {n m} (h : n ≤ m) : icc n m = (range (m - n + 1)).map (n + ·) := by
  change (range _).map _ = _; rw [Nat.add_one_sub h]

theorem icc_split (k : ℕ) {n m} (h₁ : n ≤ k) (h₂ : k < m) :
icc n m = icc n k ++ icc (k + 1) m := by
  rw [icc_eq_range (by omega), icc_eq_range h₁, icc_eq_range # by omega]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h₂; clear h₂
  rw [show n + k + m + 1 - n + 1 = m + k + 2 by omega]
  rw [show n + k - n + 1 = k + 1 by omega]
  rw [show n + k + m + 1 - (n + k + 1) = m by omega]
  rw [List.ext_getElem_iff]
  split_ands <;> simp; omega
  intro i h₁ h₂
  rw [getElem_append]
  simp; omega

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
  split_ifs with h₁; exact min_eq_left h₁; push Not at h₁; exact min_eq_right_of_lt h₁

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

section

variable {α : Type*} [ha₁ : DecidableEq α] [ha₂ : Fintype α]

noncomputable
def fintypeIdx (x : α) : ℕ :=
  Finset.univ.toList.idxOf x

@[simp]
theorem fintypeIdx_eq_iff {x y : α} : fintypeIdx x = fintypeIdx y ↔ x = y := by
  symm; constructor; rintro rfl; rfl; intro h; unfold fintypeIdx at h
  rwa [List.idxOf_inj] at h; simp

open Classical in @[reducible] noncomputable
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

section

variable {α : Type*} [LinearOrder α] [NormedField α] [IsStrictOrderedRing α]

theorem abs_sub_lt_trans {a c e : α} (b : α)
(h : |a - b| + |b - c| < e) : |a - c| < e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_le_trans {a c e : α} (b : α)
(h : |a - b| + |b - c| ≤ e) : |a - c| ≤ e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_lt_trans_half {a c e : α} (b : α)
(h₁ : |a - b| < e / 2) (h₂ : |b - c| < e / 2) : |a - c| < e := by
  linarith [abs_sub_le a b c]

theorem abs_sub_le_trans_half {a c e : α} (b : α)
(h₁ : |a - b| ≤ e / 2) (h₂ : |b - c| ≤ e / 2) : |a - c| ≤ e := by
  linarith [abs_sub_le a b c]

end

section

variable {α : Type*}

structure LeCnd (le : α → α → Prop) : Prop where
  refl : ∀ x, le x x
  trans : ∀ x y z, le x y → le y z → le x z
  antisymm : ∀ x y, le x y → le y x → x = y
  total : ∀ x y, le x y ∨ le y x

theorem exi_leCnd : ∃ le, @LeCnd α le := by
  obtain ⟨lin, h⟩ := @exists_wellFoundedLT α
  use (· ≤ ·)
  constructor
  · simp
  · intro x y z h₁ h₂
    exact h₁.trans h₂
  · intro x y; exact le_antisymm
  · exact le_total

def leClassical : α → α → Prop :=
  τ x, LeCnd x

theorem leCnd_leClassical : LeCnd # @leClassical α :=
  τ_spec exi_leCnd

open Classical in @[reducible] noncomputable
def linearOrderClassical : LinearOrder α where
  le := leClassical
  le_refl := leCnd_leClassical.refl
  le_trans := leCnd_leClassical.trans
  le_antisymm := leCnd_leClassical.antisymm
  le_total := leCnd_leClassical.total
  toDecidableLE := inferInstance

noncomputable
instance (priority := low) [∀ P, Decidable P] : LinearOrder α :=
  linearOrderClassical

end

theorem le_congr {α : Type*} [ha : LinearOrder α] {a b c d : α}
(h₁ : a = c) (h₂ : b = d) : a ≤ b ↔ c ≤ d := by
  rw [h₁, h₂]

section

variable {α : Type*}
variable [ha : CompleteLattice α]

theorem exists_not_le_of_sInf_not_mem {s : Set α} {x : α}
(h : sInf s ∉ s) (hx : x ∈ s) : ∃ y ∈ s, ¬(x ≤ y) := by
  contrapose! h; have : sInf s = x
  apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
  all_goals grind

theorem exists_not_le_of_sSup_not_mem {s : Set α} {x : α}
(h : sSup s ∉ s) (hx : x ∈ s) : ∃ y ∈ s, ¬(y ≤ x) := by
  contrapose! h; have : sSup s = x
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  all_goals grind

@[simp]
theorem sInf_mem_iff {s : Set α} : sInf s ∈ s ↔ ∃ x ∈ s, ∀ y ∈ s, x ≤ y := by
  constructor
  · intro h; use sInf s, h; intro y hy; exact sInf_le hy
  · rintro ⟨x, hx, h⟩; contrapose! h; exact exists_not_le_of_sInf_not_mem h hx

@[simp]
theorem sSup_mem_iff {s : Set α} : sSup s ∈ s ↔ ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  constructor
  · intro h; use sSup s, h; intro y hy; exact le_sSup hy
  · rintro ⟨x, hx, h⟩; contrapose! h; exact exists_not_le_of_sSup_not_mem h hx

end

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

theorem eq_of_sortedLE_and_perm [ha : LinearOrder α]
(h₁ : xs.SortedLE) (h₂ : ys.SortedLE) (h₃ : xs ~ ys) : xs = ys := by
  rw [sortedLE_iff_pairwise] at h₁ h₂; apply eq_of_perm_of_pairwise h₃ h₁ h₂ <;> simp

end List