import AP.Util.Nat
import AP.Util.Fintype
import AP.Util.Function

namespace Finset

theorem sum_eq_sum_of_fn_cong {S : Finset ℕ} {f g : ℕ → ℕ}
(h : ∀ i ∈ S, f i = g i) : ∑ x ∈ S, f x = ∑ x ∈ S, g x := by
  apply Finset.sum_equiv (e := Equiv.refl ℕ); simp; simpa

@[simp]
theorem sum_fn_set_eq {S : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} (ha : a ∈ S) :
∑ x ∈ S, fn_set a b f x =
∑ x ∈ S, f x + b - f a := by
  have h₁ : ∑ x ∈ S.erase a, f x + f a = ∑ x ∈ S, f x := by
    apply Finset.sum_erase_add; exact ha
  have h₂ : ∑ x ∈ S.erase a, fn_set a b f x + b =
  ∑ x ∈ S, fn_set a b f x := by
    convert Finset.sum_erase_add _ _ ha; simp
  rw [←h₁, ←h₂, Nat.add_add_sub_cancel]; clear h₁ h₂
  congr 1; apply sum_eq_sum_of_fn_cong
  intro i hi; simp at hi; simp [fn_set_eq, hi]

@[simp]
theorem sum_fn_swap_eq {S : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ}
(ha : a ∈ S) (hb : b ∈ S) :
∑ x ∈ S, fn_swap a b f x =
∑ x ∈ S, f x := by
  apply Finset.sum_equiv (e := fn_swap'_equiv a b) <;>
    intros <;> simp [fn_swap'] <;> aesop

def toSortedList {α : Type*} [h : LinearOrder α]
(s : Finset α) : List α := by
  apply s.val.lift # λ xs => xs.mergeSort
  intro xs ys hxy
  reduce at hxy
  dsimp
  generalize hx : xs.mergeSort (· ≤ ·) = xs'
  generalize hy : ys.mergeSort (· ≤ ·) = ys'
  obtain ⟨h₁, h₂⟩ : xs'.Sorted (· ≤ ·) ∧ ys'.Sorted (· ≤ ·) := by
    subst hx hy; constructor <;> apply List.sorted_mergeSort'
  have h₃ : xs'.Perm ys' := by
    subst hx hy
    trans xs
    · apply List.mergeSort_perm
    symm; trans ys
    · apply List.mergeSort_perm
    exact hxy.symm
  exact List.eq_of_perm_of_sorted h₃ h₁ h₂

noncomputable
def mkRaw {α β : Type*} (f : α → β) : Finset β := by
  classical
  by_cases h : Infinite α
  · exact {}
  simp at h
  replace h := Fintype.ofFinite α
  exact (Fintype.elems.toList.map f).toFinset

-----

@[simp]
theorem toSortedList_toFinset {α : Type*} [h : LinearOrder α]
{s : Finset α} : s.toSortedList.toFinset = s := by
  ext x
  unfold toSortedList
  rcases s with ⟨m, h₁⟩
  simp
  apply m.ind
  intro xs
  simp

def mkRaw_comp {α β : Type*} [Fintype α] [LinearOrder α] [DecidableEq β]
(f : α → β) : Finset β :=
  (Fintype.elems.toSortedList.map f).toFinset

@[simp]
theorem mem_toList_iff {α : Type*} {s : Finset α} {x} :
x ∈ s.toList ↔ x ∈ s := by
  classical
  simp [←List.mem_toFinset]

@[simp]
theorem mem_toSortedList_iff {α : Type*} [LinearOrder α] {s : Finset α} {x} :
x ∈ s.toSortedList ↔ x ∈ s := by simp [←List.mem_toFinset]

theorem mkRaw_eq {α β : Type*}
[ha : Fintype α] [DecidableEq α] [DecidableEq β] {f : α → β} :
mkRaw f = (Fintype.elems.toList.map f).toFinset := by
  simp [mkRaw]
  split_ifs with h₁
  · exfalso; exact ha.false
  ext x
  simp

@[simp]
theorem mem_mkRaw_iff {α β : Type*} [Fintype α]
{f : α → β} {b : β} : b ∈ mkRaw f ↔ ∃ a, f a = b := by
  classical
  simp [mkRaw_eq]

@[simp]
theorem mem_mkRaw_comp_iff {α β : Type*} [Fintype α] [LinearOrder α] [DecidableEq β]
{f : α → β} {b : β} : b ∈ mkRaw_comp f ↔ ∃ a, f a = b := by simp [mkRaw_comp]

@[simp]
theorem mkRaw_comp_eq_mkRaw {α β} [Fintype α] [LinearOrder α] [DecidableEq β]
{f : α → β} : mkRaw_comp f = mkRaw f := by ext x; simp

@[simp]
theorem mkRaw_const_of_nonempty {α β : Type*}
[Fintype α] [Nonempty α] [DecidableEq α] [DecidableEq β] {b : β} :
mkRaw (λ (_ : α) => b) = {b} := by ext x; simp [eq_comm]

@[simp]
theorem mkRaw_const_of_empty {α β : Type*}
[IsEmpty α] [DecidableEq β] {b : β} : mkRaw (λ (_ : α) => b) = {} := by
  ext x; simp

theorem mkRaw_fin_succ_eq_insert {α : Type*}
[ha : DecidableEq α] {n} {f : Fin (n + 1) → α} : mkRaw f =
insert (f ⟨n, by linarith⟩) (mkRaw # λ (⟨k, hk⟩ : Fin n) => f ⟨k, by linarith⟩) := by
  ext x
  simp
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hk
    rcases hk with hk | rfl
    · right
      use ⟨_, hk⟩
    simp
  rintro (rfl | ⟨⟨k, hk⟩, h₁⟩)
  · simp
  use ⟨k, by linarith⟩

theorem mkRaw_card_le {α β} [ha₁ : Fintype α] {f : α → β} :
(mkRaw f).card ≤ Fintype.card α := by
  apply Finset.card_le_card_of_surjOn f
  simp
  intro y
  simp

theorem mkRaw_toSet_eq {α β : Type*} [ha : Fintype α] {f : α → β} :
(mkRaw f).toSet = Set.range f := by ext x; simp

theorem card_eq_cardinal_mk_to_nat {α : Type*} {s : Finset α} :
s.card = (Cardinal.mk s).toNat := by simp

theorem card_eq_toSet_ncard {α : Type*} {s : Finset α} :
s.card = s.toSet.ncard := by simp

theorem image_toSet_eq {α β : Type*} [DecidableEq β] {s : Finset α} {f : α → β} :
f '' s.toSet = (s.image f).toSet := by
  symm; exact coe_image

theorem ncard_toSet {α : Type*} {s : Finset α} :
s.toSet.ncard = s.card := by simp

theorem sum_insert_eq_of_mem {α : Type*} [ha : DecidableEq α] {s : Finset α} {x}
{f : α → ℕ} (h₁ : x ∈ s) : ∑ i ∈ s, f i = ∑ i ∈ (s.erase x), f i := by
  sorry

#check 0 #exit

end Finset namespace Multiset

theorem card_eq_sum_count_of_subset {α : Type*} [ha : DecidableEq α]
{m₁ m₂ : Multiset α} (h₁ : m₁ ⊆ m₂) :
m₁.card = ∑ i ∈ m₁.toFinset ∪ m₂.toFinset, m₁.count i := by
  induction m₁ using Multiset.induction generalizing m₂ <;> simp
  nm x m₁ ih
  simp at h₁
  rcases h₁ with ⟨h₁, h₂⟩

#check 0 #exit

theorem eq_of_le_and_card_eq {α : Type*} {m₁ m₂ : Multiset α}
(h₁ : m₁ ≤ m₂) (h₂ : m₁.card = m₂.card) : m₁ = m₂ := by
  classical
  ext x
  apply le_antisymm # count_le_of_le x h₁

end Multiset namespace List

#check 0 #exit

theorem perm_of_nodup_and_subset_and_length_eq {α : Type*} {xs ys : List α}
(hx : xs.Nodup) (h₁ : xs.Subset ys)
(h₂ : xs.length = ys.length) : ys.Subset xs

theorem subperm_of_subperm_and_length_eq {α : Type*} {xs ys : List α}
(h₁ : xs <+~ ys) (h₂ : xs.length = ys.length) : ys <+~ xs := by
  generalize hm₁ : Multiset.ofList xs = m₁
  generalize hm₂ : Multiset.ofList ys = m₂
  replace h₁ : m₁ ≤ m₂ := by subst m₁ m₂; simpa
  replace h₂ : m₁.card = m₂.card := by subst m₁ m₂; simpa
  suffices m₂ ≤ m₁ by subst m₁ m₂; simp at this; exact this
  clear hm₁ hm₂

#check 0 #exit

theorem subset_of_nodup_and_subset_and_length_eq {α : Type*} {xs ys : List α}
(h₁ : xs.Nodup) (h₂ : xs ⊆ ys)
(h₃ : xs.length = ys.length) : ys ⊆ xs := by
  have h₄ := nodup_of_nodup_and_subset_and_length_eq h₁ h₂ h₃
  rw [subset_iff_subperm_of_nodup h₁] at h₂
  apply le_antisymmrw [subset_iff_subperm_of_nodup h₄]

end List namespace Finset