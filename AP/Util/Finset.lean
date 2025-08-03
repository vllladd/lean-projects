import AP.Util.Nat
import AP.Util.Fintype
import AP.Util.Function

namespace Finset

theorem sum_eq_sum_of_fn_cong {α : Type*} {S : Finset α} {f g : α → ℕ}
(h : ∀ i ∈ S, f i = g i) : ∑ x ∈ S, f x = ∑ x ∈ S, g x := by
  apply Finset.sum_equiv (e := Equiv.refl α); simp; simpa

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

theorem sum_eq_add_sum_erase_of_mem {α : Type*} [ha : DecidableEq α]
{s : Finset α} {x} {f : α → ℕ} (h : x ∈ s) :
∑ i ∈ s, f i = f x + ∑ i ∈ s.erase x, f i := by
  rwa [add_sum_erase]

theorem eq_of_sum_eq_sum_and_forall_le {α : Type*} {s : Finset α}
{f g : α → ℕ} (h₁ : ∑ i ∈ s, f i = ∑ i ∈ s, g i)
(h₂ : ∀ i ∈ s, f i ≤ g i) {i} (h₃ : i ∈ s) : f i = g i := by
  classical
  apply le_antisymm # h₂ i h₃
  obtain ⟨r, hr⟩ : ∃ (r : α → ℕ), ∀ i ∈ s, g i = f i + r i :=
    by
      clear! i
      let p := λ i k => f i + k = g i
      use λ i => Classical.epsilon # p i
      intro i h₃
      specialize h₂ i h₃
      have h₄ := Classical.epsilon_spec (p := p i)
      specialize h₄ _
      · simp [p]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h₂
        simp [hk]
      simp [p] at h₄ ⊢
      rw [h₄]
  nth_rw 2 [sum_eq_sum_of_fn_cong (g := λ i => f i + r i)] at h₁
  rotate_left; exact hr
  simp [sum_add_distrib] at h₁
  specialize hr i h₃
  rw [hr]
  simp
  exact h₁ i h₃

end Finset namespace Multiset

theorem card_eq_sum_count_of_subset {α : Type*} [ha : DecidableEq α]
{m₁ m₂ : Multiset α} (h₁ : m₁ ⊆ m₂) :
m₁.card = ∑ i ∈ m₁.toFinset ∪ m₂.toFinset, m₁.count i := by
  induction m₁ using Multiset.induction generalizing m₂ <;> simp
  nm x m₁ ih
  simp at h₁
  rcases h₁ with ⟨h₁, h₂⟩
  rw [Finset.insert_eq_of_mem # by simp [h₁]]
  rw [ih h₂]
  clear! ih
  generalize hs : m₁.toFinset ∪ m₂.toFinset = s
  have h₃ : x ∈ s :=
    by
      subst hs
      simp [h₁]
  simp [Finset.sum_eq_add_sum_erase_of_mem h₃]
  nth_rw 2 [Finset.sum_eq_sum_of_fn_cong (g := m₁.count)]
  rotate_left
  · rintro y hy
    simp at hy
    rcases hy with ⟨h₄, h₅⟩
    rw [count_cons_of_ne h₄]
  ring_nf

@[simp]
theorem subset_add_left' {α : Type*} {m₁ m₂ : Multiset α} :
m₁ ⊆ m₁ + m₂ := subset_add_left

@[simp]
theorem subset_add_right' {α : Type*} {m₁ m₂ : Multiset α} :
m₁ ⊆ m₂ + m₁ := subset_add_right

theorem eq_of_le_and_card_eq {α : Type*} {m₁ m₂ : Multiset α}
(h₁ : m₁ ≤ m₂) (h₂ : m₁.card = m₂.card) : m₁ = m₂ := by
  classical
  ext x
  have h₃ := subset_of_le h₁
  rw [card_eq_sum_count_of_subset h₃] at h₂
  rw [le_iff_count] at h₁
  have h₄ : m₂ ⊆ m₁ + m₂ := by simp
  rw [card_eq_sum_count_of_subset h₄] at h₂
  rw [toFinset_add] at h₂
  nth_rw 3 [Finset.union_comm] at h₂
  rw [Finset.union_left_idem] at h₂
  nth_rw 2 [Finset.union_comm] at h₂
  by_cases hx : x ∉ m₂
  · rw [count_eq_zero_of_notMem hx]
    rw [count_eq_zero_of_notMem]
    contrapose! hx
    exact h₃ hx
  simp at hx
  clear h₄
  apply Finset.eq_of_sum_eq_sum_and_forall_le h₂
  rotate_left
  · simp [hx]
  simp
  intro y hy
  apply h₁

theorem eq_of_le_and_le {α : Type*} {m₁ m₂ : Multiset α}
(h₁ : m₁ ≤ m₂) (h₂ : m₂ ≤ m₁) : m₁ = m₂ := by
  apply eq_of_le_and_card_eq h₁
  apply le_antisymm
  · exact card_le_card h₁
  · exact card_le_card h₂

theorem eq_of_nodup_and_subset_and_subset {α : Type*} {m₁ m₂ : Multiset α}
(h₁ : m₁.Nodup) (h₂ : m₂.Nodup) (h₃ : m₁ ⊆ m₂) (h₄ : m₂ ⊆ m₁) : m₁ = m₂ := by
  rw [←le_iff_subset h₁] at h₃
  rw [←le_iff_subset h₂] at h₄
  exact eq_of_le_and_le h₃ h₄

end Multiset namespace List

theorem subperm_of_subperm_and_length_eq {α : Type*} {xs ys : List α}
(h₁ : xs <+~ ys) (h₂ : xs.length = ys.length) : ys <+~ xs := by
  generalize hm₁ : Multiset.ofList xs = m₁
  generalize hm₂ : Multiset.ofList ys = m₂
  replace h₁ : m₁ ≤ m₂ := by subst m₁ m₂; simpa
  replace h₂ : m₁.card = m₂.card := by subst m₁ m₂; simpa
  suffices m₂ ≤ m₁ by subst m₁ m₂; simp at this; exact this
  clear hm₁ hm₂
  apply le_of_eq; symm
  exact Multiset.eq_of_le_and_card_eq h₁ h₂

theorem perm_of_nodup_and_subset_and_length_eq {α : Type*} {xs ys : List α}
(hx : xs.Nodup) (h₁ : xs ⊆ ys)
(h₂ : xs.length = ys.length) : ys ~ xs := by
  generalize hm₁ : Multiset.ofList xs = m₁
  generalize hm₂ : Multiset.ofList ys = m₂
  replace h₁ : m₁ ⊆ m₂ := by subst m₁ m₂; simpa
  replace h₂ : m₁.card = m₂.card := by subst m₁ m₂; simpa
  suffices m₁ = m₂ by subst m₁ m₂; simp at this; exact this.symm
  replace hx : m₁.Nodup := by subst hm₁; simpa
  clear hm₁ hm₂
  apply Multiset.eq_of_le_and_card_eq _ h₂
  rwa [Multiset.le_iff_subset hx]

theorem subset_of_nodup_and_subset_and_length_eq
{α : Type*} {xs ys : List α} (h₁ : xs.Nodup) (h₂ : xs ⊆ ys)
(h₃ : xs.length = ys.length) : ys ⊆ xs := by
  apply Perm.subset
  exact perm_of_nodup_and_subset_and_length_eq h₁ h₂ h₃

@[simp]
theorem count_eq_zero' {α : Type*} [ha : DecidableEq α]
{xs : List α} {x} : xs.count x = 0 ↔ x ∉ xs := count_eq_zero

theorem mem_iff_count_ne_zero {α : Type*} [ha : DecidableEq α]
{xs : List α} {x} : x ∈ xs ↔ xs.count x ≠ 0 := by
  rw [←not_iff_comm']; simp

theorem perm_of_subset_and_nodup {α : Type*} {xs ys : List α}
(h₁ : xs.Nodup) (h₂ : ys.Nodup) (h₃ : xs ⊆ ys) (h₄ : ys ⊆ xs) :
xs ~ ys := by
  classical
  generalize hm₁ : Multiset.ofList xs = m₁
  generalize hm₂ : Multiset.ofList ys = m₂
  replace h₁ : m₁.Nodup := by subst hm₁; simpa
  replace h₂ : m₂.Nodup := by subst hm₂; simpa
  replace h₃ : m₁ ⊆ m₂ := by subst hm₁ hm₂; simpa
  replace h₄ : m₂ ⊆ m₁ := by subst hm₁ hm₂; simpa
  suffices m₁ = m₂ by
    subst hm₁ hm₂
    exact Multiset.coe_eq_coe.mp this
  exact Multiset.eq_of_nodup_and_subset_and_subset h₁ h₂ h₃ h₄

theorem length_eq_of_subset_and_nodup {α : Type*} {xs ys : List α}
(h₁ : xs.Nodup) (h₂ : ys.Nodup) (h₃ : xs ⊆ ys) (h₄ : ys ⊆ xs) :
xs.length = ys.length := by
  apply Perm.length_eq
  exact perm_of_subset_and_nodup h₁ h₂ h₃ h₄

end List namespace Finset