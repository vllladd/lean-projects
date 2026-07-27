import Projects.Util.Nat
import Projects.Util.List
import Projects.Util.Function
import Projects.Util.Quotient

section

variable {α : Type*}
variable [ha : LinearOrder α]

@[simp]
theorem le_trans_simp {a b c : α} : (a ≤ b → b ≤ c → a ≤ c) ↔ True := by
  simp; exact le_trans

@[simp]
theorem le_trans_simp' {a b c : α} : (b ≤ c → a ≤ b → a ≤ c) ↔ True := by
  simp; exact le_trans'

@[simp]
theorem le_total_simp {a b : α} : (a ≤ b ∨ b ≤ a) ↔ True := by
  simp; apply le_total

@[simp]
theorem le_antisymm_simp {a b : α} : (a ≤ b → b ≤ a → a = b) ↔ True := by
  simp; apply le_antisymm

@[simp]
theorem lt_trans_simp {a b c : α} : (a < b → b < c → a < c) ↔ True := by
  simp; exact lt_trans

@[simp]
theorem lt_trans_simp' {a b c : α} : (b < c → a < b → a < c) ↔ True := by
  simp; exact lt_trans'

end

namespace Fintype

variable {α : Type*} [ha : Fintype α]

theorem exi_iter_cycle
{f : α → α} {x : α} : ∃ n m, n < m ∧ f^[n] x = f^[m] x := by
  obtain ⟨g, hg⟩ := hv # λ n => f^[n] x
  suffices h : ∃ n m, g n = g m ∧ n ≠ m by
    subst hg
    obtain ⟨n, m, h₁, h₂⟩ := h
    wlog h₃ : n < m with ih
    · symm at h₁ h₂
      apply @ih α _ f x m n h₁ h₂ _
      simp at h₃
      exact Nat.lt_of_le_of_ne h₃ h₂
    use n, m
  by_contra! h₁
  exact Fintype.false # Fintype.ofInjective g h₁

@[simp]
theorem complete' {x : α} : x ∈ Fintype.elems := Fintype.complete _

instance {α : Type*} [h : IsEmpty α] : Fintype α := ⟨{}, by simp⟩

noncomputable
instance {β : Type*} {f : α → β} : Fintype # Set.range f := Fintype.ofFinite _

@[simp]
theorem elems_eq_empty_iff : ha.elems = ∅ ↔ ∀ (_ : α), False := by
  simp [Finset.ext_iff]

noncomputable
instance {s : Set α} : Fintype s := Fintype.ofFinite _

end Fintype

namespace Finset

variable {α β γ : Type*}
variable {s s₁ s₂ s₃ : Finset α}

def fold' (s : Finset α) (f : β → α → β) (z : β)
(h : ∀ {acc x y}, f (f acc x) y = f (f acc y) x) : β :=
  haveI : RightCommutative f := ⟨@h⟩; s.val.foldl f z

-----

theorem sum_eq_sum_of_fn_congr {α : Type*} {S : Finset α} {f g : α → ℕ}
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
  congr 1; apply sum_eq_sum_of_fn_congr
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
  apply Quot.liftOn s.val ## λ xs => xs.mergeSort
  intro xs ys hxy
  reduce at hxy
  generalize hx : xs.mergeSort (· ≤ ·) = xs'
  generalize hy : ys.mergeSort (· ≤ ·) = ys'
  obtain ⟨h₁, h₂⟩ : xs'.Pairwise (· ≤ ·) ∧ ys'.Pairwise (· ≤ ·) := by
    subst hx hy; constructor <;> apply List.pairwise_mergeSort'
  have h₃ : xs'.Perm ys' := by
    subst hx hy
    trans xs
    · apply List.mergeSort_perm
    symm; trans ys
    · apply List.mergeSort_perm
    exact hxy.symm
  apply List.eq_of_perm_of_pairwise h₃ h₁ h₂ <;> simp

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
mkRaw f = Set.range f := by ext x; simp

theorem card_eq_cardinal_mk_to_nat {α : Type*} {s : Finset α} :
s.card = (Cardinal.mk s).toNat := by simp

theorem card_eq_toSet_ncard {α : Type*} {s : Finset α} :
s.card = (s : Set α).ncard := by simp

theorem image_toSet_eq {α β : Type*} [DecidableEq β]
{s : Finset α} {f : α → β} : f '' s = s.image f :=
  coe_image.symm

theorem ncard_toSet {α : Type*} {s : Finset α} :
(s : Set α).ncard = s.card := by simp

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
      use λ i => τ x, p i x
      intro i h₃
      specialize h₂ i h₃
      have h₄ := τ_spec (p := p i)
      specialize h₄ _
      · simp [p]
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h₂
        simp [hk]
      simp [p] at h₄ ⊢
      rw [h₄]
  nth_rw 2 [sum_eq_sum_of_fn_congr (g := λ i => f i + r i)] at h₁
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
  nth_rw 2 [Finset.sum_eq_sum_of_fn_congr (g := m₁.count)]
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

@[simp]
theorem card_filter_eq_eq_count {α : Type*} [ha : DecidableEq α]
{m : Multiset α} {x} : (m.filter (x = ·)).card = m.count x := by
  rw [←count_eq_card_filter_eq]

theorem map_eq_map_iff_loc {α β : Type*} {m₁ m₂ : Multiset α} {f : α → β}
(hf : ∀ x y, x ∈ m₁ ∨ x ∈ m₂ → y ∈ m₁ ∨ y ∈ m₂ → f x = f y → x = y) :
m₁.map f = m₂.map f ↔ m₁ = m₂ := by
  classical
  refine' ⟨λ h => _, by rintro rfl; rfl⟩
  ext x
  replace h := congrArg (·.count # f x) h
  simp [count_map] at h
  by_cases hx : x ∉ m₁ ∧ x ∉ m₂
  · rw [count_eq_zero_of_notMem hx.1]
    rw [count_eq_zero_of_notMem hx.2]
  rw [not_and_or] at hx
  simp at hx
  obtain ⟨h₁, h₂⟩ :
    m₁.filter (f x = f ·) = m₁.filter (x = ·) ∧
    m₂.filter (f x = f ·) = m₂.filter (x = ·) := by
    constructor
    all_goals
      clear h
      ext y
      simp [count_filter]
      by_cases hx : x = y <;> simp [hx]
      intro h₁
      contrapose! hx
      apply hf <;> try simp_all
  rw [h₁, h₂] at h; clear h₁ h₂
  simp at h
  exact h

@[simp]
theorem toList_ofList_perm {α : Type*} {xs : List α} : (ofList xs).toList.Perm xs := by
  change ⟦xs⟧.out ≈ xs; exact Quotient.out_equiv

@[simp]
theorem nodup_out_iff {α : Type*} {m : Multiset α} : m.out.Nodup ↔ m.Nodup := by
  induction m using Quotient.inductionOn
  nm xs
  simp
  apply List.Perm.nodup_iff
  change (ofList xs).toList.Perm xs
  simp

end Multiset namespace List

variable {α β : Type*} {xs ys : List α}

theorem subperm_of_subperm_and_length_eq
(h₁ : xs <+~ ys) (h₂ : xs.length = ys.length) : ys <+~ xs := by
  generalize hm₁ : Multiset.ofList xs = m₁
  generalize hm₂ : Multiset.ofList ys = m₂
  replace h₁ : m₁ ≤ m₂ := by subst m₁ m₂; simpa
  replace h₂ : m₁.card = m₂.card := by subst m₁ m₂; simpa
  suffices m₂ ≤ m₁ by subst m₁ m₂; simp at this; exact this
  clear hm₁ hm₂
  apply le_of_eq; symm
  exact Multiset.eq_of_le_and_card_eq h₁ h₂

theorem perm_of_nodup_and_subset_and_length_eq
(hx : xs.Nodup) (h₁ : xs ⊆ ys) (h₂ : xs.length = ys.length) : ys ~ xs := by
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
(h₁ : xs.Nodup) (h₂ : xs ⊆ ys) (h₃ : xs.length = ys.length) : ys ⊆ xs := by
  apply Perm.subset; exact perm_of_nodup_and_subset_and_length_eq h₁ h₂ h₃

attribute [simp] count_eq_zero

theorem mem_iff_count_ne_zero [ha : DecidableEq α] {x} : x ∈ xs ↔ xs.count x ≠ 0 := by
  rw [←not_iff_comm']; simp

theorem perm_of_subset_and_nodup
(h₁ : xs.Nodup) (h₂ : ys.Nodup) (h₃ : xs ⊆ ys) (h₄ : ys ⊆ xs) : xs ~ ys := by
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

theorem length_eq_of_subset_and_nodup
(h₁ : xs.Nodup) (h₂ : ys.Nodup) (h₃ : xs ⊆ ys) (h₄ : ys ⊆ xs) :
xs.length = ys.length := by
  apply Perm.length_eq
  exact perm_of_subset_and_nodup h₁ h₂ h₃ h₄

theorem map_perm_map_iff_loc {f : α → β}
(hf : ∀ x y, x ∈ xs ∨ x ∈ ys → y ∈ xs ∨ y ∈ ys → f x = f y → x = y) :
xs.map f ~ ys.map f ↔ xs ~ ys := by
  classical
  obtain ⟨m₁, hm₁⟩ := hv # Multiset.ofList xs
  obtain ⟨m₂, hm₂⟩ := hv # Multiset.ofList ys
  trans m₁ = m₂; rotate_left; simp [hm₁, hm₂]
  trans m₁.map f = m₂.map f; simp [hm₁, hm₂]
  replace hf : ∀ x y, x ∈ m₁ ∨ x ∈ m₂ →
    y ∈ m₁ ∨ y ∈ m₂ → f x = f y → x = y :=
    by simpa [hm₁, hm₂]
  exact Multiset.map_eq_map_iff_loc hf

theorem nodup_of_nodup_and_subperm
(h₁ : ys.Nodup) (h₂ : xs <+~ ys) : xs.Nodup := by
  classical
  obtain ⟨m₁, hm₁⟩ := hv # Multiset.ofList xs
  obtain ⟨m₂, hm₂⟩ := hv # Multiset.ofList ys
  replace h₂ : m₁ ≤ m₂ := by subst hm₁ hm₂; simpa
  simp only [←Multiset.coe_nodup, ←hm₁, ←hm₂] at h₁ ⊢
  exact Multiset.nodup_of_le h₂ h₁

theorem nodup_filterMap_iff [ha : DecidableEq α] {f : α → Option β} :
(xs.filterMap f).Nodup ↔ ∀ x ∈ xs, ∀ y, f x = some y → xs.count x ≤ 1 ∧
∀ x' ∈ xs, f x' = some y → x = x' := by
  classical
  induction xs <;> simp
  nm x xs ih
  simp [filterMap, count_cons]
  split <;> simp [ih] <;> clear ih
  · nm o h₁; clear o
    constructor
    · intro h₂
      simp [h₁]
      intro a h₃ b h₄
      split_ifs with hx <;> simp
      · subst hx; simp [h₁] at h₄
      · exact h₂ _ h₃ _ h₄
    · intro ⟨h₂, h₃⟩ a h₄ b h₅
      specialize h₃ _ h₄ _ h₅
      rcases h₃ with ⟨h₃, h₆, h₇⟩
      split_ifs at h₃ with hx
      · subst hx; simp [h₁] at h₅
      · use h₃
  nm o y h₁; clear o
  simp [h₁]
  constructor
  · intro ⟨h₂, h₃⟩
    refine' ⟨⟨_, _⟩, _⟩
    · intro hx
      specialize h₂ _ hx
      exact h₂ h₁
    · intro a h₄ h₅
      specialize h₂ _ h₄
      contradiction
    · intro a h₄ b h₅
      specialize h₃ _ h₄ _ h₅
      rcases h₃ with ⟨h₃, h₆⟩
      split_ifs with hx
      · subst hx
        simp [h₁] at h₅
        subst h₅
        simp [h₂ _ h₄] at h₁
      refine' ⟨h₃, _, h₆⟩
      rintro rfl
      specialize h₂ _ h₄
      contradiction
  · intro ⟨⟨h₂, h₃⟩, h₆⟩
    constructor
    · intro a h₄ h₅
      specialize h₃ _ h₄ h₅
      subst h₃
      contradiction
    · intro a h₇ b h₈
      specialize h₆ _ h₇ _ h₈
      rcases h₆ with ⟨h₆, h₉, H₁⟩
      refine' ⟨_, H₁⟩
      split_ifs at h₆ with H₂
      · subst H₂; contradiction
      · exact h₆

theorem filterMap_perm_filterMap_iff_filter_map_perm {f : α → Option β} :
xs.filterMap f ~ ys.filterMap f ↔ (xs.map f).filter Option.isSome ~
(ys.map f).filter Option.isSome := by
  classical
  by_cases hb : IsEmpty β
  · have h₁ : f = λ _ => none
    · ext a b
      cases hb.1 b
    subst h₁
    simp
  simp at hb
  replace hb := hb.inhabited
  simp only [filterMap_eq]
  rw [map_perm_map_iff_loc]
  intro b₁ b₂
  simp [Option.isSome_iff_exists]
  aesop

theorem count_filter_pos [ha : DecidableEq α] {f : α → Bool} {x} (h : f x) :
(xs.filter f).count x = xs.count x := count_filter h

theorem count_filter_neg [ha : DecidableEq α] {f : α → Bool} {x} (h : f x = false) :
(xs.filter f).count x = 0 := by simp [h]

theorem count_filter_neg' [ha : DecidableEq α] {f : α → Bool}
{x} (h : ¬f x) : (xs.filter f).count x = 0 := by simp [h]

theorem count_filter_eq_ite [ha : DecidableEq α] {f : α → Bool} {x} :
(xs.filter f).count x = if f x then xs.count x else 0 := by
  split_ifs with h₁
  · exact count_filter_pos h₁
  · exact count_filter_neg' h₁

theorem filter_perm_of_perm {f : α → Bool} (h : xs ~ ys) :
xs.filter f ~ ys.filter f := by
  classical
  have h₁ := h
  rw [perm_iff_count] at h₁ ⊢
  intro x
  specialize h₁ x
  by_cases h₂ : x ∈ xs
  simp only [count_filter_eq_ite, h₁]
  convert rfl (a := 0); simp [h₂]; rw [h.mem_iff] at h₂; simp [h₂]

theorem count_map_of_loc [ha : DecidableEq α] [hb : DecidableEq β]
{f : α → β} {x : α} (h : ∀ y ∈ xs, f x = f y → x = y) :
(xs.map f).count (f x) = xs.count x := by
  induction xs <;> simp
  nm a xs ih
  specialize ih _
  · intro b h₁ h₂
    specialize h b
    simp [h₁, h₂] at h
    exact h
  simp [count_cons, ih]
  rw [eq_comm]
  nth_rw 2 [eq_comm]
  constructor
  · apply h
    simp
  rintro rfl; rfl

theorem count_map_eq_sum [ha : DecidableEq α] [hb : DecidableEq β] {f : α → β} {y : β} :
(xs.map f).count y = ∑ x ∈ xs.toFinset, if f x = y then xs.count x else 0 := by
  induction xs; rfl
  nm x xs ih
  simp
  generalize hs : xs.toFinset = s at ih ⊢
  simp [count_cons, ih]; clear ih
  by_cases hx : x ∉ s
  · have hx' : x ∉ xs := by simp [←hs] at hx; exact hx
    rw [add_comm]
    simp [Finset.sum_insert hx]
    congr 1
    · simp [count_eq_zero_of_not_mem hx']
    apply Finset.sum_eq_sum_of_fn_congr
    intro i h₁
    congr
    simp
    rintro rfl
    contradiction
  simp at hx
  have hx' : x ∈ xs := by simp [←hs] at hx; exact hx
  simp [Finset.insert_eq_of_mem hx]
  generalize hs' : s.erase x = s'
  have h₁ : x ∉ s' := by subst hs'; simp
  have h₂ : insert x s' = s
  · subst s'; rwa [Finset.insert_erase]
  simp [←h₂, Finset.sum_insert h₁]
  rw [add_assoc]
  nth_rw 2 [add_comm]
  split_ifs with h₃
  · simp only [add_assoc, Nat.add_left_cancel_iff]
    apply Finset.sum_eq_sum_of_fn_congr
    subst hs'
    intro i h₄
    simp at h₄
    rcases h₄ with ⟨h₄, h₅⟩
    subst h₃
    simp [ne_symm' h₄]
  simp
  apply Finset.sum_eq_sum_of_fn_congr
  subst hs'
  intro i h₄
  simp at h₄
  rcases h₄ with ⟨h₄, h₅⟩
  simp [ne_symm' h₄]

@[simp]
theorem cons_erase_perm_iff_mem [ha : DecidableEq α] {x} :
(x :: xs.erase x).Perm xs ↔ x ∈ xs := by
  rw [perm_iff_count, mem_iff_count_ne_zero]
  constructor
  · intro h
    specialize h x
    simp at h
    linarith
  intro h y
  simp [count_cons]
  split_ifs with h₁
  · subst h₁
    simp
    generalize xs.count x = n at h ⊢
    cases n; simp at h; rfl
  rw [count_erase_of_ne # ne_symm' h₁]; rfl

@[simp]
theorem perm_cons_erase_iff_mem [ha : DecidableEq α] {x} :
xs.Perm (x :: xs.erase x) ↔ x ∈ xs := by rw [perm_comm]; simp

theorem le_max? [ha : LinearOrder α] {x m : α}
(h₁ : x ∈ xs) (h₂ : xs.max? = some m) : x ≤ m := by
  generalize hy : x :: xs.erase x = ys
  have h₃ : ys.max? = some m
  · rw [←hy, ←h₂]
    apply max?_eq_max?_of_perm
    simpa
  subst hy
  simp at h₃
  cases h₄ : (xs.erase x).max? <;> simp [h₄] at h₃ <;> simp [←h₃]

theorem nodup_erase [ha : DecidableEq α] {x} (h : xs.Nodup) : (xs.erase x).Nodup :=
  nodup_of_nodup_and_subperm h # erase_subperm _ _

theorem pairwise_erase [ha : DecidableEq α] {r x} (h : xs.Pairwise r) : (xs.erase x).Pairwise r :=
  pairwise_of_pairwise_and_sublist h erase_sublist

theorem Perm.mapWith {f : (x : α) → x ∈ xs → β} (h : xs ~ ys) :
xs.mapWith f ~ ys.mapWith (λ x h₁ => f x # h.mem_iff.mpr h₁) := by
  classical
  simp_rw [mapWith_eq_map]
  split_ifs with h₁ h₂ h₂; rfl
  iterate 2
    rw [eq_nil_iff_length_eq_zero] at h₁ h₂; simp [←h.length_eq, h₁] at h₂
  have h₃ : Nonempty β
  · cases xs; simp at h₁; nm x xs
    use f x # by simp
  simp
  have h : (λ (x : α) => if h₄ : x ∈ ys then f x # h.mem_iff.mpr h₄ else h₃.some) =
    (λ (x : α) => if h₄ : x ∈ xs then f x h₄ else h₃.some)
  ·
    ext x
    rw! (castMode := .all) [h.mem_iff]
    split_ifs <;> rfl
  rw [h]; clear h
  apply Perm.map
  exact h

end List namespace Finset

variable {α β γ : Type*} {s : Finset α}

@[simp]
theorem nodup_out_val : s.val.out.Nodup := by
  rcases s with ⟨m, h⟩; simpa

@[simp]
theorem nodup_val : s.val.Nodup := by
  rcases s with ⟨m, h⟩; simpa

@[simp]
theorem mem_out_val {x} : x ∈ s.val.out ↔ x ∈ s :=
  mem_toList

theorem card_insert_erase_eq {x y : α} [ha : DecidableEq α]
(h₁ : x ∈ s) (h₂ : y ∉ s) : (insert y (s.erase x)).card = s.card := by
  rw [card_insert_of_notMem # by simp [h₂]]
  rw [card_erase_of_mem h₁]
  cases h₃ : s.card
  · simp at h₃; simp [h₃] at h₁
  simp

def map' [DecidableEq β] (s : Finset α) (f : α → β) : Finset β :=
  s.biUnion ({f ·})

@[simp]
theorem mem_map'' [hb : DecidableEq β] {f : α → β} {y : β} :
y ∈ s.map' f ↔ ∃ x ∈ s, f x = y := by simp [map', eq_comm]

theorem sum_range_list_get! {xs : List ℝ} {f : ℝ → ℝ} :
∑ i ∈ range xs.length, f (xs[i]!) = (xs.map f).sum := by
  induction xs using List.reverseRecOn; simp; nm xs x ih
  simp [sum_range_succ]; convert ih; clear ih
  nm k h; simp at h; simp [List.getElem?_append_left h]

theorem prod_range_list_get! {xs : List ℝ} {f : ℝ → ℝ} :
∏ i ∈ range xs.length, f (xs[i]!) = (xs.map f).prod := by
  induction xs using List.reverseRecOn; simp; nm xs x ih
  simp [prod_range_succ]; left; convert ih; clear ih
  nm k h; simp at h; simp [List.getElem?_append_left h]

theorem le_sum_range {a : ℕ → ℝ} {N n : ℕ} (h : n < N) :
|a n| ≤ ∑ i ∈ range N, |a i| := by
  obtain ⟨s, h₁, h₂⟩ : ∃ (s : Finset ℕ), n ∉ s ∧ range N = insert n s
  · use range N |>.erase n; simp; rw [insert_erase]; simpa
  simp [h₂, sum_insert h₁]; apply sum_nonneg; simp

theorem one_le_prod_of_forall_one_le {ι : Type*} {s : Finset ι} {f : ι → ℝ}
(h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction
  · simp
  nm i s hi ih
  rw [Finset.prod_insert hi]
  simp at h
  rcases h with ⟨h₁, h₂⟩
  specialize ih h₂
  nlinarith

theorem sum_geom_eq {b : ℝ} {n : ℕ} (hb : b ≠ 1) :
∑ k ∈ range n, b ^ k = (1 - b ^ n) / (1 - b) := by
  by_cases hn : n = 0; simp [hn]; replace hn : 1 ≤ n; omega
  have h : ∑ k ∈ range n, b ^ k = b * ∑ k ∈ range n, b ^ k + 1 - b ^ n
  · calc
    _ = (∑ k ∈ range n, b ^ k : ℝ) := by simp
    _ = 1 + ∑ k ∈ range (n - 1), b ^ (k + 1) := by
      cases n; simp at hn; nm n; simp
      rw [sum_range_succ']; ring_nf
    _ = 1 + ∑ k ∈ range n, b ^ (k + 1) - b ^ n := by
      cases n; simp at hn; nm n
      simp; rw [sum_range_succ]; ring_nf
    _ = 1 + b * ∑ k ∈ range n, b ^ k - b ^ n := by
      congr; simp_rw [pow_succ, ←sum_mul]; ring_nf
    _ = _ := by ring_nf
  generalize ∑ k ∈ range n, b ^ k = x at h ⊢
  have h₁ : 1 - b ≠ 0; grind
  field_simp; linarith

theorem sum_add_geom_eq' {b : ℝ} {n : ℕ} (hb : b ≠ 1) :
∑ k ∈ range n, k * b ^ k = (b * ∑ k ∈ range n, b ^ k - n * b ^ n) / (1 - b) := by
  by_cases hn : n = 0; simp [hn]; replace hn : 1 ≤ n; omega
  have h : ∑ k ∈ range n, k * b ^ k = -n * b ^ n +
    b * ∑ k ∈ range n, k * b ^ k + b * ∑ k ∈ range n, b ^ k
  · calc
    _ = (∑ k ∈ range n, k * b ^ k : ℝ) := by simp
    _ = ∑ k ∈ range (n - 1), (k + 1) * b ^ (k + 1) := by
      cases n; simp at hn; nm n; simp
      rw [sum_range_succ']; simp
    _ = -n * b ^ n + ∑ k ∈ range n, (k + 1) * b ^ (k + 1) := by
      cases n; simp at hn; nm n; simp
      rw [sum_range_succ]; ring_nf; congr; ext; ring_nf
    _ = -n * b ^ n + b * ∑ k ∈ range n, (k + 1) * b ^ k := by
      congr; simp_rw [pow_succ, ←mul_assoc, ←sum_mul]
      ring_nf; congr; ext; ring_nf
    _ = -n * b ^ n + (b * ∑ k ∈ range n, k * b ^ k + b * ∑ k ∈ range n, b ^ k) := by
      congr; simp_rw [add_mul]
      rw [sum_add_distrib, mul_add]; congr; simp
    _ = -n * b ^ n + b * ∑ k ∈ range n, k * b ^ k + b * ∑ k ∈ range n, b ^ k := by ring_nf
  have h₁ : 1 - b ≠ 0; grind
  field_simp; linarith

theorem sum_add_geom_eq {b : ℝ} {n : ℕ} (hb : b ≠ 1) :
∑ k ∈ range n, k * b ^ k = (b ^ n * (n * b - n - b) + b) / (1 - b) ^ 2 := by
  have h := sum_add_geom_eq' (n := n) hb
  rw [sum_geom_eq hb] at h
  have h₁ : 1 - b ≠ 0; grind
  field_simp at h ⊢
  linarith

theorem card_filter_range_le_of_le {p : ℕ → Prop} {i j : ℕ} [hp : DecidablePred p]
(h : i ≤ j) : (Finset.range i |>.filter p).card ≤ (Finset.range j |>.filter p).card := by
  apply Finset.card_le_card
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Finset.range_add]
  rw [Finset.filter_union]
  simp

theorem Ico_add_right {n m k : ℕ} (h : n ≤ m) : Ico n (m + k) = Ico n m ∪ Ico m (m + k) := by
  ext; simp; omega

theorem card_filter_range_add {p : ℕ → Prop} {n k : ℕ} [hp : DecidablePred p] :
{i ∈ Finset.range (n + k) | p i}.card = {i ∈ Finset.range n | p i}.card +
{i ∈ Finset.Ico n (n + k) | p i}.card := by
  simp_rw [range_eq_Ico]
  rw [Ico_add_right # by simp]
  rw [filter_union, card_union_of_disjoint]
  rw [Finset.disjoint_iff_ne]
  intro; simp; omega

theorem card_eq_one_iff_exiu : s.card = 1 ↔ ∃! x, x ∈ s := by
  rw [card_eq_one]
  apply exists_congr; intro x
  simp [Finset.ext_iff]
  grind

theorem forall_iff_of_fintype [ha : Fintype α] {p : α → Prop} :
(∀ x, p x) ↔ ∀ x ∈ ha.elems, p x := by
  constructor
  · intro h
    simp [h]
  intro h b
  simp at h
  simp [h]

instance [ha : Fintype α] {p : α → Prop} [hp : DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff' _ forall_iff_of_fintype