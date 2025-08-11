import AP.Util.Function

import Init.Data.List.Perm
import Init.Data.List.Sublist

namespace List

variable {α β : Type*} {xs ys : List α}

@[simp]
def init {α : Type*} : List α → List α
| [] => []
| [_] => []
| (x :: ys) => x :: ys.init

theorem init_cons_of_ne_nil {α : Type*} {x : α} {xs : List α}
(h : xs ≠ []) : (x :: xs).init = x :: xs.init := by
  cases xs; simp at h; rfl

@[simp]
theorem init_snoc {x : α} : (xs ++ [x]).init = xs := by
  induction xs; rfl
  nm y xs ih
  rw [List.cons_append, init_cons_of_ne_nil # by simp, ih]

@[simp]
theorem snoc_inj {α : Type*} {xs ys : List α} {x y : α} :
xs ++ [x] = ys ++ [y] ↔ xs = ys ∧ x = y := by
  symm; constructor; rintro ⟨rfl, rfl⟩; rfl
  intro h
  replace h := congrArg reverse h
  simp at h
  exact h.symm

@[simp]
theorem not_mem_failure {α : Type*} {x : α} : x ∉ (failure : List α) := by
  classical exact List.count_eq_zero.mp rfl

@[simp]
theorem unit_mem_guard_iff {P : Prop} [Decidable P] :
() ∈ (guard P : List Unit) ↔ P := by
  by_cases h : P <;> simp [h]

theorem eq_of_prefix_and_length_eq {α : Type*} {xs ys zs : List α}
(hx : xs <+: zs) (hy : ys <+: zs) (hn : xs.length = ys.length) : xs = ys := by
  induction ys generalizing xs zs
  · simp at hn; exact hn
  nm y ys ih
  cases xs
  · simp at hn
  nm x xs
  simp at hn ⊢
  cases zs
  · simp at hx
  nm z zs
  simp at hx hy
  constructor
  · rw [hx.1, hy.1]
  exact ih hx.2 hy.2 hn

theorem prefix_of_prefix_snoc_and_ne {α : Type*} {xs ys : List α} {y : α}
(h₁ : xs <+: ys ++ [y]) (h₂ : xs ≠ ys ++ [y]) : xs <+: ys := by
  induction ys generalizing xs y
  · cases xs; rfl
    nm x xs
    simp at h₁ h₂
    tauto
  nm z zs ih
  cases xs
  · simp
  nm x xs
  simp at h₁
  rcases h₁ with ⟨rfl, h₁⟩
  simp at h₂
  simp
  exact ih h₁ h₂

@[simp]
theorem append_prefix_left_iff {α : Type*} {xs ys : List α} :
xs ++ ys <+: xs ↔ ys = [] := by
  symm
  constructor
  · rintro rfl; simp
  rintro ⟨zs, h⟩
  simp at h
  exact h.1

@[simp]
theorem prefix_snoc_iff {α : Type*} {xs ys : List α} {y : α} :
xs <+: ys ++ [y] ↔ xs <+: ys ∨ xs = ys ++ [y] := by
  induction xs generalizing ys y
  · simp
  nm x xs ih
  cases ys
  · simp
  nm z ys
  simp
  by_cases h : x = z <;> simp [h]
  exact ih

theorem prefix_antisymm {α : Type*} {xs ys : List α}
(h₁ : xs <+: ys) (h₂ : ys <+: xs) : xs = ys := by
  obtain ⟨ys, rfl⟩ := h₁
  obtain ⟨zs, h₂⟩ := h₂
  simp at h₂
  simp [h₂]

theorem take_length_eq_of_prefix {α : Type*} {xs ys : List α}
(h₁ : ys <+: xs) : xs.take ys.length = ys := by
  obtain ⟨xs, rfl⟩ := h₁; simp

@[simp]
theorem nodup_inits : xs.inits.Nodup := by
  induction xs
  · simp
  nm x xs ih
  simp
  rwa [List.nodup_map_iff]
  simp

theorem length_takeWhile_le {α : Type*} {P : α → Bool} {xs : List α} :
(xs.takeWhile P).length ≤ xs.length := by
  induction xs
  · simp
  nm x xs ih
  simp [takeWhile]
  split; simpa; simp

theorem not_apply_of_takeWhile_append_cons_eq_self
{α : Type*} {xs ys : List α} {P : α → Bool} {y}
(h : xs.takeWhile P ++ y :: ys = xs) : P y = false := by
  induction xs using reverseRecOn generalizing y ys
  · simp at h
  nm xs x ih
  rw [takeWhile_append] at h
  split_ifs at h with h₁
  · simp [takeWhile_cons] at h
    split_ifs at h with h₂ <;> simp at h
    simp [←h] at h₂
    exact h₂
  suffices h₂ : xs.takeWhile P ++ [y] <+: xs
    by
      obtain ⟨zs, h₂⟩ := h₂
      simp at h₂
      exact ih h₂
  rw [append_cons] at h
  induction ys using reverseRecOn
  · rw [append_nil, snoc_inj] at h
    simp [h.1] at h₁
  nm ys z x; clear x
  rw [←append_assoc, snoc_inj] at h
  rcases h with ⟨h, rfl⟩
  use ys

theorem exists_takeWhile_eq {α : Type*} (xs : List α) (P : α → Bool) :
∃ k ≤ xs.length, xs.takeWhile P = xs.take k ∧ (∀ x ∈ xs.take k, P x) ∧
((h : k < xs.length) → P xs[k] = false) := by
  use (xs.takeWhile P).length
  use length_takeWhile_le
  use by rw [take_length_eq_of_prefix # takeWhile_prefix _]
  constructor
  · intro x hx
    induction xs using reverseRecOn
    · simp at hx
    nm xs y ih
    rw [takeWhile_append] at hx
    split_ifs at hx with h₁
    · simp [take_append, take_add] at hx
      simp [h₁] at ih
      rcases hx with h₂ | h₂
      · exact ih h₂
      rw [takeWhile_cons] at h₂
      split_ifs at h₂ with h₃
      · simp at h₂
        rwa [h₂]
      simp at h₂
    rw [take_append] at hx
    simp at hx
    rcases hx with h₂ | h₂
    · exact ih h₂
    have h₃ : (takeWhile P xs).length - xs.length = 0 :=
      by
        exact Nat.sub_eq_zero_of_le length_takeWhile_le
    simp [h₃] at h₂
  have h₁ : takeWhile P xs <+: xs := takeWhile_prefix P
  obtain ⟨ys, h₁⟩ := h₁
  rw [←h₁]
  cases ys
  · simp at h₁ ⊢
    rw [←takeWhile_eq_self_iff] at h₁
    simp [h₁]
  nm y ys
  have h₂ := not_apply_of_takeWhile_append_cons_eq_self h₁
  rw [append_cons, takeWhile_append, takeWhile_append, takeWhile_idem]
  simp [h₂]

theorem ext {α : Type*} {xs ys : List α} : xs = ys ↔ xs.length = ys.length ∧
∀ {i} (_ : i < xs.length) (_ : i < ys.length), xs[i] = ys[i] := by
  constructor
  · rintro rfl; simp
  rintro ⟨h₁, h₂⟩
  ext i x
  have h₄ : i < xs.length ↔ i < ys.length := by rw [h₁]
  by_cases h₃ : i < xs.length <;> simp [h₃] at h₄
  · rw [List.getElem?_eq_getElem h₃]
    rw [List.getElem?_eq_getElem h₄]
    simp
    rw [h₂ h₃ h₄]
  simp at h₃
  rw [List.getElem?_eq_none h₃]
  rw [List.getElem?_eq_none h₄]

theorem suffix_cons_of_suffix {α : Type*} {xs ys : List α} {y}
(h : xs <:+ ys) : xs <:+ y :: ys := by
  simp [List.suffix_cons_iff, h]

@[simp]
theorem not_cons_suffix {x} : ¬(x :: xs <:+ xs) := by
  rintro ⟨ys, h⟩
  replace h := congrArg (·.length) h
  simp at h
  linarith

theorem perm_swap_left {α : Type*} {xs ys : List α} {x y} :
(x :: y :: xs).Perm ys ↔ (y :: x :: xs).Perm ys := by
  constructor <;> intro h
  · trans x :: y :: xs
    rotate_left; exact h
    apply List.Perm.swap
  · trans y :: x :: xs
    rotate_left; exact h
    apply List.Perm.swap

theorem perm_swap_right {α : Type*} {xs ys : List α} {x y} :
xs.Perm (x :: y :: ys) ↔ xs.Perm (y :: x :: ys) := by
  rw [List.perm_comm]
  nth_rw 2 [List.perm_comm]
  exact perm_swap_left

@[simp]
theorem count_mergeSort {α : Type*} [ha : DecidableEq α]
{xs : List α} {x r} : (xs.mergeSort r).count x = xs.count x := by
  have h₁ := mergeSort_perm xs r
  rw [perm_iff_count] at h₁
  apply h₁

theorem count_eq_count_unattach {α : Type*} [ha : DecidableEq α]
{xs : List α} {ys : List {x // x ∈ xs}} {x} :
count x ys = count x.1 ys.unattach := by
  rcases x with ⟨x, hx⟩
  dsimp
  induction ys generalizing x
  · rfl
  nm y ys ih
  simp only [unattach_cons, count_cons]
  split_ifs with h₁ h₂ h₂ <;> simp at h₁ h₂ <;>
    (try contradiction) <;> simp <;> apply ih

theorem count_unattach_eq_ite {α : Type*} [ha : DecidableEq α]
{xs : List α} {ys : List {x // x ∈ xs}} {x : α} :
count x ys.unattach = if h : x ∈ xs then count ⟨x, h⟩ ys else 0 := by
  split_ifs with h₁
  · rw [count_eq_count_unattach]
  · simp [count_eq_zero, h₁]

theorem mergeSort_attach_perm {r} :
(xs.attach.mergeSort (r ·.1 ·.1)).unattach.Perm (xs.mergeSort r) := by
  classical
  rw [perm_iff_count]
  intro a
  simp
  rw [count_unattach_eq_ite]
  split_ifs with ha
  · convert @List.count_mergeSort {x // x ∈ xs} _ xs.attach
      ⟨a, ha⟩ (r ·.1 ·.1)
    convert (@count_attach α _ xs ⟨a, ha⟩).symm
  symm; rwa [count_eq_zero]

@[simp]
theorem sorted_unattach {α : Type*}
{xs : List α} {ys : List {x // x ∈ xs}} {r : α → α → Prop} :
ys.unattach.Sorted r ↔ ys.Sorted (r ·.1 ·.1) := by
  induction ys <;> simp
  nm y ys ih
  intro h
  exact ih

theorem mergeSort_attach {r} :
(xs.attach.mergeSort (r ·.1 ·.1)).unattach = xs.mergeSort r := by
  rw [unattach, map_mergeSort (s := (r · ·))] <;> simp

theorem eq_of_perm_of_sorted_loc {α : Type*} {xs ys : List α} {r}
(hp : xs.Perm ys) (hx : xs.Sorted r) (hy : ys.Sorted r)
(h_tra : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → r a b → r b c → r a c)
(h_tot : ∀ a b, a ∈ xs → b ∈ xs → r a b ∨ r b a)
(h_ant : ∀ a b, a ∈ xs → b ∈ xs → r a b → r b a → a = b) : xs = ys := by
  induction xs generalizing ys
  · simp at hp
    rw [hp]
  nm x xs ih
  cases ys
  · simp at hp
  nm y ys
  simp at ⊢
  rw [sorted_cons] at hx hy
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  apply and_of
  · by_contra hxy
    change x ≠ y at hxy
    have h₁ := @hp.mem_iff
    have h₂ := h₁ x; simp [hxy] at h₂
    have h₃ := h₁ y; simp [hxy.symm] at h₃
    specialize hx₁ y h₃
    specialize hy₁ x h₂
    specialize h_ant x y
    simp [hxy.symm, h₃, hx₁, hy₁] at h_ant
    contradiction
  rintro rfl
  simp at hp
  apply @ih ys hp hx₂ hy₂
  · intro a b c ha hb hc h₁ h₂
    apply h_tra a b c <;> simp [ha, hb, hc, h₁, h₂]
  · intro a b ha hb
    apply h_tot a b <;> simp [ha, hb]
  · intro a b ha hb h₁ h₂
    apply h_ant <;> simp [ha, hb, h₁, h₂]

theorem sorted_mergeSort_loc' {r : α → α → Bool}
(h_tra : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → r a b → r b c → r a c)
(h_tot : ∀ a b, a ∈ xs → b ∈ xs → r a b ∨ r b a) :
(xs.mergeSort r).Sorted (r · ·) := by
  rw [←@mergeSort_attach α xs r]
  simp
  apply sorted_mergeSort
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    apply h_tra <;> assumption
  · rintro ⟨a, ha⟩ ⟨b, hb⟩; simp
    apply h_tot <;> assumption

theorem sorted_mergeSort_loc
{r : α → α → Prop} [hr : DecidableRel r]
(h_tra : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → r a b → r b c → r a c)
(h_tot : ∀ a b, a ∈ xs → b ∈ xs → r a b ∨ r b a) :
(xs.mergeSort (r · ·)).Sorted r := by
  have h₁ := sorted_mergeSort_loc' (xs := xs) (r := (r · ·))
    (by simpa using h_tra) (by simpa using h_tot)
  simp at h₁; exact h₁

theorem eq_iff_of_nodup_and_sorted {α : Type*}
(r : α → α → Prop) {xs ys : List α} (hx₁ : xs.Nodup) (hy₁ : ys.Nodup)
(h_ant : ∀ a b, a ∈ xs → b ∈ xs → r a b → r b a → a = b)
(hx₂ : xs.Sorted r) (hy₂ : ys.Sorted r) :
xs = ys ↔ ∀ x, x ∈ xs ↔ x ∈ ys := by
  refine' ⟨λ h => by simp [h], λ h => _⟩
  induction xs generalizing ys
  · cases ys
    · rfl
    nm y ys
    specialize h y
    simp at h
  nm x xs ih
  cases ys
  · specialize h x
    simp at h
  nm y ys
  simp at h ⊢
  simp at hx₁ hx₂ hy₁ hy₂
  rcases hx₁ with ⟨hx₁, hx₃⟩
  rcases hy₁ with ⟨hy₁, hy₃⟩
  rcases hx₂ with ⟨hx₂, hx₄⟩
  rcases hy₂ with ⟨hy₂, hy₄⟩
  apply and_of
  · by_contra! h₁
    have h₂ := h x
    have h₃ := h y
    simp [h₁, h₁.symm] at h₂ h₃
    specialize hx₂ _ h₃
    specialize hy₂ _ h₂
    apply h₁
    apply h_ant <;> simp [h₃, hx₂, hy₂]
  rintro rfl
  apply ih hx₃ hy₃
  · intro a b ha hb h₁ h₂
    apply h_ant <;> simp [ha, hb, h₁, h₂]
  any_goals assumption
  intro z
  specialize h z
  by_cases hz : z = x
  · subst hz
    tauto
  · simp [hz] at h
    exact h

theorem take_length_add {n} :
xs.take (xs.length + n) = xs := by
  simp [take_add]

@[simp]
theorem mergeSort_perm' {r : α → α → Bool} :
xs.mergeSort r ~ xs := by apply mergeSort_perm

@[simp]
theorem perm_mergeSort {r : α → α → Bool} :
xs ~ xs.mergeSort r := by symm; simp

theorem perm_of_mergeSort_perm_mergeSort {α : Type*}
{xs ys : List α} {r₁ r₂ : α → α → Bool}
(h : xs.mergeSort r₁ ~ ys.mergeSort r₂) : xs ~ ys := by
  trans xs.mergeSort r₁; simp
  apply h.trans; simp

theorem perm_of_mergeSort_eq_mergeSort {α : Type*}
{xs ys : List α} {r₁ r₂ : α → α → Bool}
(h : xs.mergeSort r₁ = ys.mergeSort r₂) : xs ~ ys := by
  trans xs.mergeSort r₁; simp; simp [h]

@[simp]
theorem mergeSort_eq_nil_iff {r : α → α → Bool} :
xs.mergeSort r = [] ↔ xs = [] := by
  cases xs <;> simp
  apply ne_of_congr List.length
  simp

@[simp]
theorem sorted_map {f : α → β} {r : β → β → Prop} :
(xs.map f).Sorted r ↔ xs.Sorted (λ a b => r (f a) (f b)) := by
  induction xs; simp
  nm x xs ih
  simp
  intro h
  exact ih

theorem foldl_eq_foldl_of_perm {α β : Type*}
{f : β → α → β} {z : β} {xs ys : List α}
(h_assoc : ∀ {acc x y}, f (f acc x) y = f (f acc y) x)
(h : xs ~ ys) : xs.foldl f z = ys.foldl f z := by
  induction h generalizing z <;> clear xs ys
  · rfl
  · nm x xs ys h ih; simp [ih]
  · nm x y xs; simp [h_assoc]
  · nm xs ys zs h₁ h₂ ih₁ ih₂; rw [ih₁, ih₂]

open Classical in
theorem foldl_bool_to_prop {α : Type*}
{xs : List α} {f : Bool → α → Bool} {z : Bool} :
xs.foldl f z = @xs.foldl Prop α (λ acc x => f acc x) z := by
  induction xs generalizing z; simp
  nm x xs ih; simp [ih]

@[simp]
theorem snoc_perm_iff {α : Type*} {xs ys : List α} {x} :
xs ++ [x] ~ ys ↔ x :: xs ~ ys := by
  classical
  rw [←reverse_perm']
  simp [cons_perm_iff_perm_erase]

@[simp]
theorem perm_snoc_iff {α : Type*} {xs ys : List α} {y} :
xs ~ ys ++ [y] ↔ xs ~ y :: ys := by
  rw [perm_comm]; nth_rw 2 [perm_comm]; simp

@[simp]
theorem cons_reverse_perm_iff {α : Type*} {xs ys : List α} {x} :
x :: xs.reverse ~ ys ↔ x :: xs ~ ys := by
  classical simp [cons_perm_iff_perm_erase]

@[simp]
theorem perm_cons_reverse_iff {α : Type*} {xs ys : List α} {y} :
xs ~ y :: ys.reverse ↔ xs ~ y :: ys := by
  rw [perm_comm]; nth_rw 2 [perm_comm]; simp

theorem foldl_and_eq_all {p : α → Bool} :
xs.foldl (λ a x => a && p x) true = xs.all p := by
  induction xs using List.reverseRecOn; simp
  nm xs x ih; simp [ih]

theorem mem_iff_mem_iff_subset {α : Type*} {xs ys : List α} :
(∀ x, x ∈ xs ↔ x ∈ ys) ↔ xs ⊆ ys ∧ ys ⊆ xs := by
  unfold instHasSubset List.Subset
  constructor
  · intro h; simp [h]
  rintro ⟨h₁, h₂⟩ a
  constructor
  · apply h₁
  · apply h₂

theorem perm_iff_subset_of_nodup {α : Type*} {xs ys : List α}
(hx : xs.Nodup) (hy : ys.Nodup) : xs ~ ys ↔ xs ⊆ ys ∧ ys ⊆ xs := by
  rw [List.perm_ext_iff_of_nodup hx hy]
  exact mem_iff_mem_iff_subset

@[simp]
theorem nil_subset' : [] ⊆ xs := by
  apply nil_subset

theorem perm_of_nodup_and_subperm_and_length_eq {α : Type*} {xs ys : List α}
(h₁ : xs <+~ ys) (h₂ : xs.length = ys.length) : ys ~ xs := by
  classical
  obtain ⟨zs, h₁, h₃⟩ := h₁
  trans zs
  rotate_left
  · exact h₁
  rw [h₁.symm.length_eq] at h₂
  clear! xs
  symm
  suffices zs = ys by rw [this]
  rwa [←h₃.length_eq]

theorem subset_iff_subperm_of_nodup {α : Type*} {xs ys : List α}
(h : xs.Nodup) : xs ⊆ ys ↔ xs <+~ ys := by
  use subperm_of_subset h
  rintro ⟨zs, h₁, h₂⟩
  apply Subset.trans (l₂ := zs)
  · exact h₁.symm.subset
  · exact h₂.subset

theorem nodup_of_nodup_and_subset_and_length_eq {α : Type*} {xs ys : List α}
(h₁ : xs.Nodup) (h₂ : xs ⊆ ys)
(h₃ : xs.length = ys.length) : ys.Nodup := by
  classical
  rw [subset_iff_subperm_of_nodup h₁] at h₂
  have h₄ := perm_of_nodup_and_subperm_and_length_eq h₂ h₃
  rwa [h₄.nodup_iff]

theorem perm_iff_mem_iff_of_nodup {α : Type*} {xs ys : List α}
(hx : xs.Nodup) (hy : ys.Nodup) : xs ~ ys ↔ ∀ x, x ∈ xs ↔ x ∈ ys := by
  rw [perm_iff_subset_of_nodup hx hy]
  change (∀ _, _) ∧ (∀ _, _) ↔ _
  use λ ⟨h₁, h₂⟩ x => ⟨h₁ x, h₂ x⟩
  intro h; simp [h]

theorem subset_iff_exi_get {α  : Type*} {xs ys : List α} :
xs ⊆ ys ↔ ∀ x ∈ xs, ∃ (i : ℕ) (_ : i < ys.length), ys[i] = x := by
  simp_rw [←mem_iff_getElem]; rfl

theorem exi_get_iff_subset {α  : Type*} {xs ys : List α} :
(∀ x ∈ xs, ∃ (i : ℕ) (_ : i < ys.length), ys[i] = x) ↔ xs ⊆ ys :=
  subset_iff_exi_get.symm

@[simp]
theorem take_prefix' {n} :
xs.take n <+: xs := take_prefix _ _

instance {α : Type*} : IsEquiv (List α) List.Perm where
  refl := Perm.refl
  symm := λ _ _ => Perm.symm
  trans := λ _ _ _ => Perm.trans

def atMostOne : List Bool → Bool
| [] => true
| b :: bs => if b then !bs.or else bs.atMostOne

@[simp]
theorem mergeSort_perm_mergeSort {α : Type*}
{r₁ r₂ : α → α → Bool} {xs ys : List α} :
xs.mergeSort r₁ ~ ys.mergeSort r₂ ↔ xs ~ ys := by
  apply iff_of_isEquiv <;> simp

@[simp]
theorem eq_nil_of_isEmpty {α : Type*} [ha : IsEmpty α]
{xs : List α} : xs = [] := by
  cases xs; rfl
  nm x xs
  simp
  exact ha.1 x

@[simp]
theorem atMostOne_nil : [].atMostOne = true := rfl

@[simp]
theorem atMostOne_singleton {b} : [b].atMostOne = true := by
  cases b <;> rfl

@[simp]
theorem atMostOne_true_succ {bs} :
(true :: bs).atMostOne = !bs.or := rfl

@[simp]
theorem atMostOne_false_succ {bs} :
(false :: bs).atMostOne = bs.atMostOne := rfl

@[simp]
theorem atMostOne_pair {b₁ b₂} :
[b₁, b₂].atMostOne = (!b₁ || !b₂) := by
  simp [atMostOne]

@[simp]
theorem nodup_snoc {x} : (xs ++ [x]).Nodup ↔ x ∉ xs ∧ xs.Nodup := by
  rw [←nodup_reverse]; simp

theorem sorted_append {p} : (xs ++ ys).Sorted p ↔
xs.Sorted p ∧ ys.Sorted p ∧ ∀ a ∈ xs, ∀ b ∈ ys, p a b :=
  pairwise_append

@[simp]
theorem pairwise_snoc {x p} : (xs ++ [x]).Pairwise p ↔
xs.Pairwise p ∧ (∀ y ∈ xs, p y x) := by simp [pairwise_append]

@[simp]
theorem sorted_snoc {x p} : (xs ++ [x]).Sorted p ↔
xs.Sorted p ∧ (∀ y ∈ xs, p y x) := pairwise_snoc

theorem filterMap_eq [hb : Inhabited β] {f : α → Option β} :
xs.filterMap f = (xs.map f |>.filter Option.isSome |>.map Option.get!) := by
  induction xs; rfl
  nm x xs ih
  simp [filterMap, filter]
  split <;> nm b h <;> simpa [h]

theorem foldl_some_some {f : α → α → α} {z} :
xs.foldl (λ acc x => some # acc.elim x (f · x)) (some z) = some (xs.foldl f z) := by
  induction xs using List.reverseRecOn; simp
  nm xs x ih; simp [ih]

theorem min?_eq_foldl [ha : LinearOrder α] :
xs.min? = xs.foldl (λ acc x => some # acc.elim x (min · x)) none := by
  cases xs; rfl; simp [foldl_some_some, min?]

theorem max?_eq_foldl [ha : LinearOrder α] :
xs.max? = xs.foldl (λ acc x => some # acc.elim x (max · x)) none := by
  cases xs; rfl; simp [foldl_some_some, max?]

theorem foldl_comm {f : β → α → β} {z x}
(h_assoc : ∀ {x y z}, f (f x y) z = f (f x z) y) :
xs.foldl f (f z x) = f (xs.foldl f z) x := by
  induction xs generalizing z; rfl; clear! xs; nm y xs ih
  simp [←ih, h_assoc]

theorem foldl_append_comm {f : β → α → β} {z}
(h_assoc : ∀ {x y z}, f (f x y) z = f (f x z) y) :
(xs ++ ys).foldl f z = (ys ++ xs).foldl f z := by
  simp; induction xs generalizing z ys; simp
  nm x xs ih; simp [ih, foldl_comm h_assoc]

theorem min?_append_comm [ha : LinearOrder α] {ys : List α} :
(xs ++ ys).min? = (ys ++ xs).min? := by
  simp only [min?_eq_foldl]; apply foldl_append_comm
  rintro (_ | x) y z <;> simp; apply min_comm; apply inf_right_comm

theorem max?_append_comm [ha : LinearOrder α] {ys : List α} :
(xs ++ ys).max? = (ys ++ xs).max? := by
  simp only [max?_eq_foldl]; apply foldl_append_comm
  rintro (_ | x) y z <;> simp; apply max_comm; apply sup_right_comm

@[simp]
theorem min?_reverse [ha : LinearOrder α] : xs.reverse.min? = xs.min? := by
  induction xs; rfl; clear! xs; nm x xs ih; simp [min?_append_comm, ih]

@[simp]
theorem max?_reverse [ha : LinearOrder α] : xs.reverse.max? = xs.max? := by
  induction xs; rfl; clear! xs; nm x xs ih; simp [max?_append_comm, ih]

theorem max?_eq_getLast? [ha : LinearOrder α]
(h : xs.Sorted (· ≤ ·)) : xs.max? = xs.getLast? := by
  have h₁ := @List.min?_eq_head?;
  specialize @h₁ α ⟨max⟩ xs.reverse
  simp [pairwise_reverse] at h₁
  specialize h₁ h
  convert h₁ using 1
  symm; exact max?_reverse

@[simp]
def foldlWith (xs : List α) (f : β → (x : α) → x ∈ xs → β) (z : β) : β :=
  match h : xs with
  | [] => z
  | x :: ys => ys.foldlWith (λ acc y h₁ => f acc y (by simp [h₁])) # f z x (by simp)

@[simp]
theorem foldlWith_snoc {x : α} {f : β → (y : α) → y ∈ xs ++ [x] → β} {z : β} :
(xs ++ [x]).foldlWith f z = f (xs.foldlWith (λ acc y h => f acc y (by simp [h])) z)
x (by simp) := by induction xs generalizing z; rfl; nm y xs ih; simp [ih]

theorem foldl_eq_foldl_of_fn_congr {f g : β → α → β} {z : β}
(h : ∀ acc, ∀ x ∈ xs, f acc x = g acc x) : xs.foldl f z = xs.foldl g z := by
  induction xs using List.reverseRecOn; rfl
  clear! xs; nm xs x ih
  simp
  specialize ih _
  · intro acc y hy
    specialize h acc y
    simp  [hy] at h
    exact h
  rw [ih]
  apply h
  simp

theorem foldlWith_eq_foldl [ha : DecidableEq α] {f : β → (x : α) → x ∈ xs → β} {z : β} :
xs.foldlWith f z = xs.foldl (λ acc x => if h : x ∈ xs then f acc x h else z) z := by
  induction xs using List.reverseRecOn; rfl
  clear! xs; nm xs x ih
  simp [ih]
  congr 1
  apply foldl_eq_foldl_of_fn_congr
  intro acc y hy
  simp [hy]