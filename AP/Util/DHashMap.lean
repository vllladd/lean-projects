import Std

import AP.Util.Array
import AP.Util.Sigma
import AP.Util.Finset
import AP.Util.Option
import AP.Util.Fintype
import AP.Util.Quotient
import AP.Util.Multiset

variable {α : Type*} {β : α → Type*} {γ : α → Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : Std.DHashMap α β}

namespace Std.DHashMap

@[simp]
theorem toList_empty : (∅ : Std.DHashMap α β).toList = [] := by
  ext:1; simp

@[simp]
theorem nodup_keys : mp.keys.Nodup := by
  unfold List.Nodup
  convert mp.distinct_keys
  simp

@[simp]
theorem nodup_toList : mp.toList.Nodup := by
  have h₁ := mp.nodup_keys
  rw [←map_fst_toList_eq_keys] at h₁
  exact List.Nodup.of_map _ h₁

theorem equiv_iff_get? {m₁ m₂ : Std.DHashMap α β} :
m₁.Equiv m₂ ↔ ∀ i, m₁.get? i = m₂.get? i := by
  constructor <;> intro h
  · intro i
    by_cases h₁ : i ∈ m₁ <;> have h₂ := h₁ <;> rw [h.mem_iff] at h₂
    · exact Equiv.get?_eq h
    · rw [get?_eq_none h₁, get?_eq_none h₂]
  rw [equiv_iff_toList_perm]
  rw [List.perm_ext_iff_of_nodup nodup_toList nodup_toList]
  rintro ⟨i, x⟩; simp [h]

theorem toList_ofList_perm {xs : List (Σ i, β i)}
(h : (xs.map (·.1)).Nodup) : (Std.DHashMap.ofList xs).toList.Perm xs := by
  rw [List.perm_ext_iff_of_nodup nodup_toList # h.of_map _]
  rintro ⟨i, x⟩
  simp
  constructor <;> intro h₁
  · contrapose! h₁
    by_cases h₂ : i ∈ ofList xs <;> simp at h₂
    · obtain ⟨y, h₂⟩ := h₂
      rw [get?_ofList_of_mem]
      rotate_left
      · simp
        rfl
      · exact y
      · simp
        unfold List.Nodup at h
        rw [List.pairwise_map] at h
        exact h
      · exact h₂
      simp
      rintro rfl
      contradiction
    rw [get?_ofList_of_contains_eq_false]; simp
    simpa
  rw [get?_ofList_of_mem]
  rotate_left
  · simp
    rfl
  · exact x
  · simp
    unfold List.Nodup at h
    rw [List.pairwise_map] at h
    exact h
  · exact h₁
  simp

@[simp]
theorem ofList_toList_equiv : ofList mp.toList ~m mp := by
  rw [equiv_iff_toList_perm]
  apply toList_ofList_perm
  simp

instance : HasEquiv (Std.DHashMap α β) :=
  ⟨Std.DHashMap.Equiv⟩

theorem equiv_def {m₁ m₂ : Std.DHashMap α β} : m₁ ≈ m₂ ↔ m₁ ~m m₂ := by rfl

def toSortedList [LinearOrder α] (m : Std.DHashMap α β) : List (Σ i, β i) :=
  m.toList.mergeSort (·.1 ≤ ·.1)

theorem toSortedList_eq_of [LinearOrder α] {m₁ m₂ : Std.DHashMap α β}
(h : m₁ ~m m₂) : m₁.toSortedList = m₂.toSortedList := by
  rename' m₁ => a
  rename' m₂ => b
  let r := λ (a b : Σ i, β i) => a.1 ≤ b.1
  change a.toList.mergeSort (r · ·) = b.toList.mergeSort (r · ·)
  rw [Std.DHashMap.equiv_iff_toList_perm] at h
  generalize hx : a.toList = xs at h ⊢
  generalize hy : b.toList = ys at h ⊢
  have h_tra : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → r a b → r b c → r a c :=
    λ a b c _ _ _ => Preorder.le_trans a.1 b.1 c.1
  have h_tot : ∀ a b, a ∈ xs → b ∈ xs → r a b ∨ r b a :=
    λ a b _ _ => LinearOrder.le_total a.1 b.1
  apply List.eq_of_perm_of_sorted_loc (r := r)
  · trans xs
    · apply List.mergeSort_perm
    apply h.trans; symm
    apply List.mergeSort_perm
  · exact List.sorted_mergeSort_loc h_tra h_tot
  · simp only [h.mem_iff] at h_tra h_tot
    exact List.sorted_mergeSort_loc h_tra h_tot
  all_goals simp only [List.mem_mergeSort]; try assumption
  clear h_tra h_tot
  rintro ⟨i, x⟩ ⟨j, y⟩ h₁ h₂ (h₃ : i ≤ j) (h₄ : j ≤ i)
  have h₅ := le_antisymm h₃ h₄; clear h₃ h₄
  subst h₅
  simp
  subst hx hy
  rw [Std.DHashMap.mem_toList_iff_get?_eq_some] at h₁ h₂
  simp [h₁] at h₂
  exact h₂

@[simp]
theorem toSortedList_eq [LinearOrder α] {m₁ m₂ : Std.DHashMap α β} :
m₁.toSortedList = m₂.toSortedList ↔ m₁ ~m m₂ := by
  refine' ⟨λ h => _, toSortedList_eq_of⟩
  unfold toSortedList at h
  rw [equiv_iff_toList_perm]
  exact List.perm_of_mergeSort_eq_mergeSort h

@[simp]
theorem nodup_toSortedList [LinearOrder α] : mp.toSortedList.Nodup := by
  simp [toSortedList]

@[simp]
theorem sorted_toSortedList [LinearOrder α] : mp.toSortedList.Sorted (·.1 ≤ ·.1) := by
  apply List.sorted_mergeSort_loc
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩
    simp
    intro h₁ h₂ h₃ h₄ h₅
    exact h₄.trans h₅
  · rintro ⟨i, x⟩ ⟨j, y⟩
    simp
    intro h₁ h₂
    apply le_total

@[simp]
theorem ofList_snoc {xs} {x : Σ i, β i} :
ofList (xs ++ [x]) = (ofList xs).insert x.fst x.snd := by
  simp_rw [ofList, insertMany_append]; rfl

@[simp]
theorem toList_eq_nil_iff : mp.toList = [] ↔ mp ~m ∅ := by
  rw [←toList_empty, List.ext_get_iff]
  simp [isEmpty_eq_size_eq_zero]

theorem fold_eq_fold_of_equiv {γ : Type*}
{f : γ → (i : α) → β i → γ} {z : γ} {m₁ m₂ : Std.DHashMap α β}
(h_assoc : ∀ {acc i x j y}, f (f acc i x) j y = f (f acc j y) i x)
(h : m₁ ~m m₂) : m₁.fold f z = m₂.fold f z := by
  simp [DHashMap.fold_eq_foldl_toList]
  replace h := Equiv.toList_perm h
  generalize m₁.toList = xs at h ⊢
  generalize m₂.toList = ys at h ⊢
  exact List.foldl_eq_foldl_of_perm h_assoc h

def decideEquiv [∀ i, DecidableEq # β i] (m₁ m₂ : DHashMap α β) : Bool :=
  m₁.size = m₂.size ∧ m₁.fold (λ acc i x => acc && m₂.get? i = some x) true

theorem mem_of_get?_eq_some {i x} (h : mp.get? i = some x) : i ∈ mp := by
  simp [mem_iff_isSome_get?, h]

theorem get?_eq_some_iff_find?_toList {i x} :
mp.get? i = some x ↔ mp.toList.find?
(λ (x : Σ (i : α), β i) => x.1 = i) = some ⟨i, x⟩ := by
  generalize hx : mp.toList = xs
  replace hx : mp.toList.Perm xs := by rw [hx]
  induction xs generalizing mp
  · simp at hx ⊢
    intro h
    replace h := mem_of_get?_eq_some h
    exact not_mem_of_isEmpty hx h
  nm y xs ih
  rcases y with ⟨j, y⟩
  simp
  have h₁ : ∀ z ∈ xs, z.1 ≠ j :=
    by
      rintro ⟨k, z⟩ hz rfl
      have h₁ := mp.nodup_keys
      dsimp at hx
      rw [←map_fst_toList_eq_keys] at h₁
      rw [List.nodup_map_iff_inj_on # by simp] at h₁
      specialize h₁ ⟨k, y⟩ _ ⟨k, z⟩ _
      · simp [hx.mem_iff]
      · simp [hx.mem_iff, hz]
      simp at h₁
      symm at h₁
      subst h₁
      replace hx : (⟨k, z⟩ :: xs).Nodup := by
        simp [hx.symm.nodup_iff]
      simp at hx
      tauto
  by_cases hj : j = i <;> simp [hj]
  · subst hj
    replace hx : mp.get? j = some y :=
      by
        rw [←mem_toList_iff_get?_eq_some]
        simp [hx.mem_iff]
    simp at hx
    simp [hx]
  specialize @ih (mp.erase j) _
  · rw [List.perm_ext_iff_of_nodup # by simp]
    · rintro ⟨k, z⟩
      simp
      rw [get?_erase]
      simp
      by_cases hk : j = k <;> simp [hk]
      · subst hk
        intro h
        specialize h₁ _ h
        simp at h₁
      rw [←mem_toList_iff_get?_eq_some]
      rw [hx.mem_iff]
      simp
      intro h₂
      tauto
    suffices (⟨j, y⟩ :: xs).Nodup from List.Nodup.of_cons this
    rw [hx.symm.nodup_iff]; simp
  rw [get?_erase] at ih
  simp [hj] at ih
  exact ih

@[simp]
theorem get_keys_eq_get_keys_iff
{i j} {h₁ : i < mp.keys.length} {h₂ : j < mp.keys.length} :
mp.keys[i] = mp.keys[j] ↔ i = j :=
  mp.nodup_keys.getElem_inj_iff

@[simp]
theorem fst_get_toList_eq_fst_get_toList_iff
{i j} {h₁ : i < mp.toList.length} {h₂ : j < mp.toList.length} :
mp.toList[i].fst = mp.toList[j].fst ↔ i = j := by
  have h₃ := @mp.get_keys_eq_get_keys_iff (i := i) (j := j)
  specialize @h₃ _ _
  · convert h₁; simp
  · convert h₂; simp
  simp only [←map_fst_toList_eq_keys, List.getElem_map] at h₃
  exact h₃

theorem equiv_iff_decideEquiv [hb : ∀ i, DecidableEq # β i]
{m₁ m₂ : DHashMap α β} : m₁ ~m m₂ ↔ m₁.decideEquiv m₂ := by
  symm; simp [decideEquiv]
  rw [fold_eq_foldl_toList]
  simp_rw [←length_toList]
  rw [equiv_iff_toList_perm]
  simp_rw [get?_eq_some_iff_find?_toList]
  rw [List.perm_iff_subset_of_nodup (by simp) (by simp)]
  generalize hx : m₁.toList = xs
  generalize hy : m₂.toList = ys
  simp [Sigma.eta, List.find?_eq_some_iff_getElem, decide_true,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
    true_and, List.foldl_and_eq_all, List.all_eq_true,
    decide_eq_true_eq]
  have hnx : xs.Nodup := by simp [←hx]
  have hny : ys.Nodup := by simp [←hy]
  have h₃ : ∀ i j (h : i < ys.length) (hj : j < i), ys[j].1 ≠ ys[i].1 :=
    by
      subst hy
      intro i j h₁ h₂
      simp
      linarith
  have h₄ : (∀ x ∈ xs, ∃ i, ∃ (h : i < ys.length), ys[i] = x ∧
    ∀ (j : ℕ) (hj : j < i), ¬ys[j].fst = x.fst) ↔
    ∀ x ∈ xs, ∃ i, ∃ (h : i < ys.length), ys[i] = x :=
    by
      constructor
      · intro h₁ x h₂
        specialize h₁ x h₂
        obtain ⟨y, h₃, h₄, h₅⟩ := h₁
        use y, h₃
      · intro h₁ x h₂
        specialize h₁ x h₂
        obtain ⟨y, h₃, h₄⟩ := h₁
        use y, h₃, h₄
        subst h₄
        nm h₅
        intro j hj
        exact h₅ y j h₃ hj
  rw [h₄]; clear h₃ h₄
  rw [List.exi_get_iff_subset]
  constructor
  · rintro ⟨h₁, h₂⟩
    use h₂
    exact List.subset_of_nodup_and_subset_and_length_eq hnx h₂ h₁
  rintro ⟨h₁, h₂⟩
  refine' ⟨_, h₁⟩
  exact List.length_eq_of_subset_and_nodup hnx hny h₁ h₂

instance [hh : ∀ i, DecidableEq # β i]
{m₁ m₂ : Std.DHashMap α β} : Decidable (m₁ ~m m₂) :=
  match h : m₁.decideEquiv m₂ with
  | true => isTrue # by rw [←equiv_iff_decideEquiv] at h; exact h
  | false => isFalse # by contrapose! h; simpa [←equiv_iff_decideEquiv]

@[simp]
theorem decideEquiv_eq [hh : ∀ i, DecidableEq # β i]
{m₁ m₂ : Std.DHashMap α β} : m₁.decideEquiv m₂ = decide (m₁ ~m m₂) := by
  simp [equiv_iff_decideEquiv]

def toSortedKeys [LinearOrder α] (m : Std.DHashMap α β) : List α :=
  m.toSortedList.map (·.1)

@[simp]
theorem nodup_toSortedKeys [LinearOrder α] : mp.toSortedKeys.Nodup := by
  unfold toSortedKeys toSortedList
  rw [List.nodup_map_iff_inj_on] <;> simp
  rintro ⟨i, x⟩ hx ⟨j, y⟩ hy h
  rw [mem_toList_iff_get?_eq_some] at hx hy
  dsimp at h
  subst h
  simp [hx] at hy
  simp [hy]

@[simp]
theorem sorted_toSortedKeys [LinearOrder α] : mp.toSortedKeys.Sorted (· ≤ ·) := by
  simp [toSortedKeys]

@[simp]
theorem toSortedList_perm_toList [LinearOrder α] : mp.toSortedList.Perm mp.toList := by
  simp [toSortedList]

@[simp]
theorem toList_perm_toSortedList [LinearOrder α] : mp.toList.Perm mp.toSortedList :=
  toSortedList_perm_toList.symm

@[simp]
theorem mem_toSortedList_iff {x} [LinearOrder α] :
x ∈ mp.toSortedList ↔ x ∈ mp.toList :=
  mp.toSortedList_perm_toList.mem_iff

theorem equiv_iff_toSortedList_perm [LinearOrder α] {m₁ m₂ : Std.DHashMap α β} :
m₁ ~m m₂ ↔ m₁.toSortedList.Perm m₂.toSortedList := by
  rw [equiv_iff_toList_perm]
  apply iff_of_isEquiv <;> simp

@[simp]
theorem nodup_map_fst_toSortedList [LinearOrder α] : (mp.toSortedList.map (·.1)).Nodup :=
  nodup_toSortedKeys

@[simp]
theorem mem_toSortedKeys {i} [LinearOrder α] : i ∈ mp.toSortedKeys ↔ i ∈ mp := by
  simp [toSortedKeys, ←Option.isSome_iff_exists]

@[simp]
theorem toSortedList_perm_iff [LinearOrder α] {m₁ m₂ : Std.DHashMap α β} :
m₁.toSortedList.Perm m₂.toSortedList ↔ m₁ ~m m₂ := by
  simp [toSortedList]; exact equiv_iff_toList_perm.symm

theorem toSortedKeys_eq_of_equiv [LinearOrder α] {m₁ m₂ : Std.DHashMap α β}
(h : m₁ ~m m₂) : m₁.toSortedKeys = m₂.toSortedKeys := by
  unfold toSortedKeys
  apply List.eq_of_perm_of_sorted_loc (r := (· ≤ ·)) <;> try simp
  · rw [List.map_perm_map_iff_loc]; try simpa
    rintro ⟨i, x⟩ ⟨j, y⟩ h₁ h₂ rfl
    simp
    rw [equiv_iff_get?] at h
    simp [h] at h₁ h₂
    simp [h₁] at h₂
    exact h₂
  · intro i j k x h₁ y h₂ z h₃ h₄ h₅
    exact h₄.trans h₅
  · intro i j k h₁ x h₂
    apply le_total
  · intro i j x h₁ y h₂
    exact le_antisymm

@[simp]
theorem toSortedKeys_eq_iff_of_subsingleton [LinearOrder α] {m₁ m₂ : Std.DHashMap α β}
[hb : ∀ i, Subsingleton # β i] :
m₁.toSortedKeys = m₂.toSortedKeys ↔ m₁ ~m m₂ := by
  refine' ⟨λ h => _, toSortedKeys_eq_of_equiv⟩
  rw [equiv_iff_toSortedList_perm]
  rw [List.perm_iff_mem_iff_of_nodup (by simp) (by simp)]
  rintro ⟨i, x⟩
  replace h := congrArg (i ∈ ·) h
  simp [Option.eq_iff_of_subsingleton] at h ⊢
  exact h

@[simp]
theorem toSortedList_eq_nil_iff [LinearOrder α] : mp.toSortedList = [] ↔ mp ~m ∅ := by
  simp [toSortedList]

@[simp]
theorem toSortedKeys_eq_nil_iff [LinearOrder α] : mp.toSortedKeys = [] ↔ mp ~m ∅ := by
  simp [toSortedKeys]

def all (mp : DHashMap α β) (p : (i : α) → β i → Bool) : Bool :=
  mp.fold (λ acc i x => acc && p i x) true

@[simp]
theorem all_def {p} : mp.all p = decide (∀ x ∈ mp.toList, p x.1 x.2) := by
  simp [all, fold_eq_foldl_toList, List.foldl_and_eq_all]
  rw [Bool.eq_iff_iff]; simp

@[simp]
theorem mem_toList_iff_get?_eq_some' (x : (i : α) × β i) :
x ∈ mp.toList ↔ mp.get? x.1 = some x.2 := by
  rcases x with ⟨i, x⟩; simp

@[simp]
def modifyMany (mp : DHashMap α β) :
List ((i : α) × (β i → β i)) → DHashMap α β
| [] => mp
| ⟨i, f⟩ :: xs => mp.modify i f |>.modifyMany xs

theorem modify_equiv_modify_of_equiv
{m₁ m₂ : Std.DHashMap α β} {i x} (h : m₁ ~m m₂) :
m₁.modify i x ~m m₂.modify i x := h.modify i x

theorem modifyMany_equiv_modifyMany_of_equiv
{m₁ m₂ : Std.DHashMap α β} {xs} (h : m₁ ~m m₂) :
m₁.modifyMany xs ~m m₂.modifyMany xs := by
  induction xs generalizing m₁ m₂; simpa
  nm x xs ih
  rcases x with ⟨i, x⟩
  simp
  exact ih # h.modify i x

theorem mem_iff_get?_eq_some {i : α} : i ∈ mp ↔ ∃ x, mp.get? i = some x := by
  rw [←Option.isSome_iff_exists]
  exact mem_iff_isSome_get?

theorem get?_eq_ite {i} [hb : Inhabited # β i] :
mp.get? i = if i ∈ mp then some # mp.get! i else none := by
  rw [get!_eq_get!_get?]
  split_ifs with h₁ <;> simp [mem_iff_get?_eq_some] at h₁
  · obtain ⟨x, h₁⟩ := h₁; simp [h₁]
  · rw [Option.eq_none_iff_forall_ne_some.mpr h₁]

theorem get?_ofList_eq_some_iff {xs : List ((i : α) × β i)} {i x}
(h : (xs.map (·.1)).Nodup) : (ofList xs).get? i = some x ↔ ⟨i, x⟩ ∈ xs := by
  induction xs using List.reverseRecOn; simp
  nm xs y ih
  rcases y with ⟨j, y⟩
  simp [get?_insert]
  simp [List.map_append] at h
  rcases h with ⟨h₁, h₂⟩
  specialize ih h₂
  split_ifs with h₃
  · subst h₃; simp [h₁]; exact eq_comm
  · simp [ih, ne_symm' h₃]

@[simp]
theorem get?_eq_some_get!_iff {i} [hb : Inhabited (β i)] :
mp.get? i = some (mp.get! i) ↔ i ∈ mp := by
  simp [get?_eq_ite]

@[simp]
theorem get?_eq_some_get?_get! {i} [hb : Inhabited (β i)] :
mp.get? i = some (mp.get? i).get! ↔ i ∈ mp := by
  simp [←get!_eq_get!_get?]

theorem ofList_equiv_ofList_of_nodup_and_perm {xs ys : List ((i : α) × β i)}
(hx : xs.map (·.1) |>.Nodup) (hy : ys.map (·.1) |>.Nodup) (h : xs.Perm ys) :
ofList xs ~m ofList ys := by
  rw [equiv_iff_toList_perm]
  trans xs; exact toList_ofList_perm hx
  trans ys; exact h; symm; exact toList_ofList_perm hy

@[simp]
theorem ofList_toSortedList_equiv [ha : LinearOrder α] :
ofList mp.toSortedList ~m mp := by
  rw [equiv_iff_toList_perm]
  trans (ofList mp.toList).toList
  rotate_left; apply toList_ofList_perm; simp
  suffices h₁ : ofList mp.toList ~m ofList mp.toSortedList
  · exact h₁.symm.toList_perm
  apply ofList_equiv_ofList_of_nodup_and_perm <;> simp

section foldlWith

namespace Internal

open Raw

omit hh₂ in
theorem distinctKeys_def {xs : List ((i : α) × β i)} :
Internal.List.DistinctKeys xs ↔
(Internal.List.keys xs).Pairwise (λ a b => (a == b) = false) :=
  ⟨λ ⟨h⟩ => h, λ h =>  ⟨h⟩⟩

omit hh₂ in
theorem distinctKeys_iff {xs : List ((i : α) × β i)} :
Internal.List.DistinctKeys xs ↔ (xs.map (·.1)).Nodup := by
  rw [distinctKeys_def, Internal.List.keys_eq_map]
  simp [List.pairwise_map, List.nodup_iff_pairwise_ne]

omit hh₂ in
private theorem AssocList.foldlWith_getCast?_cons_aux
{xs : AssocList α β} {i j : α} {x : β i} {y : β j}
(h₁ : (cons i x xs).toList.map (·.1) |>.Nodup)
(h₂ : xs.getCast? j = some y) : (cons i x xs).getCast? j = some y := by
  simp at h₁
  rcases h₁ with ⟨h₁, h₃⟩
  simp at h₂ ⊢
  rwa [Internal.List.getValueCast?_cons_of_false]
  simp
  rintro rfl
  rw [←Internal.List.mem_iff_getValueCast?_eq_some] at h₂
  rotate_left
  · rwa [distinctKeys_iff]
  simp [h₁] at h₂

@[simp]
def AssocList.foldlWith {γ : Sort*} (xs : AssocList α β)
(f : γ → (i : α) → (x : β i) → xs.getCast? i = some x → γ) (z : γ)
(h : xs.toList.map (·.1) |>.Nodup) : γ :=
  match h₁ : xs with
  | .nil => z
  | .cons i x ys => ys.foldlWith
    (λ acc j y h₂ => f acc j y # foldlWith_getCast?_cons_aux h h₂)
    (f z i x # by simp) (by simp at h; exact h.2)

open Classical in omit hh₂ in
theorem foldlWith_eq_foldl {γ : Type*} {xs : AssocList α β}
{f : γ → (i : α) → (x : β i) → xs.getCast? i = some x → γ} {z : γ}
(h : xs.toList.map (·.1) |>.Nodup) :
xs.foldlWith f z h = xs.foldl (λ acc i x =>
if h : xs.getCast? i = some x then f acc i x h else z) z := by
  simp
  induction xs generalizing z <;> simp
  nm i x xs ih
  simp at h
  rcases h with ⟨h₁, h₂⟩
  rw [ih]
  apply List.foldl_eq_foldl_of_fn_congr
  rintro acc ⟨j, y⟩ hj
  split_ifs with h₃ h₄ h₄; rfl
  any_goals
    rw [Internal.List.getValueCast?_cons_of_false] at h₄; contradiction
    simp
    rintro rfl
    simp [h₁] at hj
  simp at h₃
  rw [Internal.List.mem_iff_getValueCast?_eq_some] at hj; contradiction
  rwa [distinctKeys_iff]

-- #check DHashMap.distinct_keys

theorem bucket_nodup_keys {mp : Raw α β} {b} (wf : mp.WF)
(h : b ∈ mp.buckets) : b.toList.map (·.1) |>.Nodup := by
  sorry

-- #check 0 #exit

theorem mem_toList_of_mem_bucket {mp : Raw α β} {x b} (wf : mp.WF)
(h₁ : b ∈ mp.buckets) (h₂ : x ∈ b.toList) : x ∈ mp.toList := by
  sorry

end Internal

open Internal

def Raw.foldlWith {γ : Sort*} (mp : Raw α β) (wf : mp.WF)
(f : γ → (i : α) → (x : β i) → Raw₀.get? ⟨mp, wf.size_buckets_pos⟩ i = some x → γ)
(z : γ) : γ :=
  (mp.buckets.foldlWith · z) # λ acc xs h₁ => xs.foldlWith (γ := γ)
  (λ acc' i' x h₂ => f acc i' x # by
    simp at h₂
    rw [←Internal.List.mem_iff_getValueCast?_eq_some] at h₂
    rotate_left; simp [distinctKeys_iff]; exact bucket_nodup_keys wf h₁
    rw [←Raw₀.mem_toList_iff_get?_eq_some]
    rotate_left; simpa
    simp
    exact mem_toList_of_mem_bucket wf h₁ h₂
  ) acc (bucket_nodup_keys wf h₁)

end foldlWith