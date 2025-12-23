import AP.Util

section logic

variable {α β γ : Type*}

theorem setoid_apply_of_eq {s : Setoid α} {x y : α} (h : x = y) : s x y := by
  rw [h]

theorem Equivalence.comm {r : α → α → Prop} {a b} (h : Equivalence r) : r a b ↔ r b a :=
  ⟨h.symm, h.symm⟩

theorem Equivalence.iff_of_left {r : α → α → Prop} {a b c}
(h₁ : Equivalence r) (h₂ : r a b) : r a c ↔ r b c :=
  ⟨h₁.trans # h₁.symm h₂, h₁.trans h₂⟩

theorem Equivalence.iff_of_right {r : α → α → Prop} {a b c}
(h₁ : Equivalence r) (h₂ : r a b) : r c a ↔ r c b := by
  nth_rw 1 [h₁.comm]; nth_rw 2 [h₁.comm]; exact h₁.iff_of_left h₂

-- #check 0 #exit

end logic

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

@[simp]
theorem perm_comm_simp : (xs ~ ys ↔ ys ~ xs) ↔ True := by
  simp [perm_comm]

@[simp]
theorem equivalence_perm : Equivalence # @Perm α where
  refl := Perm.refl
  symm := Perm.symm
  trans := Perm.trans

theorem perm_iff_perm_of_left (h : xs ~ ys) : xs ~ zs ↔ ys ~ zs :=
  Equivalence.iff_of_left (by simp) h

theorem perm_iff_perm_of_right (h : xs ~ ys) : zs ~ xs ↔ zs ~ ys :=
  Equivalence.iff_of_right (by simp) h

@[simp]
theorem mergeSort_perm_iff {p} : xs.mergeSort p ~ ys ↔ xs ~ ys := by
  constructor; all_goals intro h; symm at h ⊢; apply h.trans; simp

@[simp]
theorem perm_mergeSort_iff {p} : xs ~ ys.mergeSort p ↔ xs ~ ys := by
  nth_rw 1 [perm_comm]; simp

@[simp]
theorem cons_mergeSort_perm_iff {p x} : x :: xs.mergeSort p ~ ys ↔ x :: xs ~ ys := by
  apply perm_iff_perm_of_left; trans (x :: xs).mergeSort p <;> simp

@[simp]
theorem perm_cons_mergeSort_iff {p y} : xs ~ y :: ys.mergeSort p ↔ xs ~ y :: ys := by
  apply perm_iff_perm_of_right; trans (y :: ys).mergeSort p <;> simp

@[simp]
theorem modify_length_append {f} : (xs ++ ys).modify xs.length f = xs ++ ys.modify 0 f := by
  induction xs; simp; simpa

theorem sorted_lt_of_sorted_le [ha : LinearOrder α]
(h₁ : xs.Sorted (· ≤ ·)) (h₂ : xs.Nodup) : xs.Sorted (· < ·) :=
  Sorted.lt_of_le h₁ h₂

theorem eq_and_eq_of_append_cons_eq {xs' ys' x} (h₁ : xs ++ x :: ys = xs' ++ x :: ys')
(h₂ : x ∉ xs) (h₃ : x ∉ xs') : xs = xs' ∧ ys = ys' := by
  induction xs generalizing xs' <;> cases xs' <;> grind

theorem map_modify_eq_of {i} {f : α → α} {g : α → β}
(h : ∀ x ∈ xs, g (f x) = g x) : (xs.modify i f).map g = xs.map g := by
  induction xs generalizing i
  · simp
  clear! xs; nm x xs ih
  simp [modify_cons]
  cases i <;> simp
  · apply h; simp
  nm i
  apply ih
  grind

-- #check 0 #exit

end List

namespace Set

variable {α β γ : Type*}
variable {s s₁ s₂ : Set α}

-- #check 0 #exit

end Set

namespace Std.DHashMap

open Std

variable {α : Type*} {β : α → Type*} {γ : α → Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp mp₁ mp₂ : DHashMap α β}

theorem eq_iff_inner : mp₁ = mp₂ ↔ mp₁.inner = mp₂.inner := by
  cases mp₁; cases mp₂; simp

theorem modify_of_notMem {i f} (h : i ∉ mp) : mp.modify i f = mp := by
  simp [eq_iff_inner, modify, Internal.Raw₀.modify]
  rw [if_neg]; simp; change ¬mp.contains i at h
  simp [contains, Internal.Raw₀.contains] at h; exact h

-- #check 0 #exit

end Std.DHashMap

namespace Std.ExtDHashMap

open Std

variable {α : Type*} {β : α → Type*} {γ : α → Type*}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp mp₁ mp₂ : ExtDHashMap α β}
variable [ha : LinearOrder α]
omit ha

theorem eq_iff_inner : mp₁ = mp₂ ↔ mp₁.inner = mp₂.inner := by
  cases mp₁; cases mp₂; simp

@[simp]
theorem mem_mk_iff {mp : DHashMap α β} {i} : i ∈ (⟨⟦mp⟧⟩ : ExtDHashMap α β) ↔ i ∈ mp := by
  rfl

theorem modify_of_notMem {i f} (h : i ∉ mp) : mp.modify i f = mp := by
  rcases mp with ⟨mp⟩
  induction mp using Quotient.inductionOn
  nm mp
  simp [modify, lift]
  simp at h
  apply setoid_apply_of_eq # DHashMap.modify_of_notMem h

include ha in
theorem toList_insert_perm_cons_of_notMem {i x} (h : i ∉ mp) :
(mp.insert i x).toList.Perm (⟨i, x⟩ :: mp.toList) := by
  rcases mp with ⟨mp⟩
  induction mp using Quotient.inductionOn; nm mp
  simp at h
  simp [insert, lift, toList, DHashMap.toSortedList]
  exact DHashMap.toList_insert_perm_cons_of_not_mem h

include ha in @[simp]
theorem nodup_keys : mp.keys.Nodup := by
  rcases mp with ⟨mp⟩
  induction mp using Quotient.inductionOn; nm mp
  simp [keys, lift]

include ha in @[simp]
theorem sorted_keys' : mp.keys.Sorted (· < ·) := by
  apply List.sorted_lt_of_sorted_le <;> simp

-- #check 0 #exit

end Std.ExtDHashMap

namespace Map

open Std

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
variable {mp : Map α β}
variable [ha : LinearOrder α]
omit ha

@[simp]
theorem modifyMany_snoc {xs i f} :
mp.modifyMany (xs ++ [(i, f)]) = (mp.modifyMany xs).modify i f := by
  induction xs generalizing mp; simp
  nm x xs ih; rcases x with ⟨j, g⟩; simp [ih]

@[simp]
theorem modify_empty {i f} : (∅ : Map α β).modify i f = ∅ := by
  simp [empty_def, modify]

@[simp]
theorem mem_mk_iff {mp i} : i ∈ (⟨mp⟩ : Map α β) ↔ i ∈ mp := by
  rfl

theorem modify_of_notMem {i f} (h : i ∉ mp) : mp.modify i f = mp := by
  rcases mp with ⟨mp⟩
  rw [modify]
  simp at h ⊢
  exact ExtDHashMap.modify_of_notMem h

theorem modify_insert_of_ne {i x j f} (h : i ≠ j) :
(mp.insert i x).modify j f = (mp.modify j f).insert i x := by
  ext; simp [get?_insert]; grind

include ha in @[simp]
theorem toList_mk {mp} : (⟨mp⟩ : Map α β).toList = mp.toList.map Sigma.toProd := by
  rcases mp with ⟨mp⟩; induction mp using Quotient.inductionOn; nm mp; rfl

include ha in
theorem toList_insert_perm_cons_of_notMem {i x} (h : i ∉ mp) :
(mp.insert i x).toList.Perm (⟨i, x⟩ :: mp.toList) := by
  rcases mp with ⟨mp⟩
  simp at h
  have h₁ := ExtDHashMap.toList_insert_perm_cons_of_notMem h (x := x)
  simp [Map.insert]
  change List.Perm _ # Sigma.toProd ⟨i, x⟩ :: _
  rwa [←List.map_cons, List.map_perm_map_iff]; simp

include ha in
theorem values_insert_perm_of_notMem {i x} (h : i ∉ mp) :
(mp.insert i x).values.Perm (x :: mp.values) := by
  simp_rw [values]; have := toList_insert_perm_cons_of_notMem h (x := x); grind

@[simp]
theorem modify_insert_of_eq {i x f} : (mp.insert i x).modify i f = mp.insert i (f x) := by
  ext; simp [get?_insert]; grind

include ha in
theorem countP_values_modify_eq_of
{p : β → Bool} {i : α} {f : β → β} (h : ∀ x, p (f x) = p x) :
(mp.modify i f).values.countP p = mp.values.countP p := by
  by_cases h₁ : i ∉ mp; rw [modify_of_notMem h₁]
  push_neg at h₁
  induction mp using ind; simp
  clear! mp
  nm mp j x ih hk
  simp at h₁
  rcases h₁ with rfl | h₁
  · clear ih
    simp
    apply List.Perm.countP_eq p (values_insert_perm_of_notMem hk) |>.trans; symm
    apply List.Perm.countP_eq p (values_insert_perm_of_notMem hk) |>.trans
    simp [List.countP_cons]
    rw [h]
  have h₂ : i ≠ j; grind
  specialize ih h₁
  rw [modify_insert_of_ne # ne_symm' h₂]
  have h₃ : j ∉ mp.modify i f; simpa
  apply List.Perm.countP_eq p (values_insert_perm_of_notMem h₃) |>.trans; symm
  apply List.Perm.countP_eq p (values_insert_perm_of_notMem hk) |>.trans
  simp [List.countP_cons, ih]

include ha in
theorem countP_values_modifyMany_eq_of
{p : β → Bool} {xs : List (α × (β → β))}
(h : ∀ k f x, (k, f) ∈ xs → p (f x) = p x) :
(mp.modifyMany xs).values.countP p = mp.values.countP p := by
  induction xs using List.reverseRecOn; simp
  nm xs x ih
  rcases x with ⟨k, f⟩
  simp
  rw [←ih # by grind]
  clear ih
  rw [countP_values_modify_eq_of]
  specialize h k f
  grind

theorem size_insert {i x} (h : i ∉ mp) : (mp.insert i x).size = mp.size + 1 := by
  rcases mp with ⟨mp⟩; simp [Map.insert, size] at h ⊢; simp [ExtDHashMap.size_insert, h]

@[simp]
theorem size_modify {i f} : (mp.modify i f).size = mp.size := by
  cases mp; simp [modify, size]

include ha in
theorem get?_eq_some_iff {i x} : mp.get? i = some x ↔ (i, x) ∈ mp.toList := by
  simp

include ha in @[simp]
theorem nodup_keys : mp.keys.Nodup := by
  simp [keys]

include ha in @[simp]
theorem sorted_keys' : mp.keys.Sorted (· < ·) := by
  simp [keys]

include ha in @[simp]
theorem mem_keys_iff_mem {k} : k ∈ mp.keys ↔ k ∈ mp := by
  simp [←mem_iff_mem_keys]

include ha in @[simp]
theorem length_keys : mp.keys.length = mp.size := by
  simp [keys_eq_map_fst_toList]

include ha in @[simp]
theorem keys_modify {i f} : (mp.modify i f).keys = mp.keys := by
  apply List.eq_of_perm_of_sorted (r := (· < ·)) <;> try simp
  apply List.perm_of_nodup_and_subset_and_length_eq <;> try simp
  intro; simp

def erase (mp : Map α β) (i : α): Map α β :=
  ⟨mp.1.erase i⟩

@[simp]
theorem mem_erase {i j} : j ∈ mp.erase i ↔ j ≠ i ∧ j ∈ mp := by
  rcases mp with ⟨mp⟩; simp [erase]; grind

include ha in @[simp]
theorem sorted_toList' : mp.toList.Sorted (·.1 < ·.1) := by
  suffices h : mp.toList.map (·.1) |>.Sorted (· < ·)
  · simp at h; exact h
  rw [←keys_eq_map_fst_toList]; simp

include ha in
theorem values_eq_map_snd_toList : mp.values = mp.toList.map (·.2) := rfl

def keyIdx (mp : Map α β) (i : α) : ℕ :=
  mp.keys.idxOf i

include ha in
theorem keyIdx_lt_size {i} (h : i ∈ mp) : mp.keyIdx i < mp.size := by
  rw [keyIdx, ←length_keys]; apply List.idxOf_lt_length_of_mem; simpa

-- #check 0 #exit

include ha in
theorem toList_modify_eq_list_modify {i f} (h : i ∈ mp) :
(mp.modify i f).toList = mp.toList.modify (mp.keyIdx i) (λ p => (p.1, f p.2)) := by
  rename' h => h₁
  have h₂ : i ∈ mp.modify i f; simpa
  rw [mem_iff_mem_keys, keys_eq_map_fst_toList, List.mem_map] at h₁ h₂
  obtain ⟨⟨i, y⟩, h₁, rfl⟩ := h₁
  obtain ⟨⟨j, z⟩, h₂, rfl⟩ := h₂
  dsimp at *
  rw [List.mem_iff_append] at h₁ h₂
  choose xs ys h₁ using h₁
  choose xs' ys' h₂ using h₂
  rw [h₁, h₂]
  have h₃ : (mp.modify j f).keys = mp.keys; simp
  have h₄' := mp.nodup_keys
  have h₅' := mp.modify j f |>.nodup_keys
  simp_rw [keys_eq_map_fst_toList] at h₃ h₄' h₅'
  simp [h₁, h₂] at h₃ h₄' h₅'
  have h₄ : j ∉ xs.map (·.1); grind
  have h₅ : j ∉ xs'.map (·.1); grind
  obtain ⟨h₆, h₇⟩ := List.eq_and_eq_of_append_cons_eq h₃ h₅ h₄
  have H : ∃ k, k = xs.length ∧ (xs' ++ (j, z) :: ys').map (·.1) =
    ((xs ++ (j, y) :: ys).modify k # λ p => (p.1, f p.2)).map (·.1)
  · simp [h₆, h₇]
  choose k hk' H using H
  have hk : k < mp.size
  · replace h₁ := congrArg (·.length) h₁
    simp at h₁
    omega
  rw [←h₁, ←h₂] at H ⊢
  have h : mp.keyIdx j = k
  · rw [keyIdx, keys_eq_map_fst_toList, h₁]; simp
    rw [List.idxOf_append]; simp [h₄, hk']
  rw [h]; clear h
  generalize H₁ : (mp.modify j f).toList = xs at H ⊢
  generalize H₂ : (mp.toList.modify k # λ p => (p.1, f p.2)) = ys at H ⊢
  have G₁ : ∀ i x, (i, x) ∈ ys → (i, x) ∈ xs
  · rename' xs => xs₁, ys => ys₁
    subst hk'
    intro c x G₁
    simp [←H₂] at G₁
    simp [h₁] at G₁
    rw [←H₁, h₂]
    simp
    rcases G₁ with G₁ | ⟨G₁, G₂⟩ | G₁
    · left
      have hc : c ≠ j
      · simp at h₄
        grind
      have G₂ : mp.get? c = some x
      · rw [get?_eq_some_iff, h₁]
        simp [G₁]
      replace G₂ : (mp.modify j f).get? c = some x
      · simpa [hc]
      rw [get?_eq_some_iff, h₂] at G₂
      simp [hc] at G₂
      rcases G₂ with G₂ | G₂; exact G₂
      exfalso
      replace G₁ : c ∈ xs.map (·.1); grind
      replace G₂ : c ∈ ys'.map (·.1); grind
      grind
    · subst G₁ G₂
      right; left
      simp
      replace h₁ := congrArg ((c, y) ∈ ·) h₁
      replace h₂ := congrArg ((c, z) ∈ ·) h₂
      simp at h₁
      simp [h₁] at h₂
      exact h₂
    · right; right
      have hc : c ≠ j
      · simp at h₄; grind
      have G₂ : mp.get? c = some x
      · rw [get?_eq_some_iff, h₁]
        simp [G₁]
      replace G₂ : (mp.modify j f).get? c = some x
      · simpa [hc]
      rw [get?_eq_some_iff, h₂] at G₂
      simp [hc] at G₂; symm at G₂
      rcases G₂ with G₂ | G₂; exact G₂
      exfalso
      replace G₁ : c ∈ ys.map (·.1); grind
      replace G₂ : c ∈ xs'.map (·.1); grind
      grind
  have H₁' : (xs.map (·.1)).Nodup
  · simp [←H₁, ←keys_eq_map_fst_toList]
  replace H₁ : xs.Sorted (·.1 ≤ ·.1)
  · simp [←H₁]
  have H₃ : ys.Sorted (·.1 < ·.1)
  · rw [←H₂, ←List.sorted_map]; simp [List.map_modify_eq_of]
  replace H₂ : ys.Sorted (·.1 ≤ ·.1)
  · rw [←H₂, ←List.sorted_map]; simp [List.map_modify_eq_of]
  replace H₃ : (ys.map (·.1)).Nodup
  · rw [←List.sorted_map] at H₃
    exact H₃.nodup
  nm a b; clear! a b xs' ys' z j f k y
  apply List.eq_of_perm_of_sorted_loc (r := (·.1 ≤ ·.1)) _ H₁ H₂ <;> try simp
  · intro i x j y h₁ h₂ h₃ h₄
    apply and_of
    · exact _root_.le_antisymm h₃ h₄
    rintro rfl
    clear h₃ h₄
    by_contra h₃
    rw [List.mem_iff_getElem] at h₁ h₂
    choose k₁ hk₁ h₁ using h₁
    choose k₂ hk₂ h₂ using h₂
    have h₄ : k₁ ≠ k₂; grind
    replace h₁ : (xs.map (·.1))[k₁]'(by grind) = i; grind
    replace h₂ : (ys.map (·.1))[k₂]'(by grind) = i; grind
    apply h₄
    rw! [←H] at h₂
    rw! [←h₂] at h₁
    rwa [←H₁'.getElem_inj_iff]
  apply List.perm_of_nodup_and_subset_and_length_eq
  · exact List.Nodup.of_map _ H₃
  · rintro ⟨i, x⟩ h₁; grind
  · replace H := congrArg (·.length) H
    simp at H; exact H.symm

include ha in
theorem keyIdx_eq_of_toList_eq_append {i x xs ys}
(h : mp.toList = xs ++ (i, x) :: ys) : mp.keyIdx i = xs.length := by
  rw [keyIdx, keys_eq_map_fst_toList, h]
  simp
  rw [List.idxOf_append]
  simp
  intro y h₁
  exfalso
  replace h := congrArg (·.map (·.1) |>.Nodup) h
  simp [←keys_eq_map_fst_toList] at h
  grind

include ha in
theorem values_modify_eq_list_modify {i f} (h : i ∈ mp) :
(mp.modify i f).values = mp.values.modify (mp.keyIdx i) f := by
  simp_rw [values_eq_map_snd_toList, toList_modify_eq_list_modify h]
  rw [←mem_keys_iff_mem, keys_eq_map_fst_toList, List.mem_map] at h
  obtain ⟨⟨i, x⟩, h, rfl⟩ := h
  dsimp
  rw [List.mem_iff_append] at h
  choose xs ys h using h
  rw [h, keyIdx_eq_of_toList_eq_append h]
  simp
  rw [show xs.length = (xs.map (·.2)).length by simp]
  rw [List.modify_length_append]; simp

include ha in
theorem countP_values_modify_eq_ite_of_get? {p : β → Bool} {i x f}
(h : mp.get? i = some x) : (mp.modify i f).values.countP p = mp.values.countP p +
(if p # f x then 1 else 0) - (if p x then 1 else 0) := by
  rw [values_modify_eq_list_modify # mem_of_get?_eq_some h]
  simp_rw [values_eq_map_snd_toList]
  rw [get?_eq_some_iff] at h
  rw [List.mem_iff_append] at h
  choose xs ys h using h
  rw [h, keyIdx_eq_of_toList_eq_append h]
  simp
  rw [show xs.length = (xs.map (·.2)).length by simp]
  rw [List.modify_length_append]; simp
  grind

-- #check 0 #exit

end Map

namespace Set'

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}
variable [ha₁ : DecidableEq α] [ha₂ : Hashable α]
variable [hb₁ : DecidableEq β] [hb₂ : Hashable β]
variable [hc₁ : DecidableEq γ] [hc₂ : Hashable γ]
variable {s s' s₁ s₂ s₃ : Set' α}
variable [ha : LinearOrder α]
omit ha

-- #check 0 #exit

end Set'