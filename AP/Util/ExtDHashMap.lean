import AP.Util.DHashMap

variable {α : Type*} {β : α → Type*} {γ : α → Type*}
variable [hh₁ : LinearOrder α] [hh₂ : Hashable α]
variable {mp : Std.ExtDHashMap α β}

namespace Std.ExtDHashMap

@[simp]
theorem not_mem_empty' {i : α} : i ∉ (∅ : Std.ExtDHashMap α β) :=
  not_mem_empty

@[simp]
theorem not_mem_lift_empty {i : α} :
¬Membership.mem (γ := Std.ExtDHashMap α β) ⟨⟦∅⟧⟩ i :=
  not_mem_empty

theorem mem_iff_get?_eq_some {i : α} : i ∈ mp ↔ ∃ x, mp.get? i = some x := by
  rw [←Option.isSome_iff_exists]
  exact mem_iff_isSome_get?

theorem get?_eq_some_of_mem {i : α} (h : i ∈ mp) : ∃ x, mp.get? i = some x := by
  rwa [←mem_iff_get?_eq_some]

theorem get?_eq_none_of_not_mem {i : α} (h : i ∉ mp) : mp.get? i = none := by
  simp [mem_iff_get?_eq_some] at h
  rwa [Option.eq_none_iff_forall_ne_some]

@[simp]
theorem get?_eq_none_iff {i} : mp.get? i = none ↔ i ∉ mp := by
  refine' ⟨_, get?_eq_none_of_not_mem⟩
  intro h
  contrapose! h
  obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
  simp [hx]

def toList (mp : Std.ExtDHashMap α β) : List (Σ i, β i) :=
  mp.lift Std.DHashMap.toSortedList # by simp

@[simp]
theorem toList_empty : (∅ : Std.ExtDHashMap α β).toList = [] := by
  change List.mergeSort _ _ = _; simp

@[simp]
theorem ofList_snoc {xs} {x : Σ i, β i} :
ofList (xs ++ [x]) = Insert.insert x (ofList xs) := by
  dsimp
  unfold Std.ExtDHashMap.ofList Std.ExtDHashMap.insert
  rw [Std.DHashMap.ofList_snoc]; rfl

@[simp]
theorem mem_insert' {x : Σ i, β i} {i} :
i ∈ Insert.insert x mp ↔ i = x.1 ∨ i ∈ mp := by
  simp; tauto

@[simp]
theorem mem_ofList' {xs : List (Σ i, β i)} {i} :
i ∈ ofList xs ↔ ∃ x, ⟨i, x⟩ ∈ xs := by
  change contains _ _ ↔ _
  simp only [contains_ofList, List.contains_eq_mem, List.mem_map,
    Sigma.exists, exists_and_right, exists_eq_right, decide_eq_true_eq]

theorem eq_empty_iff : mp = ∅ ↔ ∀ i, i ∉ mp := by
  change mp = ⟨⟦∅⟧⟩ ↔ _
  rcases mp with ⟨mp⟩
  simp
  apply mp.ind
  intro m
  rw [Quotient.eq_iff_equiv]
  change m.Equiv ∅ ↔ _
  simp
  exact Std.DHashMap.isEmpty_iff_forall_not_mem

theorem ext_iff' {m₁ m₂ : Std.ExtDHashMap α β} :
m₁ = m₂ ↔ m₁.1.out.Equiv m₂.1.out := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩
  symm; simp
  induction m₁, m₂ using Quotient.inductionOn₂
  nm m₁ m₂
  change ⟦m₁⟧.out ≈ ⟦m₂⟧.out ↔ _
  rw [Quotient.eq_iff_equiv]
  simp
  rfl

theorem ext_iff {m₁ m₂ : Std.ExtDHashMap α β} :
m₁ = m₂ ↔ ∀ i, m₁.get? i = m₂.get? i := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp
  induction m₁, m₂ using Quotient.inductionOn₂
  rw [Quotient.eq_iff_equiv]
  exact Std.DHashMap.equiv_iff_get?

theorem get?_eq_ite_of_unit {m : Std.ExtDHashMap α (λ _ => Unit)} {i} :
m.get? i = if i ∈ m then some () else none := by
  split_ifs with h
  · obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
    simp [hx]
  rw [get?_eq_none_of_not_mem h]

theorem ofList_eq_ofList_iff {xs ys : List (Σ i, β i)}
(hx : (xs.map (·.1)).Nodup) (hy : (ys.map (·.1)).Nodup) :
ofList xs = ofList ys ↔ xs.Perm ys := by
  have hx' := hx.of_map _
  have hy' := hy.of_map _
  simp [ofList]
  change Std.DHashMap.Equiv _ _ ↔ _
  rw [Std.DHashMap.equiv_iff_toList_perm]
  rw [List.perm_ext_iff_of_nodup hx' hy']
  rw [List.perm_ext_iff_of_nodup (by simp) (by simp)]
  apply forall_congr'
  rintro ⟨i, x⟩
  simp
  generalize h₁ : Std.DHashMap.ofList xs = m₁
  generalize h₂ : Std.DHashMap.ofList ys = m₂
  have h₃ : xs.Perm m₁.toList :=
    by
      subst h₁
      exact (Std.DHashMap.toList_ofList_perm hx).symm
  have h₄ : ys.Perm m₂.toList :=
    by
      subst h₂
      exact (Std.DHashMap.toList_ofList_perm hy).symm
  rw [h₃.mem_iff, h₄.mem_iff]
  simp

def range [ha : Fintype α] (f : (i : α) → β i) : Std.ExtDHashMap α β := by
  rcases ha with ⟨⟨m, hm⟩, ha⟩
  refine' m.liftWith _ _
  · intro xs
    exact ofList # xs.map # λ i => ⟨i, f i⟩
  clear ha
  replace hm : m.toList.Nodup := by simpa
  intro xs ys (hx : m.toList.Perm xs) (hy : m.toList.Perm ys)
  rw [ofList_eq_ofList_iff]
  rotate_left
  · simp; exact hx.nodup hm
  · simp; exact hy.nodup hm
  rw [List.map_perm_map_iff]
  · exact hx.symm.trans hy
  intro x y h
  simp at h
  exact h.1

@[simp]
theorem mem_range [ha : Fintype α] {f : (i : α) → β i} {i : α} : i ∈ range f := by
  simp [range]
  change i ∈ ha.elems.val.toList
  simp

@[simp]
theorem nonempty_insert {x} : Insert.insert x mp ≠ ⟨⟦∅⟧⟩ := by
  apply ne_of_congr (x.1 ∈ ·); simp

@[simp]
theorem nodup_toList : mp.toList.Nodup := by
  rcases mp with ⟨mp⟩
  apply mp.ind; intro mp
  exact Std.DHashMap.nodup_toSortedList

@[simp]
theorem sorted_toList : mp.toList.Sorted (·.1 ≤ ·.1) := by
  rcases mp with ⟨mp⟩
  apply mp.ind; simp [toList, lift]

@[simp]
theorem mem_toList {x} : x ∈ mp.toList ↔ mp.get? x.1 = x.2 := by
  rcases mp with ⟨mp⟩
  unfold toList get? lift
  apply mp.ind
  clear mp; intro mp
  rcases x with ⟨i, x⟩
  simp [Std.DHashMap.toSortedList]

@[simp]
theorem toList_eq_toList {m₁ m₂ : Std.ExtDHashMap α β} :
m₁.toList = m₂.toList ↔ m₁ = m₂ := by
  refine' ⟨λ h => _, λ h => by rw [h]⟩
  rw [List.eq_iff_of_nodup_and_sorted (·.1 ≤ ·.1)] at h
  any_goals simp
  rotate_left
  · rintro ⟨i, x⟩ ⟨j, y⟩
    simp
    intro h₁ h₂ h₃ h₄
    have h₅ := le_antisymm h₃ h₄
    subst h₅
    use rfl
    simp [h₁] at h₂
    simpa
  rw [ext_iff]
  intro i
  ext x
  specialize h ⟨i, x⟩
  simp at h
  exact h

@[simp]
theorem toList_eq_nil_iff : mp.toList = [] ↔ mp = ∅ := by
  rw [←toList_empty, toList_eq_toList]

theorem eq_iff_inner_eq {m₁ m₂ : Std.ExtDHashMap α β} :
m₁ = m₂ ↔ m₁.1 = m₂.1 := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp

theorem inner_eq_iff_eq {m₁ m₂ : Std.ExtDHashMap α β} :
m₁.1 = m₂.1 ↔ m₁ = m₂ := by
  rcases m₁ with ⟨m₁⟩; rcases m₂ with ⟨m₂⟩; simp

def fold {γ : Type*}
(mp : Std.ExtDHashMap α β) (f : γ → (i : α) → β i → γ) (z : γ)
(h : ∀ acc i x j y, f (f acc i x) j y = f (f acc j y) i x) : γ :=
  mp.lift (·.fold f z) # λ _ _ => DHashMap.fold_eq_fold_of_equiv h