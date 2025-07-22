import AP.Util.Data.Map.Defs

namespace Util.Data

universe u v w
variable {α : Type u} [hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type v}

namespace DMap

theorem equiv_def {m₁ m₂ : Std.DHashMap α β} :
m₁ ≈ m₂ ↔ m₁.Equiv m₂ := by rfl

def insertP (x : Σ i, β i) (mp : DMap α β) : DMap α β := by
  refine' mp.map _ _
  · intro mp
    exact insert x mp
  intro a b h
  rcases x with ⟨i, x⟩
  simp only [Std.DHashMap.insert_eq_insert]
  exact Std.DHashMap.Equiv.insert i x h

instance : Insert (Σ i, β i) (DMap α β) := ⟨insertP⟩

@[simp]
protected def insert (mp : DMap α β) (i : α) (x : β i) : DMap α β :=
  mp.insertP ⟨i, x⟩

def ofList (xs : List (Σ i, β i)) : DMap α β :=
  ⟦.ofList xs⟧

def get? (i : α) (mp : DMap α β) : Option (β i) := by
  refine' mp.lift _ _
  · intro mp
    exact mp.get? i
  intro a b h
  exact Std.DHashMap.Equiv.get?_eq h

def get! (i : α) [h : Inhabited (β i)] (mp : DMap α β) : β i :=
  (mp.get? i).get!

end DMap namespace Map

def ofList {β : Type u} (xs : List (α × β)) : Map α β :=
  DMap.ofList # xs.map # λ ⟨i, x⟩ => ⟨i, x⟩

end Map namespace DMap

def map {γ : α → Type w} (mp : DMap α β) (f : ∀ i, β i → γ i) : DMap α γ := by
  refine' Quotient.map _ _ mp
  use (·.map @f)
  intro a b h
  exact Std.DHashMap.Equiv.map _ h

def mem (mp : DMap α β) (i : α) : Prop := by
  apply mp.lift (i ∈ ·)
  intro a b h
  simp
  exact Std.DHashMap.Equiv.mem_iff h

instance : Membership α (DMap α β) := ⟨mem⟩

variable {mp : DMap α β}

theorem mem_def {i} : i ∈ mp ↔ mp.mem i := by rfl

instance {i} : Decidable (mp.mem i) := by
  unfold mem; infer_instance

instance {i} : Decidable (i ∈ mp) := by
  change Decidable (mp.mem i)
  infer_instance

end DMap namespace Map

variable {β : Type v} {mp : Map α β}

instance : Membership α (Map α β) := ⟨DMap.mem⟩

theorem mem_def {i} : i ∈ mp ↔ DMap.instMembership.mem mp i := by rfl

instance {i} : Decidable (i ∈ mp) := by
  change Decidable (mp.mem i)
  infer_instance

end Map namespace DMap

variable {mp : DMap α β}

theorem mem_iff_get?_eq_some {i : α} : i ∈ mp ↔ ∃ x, mp.get? i = some x := by
  apply mp.ind; clear! mp; intro mp
  simp [mem, get?]
  rw [←Option.isSome_iff_exists]
  exact Std.DHashMap.mem_iff_isSome_get?

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

theorem get?_map {γ : α → Type w} {f : ∀ i, β i → γ i} {i : α} :
(mp.map f).get? i = (mp.get? i).map (f i) := by
  apply mp.ind; clear! mp; intro mp
  simp [get?, map]

theorem get!_map_eq_of_pos {γ : α → Type w} {f : ∀ i, β i → γ i} {i : α}
[ha : Inhabited (β i)] [hb : Inhabited (γ i)]
(h : i ∈ mp) : (mp.map f).get! i = f i (mp.get! i) := by
  simp [get!]
  obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
  simp [get?_map, hx]

def toList (mp : DMap α β) : List (Σ i, β i) := by
  let r := λ (a b : Σ i, β i) => a.1 ≤ b.1
  
  refine' mp.lift _ _
  · intro mp
    exact mp.toList.mergeSort (r · ·)
  intro a b h
  rw [equiv_def] at h
  rw [Std.DHashMap.equiv_iff_toList_perm] at h
  
  generalize hx : a.toList = xs at h ⊢
  generalize hy : b.toList = ys at h ⊢
  
  have h_tra : ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → r a b → r b c → r a c :=
    λ a b c _ _ _ ↦ Preorder.le_trans a.1 b.1 c.1
  have h_tot : ∀ a b, a ∈ xs → b ∈ xs → r a b ∨ r b a :=
    λ a b _ _ ↦ LinearOrder.le_total a.1 b.1
  
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

end DMap namespace Map

def toList {β : Type v} (mp : Map α β) : List (α × β) :=
  (DMap.toList mp).map # λ ⟨i, x⟩ => (i, x)

end Map namespace DMap

variable {mp : DMap α β}

@[simp]
theorem ofList_nil : ofList (α := α) (β := β) [] = ∅ := rfl

@[simp]
theorem toList_empty : (∅ : DMap α β).toList = [] := by
  simp [empty_def, toList]

@[simp]
theorem ofList_snoc {x : Σ i, β i} {xs} :
ofList (xs ++ [x]) = (ofList xs).insertP x := by
  simp_rw [ofList]
  unfold insertP
  simp
  rw [Quotient.eq_iff_equiv]
  whnf
  unfold Std.DHashMap.ofList
  rw [Std.DHashMap.insertMany_append]
  rfl

@[simp]
theorem mem_insertP {x : Σ i, β i} {i} :
i ∈ mp.insertP x ↔ i = x.1 ∨ i ∈ mp := by
  rw [insertP, mem_def, mem]
  apply mp.ind
  intro m
  simp
  tauto

@[simp]
theorem mem_insert' {i x j} :
j ∈ mp.insert i x ↔ j = i ∨ j ∈ mp := by simp

@[simp]
theorem mem_insert {x i} :
i ∈ insert x mp ↔ i = x.1 ∨ i ∈ mp := by simp [insert]

@[simp]
theorem mem_ofList {xs : List (Σ i, β i)} {i} :
i ∈ ofList xs ↔ ∃ x, ⟨i, x⟩ ∈ xs := by
  simp only [ofList, mem_def, mem, Quotient.lift_mk, Std.DHashMap.mem_ofList,
    List.contains_eq_mem, List.mem_map, Sigma.exists, exists_and_right,
    exists_eq_right, decide_eq_true_eq]

@[simp]
theorem mem_map {γ : α → Type w} {f : ∀ i, β i → γ i} {i} : i ∈ mp.map f ↔ i ∈ mp := by
  simp_rw [mem_def, mem, map]
  apply mp.ind
  simp

theorem eq_empty_iff : mp = ∅ ↔ ∀ i, i ∉ mp := by
  simp_rw [mem_def, mem, empty_def]
  apply mp.ind
  intro m
  rw [Quotient.eq_iff_equiv]
  simp
  change m.Equiv ∅ ↔ _
  simp
  exact Std.DHashMap.isEmpty_iff_forall_not_mem

@[simp]
theorem not_mem_empty' {i} : ¬(∅ : DMap α β).mem i := by
  simp [mem, empty_def, empty]

@[simp]
theorem not_mem_empty {i} : i ∉ (∅ : DMap α β) :=
  not_mem_empty'

theorem ext_iff' {m₁ m₂ : DMap α β} : m₁ = m₂ ↔ m₁.out.Equiv m₂.out := by
  symm
  induction m₁, m₂ using Quotient.inductionOn₂
  nm m₁ m₂
  change ⟦m₁⟧.out ≈ ⟦m₂⟧.out ↔ _
  rw [Quotient.eq_iff_equiv]
  simp
  rfl

theorem ext' {m₁ m₂ : DMap α β} (h : m₁.out.Equiv m₂.out) : m₁ = m₂ := by
  rwa [ext_iff']

theorem ext_iff {m₁ m₂ : DMap α β} : m₁ = m₂ ↔ ∀ i, m₁.get? i = m₂.get? i := by
  induction m₁, m₂ using Quotient.inductionOn₂
  rw [Quotient.eq_iff_equiv]
  exact Std.DHashMap.equiv_iff_get?

@[ext]
theorem ext {m₁ m₂ : DMap α β} (h : ∀ i, m₁.get? i = m₂.get? i) : m₁ = m₂ := by
  rwa [ext_iff]

theorem get?_eq_ite_of_unit {m : Map α Unit} {i} :
m.get? i = if i ∈ m then some () else none := by
  split_ifs with h
  · obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
    simp [hx]
  rw [get?_eq_none_of_not_mem h]

end DMap namespace Map

variable {β : Type v} {mp : Map α β}

theorem ext_iff {m₁ m₂ : Map α β} : m₁ = m₂ ↔ ∀ i, m₁.get? i = m₂.get? i :=
  DMap.ext_iff

@[ext]
theorem ext {m₁ m₂ : Map α β} (h : ∀ i, m₁.get? i = m₂.get? i) : m₁ = m₂ :=
  DMap.ext h

@[simp]
theorem get?_empty {i} : (∅ : Map α β).get? i = none := by simp [empty_def]

theorem eq_empty_iff : mp = ∅ ↔ ∀ i, i ∉ mp := DMap.eq_empty_iff

end Map namespace DMap

variable {mp : DMap α β}

@[simp]
theorem get?_empty {i} : (∅ : DMap α β).get? i = none := by simp

theorem ofList_eq_ofList_iff {xs ys : List (Σ i, β i)}
(hx : (xs.map (·.1)).Nodup) (hy : (ys.map (·.1)).Nodup) :
ofList xs = ofList ys ↔ xs.Perm ys := by
  have hx' := hx.of_map _
  have hy' := hy.of_map _
  unfold ofList
  rw [Quotient.eq_iff_equiv]
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

def range [ha : Fintype α] (f : (i : α) → β i) : DMap α β := by
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
theorem nonempty_insert {x} : insert x mp ≠ ∅ := by
  simp [eq_empty_iff]
  use x.1
  tauto

@[simp]
theorem nodup_toList : mp.toList.Nodup := by
  unfold toList
  apply mp.ind
  intro m
  simp

@[simp]
theorem sorted_toList : mp.toList.Sorted (·.1 ≤ ·.1) := by
  unfold toList
  apply mp.ind
  intro m
  simp
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
theorem mem_toList {x} : x ∈ mp.toList ↔ mp.get? x.1 = x.2 := by
  unfold toList get?
  apply mp.ind
  intro m
  rcases x with ⟨i, x⟩
  simp

@[simp]
theorem toList_eq_toList {m₁ m₂ : DMap α β} :
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