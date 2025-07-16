import AP.Util.Data.Map.Defs

namespace Util.Data

universe u v w
variable {α : Type u} [hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type v}

namespace DMap

theorem equiv_def {m₁ m₂ : Std.DHashMap α β} :
m₁ ≈ m₂ ↔ m₁.Equiv m₂ := by rfl

protected def insert' (x : Σ i, β i) (mp : DMap α β) : DMap α β := by
  refine' mp.map _ _
  · intro mp
    exact insert x mp
  intro a b h
  rcases x with ⟨i, x⟩
  simp only [Std.DHashMap.insert_eq_insert]
  exact Std.DHashMap.Equiv.insert i x h

instance : Insert (Σ i, β i) (DMap α β) := ⟨DMap.insert'⟩

@[simp]
def insert (i : α) (x : β i) (mp : DMap α β) : DMap α β :=
  mp.insert' ⟨i, x⟩

def ofList (xs : List (Σ i, β i)) : DMap α β :=
  Quotient.mk' # .ofList xs

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

def map {γ : α → Type w} (f : ∀ {i}, β i → γ i) (mp : DMap α β) : DMap α γ := by
  refine' Quotient.map _ _ mp
  use (·.map @f)
  intro a b h
  exact Std.DHashMap.Equiv.map _ h

def range [fin : Fintype α] (f : (i : α) → β i) : DMap α β :=
  ofList # fin.1.to_sorted_list.map # λ i => ⟨i, f i⟩

def mem (mp : DMap α β) (i : α) : Prop := by
  apply mp.lift (i ∈ ·)
  intro a b h
  simp
  exact Std.DHashMap.Equiv.mem_iff h

instance : Membership α (DMap α β) := ⟨mem⟩

variable {mp : DMap α β}

theorem mem_iff_get?_eq_some {i : α} : i ∈ mp ↔ ∃ x, mp.get? i = some x := by
  change mem _ _ ↔ _
  apply mp.ind; clear! mp; intro mp
  simp [mem, get?]
  rw [←Option.isSome_iff_exists]
  exact Std.DHashMap.mem_iff_isSome_get?

theorem get?_eq_some_of_mem {i : α} (h : i ∈ mp) : ∃ x, mp.get? i = some x := by
  rwa [←mem_iff_get?_eq_some]

theorem get?_eq_none_of_not_mem {i : α} (h : i ∉ mp) : mp.get? i = none := by
  simp [mem_iff_get?_eq_some] at h
  rwa [Option.eq_none_iff_forall_ne_some]

theorem get?_map_eq {γ : α → Type w} {f : ∀ {i}, β i → γ i} {i : α} :
(mp.map f).get? i = (mp.get? i).map f := by
  apply mp.ind; clear! mp; intro mp
  simp [get?, map]

theorem get!_map_eq_of_pos {γ : α → Type w} {f : ∀ {i}, β i → γ i} {i : α}
[ha : Inhabited (β i)] [hb : Inhabited (γ i)]
(h : i ∈ mp) : (mp.map f).get! i = f (mp.get! i) := by
  simp [get!]
  obtain ⟨x, hx⟩ := get?_eq_some_of_mem h
  simp [get?_map_eq, hx]

def toList (mp : DMap α β) : List (Σ i, β i) := by
  nm x; clear x
  refine' mp.lift _ _
  · intro mp
    exact mp.toList.mergeSort (·.1 ≤ ·.1)
  intro a b h
  rw [equiv_def] at h
  rw [Std.DHashMap.equiv_iff_toList_perm] at h
  
  rw [←List.mergeSort_attach]
  nth_rw 2 [←List.mergeSort_attach]
  -- apply List.eq_of_perm_of_sorted
  sorry

#check 0 #exit

@[simp]
theorem ofList_nil : ofList (α := α) (β := β) [] = ∅ := rfl

@[simp]
theorem toList_empty : (∅ : DMap α β).toList = [] := rfl

@[simp]
theorem ofList_snoc {x : Σ i, β i} {xs} :
ofList (xs ++ [x]) = (ofList xs).insert' x := by
  unfold ofList insert'
  ext:1
  dsimp only
  generalize ha : [] = acc
  nth_rewrite 2 [←ha]
  clear ha
  induction xs generalizing x acc
  · simp
  nm y ys ih
  dsimp at ih ⊢
  rw [ih]

@[simp]
theorem mem_insert' {x : Σ i, β i} {i} :
i ∈ mp.insert' x ↔ i = x.1 ∨ i ∈ mp := by
  simp [insert', mem_def]

theorem mem_insert {i x j} :
j ∈ mp.insert i x ↔ j = i ∨ j ∈ mp := by simp

@[simp]
theorem mem_ofList {xs : List (Σ i, β i)} {i} :
i ∈ ofList xs ↔ ∃ x, ⟨i, x⟩ ∈ xs := by
  induction xs using List.reverseRecOn
  · simp [mem_def]
  nm xs x ih
  simp
  constructor
  · rintro (rfl | h)
    · use x.2
      simp
    · rw [ih] at h
      obtain ⟨y, hy⟩ := h
      use y
      simp [hy]
  · rintro ⟨y, hy | rfl⟩
    · right
      rw [ih]
      use y
    · simp

@[simp]
theorem mem_range [fin : Fintype α] {f : (i : α) → β i} {i : α} : i ∈ range f := by
  simp [range]

@[simp]
theorem mem_map {f : ∀ {i}, β i → β i} {i} : i ∈ mp.map f ↔ i ∈ mp := by
  simp [map, mem_def]
  obtain ⟨xs, h⟩ := mp
  dsimp
  induction xs <;> simp
  nm x xs ih
  specialize ih # listCnd_of_cons h
  rw [ih]