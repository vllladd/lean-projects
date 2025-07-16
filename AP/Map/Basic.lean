import AP.Map.Defs

universe u
variable {ι : Type u} {α β : ι → Type u} [hhι : LinearOrder ι] {mp : DMap ι α}

namespace DMap

@[simp]
theorem insert'_nil {x : Σ i, α i} : insert' x [] = [x] := rfl

@[simp]
theorem insert'_cons {x y : Σ i, α i} {xs : List (Σ i, α i)} :
insert' x (y :: xs) = (match compare x.1 y.1 with
| .eq => x :: xs
| .lt => x :: y :: xs
| .gt => y :: insert' x xs) := rfl

theorem listCnd_of_cons {x : Σ i, α i} {xs}
(h : listCnd (x :: xs)) : listCnd xs := by
  cases xs; trivial; exact h.2

theorem listCnd_cons_of_le {x y : Σ i, α i} {xs}
(h₁ : listCnd (x :: xs)) (h₂ : y.1 ≤ x.1) : listCnd (y :: xs) := by
  cases xs
  · simp
  nm z xs
  simp at h₁ ⊢
  rcases h₁ with ⟨h₁, h₃⟩
  simp [h₃]
  exact lt_of_le_of_lt h₂ h₁

theorem listCnd_cons_of_eq {x y : Σ i, α i} {xs}
(h₁ : listCnd (x :: xs)) (h₂ : y.1 = x.1) : listCnd (y :: xs) := by
  apply listCnd_cons_of_le h₁; rw [h₂]

theorem listCnd_cons_of_lt {x y : Σ i, α i} {xs}
(h₁ : listCnd (x :: xs)) (h₂ : y.1 < x.1) : listCnd (y :: xs) := by
  apply listCnd_cons_of_le h₁; exact le_of_lt h₂

theorem listCnd_map_of (f : ∀ {i}, α i → β i)
{xs : List (Σ i, α i)} (h : listCnd xs) :
listCnd # xs.map # λ x => ⟨x.1, f x.2⟩ := by
  induction xs
  · simp
  nm x xs ih
  specialize ih # listCnd_of_cons h
  cases xs <;> simp
  nm y xs
  simp at h ih
  use h.1

theorem listCnd_insert'_of {xs : List (Σ i, α i)} {x}
(h : listCnd xs) : listCnd (insert' x xs) := by
  rcases x with ⟨i, x⟩
  generalize hn : xs.length = n
  induction n using Nat.strong_induction_on generalizing i x xs
  nm n ih
  cases xs
  · simp
  nm y xs
  rcases y with ⟨j, y⟩
  simp
  split <;> nm a h₁ <;> clear a
  · rw [compare_eq_iff_eq] at h₁
    subst h₁
    exact listCnd_cons_of_eq h rfl
  · rw [compare_lt_iff_lt] at h₁
    simp
    use h₁
  rw [compare_gt_iff_gt, gt_iff_lt] at h₁
  simp at hn
  have h₂ := ih (n - 1)
  rw [←hn] at h₂
  specialize @h₂ (by simp) xs (listCnd_of_cons h) i x (by simp)
  generalize hy : insert' ⟨i, x⟩ xs = ys at h₂ ⊢
  cases ys
  · simp
  nm z ys
  simp [h₂]
  cases xs
  · simp at hy
    simpa [←hy.1]
  nm r xs
  simp at h hy
  split at hy <;> nm a h₃ <;> clear a <;>
    simp at hy <;> rcases hy with ⟨rfl, hy⟩
  · rw [compare_eq_iff_eq] at h₃
    subst h₃
    exact h.1
  · rw [compare_lt_iff_lt] at h₃
    exact h₁
  exact h.1

def insertProd (x : Σ i, α i) (mp : DMap ι α) : DMap ι α :=
  ⟨_, listCnd_insert'_of (x := x) mp.h⟩

instance : Insert (Σ i, α i) (DMap ι α) :=
  ⟨λ p mp => mp.insertProd p⟩

@[simp]
def insert (i : ι) (x : α i) (mp : DMap ι α) : DMap ι α :=
  mp.insertProd ⟨i, x⟩

theorem listCnd_ofList'_of {xs ys : List (Σ i, α i)}
(h : listCnd xs) : listCnd (ofList' xs ys) := by
  induction ys generalizing xs
  · simpa
  nm y ys ih
  exact ih # listCnd_insert'_of h

@[simp]
theorem listCnd_ofList'_of_fst_nil {xs : List (Σ i, α i)} :
listCnd (ofList' [] xs) := by
  apply listCnd_ofList'_of; simp

def ofList (xs : List (Σ i, α i)) : DMap ι α :=
  ⟨_, listCnd_ofList'_of_fst_nil (xs := xs)⟩

def get? (i : ι) (mp : DMap ι α) : Option (α i) :=
  get' i mp.toList

def get! (i : ι) [h : Inhabited (α i)] (mp : DMap ι α) : α i :=
  (mp.get? i).get!

end DMap namespace Map

def ofList {α : Type u} (xs : List (ι × α)) : Map ι α :=
  DMap.ofList # xs.map # λ ⟨i, x⟩ => ⟨i, x⟩

end Map namespace DMap

theorem lt_of_listCnd_cons_and_mem {xs : List (Σ i, α i)} {x y}
(h₁ : listCnd (x :: xs)) (h₂ : y ∈ xs) : x.1 < y.1 := by
  generalize hn : xs.length = n
  induction n using Nat.strong_induction_on generalizing x y xs
  nm n ih
  cases xs
  · simp at h₂
  nm z xs
  simp at h₁
  rcases h₁ with ⟨h₁, h₃⟩
  simp at h₂
  rcases h₂ with rfl | h₂
  · exact h₁
  specialize @ih (n - 1)
  rw [←hn] at ih
  apply @ih (by simp) xs x y _ h₂ (by simp)
  exact listCnd_cons_of_lt h₃ h₁

theorem listCnd_cons_of_forall_le {xs : List (Σ i, α i)} {x}
(h₁ : listCnd xs) (h₂ : ∀ y ∈ xs, x.1 < y.1) : listCnd (x :: xs) := by
  cases xs
  · simp
  nm z xs
  simp [h₁]
  specialize h₂ z
  simp at h₂
  exact h₂

theorem listCnd_cons_iff {xs : List (Σ i, α i)} {x} :
listCnd (x :: xs) ↔ listCnd xs ∧ ∀ y ∈ xs, x.1 < y.1 := by
  use λ h => ⟨listCnd_of_cons h, λ _ => lt_of_listCnd_cons_and_mem h⟩
  use λ h => listCnd_cons_of_forall_le h.1 h.2

theorem sorted_of_listCnd {xs : List (Σ i, α i)}
(h : listCnd xs) : xs.Sorted # λ (x y : Σ i, α i) => x.1 < y.1 := by
  induction xs
  · simp
  nm x xs ih
  specialize ih # listCnd_of_cons h
  rw [List.sorted_cons]
  simp only [ih, and_true]
  intro y hy
  exact lt_of_listCnd_cons_and_mem h hy

theorem listCnd_of_sorted {xs : List (Σ i, α i)}
(h : xs.Sorted # λ (x y : Σ i, α i) => x.1 < y.1) : listCnd xs := by
  induction xs
  · simp
  nm x xs ih
  rw [List.sorted_cons] at h
  rcases h with ⟨h₁, h₂⟩
  specialize ih h₂
  rw [listCnd_cons_iff]
  use ih

theorem listCnd_iff_sorted {xs : List (Σ i, α i)} :
listCnd xs ↔ xs.Sorted (λ (x y : Σ i, α i) => x.1 < y.1) :=
  ⟨sorted_of_listCnd, listCnd_of_sorted⟩

theorem nodup_of_listCnd {xs : List (Σ i, α i)} (h : listCnd xs) : xs.Nodup := by
  induction xs
  · simp
  nm x xs ih
  specialize ih # listCnd_of_cons h
  simp [ih]
  rw [listCnd_cons_iff] at h
  replace h := h.2
  intro hx
  specialize h x hx
  simp at h

def map (f : ∀ {i}, α i → β i) : DMap ι β := by
  use mp.toList.map # λ ⟨i, x⟩ => ⟨i, f x⟩
  apply listCnd_map_of
  exact mp.h

def range [fin : Fintype ι] (f : (i : ι) → α i) : DMap ι α :=
  ofList # fin.1.to_sorted_list.map # λ i => ⟨i, f i⟩

def mem (mp : DMap ι α) (i : ι) : Prop :=
  mem' i mp.toList

instance : Membership ι (DMap ι α) := ⟨mem⟩

theorem mem_def {i : ι} : i ∈ mp ↔ mem' i mp.toList := by rfl

theorem mem_iff_get?_eq_some {i : ι} : i ∈ mp ↔ ∃ x, mp.get? i = some x := by
  rcases mp with ⟨xs, h₁⟩
  simp [mem_def]
  simp [get?]; clear h₁
  induction xs <;> simp
  nm x xs ih
  split_ifs with h₁ <;> simp [h₁]
  exact ih

theorem get?_eq_some_of_mem {i : ι} (h : i ∈ mp) : ∃ x, mp.get? i = some x := by
  rwa [←mem_iff_get?_eq_some]

theorem get?_eq_none_of_not_mem {i : ι} (h : i ∉ mp) : mp.get? i = none := by
  simp [mem_iff_get?_eq_some] at h
  rwa [Option.eq_none_iff_forall_ne_some]

theorem get?_map_eq {f : ∀ {i}, α i → β i} {i : ι} :
(mp.map f).get? i = (mp.get? i).map f := by
  rcases mp with ⟨xs, h⟩
  simp [get?, map]
  clear h
  induction xs
  · rfl
  nm x xs ih
  simp
  split_ifs with h₁
  · subst h₁
    simp
  exact ih

theorem get!_map_eq_of_pos {f : ∀ {i}, α i → β i} {i : ι}
[ha : Inhabited (α i)] [hb : Inhabited (β i)]
(h : i ∈ mp) : (mp.map f).get! i = f (mp.get! i) := by
  rcases mp with ⟨xs, h₁⟩
  simp [get!, get?_map_eq]
  rw [mem_iff_get?_eq_some] at h
  obtain ⟨x, h⟩ := h
  simp [h]

@[simp]
theorem ofList_nil : ofList (ι := ι) (α := α) [] = ∅ := rfl

@[simp]
theorem toList_empty : (∅ : DMap ι α).toList = [] := rfl

@[simp]
theorem ofList_snoc {x : Σ i, α i} {xs} :
ofList (xs ++ [x]) = (ofList xs).insertProd x := by
  unfold ofList insertProd
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
theorem mem'_insert' {x : Σ i, α i} {xs i} :
mem' i (insert' x xs) ↔ i = x.1 ∨ mem' i xs := by
  induction xs generalizing x
  · simp
  nm y xs ih
  simp
  split <;> nm x h₁ <;> clear x
  · rw [compare_eq_iff_eq] at h₁
    simp [h₁]
  · simp
  · rw [compare_gt_iff_gt, gt_iff_lt] at h₁
    simp [ih]
    tauto

@[simp]
theorem mem_insertProd {x : Σ i, α i} {i} :
i ∈ mp.insertProd x ↔ i = x.1 ∨ i ∈ mp := by
  simp [insertProd, mem_def]

-- #check 0 #exit

@[simp]
theorem mem_ofList {xs : List (Σ i, α i)} {i} :
i ∈ ofList xs ↔ ∃ x, ⟨i, x⟩ ∈ xs := by
  induction xs using List.reverseRecOn
  · simp [mem_def]
  nm xs x ih
  simp
  constructor
  · rintro (rfl | h)
    · sorry
    · sorry
  · sorry

#check 0 #exit

@[simp]
theorem mem_range [fin : Fintype ι] {f : (i : ι) → α i} {i : ι} : i ∈ range f := by
  simp [range]