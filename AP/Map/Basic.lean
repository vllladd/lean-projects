import AP.Map.Defs

namespace Map

set_option linter.unusedVariables false
universe u
variable {ι α : Type u} [hhι : LinearOrder ι] [hhα : DecidableEq α] {mp : Map ι α}
set_option linter.unusedSectionVars true

omit hhα in
@[simp]
theorem insert'_nil {x : ι × α} : insert' x [] = [x] := rfl

omit hhα in
@[simp]
theorem insert'_cons {x y : ι × α} {xs : List (ι × α)} :
insert' x (y :: xs) = (match compare x.1 y.1 with
| .eq => x :: xs
| .lt => x :: y :: xs
| .gt => y :: insert' x xs) := rfl

theorem listCnd_of_cons {x : ι × α} {xs}
(h : listCnd (x :: xs)) : listCnd xs := by
  cases xs; trivial; exact h.2

theorem listCnd_cons_of_le {x y : ι × α} {xs}
(h₁ : listCnd (x :: xs)) (h₂ : y.1 ≤ x.1) : listCnd (y :: xs) := by
  cases xs
  · simp
  nm z xs
  simp at h₁ ⊢
  rcases h₁ with ⟨h₁, h₃⟩
  simp [h₃]
  exact lt_of_le_of_lt h₂ h₁

theorem listCnd_cons_of_eq {x y : ι × α} {xs}
(h₁ : listCnd (x :: xs)) (h₂ : y.1 = x.1) : listCnd (y :: xs) := by
  apply listCnd_cons_of_le h₁; rw [h₂]

theorem listCnd_cons_of_lt {x y : ι × α} {xs}
(h₁ : listCnd (x :: xs)) (h₂ : y.1 < x.1) : listCnd (y :: xs) := by
  apply listCnd_cons_of_le h₁; exact le_of_lt h₂

theorem listCnd_map_of {β : Type u} [hb : DecidableEq β] (f : α → β)
{xs : List (ι × α)} (h : listCnd xs) :
listCnd # xs.map # λ x => (x.1, f x.2) := by
  induction xs
  · simp
  nm x xs ih
  specialize ih # listCnd_of_cons h
  cases xs <;> simp
  nm y xs
  simp at h ih
  use h.1

theorem listCnd_insert'_of {xs : List (ι × α)} {x}
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
  generalize hy : insert' (i, x) xs = ys at h₂ ⊢
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

def insert_prod (x : ι × α) (mp : Map ι α) : Map ι α :=
  ⟨_, listCnd_insert'_of (x := x) mp.h⟩

instance : Insert (ι × α) (Map ι α) :=
  ⟨λ p mp => mp.insert_prod p⟩

@[simp]
def insert (i : ι) (x : α) (mp : Map ι α) : Map ι α :=
  mp.insert_prod (i, x)

theorem listCnd_ofList'_of {xs ys : List (ι × α)}
(h : listCnd xs) : listCnd (ofList' xs ys) := by
  induction ys generalizing xs
  · simpa
  nm y ys ih
  exact ih # listCnd_insert'_of h

@[simp]
theorem listCnd_ofList'_of_fst_nil {xs : List (ι × α)} :
listCnd (ofList' [] xs) := by
  apply listCnd_ofList'_of; simp

def ofList (xs : List (ι × α)) : Map ι α :=
  ⟨_, listCnd_ofList'_of_fst_nil (xs := xs)⟩

def get? (i : ι) (mp : Map ι α) : Option α :=
  lookup' i mp.toList

def get! [Inhabited α] (i : ι) (mp : Map ι α) : α :=
  (mp.get? i).get!

theorem lt_of_listCnd_cons_and_mem {xs : List (ι × α)} {x y}
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

theorem listCnd_cons_of_forall_le {xs : List (ι × α)} {x}
(h₁ : listCnd xs) (h₂ : ∀ y ∈ xs, x.1 < y.1) : listCnd (x :: xs) := by
  cases xs
  · simp
  nm z xs
  simp [h₁]
  specialize h₂ z
  simp at h₂
  exact h₂

theorem listCnd_cons_iff {xs : List (ι × α)} {x} :
listCnd (x :: xs) ↔ listCnd xs ∧ ∀ y ∈ xs, x.1 < y.1 := by
  use λ h => ⟨listCnd_of_cons h, λ _ => lt_of_listCnd_cons_and_mem h⟩
  use λ h => listCnd_cons_of_forall_le h.1 h.2

theorem sorted_of_listCnd {xs : List (ι × α)}
(h : listCnd xs) : xs.Sorted # λ (x y : ι × α) => x.1 < y.1 := by
  induction xs
  · simp
  nm x xs ih
  specialize ih # listCnd_of_cons h
  rw [List.sorted_cons]
  simp only [ih, and_true]
  intro y hy
  exact lt_of_listCnd_cons_and_mem h hy

theorem listCnd_of_sorted {xs : List (ι × α)}
(h : xs.Sorted # λ (x y : ι × α) => x.1 < y.1) : listCnd xs := by
  induction xs
  · simp
  nm x xs ih
  rw [List.sorted_cons] at h
  rcases h with ⟨h₁, h₂⟩
  specialize ih h₂
  rw [listCnd_cons_iff]
  use ih

theorem listCnd_iff_sorted {xs : List (ι × α)} :
listCnd xs ↔ xs.Sorted (λ (x y : ι × α) => x.1 < y.1) :=
  ⟨sorted_of_listCnd, listCnd_of_sorted⟩

theorem nodup_of_listCnd {xs : List (ι × α)} (h : listCnd xs) : xs.Nodup := by
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