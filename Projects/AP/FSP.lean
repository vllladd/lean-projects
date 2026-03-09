import Projects.AP.MkFold

namespace AP

@[ext]
structure FSP : Type where
  get : ℕ → Set PointZ

namespace FSP

variable {fsp a b c : FSP}

instance : EmptyCollection FSP := ⟨⟨λ _ => ∅⟩⟩
theorem empty_def : (∅ : FSP) = ⟨λ _ => ∅⟩ := rfl

instance : Inhabited FSP := ⟨∅⟩
theorem default_def : (default : FSP) = ∅ := rfl

instance : Union FSP := ⟨λ a b => ⟨λ i => a.get i ∪ b.get i⟩⟩
theorem union_def : a ∪ b = ⟨λ i => a.get i ∪ b.get i⟩ := rfl

instance : Inter FSP := ⟨λ a b => ⟨λ i => a.get i ∩ b.get i⟩⟩
theorem inter_def : a ∩ b = ⟨λ i => a.get i ∩ b.get i⟩ := rfl

def next (fsp : FSP) : FSP where
  get i := match i with
  | 0 => fsp.get 0 ∪ fsp.get 1
  | n + 1 => fsp.get # n + 2

def offset (fsp : FSP) (n : ℕ) : FSP :=
  next^[n] fsp

def hasLe (a : FSP) (n : ℕ) (p : PointZ) : Prop :=
  ∃ k ≤ n, p ∈ a.get k

def insertSet (fsp : FSP) (n : ℕ) (ps : Set PointZ) : FSP where
  get i := if i = n then ps ∪ fsp.get i else fsp.get i

protected def insert (fsp : FSP) (n : ℕ) (p : PointZ) : FSP :=
  fsp.insertSet n {p}

def Subset (a b : FSP) : Prop :=
  ∀ ⦃i⦄, a.get i ⊆ b.get i

instance : HasSubset FSP := ⟨Subset⟩

-- #check 0 #exit

-----
  
@[simp]
theorem hasLe_next {n p} : a.next.hasLe n p ↔ a.hasLe (n + 1) p := by
  rw [←not_iff_not]; dsimp [next, hasLe]; push_neg
  constructor <;> intro h k hk
  · specialize h (k - 1) # Nat.sub_le_of_le_add hk
    iterate 2 cases k; simp at h; simp [h]; nm k
    simp at h; simp [h]
  · have h₁ := h k (by linarith)
    have h₂ := h (k + 1) (by simpa)
    cases k <;> simp_all

theorem hasLe_insertSet_eq_of_lt {n k ps} (h : k < n) :
(fsp.insertSet n ps).hasLe k = fsp.hasLe k := by
  ext p; rw [←not_iff_not]; dsimp [hasLe, insertSet]; push_neg
  apply forall_congr'
  intro i
  split_ifs with h₁
  · subst h₁
    rw [←not_le] at h
    simp [h]
  simp

theorem hasLe_insert_eq_of_lt {n k p} (h : k < n) :
(fsp.insert n p).hasLe k = fsp.hasLe k := hasLe_insertSet_eq_of_lt h

@[simp]
theorem insertSet_empty {n} : fsp.insertSet n ∅ = fsp := by
  simp [insertSet]

theorem insertSet_insert {n p ps} :
(fsp.insertSet n ps).insert n p = fsp.insertSet n (insert p ps) := by
  unfold FSP.insert insertSet; aesop

theorem insertSet_set_insert {n p ps} :
fsp.insertSet n (insert p ps) = (fsp.insertSet n ps).insert n p :=
  insertSet_insert.symm

@[simp]
theorem get_insertSet_of_eq {n ps} : (fsp.insertSet n ps).get n = ps ∪ fsp.get n := by
  simp [insertSet]

@[simp]
theorem get_insert_of_eq {n p} : (fsp.insert n p).get n = insert p (fsp.get n) :=
  get_insertSet_of_eq

theorem hasLe_insertSet_of_le {m n k ps p} (h₁ : (fsp.insertSet m ps).hasLe k p)
(h₂ : m ≤ k) (h₃ : n ≤ k) : (fsp.insertSet n ps).hasLe k p := by
  obtain ⟨r, hr, h₁⟩ := h₁
  by_cases hp : p ∈ ps
  · use n, h₃; simp [hp]
  use r, hr
  simp [insertSet] at h₁ ⊢
  aesop

theorem hasLe_insert_of_le {m n k p p₁} (h₁ : (fsp.insert m p).hasLe k p₁)
(h₂ : m ≤ k) (h₃ : n ≤ k) : (fsp.insert n p).hasLe k p₁ :=
  hasLe_insertSet_of_le h₁ h₂ h₃

theorem insertSet_comm {n m ps₁ ps₂} : (fsp.insertSet n ps₁).insertSet m ps₂ =
(fsp.insertSet m ps₂).insertSet n ps₁ := by
  unfold insertSet; aesop

theorem insert_comm {n m p₁ p₂} : (fsp.insert n p₁).insert m p₂ =
(fsp.insert m p₂).insert n p₁ := insertSet_comm

theorem insertSet_insert_comm {n m ps₁ p₂} : (fsp.insertSet n ps₁).insert m p₂ =
(fsp.insert m p₂).insertSet n ps₁ := insertSet_comm

theorem insert_insertSet_comm {n m p₁ ps₂} : (fsp.insert n p₁).insertSet m ps₂ =
(fsp.insertSet m ps₂).insert n p₁ := insertSet_comm

theorem hasLe_insertSet_of_hasLe {n k ps p} (h₁ : fsp.hasLe k p) :
(fsp.insertSet n ps).hasLe k p := by
  dsimp [insertSet, hasLe] at h₁ ⊢; aesop

theorem hasLe_insertSet_of_le_and_le {m n k ps p} (h₁ : (fsp.insertSet n ps).hasLe k p)
(h₂ : m ≤ n) : (fsp.insertSet m ps).hasLe k p := by
  by_cases h₃ : n ≤ k
  · exact hasLe_insertSet_of_le h₁ h₃ # h₂.trans h₃
  push_neg at h₃
  rw [hasLe_insertSet_eq_of_lt h₃] at h₁
  exact hasLe_insertSet_of_hasLe h₁

theorem hasLe_insert_of_le_and_le {m n k p p₁} (h₁ : (fsp.insert n p).hasLe k p₁)
(h₂ : m ≤ n) : (fsp.insert m p).hasLe k p₁ :=
  hasLe_insertSet_of_le_and_le h₁ h₂

@[simp]
theorem get_insertSet_of_ne {n k ps} (h : k ≠ n) : (fsp.insertSet n ps).get k = fsp.get k := by
  simp [insertSet, h]

@[simp]
theorem get_insert_of_ne {n k p} (h : k ≠ n) : (fsp.insert n p).get k = fsp.get k :=
  get_insertSet_of_ne h

theorem insert_eq_of_mem {n p} (h : p ∈ fsp.get n) : fsp.insert n p = fsp := by
  ext k p₁; simp [FSP.insert, insertSet]; aesop

@[simp] theorem offset_zero : fsp.offset 0 = fsp := rfl
@[simp] theorem offset_one : fsp.offset 1 = fsp.next := rfl

theorem offset_succ {n} : fsp.offset (n + 1) = fsp.next.offset n :=
  next.iterate_succ_apply n fsp

theorem offset_succ' {n} : fsp.offset (n + 1) = (fsp.offset n).next :=
  next.iterate_succ_apply' n fsp

@[simp]
theorem mem_get_zero_next_iff {p} : p ∈ fsp.next.get 0 ↔ p ∈ fsp.get 0 ∨ p ∈ fsp.get 1 := by
  simp [next]

@[simp]
theorem mem_get_zero_offset_iff {n p} : p ∈ (fsp.offset n).get 0 ↔ ∃ k ≤ n, p ∈ fsp.get k := by
  induction n generalizing fsp; simp; nm n ih
  rw [offset_succ, ih]; clear ih
  constructor <;> rintro ⟨k, hk, h⟩
  · cases k
    · simp at h
      rcases h with h | h
      · use 0; simpa
      · use 1; simpa
    nm k; simp [next] at h
    use k + 2, by linarith
  · cases k; use 0; simp [h]
    nm k; use k, by linarith
    simp [next]; split
    · simp_all only [zero_add, le_add_iff_nonneg_left, zero_le, Set.mem_union, or_true]
    · simp_all only [Nat.succ_eq_add_one, add_le_add_iff_right]

@[simp]
theorem hasLe_offset {n k p} : (fsp.offset n).hasLe k p ↔ fsp.hasLe (k + n) p := by
  induction n generalizing fsp; simp; nm n ih
  simp [offset_succ, ih, Nat.add_assoc]

theorem hasLe_of_le {n k p} (h₁ : fsp.hasLe k p) (h₂ : k ≤ n) : fsp.hasLe n p := by
  obtain ⟨r, hr, h₁⟩ := h₁; use r, by linarith

theorem hasLe_of_add_left {n k p} (h : fsp.hasLe n p) : fsp.hasLe (k + n) p := by
  apply hasLe_of_le h; simp

theorem hasLe_of_add_right {n k p} (h : fsp.hasLe n p) : fsp.hasLe (n + k) p := by
  apply hasLe_of_le h; simp

@[simp]
theorem hasLe_zero {p} : fsp.hasLe 0 p ↔ p ∈ fsp.get 0 := by
  simp [hasLe]

theorem next_offset {n} : (fsp.offset n).next = fsp.offset (n + 1) :=
  offset_succ'.symm

theorem next_insertSet_succ {n set} :
(fsp.insertSet (n + 1) set).next = fsp.next.insertSet n set := by
  simp [next, insertSet]; grind

theorem next_insert_succ {n p} : (fsp.insert (n + 1) p).next = fsp.next.insert n p :=
  next_insertSet_succ

@[simp]
theorem insertSet_idem {n set} :
(fsp.insertSet n set).insertSet n set = fsp.insertSet n set := by
  simp [insertSet]; grind

@[simp]
theorem insert_idem {n p} : (fsp.insert n p).insert n p = fsp.insert n p :=
  insertSet_idem

@[simp]
theorem mem_get_succ_offset_iff {n k p} :
p ∈ (fsp.offset n).get (k + 1) ↔ p ∈ fsp.get (n + k + 1) := by
  induction n generalizing k
  · simp
  nm n ih
  rw [offset_succ']
  simp [next, ih]
  ring_nf

@[simp]
theorem get_empty : (∅ : FSP).get = λ _ => ∅ := by
  simp [empty_def]

@[simp]
theorem hasLe_empty : (∅ : FSP).hasLe = λ _ _ => False := by
  unfold hasLe; simp

theorem subset_def : a ⊆ b ↔ ∀ ⦃i⦄, a.get i ⊆ b.get i := by rfl

@[simp]
theorem get_union {i} : (a ∪ b).get i = a.get i ∪ b.get i := rfl

@[simp]
theorem hasLe_union {i p} : (a ∪ b).hasLe i p ↔ a.hasLe i p ∨ b.hasLe i p := by
  simp [hasLe]; grind

theorem insert_union {i p} : (a ∪ b).insert i p = a.insert i p ∪ b.insert i p := by
  ext; simp [FSP.insert, insertSet]; grind

@[simp]
theorem union_empty : a ∪ ∅ = a := by
  simp [union_def]

@[simp]
theorem union_insertSet {i ps} : a ∪ b.insertSet i ps = (a ∪ b).insertSet i ps := by
  ext; simp [insertSet]; grind

theorem hasLe_succ {i p} : a.hasLe (i + 1) p ↔ a.hasLe i p ∨ p ∈ a.get (i + 1) := by
  simp [hasLe]; grind

theorem get_offset {n i} :
(a.offset n).get i = if i = 0 then {p | a.hasLe n p} else a.get (n + i) := by
  induction n generalizing i
  · simp; rintro rfl; rfl
  nm n ih
  simp [offset_succ', next]
  split
  · nm i
    simp at ih ⊢
    simp [ih]
    ext p
    simp [hasLe]
    grind
  nm x i; clear x
  simp at ih ⊢
  simp [ih]; clear ih
  ring_nf