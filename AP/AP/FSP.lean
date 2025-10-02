import AP.AP.MkFold

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

def next (a : FSP) : FSP where
  get i := match i with
  | 0 => a.get 0 ∪ a.get 1
  | n + 1 => a.get # n + 2

def hasLe (a : FSP) (n : ℕ) (p : PointZ) : Prop :=
  ∃ k ≤ n, p ∈ a.get k
  
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

def insertSet (fsp : FSP) (n : ℕ) (ps : Set PointZ) : FSP where
  get i := if i = n then ps ∪ fsp.get i else fsp.get i

protected def insert (fsp : FSP) (n : ℕ) (p : PointZ) : FSP :=
  fsp.insertSet n {p}

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
theorem get_insert_of_eq {n p} : (fsp.insert n p).get n = insert p (fsp.get n) := by
  simp [FSP.insert]

theorem hasLe_insertSet_of_le {m n k ps p} (h₁ : (fsp.insertSet m ps).hasLe k p)
(h₂ : m ≤ k) (h₃ : n ≤ k) : (fsp.insertSet n ps).hasLe k p := by
  obtain ⟨r, hr, h₁⟩ := h₁
  by_cases hp : p ∈ ps
  · use n, h₃; simp [hp]
  use r, hr
  simp [insertSet] at h₁ ⊢
  aesop

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