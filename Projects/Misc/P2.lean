import Projects.Digits

namespace Nat

-- #check 0 #exit

end Nat

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

attribute [simp] sortedLT_range

theorem sortedLE.filter [ha : LinearOrder α] {p : α → Bool}
(h : xs.SortedLE) : (xs.filter p).SortedLE := by
  rw [sortedLE_iff_pairwise] at h ⊢; apply h.filter

theorem sortedLT.filter [ha : LinearOrder α] {p : α → Bool}
(h : xs.SortedLT) : (xs.filter p).SortedLT := by
  rw [sortedLT_iff_pairwise] at h ⊢; apply h.filter

@[simp]
theorem sortedLE_range {n} : (range n).SortedLE := by
  apply SortedLT.sortedLE; simp

@[simp]
theorem sortedLE_filter_range {n} {p : ℕ → Bool} : (range n |>.filter p).SortedLE := by
  apply sortedLE.filter; simp

@[simp]
theorem sortedLT_filter_range {n} {p : ℕ → Bool} : (range n |>.filter p).SortedLT := by
  apply sortedLT.filter; simp

theorem filter_eq_filter_of {p q : α → Bool}
(h : ∀ x ∈ xs, p x ↔ q x) : xs.filter p = xs.filter q := by
  induction xs <;> grind

theorem icc_eq_range {n m} (h : n ≤ m) : icc n m = (range (m - n + 1)).map (n + ·) := by
  change (range _).map _ = _; rw [Nat.add_one_sub h]

theorem icc_split (k : ℕ) {n m} (h₁ : n ≤ k) (h₂ : k < m) :
icc n m = icc n k ++ icc (k + 1) m := by
  rw [icc_eq_range (by omega), icc_eq_range h₁, icc_eq_range # by omega]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h₁; clear h₁
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt h₂; clear h₂
  rw [show n + k + m + 1 - n + 1 = m + k + 2 by omega]
  rw [show n + k - n + 1 = k + 1 by omega]
  rw [show n + k + m + 1 - (n + k + 1) = m by omega]
  rw [List.ext_getElem_iff]
  split_ands <;> simp; omega
  intro i h₁ h₂
  rw [getElem_append]
  simp; omega

theorem filter_and {p q : α → Bool} :
xs.filter (λ x => p x && q x) = (xs.filter q).filter p := by
  simp

theorem filter_and' {p q : α → Bool} :
xs.filter (λ x => p x && q x) = (xs.filter p).filter q := by
  simp [Bool.and_comm]

theorem filter_eq_self_of {p : α → Bool} (h : ∀ x ∈ xs, p x) : xs.filter p = xs := by
  simpa

-- #check 0 #exit

end List

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

namespace Misc.P002

namespace P1

def Cnd₁ (n : ℕ) : Prop :=
  (Nat.toDigList 10 n).length = 2 ∧ n.Prime ∧ (Nat.digRev 10 n).Prime

open Classical in noncomputable
def set₁ : Set' ℕ :=
  setOf Cnd₁

instance {n} : Decidable (Cnd₁ n) := by
  unfold Cnd₁; infer_instance

def list₁ : List ℕ :=
  List.range 100 |>.filter Cnd₁

-- #check 0 #exit

-----

theorem setOf_cnd₁_subset {n} (h : n ∈ setOf Cnd₁) : n ∈ Finset.range 100 := by
  replace h := Nat.lt_pow_of_length_toDigList_eq h.1; simpa using h

@[simp]
theorem finite_setOf_cnd₁ : (setOf Cnd₁).Finite :=
  Set.finite_of_subset_finset _ @setOf_cnd₁_subset

@[simp]
theorem sortedLT_list₁ : list₁.SortedLT := by
  simp [list₁]

theorem toList_set'_ofList_list₁ : (Set'.ofList list₁).toList = list₁ := by
  simp

@[simp]
theorem mem_list₁_iff_cnd₁ {n} : n ∈ list₁ ↔ Cnd₁ n := by
  simp [list₁]; rintro ⟨h, -⟩
  replace h := Nat.lt_pow_of_length_toDigList_eq h
  simpa using h

@[simp]
theorem toList_set₁ : set₁.toList = list₁ := by
  unfold set₁; rw [Set'.ofSet]; simp; rw [←toList_set'_ofList_list₁]; congr; ext n; simp

theorem filter_prime_icc_11_30 :
(List.icc 11 30).filter Nat.Prime = [11, 13, 17, 19, 23, 29] := by
  rw [List.icc_eq_range # by norm_num]; simp only [List.range_succ]; norm_num

theorem filter_prime_icc_31_60 :
(List.icc 31 60).filter Nat.Prime = [31, 37, 41, 43, 47, 53, 59] := by
  rw [List.icc_eq_range # by norm_num]; simp only [List.range_succ]; norm_num

theorem filter_prime_icc_61_99 :
(List.icc 61 99).filter Nat.Prime = [61, 67, 71, 73, 79, 83, 89, 97] := by
  rw [List.icc_eq_range # by norm_num]; simp only [List.range_succ]; norm_num

theorem filter_prime_icc_11_99 : (List.icc 11 99 |>.filter Nat.Prime) =
[11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] := by
  rw [List.icc_split 30] <;> try omega;; rw [List.filter_append, filter_prime_icc_11_30]
  rw [List.icc_split 60] <;> try omega;; rw [List.filter_append, filter_prime_icc_31_60]
  rw [filter_prime_icc_61_99]; rfl

-- -- #check 0 #exit
-- 
-- theorem list₁_eq_filter₁ : list₁ = (List.icc 11 99 |>.filter Nat.Prime).filter
-- λ n => (Nat.digRev 10 n).Prime := by
--   unfold list₁ Cnd₁
--   rw [filter_prime_icc_11_99]
--   simp
--   conv =>
--     left
--     arg 1
--     intro
--     rw [←Bool.and_assoc]
--   rw [List.filter_and']; congr
--   rw [List.filter_and']
--   nth_rw 2 [List.filter_eq_self_of]
--   rotate_left
--   ·
--     simp
-- 
-- #check 0 #exit
-- 
-- theorem list₁_eq : list₁ = [11, 13, 17, 31, 37, 71, 73, 79, 97] := by
--   unfold list₁
-- 
-- @[simp]
-- theorem length_list₁ : list₁.length = 9 := by
--   simp [list₁_eq]
-- 
-- @[simp]
-- theorem size_set₁ : set₁.size = 9 := by
--   rw [←Set'.length_toList, toList_set₁, length_list₁]