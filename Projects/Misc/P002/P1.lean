import Projects.Digits

namespace Misc.P002.P1

def Cnd₁ (n : ℕ) : Prop :=
  Nat.digsNum 10 n = 2 ∧ n.Prime ∧ (Nat.digRev 10 n).Prime

open Classical in noncomputable
def set₁ : Set' ℕ :=
  setOf Cnd₁

instance : DecidablePred Cnd₁ := by
  unfold Cnd₁; infer_instance

def list₁ : List ℕ :=
  List.range 100 |>.filter Cnd₁

-----

theorem setOf_cnd₁_subset {n} (h : n ∈ setOf Cnd₁) : n ∈ Finset.range 100 := by
  replace h := Nat.lt_pow_of_digsNum_eq h.1; simpa using h

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
  replace h := Nat.lt_pow_of_digsNum_eq h
  simpa using h

@[simp]
theorem toList_set₁ : set₁.toList = list₁ := by
  unfold set₁; rw [Set'.ofSet]; simp; rw [←toList_set'_ofList_list₁]; congr; ext n; simp

theorem filter_prime_icc_10_30 :
(List.icc 10 30).filter Nat.Prime = [11, 13, 17, 19, 23, 29] := by
  rw [List.icc_eq_range # by norm_num]; simp only [List.range_succ]; norm_num

theorem filter_prime_icc_31_60 :
(List.icc 31 60).filter Nat.Prime = [31, 37, 41, 43, 47, 53, 59] := by
  rw [List.icc_eq_range # by norm_num]; simp only [List.range_succ]; norm_num

theorem filter_prime_icc_61_99 :
(List.icc 61 99).filter Nat.Prime = [61, 67, 71, 73, 79, 83, 89, 97] := by
  rw [List.icc_eq_range # by norm_num]; simp only [List.range_succ]; norm_num

theorem filter_prime_icc_10_99 : (List.icc 10 99 |>.filter Nat.Prime) =
[11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] := by
  rw [List.icc_split 30] <;> try omega;; rw [List.filter_append, filter_prime_icc_10_30]
  rw [List.icc_split 60] <;> try omega;; rw [List.filter_append, filter_prime_icc_31_60]
  rw [filter_prime_icc_61_99]; rfl

theorem list₁_eq_aux₁ : list₁ = (List.icc 10 99 |>.filter Nat.Prime).filter
λ n => (Nat.digRev 10 n).Prime := by
  unfold list₁ Cnd₁
  rw [filter_prime_icc_10_99]
  simp
  conv =>
    left
    arg 1
    intro
    rw [←Bool.and_assoc]
  rw [List.filter_and']; congr
  rw [List.filter_and']
  generalize h₁ : (List.range 100).filter _ = xs
  replace h₁ : xs = List.icc 10 99
  · subst h₁
    rw [List.icc_eq_range (by omega)]
    simp
    rw [show 100 = 10 + 90 by rfl]
    rw [List.range_add]
    simp
    generalize h₁ : (List.range 10).filter _ = xs
    replace h₁ : xs = []
    · subst h₁
      simp
      intro k hk
      simp [Nat.digsNum_eq_iff]
      omega
    subst h₁
    simp
    intro k hk
    simp [Nat.digsNum_eq_iff]
    omega
  subst h₁
  rw [filter_prime_icc_10_99]

theorem list₁_eq_aux₂ : list₁ = [11, 13, 17, 19, 31, 37, 71, 73, 79, 97].filter
λ n => (Nat.digRev 10 n).Prime := by
  rw [list₁_eq_aux₁, filter_prime_icc_10_99]
  apply List.filter_eq_filter_of' λ n => n / 10 % 2 ≠ 0 ∧ n / 10 ≠ 5; simp
  intro n h₁ h₂
  simp at h₂
  generalize hm : n / 10 = m
  generalize hx : (11 :: _) = xs at h₁
  have h₃ : ∀ k ∈ xs, Nat.digsNum 10 k = 2
  · intro k hk
    have h₁ := filter_prime_icc_10_99
    rw [hx] at h₁
    rw [←h₁] at hk; clear h₁
    simp at hk
    simp [Nat.digsNum_eq_iff]
    omega
  have h₅ := h₃ _ h₁
  rw [Nat.digRev_eq_of_digsNum_eq_two h₅] at h₂
  subst hm hx
  clear h₃ h₅
  simp at h₁
  repeat rcases h₁ with rfl | h₁; norm_num at h₂ <;> simp

theorem list₁_eq_aux₃ : list₁ = [11, 13, 17, 19, 31, 37, 71, 73, 79, 97].filter
λ n => (n % 10 * 10 + n / 10).Prime := by
  rw [list₁_eq_aux₂, List.filter_eq_filter]; intro n h₁
  rw [Nat.digRev_eq_of_digsNum_eq_two]; simp at h₁
  simp [Nat.digsNum_eq_iff]; omega

theorem list₁_eq : list₁ = [11, 13, 17, 31, 37, 71, 73, 79, 97] := by
  rw [list₁_eq_aux₃]; decide

@[simp]
theorem length_list₁ : list₁.length = 9 := by
  simp [list₁_eq]

@[simp]
theorem size_set₁ : set₁.size = 9 := by
  rw [←Set'.length_toList, toList_set₁, length_list₁]