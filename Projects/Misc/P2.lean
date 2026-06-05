import Projects.Util

namespace Nat

-- #check 0 #exit

end Nat

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}

@[simp]
theorem nodup_filter_range {n p} : (range n |>.filter p).Nodup :=
  Nodup.filter _ (by simp)

theorem eq_of_sortedLE_and_perm [ha : LinearOrder α]
(h₁ : xs.SortedLE) (h₂ : ys.SortedLE) (h₃ : xs ~ ys) : xs = ys := by
  rw [sortedLE_iff_pairwise] at h₁ h₂; apply eq_of_perm_of_pairwise h₃ h₁ h₂ <;> simp

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

include ha in @[simp]
theorem toList_ofList_eq_self_iff {xs : List α} : (ofList xs).toList = xs ↔ xs.SortedLT := by
  have h₁ : (ofList xs).toList.SortedLT; simp
  constructor <;> intro h; rwa [←h]
  apply List.eq_of_sortedLE_and_perm h₁.sortedLE h.sortedLE
  apply List.perm_of_subset_and_nodup (by simp) h.nodup
  all_goals intro; simp

-- #check 0 #exit

end Set'

namespace Misc.P002

namespace P1

def Cnd₁ (n : ℕ) : Prop :=
  (Nat.toDigList 10 n).length = 2 ∧ n.Prime ∧
  (Nat.ofDigList 10 (Nat.toDigList 10 n).reverse).Prime

open Classical in noncomputable
def set₁ : Set' ℕ :=
  setOf Cnd₁

instance {n} : Decidable (Cnd₁ n) := by
  unfold Cnd₁; infer_instance

def list₁ : List ℕ :=
  List.range 100 |>.filter Cnd₁

-- #check 0 #exit

-----

theorem list₁_eq : list₁ = [11, 13, 17, 31, 37, 71, 73, 79, 97] := by
  native_decide

@[simp]
theorem length_list₁ : list₁.length = 9 := by
  simp [list₁_eq]

theorem setOf_cnd₁_subset {n} (h : n ∈ setOf Cnd₁) : n ∈ Finset.range 100 := by
  replace h := Nat.lt_pow_of_length_toDigList_eq h.1 (by omega); simpa using h

@[simp]
theorem finite_setOf_cnd₁ : (setOf Cnd₁).Finite :=
  Set.finite_of_subset_finset _ @setOf_cnd₁_subset

@[simp]
theorem sortedLT_list₁ : list₁.SortedLT := by
  rw [list₁_eq]; decide

theorem toList_set'_ofList_list₁ : (Set'.ofList list₁).toList = list₁ := by
  simp

@[simp]
theorem mem_list₁_iff_cnd₁ {n} : n ∈ list₁ ↔ Cnd₁ n := by
  simp [list₁]; rintro ⟨h, -⟩
  replace h := Nat.lt_pow_of_length_toDigList_eq h (by omega)
  simpa using h

@[simp]
theorem toList_set₁ : set₁.toList = list₁ := by
  unfold set₁; rw [Set'.ofSet]; simp; rw [←toList_set'_ofList_list₁]; congr; ext n; simp

@[simp]
theorem size_set₁ : set₁.size = 9 := by
  rw [←Set'.length_toList, toList_set₁, length_list₁]