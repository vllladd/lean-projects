import AP.Util.List

namespace Std.DHashMap

@[simp]
theorem toList_empty {α : Type*}
[hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type*} :
(∅ : Std.DHashMap α β).toList = [] := by
  ext:1; simp

@[simp]
theorem nodup_keys {α : Type*}
[hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type*}
{m : Std.DHashMap α β} : m.keys.Nodup := by
  unfold List.Nodup
  convert m.distinct_keys
  simp

@[simp]
theorem nodup_toList {α : Type*}
[hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type*}
{m : Std.DHashMap α β} : m.toList.Nodup := by
  have h₁ := m.nodup_keys
  rw [←map_fst_toList_eq_keys] at h₁
  exact List.Nodup.of_map _ h₁

theorem equiv_iff_get? {α : Type*}
[hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type*}
{m₁ m₂ : Std.DHashMap α β} : m₁.Equiv m₂ ↔ ∀ i, m₁.get? i = m₂.get? i := by
  constructor <;> intro h
  · intro i
    by_cases h₁ : i ∈ m₁ <;> have h₂ := h₁ <;> rw [h.mem_iff] at h₂
    · exact Equiv.get?_eq h
    · rw [get?_eq_none h₁, get?_eq_none h₂]
  rw [equiv_iff_toList_perm]
  rw [List.perm_ext_iff_of_nodup nodup_toList nodup_toList]
  rintro ⟨i, x⟩; simp [h]

theorem toList_ofList_perm {α : Type*}
[hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type*}
{xs : List (Σ i, β i)} (h : (xs.map (·.1)).Nodup) :
(Std.DHashMap.ofList xs).toList.Perm xs := by
  rw [List.perm_ext_iff_of_nodup nodup_toList # h.of_map _]
  rintro ⟨i, x⟩
  simp
  constructor <;> intro h₁
  · contrapose! h₁
    by_cases h₂ : i ∈ ofList xs <;> simp at h₂
    · obtain ⟨y, h₂⟩ := h₂
      rw [get?_ofList_of_mem]
      rotate_left
      · simp
        rfl
      · exact y
      · simp
        unfold List.Nodup at h
        rw [List.pairwise_map] at h
        exact h
      · exact h₂
      simp
      rintro rfl
      contradiction
    rw [get?_ofList_of_contains_eq_false]; simp
    simpa
  rw [get?_ofList_of_mem]
  rotate_left
  · simp
    rfl
  · exact x
  · simp
    unfold List.Nodup at h
    rw [List.pairwise_map] at h
    exact h
  · exact h₁
  simp

theorem ofList_toList_equiv {α : Type*}
[hh₁ : LinearOrder α] [hh₂ : Hashable α] {β : α → Type*}
{m : Std.DHashMap α β} : (Std.DHashMap.ofList m.toList).Equiv m := by
  rw [equiv_iff_toList_perm]
  apply toList_ofList_perm
  simp