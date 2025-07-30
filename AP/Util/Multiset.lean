import AP.Util.Quotient

namespace Multiset

@[simp]
theorem nodup_toList_iff {α : Type*}
{m : Multiset α} : m.toList.Nodup ↔ m.Nodup := Quotient.apply_of

@[simp]
theorem ofList_toList_perm {α : Type*} {xs : List α} :
(xs : Multiset α).toList.Perm xs := by
  apply Quotient.mk_out (s := List.isSetoid α)

@[simp]
theorem ofList_cons {α : Type*} {m : Multiset α} {x} :
↑(x :: m.toList) = x ::ₘ m := by
  induction m using Quotient.ind; simp

@[simp]
theorem toList_append_perm {α : Type*} {m : Multiset α} {x} :
(x ::ₘ m).toList.Perm (x :: m.toList) := by
  simp [←ofList_cons]

@[simp]
theorem length_filter_toList_cons_eq {α : Type*}
{P : α → Bool} {ms : Multiset α} {x} :
((x ::ₘ ms).toList.filter P).length = (ms.toList.filter P).length +
if P x then 1 else 0 := by
  have h₁ : (x ::ₘ ms).toList.Perm (x :: ms.toList) := by simp
  replace h₁ := List.Perm.filter P h₁
  replace h₁ := List.Perm.length_eq h₁
  rw [h₁]
  rw [List.filter_cons]
  split_ifs <;> simp