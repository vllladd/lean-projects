import Projects.Util.Order

namespace Char

theorem min_max_def {a b : Char} : (min a b = if a ≤ b then a else b) ∧
(max a b = if a ≤ b then b else a) := by
  split_ands; all_goals
    change ite _ _ _ = _
    congr
    simp
    unfold instOrdChar compareOfLessAndEq; simp
    split_ifs with h₁ h₂ <;> simp
    · exact Std.le_of_lt h₁
    · subst h₂; simp
    · rw [Std.LawfulOrderLT.lt_iff] at h₁ ⊢
      push Not at h₁
      symm
      apply and_of
      · intro h₃; exact h₂ # Char.le_antisymm h₃ # h₁ h₃
      · intro h₃; exact Std.le_of_not_ge h₃

theorem min_def {a b : Char} : min a b = if a ≤ b then a else b :=
  min_max_def.1

theorem max_def {a b : Char} : max a b = if a ≤ b then b else a :=
  min_max_def.2

instance : LinearOrder Char where
  le_refl := Char.le_refl
  le_trans a b c := Char.le_trans
  le_antisymm a b := Char.le_antisymm
  le_total := Char.le_total
  lt_iff_le_not_ge := Std.LawfulOrderLT.lt_iff
  min_def a b := Char.min_def
  max_def a b := Char.max_def
  toDecidableLE a b := inferInstance