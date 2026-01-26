import AP.Util.List.Part_001

namespace List

variable {α β γ : Type*}
variable {xs ys zs : List α}
variable {L : List (List α)}

theorem bw_law_1 [M : Monoid α] : xs.foldr (· * ·) 1 = xs.foldl (· * ·) 1 := by
  induction xs; rfl; nm x xs ih; simp; rw [show x = x * 1 by simp, foldl_assoc, ih]; simp

theorem bw_law_2 {f g} {a : α} (h₁ : ∀ {x y z}, f x (g y z) = g (f x y) z)
(h₂ : ∀ {x a}, f x a = g a x) : xs.foldr f a = xs.foldl g a := by
  cases show f = λ a b => g b a by grind
  induction xs; rfl; nm x xs ih; simp [ih]; clear ih
  induction xs using List.reverseRecOn; rfl; grind

theorem bw_law_3 {f} {a : α} : xs.foldr f a = xs.reverse.foldl (flip f) a := by
  simp [flip]