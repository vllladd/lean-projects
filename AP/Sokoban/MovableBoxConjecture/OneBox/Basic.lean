import AP.Sokoban.MovableBoxConjecture.OneBox.Defs

namespace Sokoban.MovableBoxConjecture1

open State MovableBoxConjecture

variable {s s₁ s₂ s₃ : State}
variable [H : MovableBoxConjecture1]
include H

theorem exi_stateCnd₀ : ∃ n s, stateCnd₀ n s := by
  choose s H using H.1; exact ⟨_, s, H, rfl⟩

theorem size₀_spec' : (∃ s, stateCnd₀ size₀ s) ∧
(∀ n, (∃ s, stateCnd₀ n s) → size₀ ≤ n) :=
  Nat.find!_spec' exi_stateCnd₀

theorem size₀_spec : ∃ s, stateCnd₀ size₀ s :=
  size₀_spec'.1

theorem size₀_le' {n} (h : ∃ s, stateCnd₀ n s) : size₀ ≤ n :=
  size₀_spec'|>.2 n h

theorem size₀_le {n s} (h : stateCnd₀ n s) : size₀ ≤ n :=
  size₀_le' ⟨_, h⟩

@[simp]
theorem state₀_spec : stateCnd₀ size₀ state₀ :=
  Classical.epsilon_spec size₀_spec

@[simp]
theorem alwaysMovable1_state₀ : AlwaysMovable1 state₀ :=
  state₀_spec.1

omit H in @[simp]
theorem stateCnd₀_self : stateCnd₀ s.boxesReachable.size s ↔ AlwaysMovable1 s := by
  simp [stateCnd₀]

theorem state₀_size_boxesReachable_le {s} (h : stateCnd₀ size₀ s) :
s.boxesReachable.size ≤ state₀.boxesReachable.size := by
  choose n h₁ using id h; rw [h₁]; apply size₀_le'; use state₀; simp