import AP.Sokoban.MovableBoxConjecture.OneBox.Defs

namespace Sokoban.MovableBoxConjecture1

open State MovableBoxConjecture

variable {s s₁ s₂ s₃ : State}
variable [H : MovableBoxConjecture1]
include H

omit H in @[simp]
instance [H : AlwaysMovable1 s] : AlwaysMovable s := H.1

theorem exi_stateAM1Cnd : ∃ n s, stateAM1Cnd n s := by
  choose s H using H.1; exact ⟨_, s, H, rfl⟩

theorem sizeAM1Min_spec' : (∃ s, stateAM1Cnd sizeAM1Min s) ∧
(∀ n, (∃ s, stateAM1Cnd n s) → sizeAM1Min ≤ n) :=
  Nat.find!_spec' exi_stateAM1Cnd

theorem sizeAM1Min_spec : ∃ s, stateAM1Cnd sizeAM1Min s :=
  sizeAM1Min_spec'.1

theorem sizeAM1Min_le' {n} (h : ∃ s, stateAM1Cnd n s) : sizeAM1Min ≤ n :=
  sizeAM1Min_spec'|>.2 n h

theorem sizeAM1Min_le {n s} (h : stateAM1Cnd n s) : sizeAM1Min ≤ n :=
  sizeAM1Min_le' ⟨_, h⟩

@[simp]
theorem stateAM1Min_spec : stateAM1Cnd sizeAM1Min stateAM1Min :=
  Classical.epsilon_spec sizeAM1Min_spec

@[simp]
theorem alwaysMovable1_stateAM1Min : AlwaysMovable1 stateAM1Min :=
  stateAM1Min_spec.1

omit H in @[simp]
theorem stateAM1Cnd_self : stateAM1Cnd s.boxesReachable.size s ↔ AlwaysMovable1 s := by
  simp [stateAM1Cnd]

theorem stateAM1Min_size_boxesReachable_le {s} (h : stateAM1Cnd sizeAM1Min s) :
s.boxesReachable.size ≤ stateAM1Min.boxesReachable.size := by
  choose n h₁ using id h; rw [h₁]; apply sizeAM1Min_le'; use stateAM1Min; simp