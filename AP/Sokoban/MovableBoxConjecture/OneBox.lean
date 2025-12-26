import AP.Sokoban.MovableBoxConjecture.Basic

namespace Sokoban

open State

def State.AlwaysMovable1 (s : State) : Prop :=
  s.AlwaysMovable ∧ s.boxes.size = 1

def stateAM1Cnd (n : ℕ) (s : State) : Prop :=
  s.AlwaysMovable1 ∧ s.boxesReachable.size = n

open Classical in noncomputable
def sizeAM1Min : ℕ :=
  Nat.find! λ n => ∃ s, stateAM1Cnd n s

open Classical in noncomputable
def stateAM1Min : State :=
  Classical.epsilon # stateAM1Cnd sizeAM1Min

class MovableBoxConjecture1 : Prop where
  h : ∃ (s : State), s.AlwaysMovable1

-- #check 0 #exit

-----

variable {s s₁ s₂ s₃ : State}
variable [H : MovableBoxConjecture1]
include H

omit H in
theorem State.AlwaysMovable1.alwaysMovable (h : s.AlwaysMovable1) : s.AlwaysMovable := h.1

omit H in
theorem State.AlwaysMovable1.wf (h : s.AlwaysMovable1) : sys.WF s := h.alwaysMovable.wf

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
theorem alwaysMovable1_stateAM1Min : stateAM1Min.AlwaysMovable1 :=
  stateAM1Min_spec.1

@[simp]
theorem alwaysMovable_stateAM1Min : stateAM1Min.AlwaysMovable :=
  alwaysMovable1_stateAM1Min.alwaysMovable

omit H in @[simp]
theorem stateAM1Cnd_self : stateAM1Cnd s.boxesReachable.size s ↔ s.AlwaysMovable1 := by
  simp [stateAM1Cnd]

theorem stateAM1Min_size_boxesReachable_le {s} (h : stateAM1Cnd sizeAM1Min s) :
s.boxesReachable.size ≤ stateAM1Min.boxesReachable.size := by
  choose n h₁ using id h; rw [h₁]; apply sizeAM1Min_le'
  use stateAM1Min; simp