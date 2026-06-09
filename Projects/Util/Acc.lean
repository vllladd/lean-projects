import Projects.Util.Finset

namespace Acc

variable {α β γ : Type*}

def SeqCnd (r : α → α → Prop) (x y : α) : Prop :=
  r y x ∧ ¬Acc r y

open Classical in noncomputable
def seqNext (r : α → α → Prop) (x : α) : α :=
  choose? (SeqCnd r x) |>.getD x

open Classical in noncomputable
def mkSeq (r : α → α → Prop) (x : α) (n : ℕ) : α :=
  match n with
  | 0 => x
  | n + 1 => seqNext r # mkSeq r x n

-- #check 0 #exit

-----

theorem not_linearOrder_imp_wellFounded : ¬∀ {α : Type} [LinearOrder α],
WellFounded λ (xs ys : List α) => xs < ys := by
  push Not
  use ℕ, inferInstance
  rintro ⟨h⟩
  specialize h [1]
  generalize h₁ : [1] = xs at h
  replace h₁ : ∃ n, .replicate n 0 ++ [1] = xs
  · use 0; simpa
  choose n h₁ using h₁
  induction h generalizing n
  clear xs
  nm xs h ih
  contrapose! ih; clear ih
  simp
  use n + 1
  simp [List.replicate_succ', ←h₁]

@[simp]
theorem mkSeq_zero {r} {x : α} : mkSeq r x 0 = x := rfl

theorem acc_iff {r : α → α → Prop} {x} : Acc r x ↔ ∀ ⦃y⦄, r y x → Acc r y := by
  constructor
  · rintro ⟨_⟩; assumption
  · intro h; constructor; assumption

theorem not_acc_iff {r : α → α → Prop} {x} : ¬Acc r x ↔ ∃ y, r y x ∧ ¬Acc r y := by
  nth_rw 1 [acc_iff]; simp

theorem not_acc_iff_seqCnd {r : α → α → Prop} {x} : ¬Acc r x ↔ ∃ y, SeqCnd r x y :=
  not_acc_iff

theorem not_acc_iff_seqNext {r : α → α → Prop} {x} : ¬Acc r x ↔ SeqCnd r x (seqNext r x) := by
  classical
  rw [not_acc_iff_seqCnd]; constructor
  · intro h; have h₁ := τ_spec (p := SeqCnd r x) h
    unfold seqNext; simpa [choose?_eq_of_exi h]
  · intro h; exact ⟨_, h⟩

theorem exi_seq_of_not_acc {r : α → α → Prop} {x} (h : ¬Acc r x) :
∃ (a : ℕ → α), r (a 0) x ∧ ∀ n, r (a # n + 1) (a n) := by
  classical
  have ha : Nonempty α; use x
  use λ n => mkSeq r x # n + 1; dsimp
  replace h : ∀ ⦃n⦄, ¬Acc r (mkSeq r x n)
  · intro n
    induction n; simpa
    nm n ih
    simp [mkSeq]
    rw [not_acc_iff_seqNext] at ih
    exact ih.2
  split_ands
  · specialize @h 0
    simp at h
    simp [mkSeq]
    rw [not_acc_iff_seqNext] at h
    exact h.1
  intro n
  nth_rw 1 [mkSeq]
  generalize h₁ : mkSeq r x (n + 1) = x'
  specialize @h # n + 1
  rw [h₁, not_acc_iff_seqNext] at h
  exact h.1

theorem acc_of_not_seq {r : α → α → Prop} {x}
(h : ∀ (a : ℕ → α), r (a 0) x → ∃ n, ¬r (a # n + 1) (a n)) : Acc r x := by
  contrapose! h; exact exi_seq_of_not_acc h

theorem acc_iff_not_seq' {r : α → α → Prop} {x} :
Acc r x ↔ ¬∃ (a : ℕ → α), r (a 0) x ∧ ∀ n, r (a # n + 1) (a n) := by
  constructor
  · rintro h ⟨a, h₁, h₂⟩
    induction h generalizing a
    clear x
    nm x h ih
    simp at ih
    specialize ih _ h₁ (a # · + 1) (h₂ _)
    choose n ih using ih
    specialize h₂ # n + 1
    contradiction
  intro h
  push Not at h
  exact acc_of_not_seq h

theorem acc_iff_not_seq {r : α → α → Prop} {x} :
Acc r x ↔ ∀ (a : ℕ → α), r (a 0) x → ∃ n, ¬r (a # n + 1) (a n) := by
  simp [acc_iff_not_seq']