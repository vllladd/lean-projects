import Projects.Fixpoint.Basic

set_option linter.dupNamespace false

namespace Fixpoint

variable {α : Type*}

@[scoped grind =]
def infPrefix [LE α] [InfSet α] (f : α → α) : α :=
  sInf # Set.ofPred # PreFixpoint f

@[scoped grind =]
def supPostfix [LE α] [SupSet α] (f : α → α) : α :=
  sSup # Set.ofPred # PostFixpoint f

-----

section

variable {f : α → α} {x y z : α}
variable [ha : CompleteLattice α]

@[scoped grind →]
theorem preFixpoint_infPrefix (hf : Monotone f) : PreFixpoint f (infPrefix f) := by
  unfold infPrefix
  generalize hs : Set.ofPred (PreFixpoint f) = s
  generalize hx : sInf s = x
  suffices : x ∈ s; grind
  simp [←hs, PreFixpoint]
  nth_rw 2 [←hx]
  apply le_sInf
  intro y hy
  have hy' := hy
  simp [←hs, PreFixpoint] at hy
  apply hy.trans'
  apply hf
  rw [←hx]
  exact sInf_le hy'

@[scoped grind →]
theorem postFixpoint_supPostfix (hf : Monotone f) : PostFixpoint f (supPostfix f) := by
  unfold supPostfix
  generalize hs : Set.ofPred (PostFixpoint f) = s
  generalize hx : sSup s = x
  unfold PostFixpoint
  nth_rw 1 [←hx]
  apply sSup_le
  intro y hy
  have hy' := hy
  simp [←hs, PostFixpoint] at hy
  apply hy.trans
  apply hf
  rw [←hx]
  exact le_sSup hy'

@[scoped grind →]
theorem postFixpoint_infPrefix (hf : Monotone f) : PostFixpoint f (infPrefix f) := by
  unfold infPrefix
  generalize hs : Set.ofPred (PreFixpoint f) = s
  generalize hx : sInf s = x
  unfold PostFixpoint
  nth_rw 1 [←hx]
  apply sInf_le
  simp [←hs, PreFixpoint]
  apply hf; grind

@[scoped grind →]
theorem preFixpoint_supPostfix (hf : Monotone f) : PreFixpoint f (supPostfix f) := by
  unfold supPostfix
  generalize hs : Set.ofPred (PostFixpoint f) = s
  generalize hx : sSup s = x
  unfold PreFixpoint
  nth_rw 2 [←hx]
  apply le_sSup
  simp [←hs, PostFixpoint]
  apply hf; grind

@[scoped grind →]
theorem fixpoint_infPrefix (hf : Monotone f) : Fixpoint f (infPrefix f) := by
  grind

@[scoped grind →]
theorem fixpoint_supPostfix (hf : Monotone f) : Fixpoint f (supPostfix f) := by
  grind

@[scoped grind →]
theorem le_of_preFixpoint_infPrefix (h : PreFixpoint f x) : infPrefix f ≤ x := by
  apply sInf_le; simpa

@[scoped grind →]
theorem le_of_postFixpoint_supPostfix (h : PostFixpoint f x) : x ≤ supPostfix f := by
  apply le_sSup; simpa

@[scoped grind →]
theorem exi_least_fixpoint_of_monotone (h : Monotone f) :
∃ x, Fixpoint f x ∧ ∀ y, Fixpoint f y → x ≤ y := by
  grind

@[scoped grind →]
theorem exi_greatest_fixpoint_of_monotone (h : Monotone f) :
∃ x, Fixpoint f x ∧ ∀ y, Fixpoint f y → y ≤ x := by
  grind

theorem exi_least_and_greatest_fixpoint_of_monotone (h : Monotone f) :
(∃ x, Fixpoint f x ∧ ∀ y, Fixpoint f y → x ≤ y) ∧
(∃ x, Fixpoint f x ∧ ∀ y, Fixpoint f y → y ≤ x) := by
  grind

end section

variable {f : α → α} {x y z : α}
variable [ha : PartialOrder α]

theorem postFixpoint_least_preFixpoint (hf : Monotone f)
(h₁ : PreFixpoint f x) (h₂ : ∀ ⦃y⦄, PreFixpoint f y → x ≤ y) : PostFixpoint f x :=
  h₂ # hf h₁

theorem preFixpoint_greatest_postFixpoint (hf : Monotone f)
(h₁ : PostFixpoint f x) (h₂ : ∀ ⦃y⦄, PostFixpoint f y → y ≤ x) : PreFixpoint f x :=
  h₂ # hf h₁

end section

variable {f : α → α} {x y z : α}
variable [ha : CompleteLattice α]

omit ha in @[simp]
theorem infPrefix_pi_const {P : Prop} :
infPrefix (λ (_ : α → Prop) (_ : α) => P) = λ _ => P := by
  ext x; induction P using prop_ind <;> simp [infPrefix, PreFixpoint]
  · intro p h; specialize h x; simp at h; exact h
  · use ⊥; simp; rfl

omit ha in @[simp]
theorem supPostfix_pi_const {P : Prop} :
supPostfix (λ (_ : α → Prop) (_ : α) => P) = λ _ => P := by
  ext x; induction P using prop_ind <;> simp [supPostfix, PostFixpoint]
  · use ⊤; simp; rfl
  · intro p h; specialize h x; simp at h; exact h