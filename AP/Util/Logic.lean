import AP.Util.Meta

theorem hv {α : Type*} (x : α) : ∃ y, y = x := exists_eq

theorem ne_of_congr {α β : Type*} {x y : α} (f : α → β)
(h : f x ≠ f y) : x ≠ y := by contrapose! h; rw [h]

theorem prop_ind (R : Prop → Prop) (h₁ : R True) (h₂ : R False) P : R P := by
  by_cases h : P; rwa [eq_true h]; rwa [eq_false h]

@[simp]
theorem ite_eq {a b : ℕ} : ite (a = b) a b = b := by
  split_ifs with h; exact h; rfl

@[simp]
theorem forall_unit_iff {p : Unit → Prop} : (∀ u, p u) ↔ p () :=
  Unique.forall_iff

@[simp]
theorem exi_unit_iff {p : Unit → Prop} : (∃ u, p u) ↔ p () :=
  Unique.exists_iff

@[simp]
theorem exi_prop_pos_and {p : Prop → Prop} : (∃ P, P ∧ p P) ↔ p True := by
  aesop

theorem forall_spec {α β : Type*} {p : α → Prop} (f : β → α)
(h : ∀ x, p x) : ∀ y, p (f y) := by intro y; apply h

theorem forall_spec₂ {α β γ : Type*} {p : α → Prop} (f : β → γ → α)
(h : ∀ x, p x) : ∀ y z, p (f y z) := by intro y z; apply h

theorem prop_bcs (P : Prop) {R : Prop} (h₁ : P → R)
(h₂ : (P → R) → ¬P → R) : R := by tauto

theorem eq_true_of {P : Prop} (h : P) : P = True := by simpa

theorem skolemize {α β : Type*} [Nonempty β] {p : α → Prop} {q : α → β → Prop} :
(∀ x, p x → ∃ y, q x y) ↔ ∃ (f : α → β), ∀ x, p x → q x (f x) := by
  constructor
  · intro h; use λ x => Classical.epsilon λ y => p x → q x y
    intro x hx; specialize h x hx;
    convert Classical.epsilon_spec h; simp [hx]
  rintro ⟨f, h⟩ x hx; specialize h x hx; use f x

theorem and_intro (P : Prop) {Q : Prop} : P ∧ Q → Q := (·.2)

theorem iff_of_and {P Q : Prop} (hp : P) (hq : Q) : P ↔ Q := by
  simp [hp, hq]

theorem iff_of_not_and {P Q : Prop} (hp : ¬P) (hq : ¬Q) : P ↔ Q := by
  simp [hp, hq]

theorem and_of {P Q : Prop} (h₁ : P) (h₂ : P → Q) : P ∧ Q := by tauto

theorem iff_of {P Q : Prop} (h₁ : P → Q)
(h₂ : (P → Q) → (Q → P)) : P ↔ Q := by tauto

theorem not_iff' {P Q : Prop} : ¬(P ↔ Q) ↔ (P ↔ ¬Q) := by tauto

theorem not_iff_comm' {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by tauto

theorem imp_cpos {P Q : Prop} : (P → Q) ↔ (¬Q → ¬P) := by tauto

theorem choose_eq_epsilon {α : Type*} [Nonempty α] {P : α → Prop} (h : ∃ x, P x) :
h.choose = Classical.epsilon P := by
  simp only [Exists.choose, Classical.choose, Classical.indefiniteDescription,
    Classical.epsilon, Classical.strongIndefiniteDescription]
  simp [h]

theorem forall_prop_iff {R : Prop → Prop} :
(∀ P, R P) ↔ R True ∧ R False := by
  constructor
  · intro h
    simp [h]
  rintro ⟨h₁, h₂⟩ P
  by_cases h : P <;> simpa [h]

theorem exi_prop_iff {R : Prop → Prop} :
(∃ P, R P) ↔ R True ∨ R False := by
  constructor
  · rintro ⟨P, h⟩
    by_cases h₁ : P <;> simp [h₁] at h <;> simp [h]
  rintro (h | h)
  · use True
  · use False

section

local instance {R : Prop → Prop}
[ht : Decidable # R True] [hf : Decidable # R False] : Decidable # ∀ P, R P :=
match h₁ : decide # R True ∧ R False with
| true => isTrue # by
  simp at h₁
  simpa [forall_prop_iff]
| false => isFalse # by
  simp only [forall_prop_iff]
  simp at h₁
  push_neg
  exact h₁

local instance {R : Prop → Prop}
[ht : Decidable # R True] [hf : Decidable # R False] : Decidable # ∃ P, R P :=
match h₁ : decide # R True ∨ R False with
| true => isTrue # by
  simp at h₁
  simpa [exi_prop_iff]
| false => isFalse # by
  simp only [exi_prop_iff]
  simp at h₁
  push_neg
  exact h₁

theorem not_forall_congr_iff : ¬∀ (α : Type*) (P Q : α → Prop),
((∀ x, P x) ↔ (∀ x, Q x)) ↔ ∀ x, P x ↔ Q x := by
  push_neg
  use ULift Prop, ULift.down, (¬·.down)
  have h₁ : (∀ P, ¬P) → False := by decide
  aesop

theorem not_exi_congr_iff : ¬∀ (α : Type*) (P Q : α → Prop),
((∃ x, P x) ↔ (∃ x, Q x)) ↔ ∃ x, P x ↔ Q x := by
  push_neg
  use ULift Prop, ULift.down, (¬·.down)
  have h₁ : ∀ P, P ∨ ¬P := by decide
  aesop

end

theorem heq_fn {α β γ : Type*} {f : α → β} {p : γ → Prop} {x : α} {y z : γ}
(h : p y ↔ p z) : HEq (λ (_ : p y) => f x) (λ (_ : p z) => f x) := by rw [h]

theorem inst_decidable_eq {P : Prop} {H₁ H₂ : Decidable P} : H₁ = H₂ := by
  rcases H₁ with h₁ | h₁ <;> rcases H₂ with h₂ | h₂
  all_goals first | contradiction | simp [h₁]

theorem inst_decidablePred_eq {α : Type*} {p : α → Prop}
{H₁ H₂ : DecidablePred p} : H₁ = H₂ := by
  ext; exact inst_decidable_eq

theorem inst_decidableRel_eq {α β : Type*} {r : α → β → Prop}
{H₁ H₂ : DecidableRel r} : H₁ = H₂ := by
  ext; exact inst_decidable_eq

theorem inst_decidableEq_eq {α : Type*} {H₁ H₂ : DecidableEq α} : H₁ = H₂ :=
  inst_decidableRel_eq