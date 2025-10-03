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

theorem skolemize {α β : Type*} [hb : Nonempty β] {p : α → Prop} {q : α → β → Prop} :
(∀ x, p x → ∃ y, q x y) ↔ ∃ (f : α → β), ∀ x, p x → q x (f x) := by
  constructor
  · intro h; use λ x => Classical.epsilon λ y => p x → q x y
    intro x hx; specialize h x hx;
    convert Classical.epsilon_spec h; simp [hx]
  rintro ⟨f, h⟩ x hx; specialize h x hx; use f x

theorem skolemize' {α β : Type*} [hb : Nonempty β] {p : α → β → Prop} :
(∀ x, ∃ y, p x y) ↔ ∃ (f : α → β), ∀ x, p x (f x) := by
  have h := skolemize (p := λ _ => True) (q := p); simp at h; exact h

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
  all_goals first | contradiction | simp

theorem inst_decidablePred_eq {α : Type*} {p : α → Prop}
{H₁ H₂ : DecidablePred p} : H₁ = H₂ := by
  ext; exact inst_decidable_eq

theorem inst_decidableRel_eq {α β : Type*} {r : α → β → Prop}
{H₁ H₂ : DecidableRel r} : H₁ = H₂ := by
  ext; exact inst_decidable_eq

theorem inst_decidableEq_eq {α : Type*} {H₁ H₂ : DecidableEq α} : H₁ = H₂ :=
  inst_decidableRel_eq

theorem forall_iff_of {α : Sort*} {p q : α → Prop}
(h : ∀ x, p x ↔ q x) : (∀ x, p x) ↔ (∀ x, q x) := by simp [h]

theorem exists_iff_of {α : Sort*} {p q : α → Prop}
(h : ∀ x, p x ↔ q x) : (∃ x, p x) ↔ (∃ x, q x) := by simp [h]

theorem iff_of_isEquiv {α : Type*} {r : α → α → Prop}
[hr : IsEquiv α r] {a b c d : α} (h₁ : r a c) (h₂ : r b d) :
r a b ↔ r c d := by
  constructor <;> intro h
  · trans a; apply hr.symm; exact h₁
    trans b <;> assumption
  · trans c; exact h₁
    trans d; exact h
    apply hr.symm; exact h₂

theorem not_and_iff_or {P Q} : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by tauto

theorem ne_symm' {α : Type*} {a b : α} (h : ¬(a = b)) : ¬(b = a) := by tauto

theorem ne_comm' {α : Type*} {a b : α} : ¬(a = b) ↔ ¬(b = a) := by tauto

noncomputable
def Nonempty.inhabited {α : Type*} (h : Nonempty α) : Inhabited α :=
  Classical.inhabited_of_nonempty h

theorem dite_eq_dite_of_pos {α : Type*} {P Q : Prop} [hp : Decidable P] [hq : Decidable Q]
{f : P → α} {g : Q → α} {x y : α} (h₁ : P) (h₂ : Q) (h₃ : f h₁ = g h₂) :
(if h : P then f h else x) = if h : Q then g h else y := by simp [h₁, h₂, h₃]

noncomputable
def choose? {α : Type*} (p : α → Prop) [Decidable # ∃ x, p x] : Option α :=
  if h : ∃ x, p x then some h.choose else none

theorem choose?_eq_ite {α : Type*} [ha : Nonempty α]
{p : α → Prop} [hd : Decidable # ∃ x, p x] :
choose? p = if ∃ x, p x then some # Classical.epsilon p else none := by
  unfold choose?; split_ifs with h₁
  simp; exact choose_eq_epsilon h₁; rfl

theorem choose?_eq_of_exi {α : Type*} (p : α → Prop)
[hh : Decidable # ∃ x, p x] (h : ∃ x, p x) : haveI : Nonempty α := ⟨h.choose⟩
choose? p = some (Classical.epsilon p) := by
  simp [choose?, h]; generalize_proofs h₁; exact choose_eq_epsilon h

theorem forall_eq_left_iff_eq_iff {α : Type*} {x y : α} :
(∀ z, z = x ↔ z = y) ↔ x = y := by aesop

theorem forall_eq_right_iff_eq_iff {α : Type*} {x y : α} :
(∀ z, x = z ↔ y = z) ↔ x = y := by aesop

theorem and_iff_and_of {P Q R S : Prop}
(h₁ : P ↔ R) (h₂ : Q ↔ S) : P ∧ Q ↔ R ∧ S := by tauto

@[simp]
theorem match_decide_eq_dite {α : Type*} {P} [H : Decidable P]
{f : decide P = true → α} {g : decide P = false → α} :
(match h : decide P with
| true => f h
| false => g h
) = if h : P then f (by simpa) else g (by simpa) := by
  split <;> nm h₁ <;> simp at h₁ <;> simp [h₁]

@[simp]
theorem match_decide_eq_ite {α : Type*} {P} [H : Decidable P] {x y : α} :
(match decide P with
| true => x
| false => y
) = if P then x else y := by
  split <;> nm h₁ <;> simp at h₁ <;> simp [h₁]

@[simp]
theorem choose?_eq_some_iff {α : Type*} {p : α → Prop} {x}
[hp : Decidable # ∃ x, p x] : choose? p = some x ↔ p x ∧
haveI : Inhabited α := ⟨x⟩; Classical.epsilon p = x := by
  have h₁ : Inhabited α := ⟨x⟩; simp [choose?]; constructor
  · rintro ⟨h₂, rfl⟩; use h₂.choose_spec, choose_eq_epsilon h₂ |>.symm
  · rintro ⟨h₂, h₃⟩; use ⟨_, h₂⟩; rwa [choose_eq_epsilon ⟨_, h₂⟩]

theorem epsilon_eq_of_exiu {α : Type*} [ha : Inhabited α] {p : α → Prop} {x}
(h₁ : p x) (h₂ : ∃! x, p x) : Classical.epsilon p = x := by
  have hp : p = λ y => x = y
  · ext y; obtain ⟨z, h₂, h₃⟩ := h₂
    constructor <;> intro h₄
    · rw [h₃ _ h₁, h₃ _ h₄]
    · rwa [←h₄]
  have h₃ := Classical.epsilon_spec h₂
  dsimp at h₃; subst hp; simp at h₃; exact h₃.symm

theorem epsilon_eq_of {α : Type*} [ha : Inhabited α] {p : α → Prop} {x}
(h₁ : p x) (h₂ : ∀ y, p y → y = x) : Classical.epsilon p = x := by
  apply epsilon_eq_of_exiu h₁; use x