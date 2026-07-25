import Projects.Util.Meta

variable {α β γ : Type*}

@[reducible] noncomputable
def Nonempty.inhabited {α : Type*} (h : Nonempty α) : Inhabited α :=
  Classical.inhabited_of_nonempty h

noncomputable
def choose? {α : Type*} (p : α → Prop) : Option α :=
  haveI := Classical.propDecidable
  if h : ∃ x, p x then some h.choose else none

noncomputable
def idNC (x : α) : α :=
  haveI : Nonempty α := ⟨x⟩
  τ y, x = y

open Classical in noncomputable
def ite' (p : Prop) (x y : α) : α :=
  if p then x else y

open Classical in noncomputable
def dite' (p : Prop) (f : p → α) (g : ¬p → α) : α :=
  if h : p then f h else g h

-- #check 0 #exit

-----

theorem τ_spec {p : α → Prop} (h : ∃ y, p y) : p # @Classical.epsilon α h.nonempty p :=
  Classical.epsilon_spec h

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
  · intro h; use λ x => τ y, p x → q x y
    intro x hx; specialize h x hx;
    convert τ_spec h; simp [hx]
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

theorem choose_eq_τ {α : Type*} [Nonempty α] {P : α → Prop} (h : ∃ x, P x) :
h.choose = τ x, P x := by
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
  push Not
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
  push Not
  exact h₁

theorem not_forall_congr_iff : ¬∀ (α : Type*) (P Q : α → Prop),
((∀ x, P x) ↔ (∀ x, Q x)) ↔ ∀ x, P x ↔ Q x := by
  push Not
  use ULift Prop, ULift.down, (¬·.down)
  have h₁ : (∀ P, ¬P) → False := by decide
  aesop

theorem not_exi_congr_iff : ¬∀ (α : Type*) (P Q : α → Prop),
((∃ x, P x) ↔ (∃ x, Q x)) ↔ ∃ x, P x ↔ Q x := by
  push Not
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

theorem dite_eq_dite_of_pos {α : Type*} {P Q : Prop} [hp : Decidable P] [hq : Decidable Q]
{f : P → α} {g : Q → α} {x y : α} (h₁ : P) (h₂ : Q) (h₃ : f h₁ = g h₂) :
(if h : P then f h else x) = if h : Q then g h else y := by simp [h₁, h₂, h₃]

theorem choose?_eq_dite {α : Type*} {p : α → Prop} :
haveI := Classical.propDecidable; choose? p =
if h : ∃ x, p x then haveI : Nonempty α := ⟨h.choose⟩
some # τ x, p x else none := by
  unfold choose?; split_ifs with h₁; on_goal 2 => rfl
  have ha : Nonempty α; use h₁.choose; rw [choose_eq_τ]

theorem choose?_eq_ite {α : Type*} {p : α → Prop} [ha : Nonempty α] :
haveI := Classical.propDecidable; choose? p =
if ∃ x, p x then some # τ x, p x else none := by
  rw [choose?_eq_dite]; split_ifs <;> simp

theorem choose?_eq_of_exi {α : Type*} {p : α → Prop} (h : ∃ x, p x) :
haveI : Nonempty α := ⟨h.choose⟩; choose? p = some (τ x, p x) := by
  simp [choose?, h]; generalize_proofs h₁; exact choose_eq_τ h

theorem choose?_eq_of_pos {α : Type*} {p : α → Prop} (h : ∃ x, p x) :
haveI : Nonempty α := ⟨h.choose⟩; choose? p = some (τ x, p x) :=
  choose?_eq_of_exi h

@[simp]
theorem choose?_eq_none_iff {α : Type*} {p : α → Prop} : choose? p = none ↔ ∀ x, ¬p x := by
  simp [choose?]

theorem choose?_eq_of_neg {α : Type*} {p : α → Prop} (h : ∀ x, ¬p x) : choose? p = none :=
  choose?_eq_none_iff.mpr h

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
theorem choose?_eq_some_iff {α : Type*} {p : α → Prop} {x} :
haveI : Nonempty α := ⟨x⟩; choose? p = some x ↔ p x ∧ (τ x, p x) = x := by
  have h₁ : Nonempty α := ⟨x⟩; simp [choose?]; constructor
  · rintro ⟨h₂, rfl⟩; use h₂.choose_spec, choose_eq_τ h₂ |>.symm
  · rintro ⟨h₂, h₃⟩; use ⟨_, h₂⟩; rwa [choose_eq_τ ⟨_, h₂⟩]

theorem τ_eq_of_exiu {α : Type*} [ha : Nonempty α] {p : α → Prop} {x}
(h₁ : p x) (h₂ : ∃! x, p x) : (τ x, p x) = x := by
  have hp : p = λ y => x = y
  · ext y; obtain ⟨z, h₂, h₃⟩ := h₂
    constructor <;> intro h₄
    · rw [h₃ _ h₁, h₃ _ h₄]
    · rwa [←h₄]
  have h₃ := τ_spec h₂
  dsimp at h₃; subst hp; simp at h₃; exact h₃.symm

theorem τ_eq_of {α : Type*} [ha : Nonempty α] {p : α → Prop} {x}
(h₁ : p x) (h₂ : ∀ y, p y → y = x) : (τ x, p x) = x := by
  apply τ_eq_of_exiu h₁; use x

theorem Bool.dite_eq_false_iff {α : Type*} {b : Bool}
{f : b = false → α} {g : ¬(b = false) → α} : (if h : b = false then f h else g h) =
(if h : b then g (by simpa) else f (by simp_all)) := by aesop

@[simp]
theorem Bool.ite_eq_false_iff {α : Type*} {b : Bool} {x y : α} :
(if b = false then x else y) = (if b then y else x) := dite_eq_false_iff

@[simp]
theorem and_not_iff_right_iff {P Q : Prop} : (P ∧ ¬Q ↔ Q) ↔ (¬P ∧ ¬Q) := by tauto

@[simp]
theorem forall_ne_iff_not {α : Type*} {p : α → Prop} {x : α} : (∀ y, p y → y ≠ x) ↔ ¬p x := by
  simp_all only [ne_eq]
  apply Iff.intro
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    apply a
    on_goal 2 => rfl
    · simp_all only
  · intro a y a_1
    apply Aesop.BuiltinRules.not_intro
    intro a_2
    subst a_2
    simp_all only

@[simp]
theorem forall_ne_iff_not' {α : Type*} {p : α → Prop} {x : α} : (∀ y, p y → x ≠ y) ↔ ¬p x := by
  convert forall_ne_iff_not using 2; tauto

@[simp] instance fact_true : Fact True := ⟨trivial⟩
@[simp] theorem not_fact_false : ¬Fact False := by rintro ⟨⟨⟩⟩

theorem iff_iff_not' {P Q : Prop} : (P ↔ Q) ↔ (¬P ↔ ¬Q) := by tauto
theorem imp_iff_not' {P Q : Prop} : (P → Q) ↔ (¬Q → ¬P) := by tauto

instance {P} [H : Fact P] : Decidable P := .isTrue H.1
instance {P} [H : Fact P] : Fact (Fact P) := ⟨H⟩

theorem eq_iff_and_apply {α β : Type*} {x y : α} (f : α → β) :
x = y ↔ x = y ∧ f x = f y := by
  simp_all only [iff_self_and, implies_true]

@[simp]
theorem epsilon_eq_left {α : Type*} {x : α} [ha : Nonempty α] : (τ y, y = x) = x := by
  apply τ_eq_of <;> simp

@[simp]
theorem epsilon_eq_right {α : Type*} {x : α} [ha : Nonempty α] : (τ y, x = y) = x := by
  apply τ_eq_of <;> simp

@[simp] theorem iff_not_left_imp_iff {P Q : Prop} : (P ↔ (¬P → Q)) ↔ (Q → P) := by tauto
@[simp] theorem not_left_iff_imp_iff {P Q : Prop} : (¬P ↔ (P → Q)) ↔ (Q → ¬P) := by tauto

theorem ne_def {α : Type*} {x y : α} : x ≠ y ↔ ¬(x = y) := by rfl

theorem setoid_apply_of_eq {s : Setoid α} {x y : α} (h : x = y) : s x y := by
  rw [h]

theorem Equivalence.comm {r : α → α → Prop} {a b} (h : Equivalence r) : r a b ↔ r b a :=
  ⟨h.symm, h.symm⟩

theorem Equivalence.iff_of_left {r : α → α → Prop} {a b c}
(h₁ : Equivalence r) (h₂ : r a b) : r a c ↔ r b c :=
  ⟨h₁.trans # h₁.symm h₂, h₁.trans h₂⟩

theorem Equivalence.iff_of_right {r : α → α → Prop} {a b c}
(h₁ : Equivalence r) (h₂ : r a b) : r c a ↔ r c b := by
  nth_rw 1 [h₁.comm]; nth_rw 2 [h₁.comm]; exact h₁.iff_of_left h₂

attribute [simp] Id.instMonad

@[simp]
theorem bif_eq_if {b : Bool} {x y : α} : (bif b then x else y) = (if b then x else y) := by
  simp

instance [ha : DecidableEq α] : DecidableEq (Id α) := ha

theorem idNC_def : idNC = λ (x : α) => x := by
  ext; simp [idNC]

noncomputable
instance (priority := low) {α : Type*} [ha : Nonempty α] : Inhabited α :=
  Classical.inhabited_of_nonempty ha

theorem ite_eq_ite' {p : Prop} {x y : α} [Decidable p] :
(if p then x else y) = ite' p x y := by
  simp [ite']

theorem ite'_eq_ite {p : Prop} {x y : α} [Decidable p] :
ite' p x y = (if p then x else y) :=
  ite_eq_ite'.symm

@[simp]
theorem ite'_true {x y : α} : ite' True x y = x := by
  simp [ite'_eq_ite]

@[simp]
theorem ite'_false {x y : α} : ite' False x y = y := by
  simp [ite'_eq_ite]

@[simp]
theorem ite'_same {p : Prop} {x : α} : ite' p x x = x := by
  classical simp [ite'_eq_ite]

theorem dite_eq_dite' {p : Prop} {f : p → α} {g : ¬p → α} [Decidable p] :
(if h : p then f h else g h) = dite' p f g := by
  simp [dite']; congr

theorem dite'_eq_dite {p : Prop} {f : p → α} {g : ¬p → α} [Decidable p] :
dite' p f g = (if h : p then f h else g h) :=
  dite_eq_dite'.symm

@[simp]
theorem dite'_true {f g} : @dite' α True f g = f trivial := by
  simp [dite'_eq_dite]

@[simp]
theorem dite'_false {f g} : @dite' α False f g = g not_false := by
  simp [dite'_eq_dite]

@[simp]
theorem decide_eq_not_decide {p q : Prop} [hp : Decidable p] [hq : Decidable q] :
decide p = (!decide q) ↔ (p ↔ ¬q) := by
  by_cases h : p <;> simp [h]

@[simp]
theorem not_decide_eq_decide {p q : Prop} [hp : Decidable p] [hq : Decidable q] :
(!decide p) = decide q ↔ (p ↔ ¬q) := by
  by_cases h : p <;> simp [h]

theorem choose?_of_pos {P : Option α → Prop} {p : α → Prop}
(h₁ : ∃ x, p x) (h₂ : ∀ x, haveI : Nonempty α := ⟨h₁.choose⟩
(τ x, p x) = x → p x → P (some x)) : P (choose? p) := by
  rw [choose?_eq_of_pos h₁]; exact h₂ _ rfl # τ_spec h₁

theorem choose?_of_neg {P : Option α → Prop} {p : α → Prop}
(h₁ : ∀ x, ¬p x) (h₂ : P none) : P (choose? p) := by
  rwa [choose?_eq_of_neg h₁]

theorem exiu_iff {p : α → Prop} : (∃! x, p x) ↔ ∃ x, p x ∧ ∀ y, p y → y = x :=
  Eq.to_iff rfl

theorem not_exiu_iff {p : α → Prop} :
¬(∃! x, p x) ↔ ∀ x, p x → ∃ y, p y ∧ y ≠ x := by
  simp [exiu_iff]

theorem not_exiu_iff_or {p : α → Prop} :
¬(∃! x, p x) ↔ (∀ x, ¬p x) ∨ (∃ x y, p x ∧ p y ∧ x ≠ y) := by
  grind [exiu_iff]

@[simp]
theorem eq_symm_iff_simp {α : Type*} {x y : α} : (x = y ↔ y = x) ↔ True := by
  tauto

theorem comm_of_symm {α : Type*} {r : α → α → Prop} {x y}
(h : ∀ {x y}, r x y → r y x) : r x y ↔ r y x := ⟨h, h⟩

theorem dite_true_eq! : @dite α True = λ _ f _ => f trivial := by
  funext; simp

theorem dite_false_eq! : @dite α False = λ _ _ g => g not_false := by
  funext; simp

theorem min_comm! [ha : SemilatticeInf α] : min = (λ (x y : α) => min y x) := by
  funext; grind

theorem max_comm! [ha : SemilatticeSup α] : max = (λ (x y : α) => max y x) := by
  funext; grind

@[simp]
theorem fmap_Id {α β : Type} {f : α → β} {x : α} : @Functor.map Id _ α β f x = f x := rfl

theorem τ_eq_of_ofPred [ha : Nonempty α] {p : α → Prop} {x}
(h : Set.ofPred p = {x}) : (τ x, p x) = x := by
  apply τ_eq_of; simpa using congrArg (x ∈ ·) h
  intro y hy; replace h := congrArg (y ∈ ·) h
  simp at h; tauto