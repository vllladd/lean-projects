import AP.Util.Logic

def fn_set' {α : Type*} [DecidableEq α] (a b x : α) : α :=
if x = a then b else x

def fn_swap' {α : Type*} [DecidableEq α] (a b x : α) : α :=
if x = a then b else if x = b then a else x

def fn_set {α β : Type*} [DecidableEq α] (a : α) (b : β) (f : α → β) (x : α) : β :=
if x = a then b else f x

def fn_swap {α β : Type*} [DecidableEq α] (a b : α) (f : α → β) (x : α) : β :=
f # fn_swap' a b x

theorem fn_set_eq {α β : Type*} [DecidableEq α] {a : α} {b : β} {f : α → β} {x : α} :
fn_set a b f x = if x = a then b else f x := rfl

theorem fn_swap_eq {α β : Type*} [DecidableEq α] {a b : α} {f : α → β} {x : α} :
fn_swap a b f x = f (if x = a then b else if x = b then a else x) := rfl

@[simp]
theorem fn_swap'_idemp {α : Type*} [DecidableEq α] {a b x : α} :
fn_swap' a b (fn_swap' a b x) = x := by
  unfold fn_swap'; aesop

@[simp]
theorem fn_swap_idemp {α β : Type*} [DecidableEq α] {a b : α} {f : α → β} :
fn_swap a b (fn_swap a b f) = f := by
  ext x; simp [fn_swap_eq]; aesop

def fn_swap'_equiv {α : Type*} [DecidableEq α] (a b : α) : α ≃ α := by
  apply Equiv.mk (fn_swap' a b) (fn_swap' a b) _ _
  all_goals exact λ x => fn_swap'_idemp

@[simp]
theorem fn_swap'_equiv_to_fun {α : Type*} [DecidableEq α] {a b : α} :
(fn_swap'_equiv a b).toFun = fn_swap' a b :=
  by simp [fn_swap'_equiv]

@[simp]
theorem fn_swap'_equiv_inv_fun {α : Type*} [DecidableEq α] {a b : α} :
(fn_swap'_equiv a b).invFun = fn_swap' a b :=
  by simp [fn_swap'_equiv]

@[simp]
theorem fn_swap'_equiv_apply {α : Type*} [DecidableEq α] {a b x : α} :
fn_swap'_equiv a b x = fn_swap' a b x := rfl

@[simp]
theorem fn_set'_eq_of_eq {α : Type*} [DecidableEq α] {a b : α} :
fn_set' a b a = b := by simp [fn_set']

@[simp]
theorem fn_swap'_eq_of_eq_left {α : Type*} [DecidableEq α] {a b : α} :
fn_swap' a b a = b := by simp [fn_swap']

@[simp]
theorem fn_swap'_eq_of_eq_right {α : Type*} [DecidableEq α] {a b : α} :
fn_swap' a b b = a := by simp [fn_swap']

@[simp]
theorem fn_set_eq_of_eq {α β : Type*} [DecidableEq α] {a : α} {b : β} {f : α → β} :
fn_set a b f a = b := by simp [fn_set_eq]

@[simp]
theorem fn_swap_eq_of_eq_left {α β : Type*} [DecidableEq α] {a b : α} {f : α → β} :
fn_swap a b f a = f b := by simp [fn_swap_eq]

@[simp]
theorem fn_swap_eq_of_eq_right {α β : Type*} [DecidableEq α] {a b : α} {f : α → β} :
fn_swap a b f b = f a := by simp [fn_swap_eq]; aesop

theorem fn_set_eq_of_ne {α β : Type*} [DecidableEq α] {a : α} {b : β}
{f : α → β} {x : α} (hx : x ≠ a) : fn_set a b f x = f x := by
  simp [fn_set_eq, hx]

theorem fn_set_fn_set_eq_fn_swap {α β : Type*} [DecidableEq α] {a b} {f : α → β} :
fn_set a (f b) (fn_set b (f a) f) = fn_swap a b f := by
  ext x; simp [fn_set_eq, fn_swap_eq]; aesop

theorem fn_set_same_value {α β : Type*} [DecidableEq α] {f : α → β} {a : α} :
fn_set a (f a) f = f := by
  unfold fn_set; ext x; split_ifs with h
  rw [h]
  rfl

theorem fn_set_twice_same {α β : Type*} [DecidableEq α]
{f : α → β} {a : α} {b₁ b₂ : β} : fn_set a b₂ (fn_set a b₁ f) = fn_set a b₂ f := by
  unfold fn_set; ext x; split_ifs with h <;> rfl

theorem fn_set_comm {α β : Type*} [DecidableEq α] {f : α → β} {a₁ a₂ : α} {b₁ b₂ : β}
(h : a₁ ≠ a₂) : fn_set a₁ b₁ (fn_set a₂ b₂ f) = fn_set a₂ b₂ (fn_set a₁ b₁ f) := by
  unfold fn_set; ext x; split_ifs with h₁ h₂ h₂ <;> try rfl
  rw [h₁] at h₂
  contradiction

theorem fn_set_ext {α β : Type*} [DecidableEq α] {f g : α → β} {a : α} {b : β} :
(∀ x, fn_set a b f x = fn_set a b g x) ↔ (∀ x, x ≠ a → f x = g x) := by
  constructor <;> intro h x
  · intro h₁
    specialize h x
    simp only [fn_set_eq_of_ne h₁] at h
    exact h
  · unfold fn_set; split_ifs with h₁; rfl
    exact h _ h₁

@[simp]
theorem Function.comp_def' {α β γ : Type*} {f : β → γ} {g : α → β} :
f ∘ g = λ x => f (g x) := comp_def _ _

@[simp] theorem leftInverse_id {α : Type*} : (@id α).LeftInverse id := congrFun rfl
@[simp] theorem rightInverse_id {α : Type*} : (@id α).RightInverse id := congrFun rfl

structure BijectiveOn {α β : Type*}
(pa : α → Prop) (pb : β → Prop) (f : α → β) (f' : β → α) : Prop where
  h : ∃ (e : {x // pa x} ≃ {y // pb y}),
    (∀ {x} hx, f x = e ⟨x, hx⟩) ∧ (∀ {y} hy, f' y = e.symm ⟨y, hy⟩)

section bijectiveOn

variable {α β : Type*}
variable {pa : α → Prop} {pb : β → Prop}
variable {f : α → β} {f' : β → α}

@[simp]
theorem bijectiveOn_id : BijectiveOn pa pa id id := by
  refine ⟨⟨⟨id, id, ?_, ?_⟩, ?_⟩⟩ <;> simp

namespace BijectiveOn

variable {H : BijectiveOn pa pb f f'}
include H

theorem cnd_right {x} (h : pa x) : pb (f x) := by
  obtain ⟨⟨e, h₁, h₂⟩⟩ := H; rw [h₁ h]; exact e _ |>.2

theorem cnd_left {y} (h : pb y) : pa (f' y) := by
  obtain ⟨⟨e, h₁, h₂⟩⟩ := H; rw [h₂ h]; exact e.symm _ |>.2

theorem cancel_left {x} (h : pa x) : f' (f x) = x := by
  obtain ⟨⟨e, h₁, h₂⟩⟩ := id H; rw [h₁ h, h₂]
  rotate_left; rw [←h₁]; apply H.cnd_right h; simp

theorem cancel_right {y} (h : pb y) : f (f' y) = y := by
  obtain ⟨⟨e, h₁, h₂⟩⟩ := id H; rw [h₂ h, h₁]
  rotate_left; rw [←h₂]; apply H.cnd_left h; simp

@[symm]
theorem symm : BijectiveOn pb pa f' f := by
  obtain ⟨⟨e, h₁, h₂⟩⟩ := H; use e.symm; simp_all

end BijectiveOn
end bijectiveOn

structure StrictBijectiveOn {α β : Type*}
(pa : α → Prop) (pb : β → Prop) (f : α → β) (f' : β → α) : Prop
extends BijectiveOn pa pb f f' where
  cnd_of_right : ∀ {x}, pb (f x) → pa x
  cnd_of_left : ∀ {y}, pa (f' y) → pb y

section strictBijectiveOn

variable {α β : Type*}
variable {pa : α → Prop} {pb : β → Prop}
variable {f : α → β} {f' : β → α}

@[simp]
theorem strictBijectiveOn_id : StrictBijectiveOn pa pa id id where
  toBijectiveOn := bijectiveOn_id
  cnd_of_right := by simp
  cnd_of_left := by simp

namespace StrictBijectiveOn

variable {H : StrictBijectiveOn pa pb f f'}
include H

@[symm]
theorem symm : StrictBijectiveOn pb pa f' f where
  toBijectiveOn := H.toBijectiveOn.symm
  cnd_of_right := H.cnd_of_left
  cnd_of_left := H.cnd_of_right

end StrictBijectiveOn
end strictBijectiveOn

namespace Equiv

variable {α β γ : Type*}
variable {e : α ≃ β} {e₁ : β ≃ γ} {e₂ : α ≃ β}

def comp (e₁ : β ≃ γ) (e₂ : α ≃ β) : α ≃ γ where
  toFun := e₁ ∘ e₂
  invFun := e₂.symm ∘ e₁.symm
  left_inv := by intros x; simp
  right_inv := by intros x; simp

@[simp]
theorem coe_toFun_comp : (e₁.comp e₂ : _ → _) = e₁ ∘ e₂ := rfl

@[simp]
theorem symm_comp : (e₁.comp e₂).symm = e₂.symm.comp e₁.symm := rfl

end Equiv

structure Inverse {α β : Type*} (f : α → β) (g : β → α) : Prop where
  fg : ∀ {x}, f (g x) = x
  gf : ∀ {x}, g (f x) = x

@[simp]
theorem inverse_id {α : Type*} : Inverse (@id α) id := by
  constructor <;> simp

namespace Inverse

variable {α β : Type*} {f : α → β} {g : β → α}
variable {H : Inverse f g}
include H

@[symm]
theorem symm : Inverse g f := ⟨H.2, H.1⟩

end Inverse

theorem Equiv.forall_iff {α β : Type*} {e : α ≃ β} {p : α → Prop} :
(∀ x, p x) ↔ ∀ y, p (e.symm y) := by
  constructor <;> intro h x; apply h; specialize h # e x; simp at h; exact h

theorem Equiv.forall_iff' {α β : Type*} {e : α ≃ β} {p : β → Prop} :
(∀ x, p x) ↔ ∀ y, p (e y) := e.symm.forall_iff