import AP.Util.Logic

def fn_set' {α : Type*} [DecidableEq α] (a b x : α) : α :=
if x = a then b else x

def fn_swap' {α : Type*} [DecidableEq α] (a b x : α) : α :=
if x = a then b else if x = b then a else x

def fn_set {α β : Type*} [DecidableEq α] (a : α) (b : β) (f : α → β) (x : α) : β :=
if x = a then b else f x

def fn_swap {α β : Type*} [DecidableEq α] (a b : α) (f : α → β) (x : α) : β :=
f # fn_swap' a b x

-----

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