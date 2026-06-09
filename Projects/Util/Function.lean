import Projects.Util.Logic

variable {α β γ : Type*}

structure Inverse (f : α → β) (g : β → α) : Prop where
  fg : ∀ {x}, f (g x) = x
  gf : ∀ {x}, g (f x) = x

structure BijectiveOn
(pa : α → Prop) (pb : β → Prop) (f : α → β) (f' : β → α) : Prop where
  h : ∃ (e : {x // pa x} ≃ {y // pb y}),
    (∀ {x} hx, f x = e ⟨x, hx⟩) ∧ (∀ {y} hy, f' y = e.symm ⟨y, hy⟩)

structure StrictBijectiveOn
(pa : α → Prop) (pb : β → Prop) (f : α → β) (f' : β → α) : Prop
extends BijectiveOn pa pb f f' where
  cnd_of_right : ∀ {x}, pb (f x) → pa x
  cnd_of_left : ∀ {y}, pa (f' y) → pb y

def fn_set' [DecidableEq α] (a b x : α) : α :=
if x = a then b else x

def fn_swap' [DecidableEq α] (a b x : α) : α :=
if x = a then b else if x = b then a else x

def fn_set [DecidableEq α] (a : α) (b : β) (f : α → β) (x : α) : β :=
if x = a then b else f x

def fn_swap [DecidableEq α] (a b : α) (f : α → β) (x : α) : β :=
f # fn_swap' a b x

namespace Function

def fixNCnd (f : α → α) (x : α) (k : ℕ) : Prop :=
  f.IsFixedPt # f^[k] x

open Classical in noncomputable
def fixN (f : α → α) (x : α) : ℕ :=
  τ y, f.fixNCnd x y

open Classical in noncomputable
def fix (f : α → α) (x : α) : α :=
  f^[f.fixN x] x

def fixCnd (f : α → α) (x : α) (k : ℕ) : Prop :=
  f.fix x = f^[k] x ∧ f (f.fix x) = f.fix x

end Function

-- #check 0 #exit

-----

theorem fn_set_eq [DecidableEq α] {a : α} {b : β} {f : α → β} {x : α} :
fn_set a b f x = if x = a then b else f x := rfl

theorem fn_swap_eq [DecidableEq α] {a b : α} {f : α → β} {x : α} :
fn_swap a b f x = f (if x = a then b else if x = b then a else x) := rfl

@[simp]
theorem fn_swap'_idemp [DecidableEq α] {a b x : α} :
fn_swap' a b (fn_swap' a b x) = x := by
  unfold fn_swap'; aesop

@[simp]
theorem fn_swap_idemp [DecidableEq α] {a b : α} {f : α → β} :
fn_swap a b (fn_swap a b f) = f := by
  ext x; simp [fn_swap_eq]; aesop

def fn_swap'_equiv [DecidableEq α] (a b : α) : α ≃ α := by
  apply Equiv.mk (fn_swap' a b) (fn_swap' a b) _ _
  all_goals exact λ x => fn_swap'_idemp

@[simp]
theorem fn_swap'_equiv_to_fun [DecidableEq α] {a b : α} :
(fn_swap'_equiv a b).toFun = fn_swap' a b :=
  by simp [fn_swap'_equiv]

@[simp]
theorem fn_swap'_equiv_inv_fun [DecidableEq α] {a b : α} :
(fn_swap'_equiv a b).invFun = fn_swap' a b :=
  by simp [fn_swap'_equiv]

@[simp]
theorem fn_swap'_equiv_apply [DecidableEq α] {a b x : α} :
fn_swap'_equiv a b x = fn_swap' a b x := rfl

@[simp]
theorem fn_set'_eq_of_eq [DecidableEq α] {a b : α} :
fn_set' a b a = b := by simp [fn_set']

@[simp]
theorem fn_swap'_eq_of_eq_left [DecidableEq α] {a b : α} :
fn_swap' a b a = b := by simp [fn_swap']

@[simp]
theorem fn_swap'_eq_of_eq_right [DecidableEq α] {a b : α} :
fn_swap' a b b = a := by simp [fn_swap']

@[simp]
theorem fn_set_eq_of_eq [DecidableEq α] {a : α} {b : β} {f : α → β} :
fn_set a b f a = b := by simp [fn_set_eq]

@[simp]
theorem fn_swap_eq_of_eq_left [DecidableEq α] {a b : α} {f : α → β} :
fn_swap a b f a = f b := by simp [fn_swap_eq]

@[simp]
theorem fn_swap_eq_of_eq_right [DecidableEq α] {a b : α} {f : α → β} :
fn_swap a b f b = f a := by simp [fn_swap_eq]; aesop

theorem fn_set_eq_of_ne [DecidableEq α] {a : α} {b : β}
{f : α → β} {x : α} (hx : x ≠ a) : fn_set a b f x = f x := by
  simp [fn_set_eq, hx]

theorem fn_set_fn_set_eq_fn_swap [DecidableEq α] {a b} {f : α → β} :
fn_set a (f b) (fn_set b (f a) f) = fn_swap a b f := by
  ext x; simp [fn_set_eq, fn_swap_eq]; aesop

theorem fn_set_same_value [DecidableEq α] {f : α → β} {a : α} :
fn_set a (f a) f = f := by
  unfold fn_set; ext x; split_ifs with h
  rw [h]
  rfl

theorem fn_set_twice_same [DecidableEq α]
{f : α → β} {a : α} {b₁ b₂ : β} : fn_set a b₂ (fn_set a b₁ f) = fn_set a b₂ f := by
  unfold fn_set; ext x; split_ifs with h <;> rfl

theorem fn_set_comm [DecidableEq α] {f : α → β} {a₁ a₂ : α} {b₁ b₂ : β}
(h : a₁ ≠ a₂) : fn_set a₁ b₁ (fn_set a₂ b₂ f) = fn_set a₂ b₂ (fn_set a₁ b₁ f) := by
  unfold fn_set; ext x; split_ifs with h₁ h₂ h₂ <;> try rfl
  rw [h₁] at h₂
  contradiction

theorem fn_set_ext [DecidableEq α] {f g : α → β} {a : α} {b : β} :
(∀ x, fn_set a b f x = fn_set a b g x) ↔ (∀ x, x ≠ a → f x = g x) := by
  constructor <;> intro h x
  · intro h₁
    specialize h x
    simp only [fn_set_eq_of_ne h₁] at h
    exact h
  · unfold fn_set; split_ifs with h₁; rfl
    exact h _ h₁

attribute [simp] Function.comp_def

@[simp]
theorem inverse_id : Inverse (@id α) id := by
  constructor <;> simp

@[simp] theorem leftInverse_id : (@id α).LeftInverse id := congrFun rfl
@[simp] theorem rightInverse_id : (@id α).RightInverse id := congrFun rfl

section bijectiveOn

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

section strictBijectiveOn

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

namespace Inverse

variable {f : α → β} {g : β → α}
variable {H : Inverse f g}
include H

@[symm]
theorem symm : Inverse g f := ⟨H.2, H.1⟩

end Inverse

theorem Equiv.forall_iff {e : α ≃ β} {p : α → Prop} :
(∀ x, p x) ↔ ∀ y, p (e.symm y) := by
  constructor <;> intro h x; apply h; specialize h # e x; simp at h; exact h

theorem Equiv.forall_iff' {e : α ≃ β} {p : β → Prop} :
(∀ x, p x) ↔ ∀ y, p (e y) := e.symm.forall_iff

@[simp]
theorem Equiv.mk_symm {f : α → β} {g : β → α} {h₁ h₂} :
(⟨f, g, h₁, h₂⟩ : α ≃ β).symm = ⟨g, f, h₂, h₁⟩ := rfl

def FinFn.{u, v} {n : ℕ} (α : Fin n → Type u) (β : Type v) : Type (max u v + 1) :=
  match n with
  | 0 => ULift.{max u v + 1} β
  | n + 1 => α 0 → FinFn (λ (k : Fin n) => α ⟨k + 1, by omega⟩) β

def mkFinFn.{u, v} {n : ℕ} {α : Fin n → Type u} {β : Type v}
(f : (∀ n, α n) → β) : FinFn α β := by
  induction n
  · exact .up # f nofun
  nm n ih
  intro x
  specialize @ih _ _
  · rintro ⟨k, hk⟩
    exact α ⟨k + 1, by omega⟩
  · intro ps
    apply f
    rintro ⟨k, hk⟩
    cases k
    · exact x
    nm k
    specialize ps ⟨k, by omega⟩
    convert ps
  exact ih

def callFinFn.{u, v} {n : ℕ} {α : Fin n → Type u} {β : Type v}
(f : FinFn α β) (ps : ∀ n, α n) : β :=
  match n with
  | 0 => f.down
  | n + 1 => callFinFn (f (ps 0)) (λ (k : Fin n) => ps ⟨k + 1, by omega⟩)

namespace Function

theorem iterate_add' {f : α → α} {n m : ℕ} : f^[n + m] = f^[m] ∘ f^[n] := by
  rw [add_comm, iterate_add]

theorem fixCnd_spec {f : α → α} {x : α} (k : ℕ)
(h : f.IsFixedPt # f^[k] x) : f.fixNCnd x (f.fixN x) := by
  unfold fixNCnd fixN; apply τ_spec (p := f.fixNCnd x)
  unfold fixNCnd; use k

theorem fix_spec {f : α → α} {x : α} (k : ℕ)
(h : f.IsFixedPt # f^[k] x) : f.fixCnd x k := by
  unfold fixCnd fix fixN fixNCnd
  generalize hp : (λ k => f.IsFixedPt # f^[k] x) = p
  generalize hm : (τ x, p x) = m
  have h₁ := τ_spec (p := p) (by subst hp; use k)
  nth_rw 1 [←hp] at h₁
  simp [hm] at h₁
  have h₂ : ∀ ⦃r⦄, f^[k + r] x = f^[k] x
  · intro r; simp [Function.iterate_add']; rwa [Function.iterate_fixed]
  have h₃ : ∀ ⦃r⦄, f^[m + r] x = f^[m] x
  · intro r; simp [Function.iterate_add']; rwa [Function.iterate_fixed]
  symm; use h₁; obtain h₂ | h₂ := le_total k m
  all_goals obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le h₂; grind

theorem fix_spec' {f : α → α} {x : α} (k : ℕ)
(h : f.IsFixedPt # f^[k] x) : f.fixCnd x (f.fixN x) :=
  fix_spec _ # fixCnd_spec k h

theorem fixCnd_fixN_of_fixCnd {f : α → α} {x : α} {k : ℕ}
(h : f.fixCnd x k) : f.fixCnd x (f.fixN x) := by
  rcases h with ⟨h₁, h₂⟩; rw [h₁] at h₂; exact fix_spec' _ h₂

theorem fixCnd_apply {f : α → α} {x : α} {k : ℕ} (h : f.fixCnd x k) : f.fixCnd (f x) k := by
  rcases h with ⟨h₁, h₂⟩
  rw [h₁] at h₂
  apply fix_spec
  change _ = _
  replace h₂ : f^[k + 1] x = f^[k] x
  · rwa [iterate_succ']
  change f (f^[k + 1] x) = f^[k + 1] x
  nth_rw 1 [h₂]; rw [iterate_succ']; rfl

theorem fix_apply {f : α → α} {x : α} {k : ℕ} (h : f.fixCnd x k) : f.fix (f x) = f.fix x := by
  choose h₃ h₄ using fixCnd_apply h
  choose h₁ h₂ using h
  rw [h₁] at h₂
  rw [h₃] at h₄
  rw [h₁, h₃]
  clear h₁ h₃ h₄
  replace h₂ : f^[k + 1] x = f^[k] x
  · rwa [iterate_succ']
  exact h₂