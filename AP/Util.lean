import Init.Coe
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Control.Monad.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
open scoped Classical
open BigOperators

syntax:min term atomic(" #" ws) term:min : term

macro_rules
| `($f $args* # $a) => `($f $args* $a)
| `($f # $a) => `($f $a)

def fn_set' {α : Type} (a b x : α) : α :=
if x = a then b else x

def fn_swap' {α : Type} (a b x : α) : α :=
if x = a then b else if x = b then a else x

def fn_set {α β : Type} (a : α) (b : β) (f : α → β) (x : α) : β :=
if x = a then b else f x

def fn_swap {α β : Type} (a b : α) (f : α → β) (x : α) : β :=
f # fn_swap' a b x

-----

theorem thm_let {α : Type} (x : α) : ∃ y, y = x := by
  apply exists_apply_eq_apply

theorem fn_set_eq {α β : Type} {a : α} {b : β} {f : α → β} {x : α} :
fn_set a b f x = if x = a then b else f x := rfl

theorem fn_swap_eq {α β : Type} {a b : α} {f : α → β} {x : α} :
fn_swap a b f x = f (if x = a then b else if x = b then a else x) := rfl

@[simp]
theorem fn_swap'_idemp {α : Type} {a b x : α} :
fn_swap' a b (fn_swap' a b x) = x := by
  unfold fn_swap'; aesop

@[simp]
theorem fn_swap_idemp {α β : Type} {a b : α} {f : α → β} :
fn_swap a b (fn_swap a b f) = f := by
  ext x; simp [fn_swap_eq]; aesop

def fn_swap'_equiv {α : Type} (a b : α) : α ≃ α := by
  apply Equiv.mk (fn_swap' a b) (fn_swap' a b) <;>
  exact λ x => fn_swap'_idemp

@[simp]
theorem fn_swap'_equiv_to_fun {α : Type} {a b : α} :
(fn_swap'_equiv a b).toFun = fn_swap' a b :=
  by simp [fn_swap'_equiv]

@[simp]
theorem fn_swap'_equiv_inv_fun {α : Type} {a b : α} :
(fn_swap'_equiv a b).invFun = fn_swap' a b :=
  by simp [fn_swap'_equiv]

@[simp]
theorem fn_swap'_equiv_apply {α : Type} {a b x : α} :
  fn_swap'_equiv a b x = fn_swap' a b x := rfl

theorem nat_rec_const (n m : ℕ) : n.rec m (λ _ a => a) = m := by
  induction n with
  | zero => simp
  | succ n => simpa

theorem nat_rec_succ' {α : Type} {z : α} (f : ℕ → α → α) {n : ℕ} :
@Nat.rec (λ _ => α) z f (n + 1) =
@Nat.rec (λ _ => α) (f 0 z) (λ m => f (m + 1)) n := by
  induction n generalizing z f with
  | zero => simp
  | succ n ih => exact congrArg (f (n + 1)) (ih f)

theorem nat_infi_eq_zero_of {f : ℕ → ℕ} k (h : f k = 0) : ⨅ x, f x = 0 := by
  rw [iInf, Nat.sInf_eq_zero]; left; simp; use k

theorem nat_thm_aux₁ {a b c : ℕ} (h : a ≤ b) : a ≤ b - c + c := by
  trans b; exact h; exact le_tsub_add

theorem nat_thm_aux₂ {a b c d : ℕ} (h : a ≤ b) : a ≤ b - c + d + c := by
  rw [Nat.add_assoc]; nth_rewrite 2 [Nat.add_comm]
  rw [←Nat.add_assoc]; trans b - c + c
  exact nat_thm_aux₁ h; apply Nat.le_add_right

theorem nat_rec_le_of_tsub_tsub {n z : ℕ} (f g : ℕ → ℕ) :
@Nat.rec (λ _ => ℕ) z (λ k x => x - f k - g k) n ≤
@Nat.rec (λ _ => ℕ) z (λ k x => x - f k) n := by
  induction n with
  | zero => simp
  | succ n ih => simp; exact nat_thm_aux₂ ih

theorem prop_ind (R : Prop → Prop) (h₁ : R True) (h₂ : R False) P : R P := by
  by_cases P
  · have h : P = True := by apply eq_true; assumption
    rwa [h]
  · have h : P = False := by apply eq_false; assumption
    rwa [h]

@[simp]
theorem ite_11_iff : ∀ {P Q h₁ h₂},
@ite _ P h₁ 1 0 = @ite _ Q h₂ 1 0 ↔ (P ↔ Q) := by
  apply prop_ind <;> apply prop_ind <;> simp

@[simp]
theorem ite_00_iff : ∀ {P Q h₁ h₂},
@ite _ P h₁ 0 1 = @ite _ Q h₂ 0 1 ↔ (P ↔ Q) := by
  apply prop_ind <;> apply prop_ind <;> simp

@[simp]
theorem ite_10_iff : ∀ {P Q h₁ h₂},
@ite _ P h₁ 1 0 = @ite _ Q h₂ 0 1 ↔ (P ↔ ¬Q) := by
  apply prop_ind <;> apply prop_ind <;> simp

@[simp]
theorem ite_01_iff : ∀ {P Q h₁ h₂},
@ite _ P h₁ 0 1 = @ite _ Q h₂ 1 0 ↔ (P ↔ ¬Q) := by
  apply prop_ind <;> apply prop_ind <;> simp

@[simp]
theorem ite_eq {a b : ℕ} : ite (a = b) a b = b := by
  split_ifs with h; exact h; rfl

theorem nat_rec_tsub {n k m : ℕ} {f : ℕ → ℕ} :
@Nat.rec (λ _ => ℕ) (n - k) (λ k a => a - f k) m =
@Nat.rec (λ _ => ℕ) n (λ k a => a - f k) m - k := by
  induction m with
  | zero => simp
  | succ m ih => simp; rw [ih]; apply Nat.sub_right_comm

@[simp]
theorem add_succ_max_ne_left {x a b : ℕ} :
x + (max a b + 1) ≠ a := by
  simp; apply ne_of_gt; apply Nat.lt_add_left
  apply Nat.lt_add_one_of_le; apply Nat.le_max_left

@[simp]
theorem add_succ_max_ne_right {x a b : ℕ} : x + (max a b + 1) ≠ b := by
  rw [max_comm]; simp

@[simp]
theorem nat_left_lt_succ_max {a b : ℕ} : a < max a b + 1 := by
  simp [Nat.lt_add_one_iff]

@[simp]
theorem nat_right_lt_succ_max {a b : ℕ} : b < max a b + 1 := by
  simp [Nat.lt_add_one_iff]

@[simp]
theorem fn_set'_eq_of_eq {α : Type} {a b : α} :
fn_set' a b a = b := by simp [fn_set']

@[simp]
theorem fn_swap'_eq_of_eq_left {α : Type} {a b : α} :
fn_swap' a b a = b := by simp [fn_swap']

@[simp]
theorem fn_swap'_eq_of_eq_right {α : Type} {a b : α} :
fn_swap' a b b = a := by simp [fn_swap']

@[simp]
theorem fn_set_eq_of_eq {α β : Type} {a : α} {b : β} {f : α → β} :
fn_set a b f a = b := by simp [fn_set_eq]

@[simp]
theorem fn_swap_eq_of_eq_left {α β : Type} {a b : α} {f : α → β} :
fn_swap a b f a = f b := by simp [fn_swap_eq]

@[simp]
theorem fn_swap_eq_of_eq_right {α β : Type} {a b : α} {f : α → β} :
fn_swap a b f b = f a := by simp [fn_swap_eq]; aesop

theorem nat_thm_aux₃ {a b c : ℕ} : a + b + c - b = a + c := by
  rw [Nat.add_assoc, Nat.add_sub_assoc] <;> simp

theorem sum_eq_sum_of_fn_cong {S : Finset ℕ} {f g : ℕ → ℕ}
(h : ∀ i ∈ S, f i = g i) : ∑ x ∈ S, f x = ∑ x ∈ S, g x := by
  apply Finset.sum_equiv (e := Equiv.refl ℕ); simp; simpa

@[simp]
theorem sum_fn_set_eq {S : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ} (ha : a ∈ S) :
∑ x ∈ S, fn_set a b f x =
∑ x ∈ S, f x + b - f a := by
  have h₁ : ∑ x ∈ S.erase a, f x + f a = ∑ x ∈ S, f x := by
    apply Finset.sum_erase_add; exact ha
  have h₂ : ∑ x ∈ S.erase a, fn_set a b f x + b =
  ∑ x ∈ S, fn_set a b f x := by
    convert Finset.sum_erase_add _ _ ha; simp
  rw [←h₁, ←h₂, nat_thm_aux₃]; clear h₁ h₂
  congr 1; apply sum_eq_sum_of_fn_cong
  intro i hi; simp at hi; simp [fn_set_eq, hi]

@[simp]
theorem sum_fn_swap_eq {S : Finset ℕ} {f : ℕ → ℕ} {a b : ℕ}
(ha : a ∈ S) (hb : b ∈ S) :
∑ x ∈ S, fn_swap a b f x =
∑ x ∈ S, f x := by
  apply Finset.sum_equiv (e := fn_swap'_equiv a b) <;>
    intros <;> simp [fn_swap'] <;> aesop

theorem nat_thm_aux₄ {a b : ℕ} : a + (b + 1) ≠ b := by
  nth_rewrite 2 [add_comm]; rw [←add_assoc]; simp

theorem fn_set_eq_of_ne {α β : Type} {a : α} {b : β}
{f : α → β} {x : α} (hx : x ≠ a) : fn_set a b f x = f x := by
  simp [fn_set_eq, hx]

theorem nat_fn_set_add {a b : ℕ} {f : ℕ → ℕ} {x : ℕ} :
fn_set a (f a + b) f x = f x + if x = a then b else 0 := by
  rw [fn_set_eq]; aesop

theorem fn_set_fn_set_eq_fn_swap {α β : Type} {a b} {f : α → β} :
fn_set a (f b) (fn_set b (f a) f) = fn_swap a b f := by
  ext x; simp [fn_set_eq, fn_swap_eq]; aesop

theorem nat_eq_add_of_sub_eq_succ {a b c} (h : a - b = c + 1) :
a = c + 1 + b := by
  rw [Nat.sub_eq_iff_eq_add] at h; exact h; by_contra! h₁
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h₁
  rw [add_assoc, Nat.sub_add_eq] at h; simp at h

theorem nat_eq_add_iff_sub_eq_succ {a b c} :
a = c + 1 + b ↔ a - b = c + 1 := by
  apply Iff.intro <;> intro h; simp [h]
  exact nat_eq_add_of_sub_eq_succ h

@[simp]
theorem univ_unit_iff {p : Unit → Prop} : (∀ u, p u) ↔ p () :=
  Unique.forall_iff

@[simp]
theorem exi_unit_iff {p : Unit → Prop} : (∃ u, p u) ↔ p () :=
  Unique.exists_iff

@[simp]
theorem exi_prop_pos_and {p : Prop → Prop} : (∃ P, P ∧ p P) ↔ p True :=
  by aesop

theorem nat_eq_add_of_one_eq_sub {a b : ℕ} (h : 1 = a - b) : a = b + 1 := by
  have h₁ : b ≤ a := by
    apply le_of_lt; apply Nat.lt_of_sub_pos; simp [←h]
  have h₂ : b + 1 = b + (a - b) := by rw [h]
  rw [←Nat.add_sub_assoc h₁] at h₂
  simp at h₂; exact h₂.symm

theorem nat_one_eq_sub_iff {a b : ℕ} : 1 = a - b ↔ a = b + 1 := by
  apply Iff.intro
  · exact nat_eq_add_of_one_eq_sub
  · rintro rfl; simp

theorem nat_thm_aux₅ {a b : ℕ} : ¬(a < a - b) := by simp

theorem nat_thm_aux₆ {a b : ℕ} : a - b = a ↔ a = 0 ∨ b = 0 := by
  cases a with
  | zero => simp
  | succ a =>
    simp; cases b with
    | zero => simp
    | succ b =>
      simp; apply ne_of_lt
      apply Nat.sub_lt_of_lt; simp

@[simp]
theorem ite_10_le_one {P : Prop} : ite P 1 0 ≤ 1 := by split_ifs <;> simp

@[simp]
theorem ite_01_le_one {P : Prop} : ite P 0 1 ≤ 1 := by split_ifs <;> simp

theorem hv {α : Type} (x : α) : ∃ y, y = x := exists_eq

theorem univ_spec {α β γ : Type} {p : α → Prop} (f : β → γ → α)
(h : ∀ x, p x) : ∀ y z, p (f y z) := by intro y z; apply h

class ListMem {α : Type} [DecidableEq α] (x : α) (xs : List α) where
  i : ℕ

@[simp]
instance {α : Type} [DecidableEq α] {x : α} {xs} :
ListMem x (x :: xs) := ⟨0⟩

@[simp]
instance {α : Type} [DecidableEq α] {x y : α} {xs}
[h : ListMem x xs] : ListMem x (y :: xs) := ⟨h.i + 1⟩

inductive Bit where
| Bit0 : Bit
| Bit1 : Bit

open Bit

@[simp] instance : OfNat Bit 0 := ⟨Bit0⟩
@[simp] instance : OfNat Bit 1 := ⟨Bit1⟩

@[simp] theorem Bit0_eq : Bit0 = 0 := rfl
@[simp] theorem Bit1_eq : Bit1 = 1 := rfl

theorem bit_ind (R : Bit → Prop) (B0 : R 0) (B1 : R 1) b : R b := by
  cases b <;> assumption

instance : {a b : Bit} → Decidable (a = b)
| 0, 0 => Decidable.isTrue (by rfl)
| 0, 1 => Decidable.isFalse (by simp)
| 1, 0 => Decidable.isFalse (by simp)
| 1, 1 => Decidable.isTrue (by rfl)

instance : DecidableEq Bit := by
  intro a b; exact instDecidableEqBit

@[simp]
def Bit.not : Bit → Bit
| 0 => 1
| 1 => 0

@[simp]
def Bit.imp : Bit → Bit → Bit
| 0, _ => 1
| 1, a => a

@[simp]
def Bit.or : Bit → Bit → Bit
| 0, a => a
| 1, _ => 1

@[simp]
def Bit.and : Bit → Bit → Bit
| 0, _ => 0
| 1, a => a

@[simp]
def Bit.iff : Bit → Bit → Bit
| 0, a => a.not
| 1, a => a

@[simp]
def Bit.xor : Bit → Bit → Bit
| 0, a => a
| 1, a => a.not

def Set.erase {α : Type} (x : α) (s : Set α) := s \ {x}

@[simp]
theorem Set.mem_erase {α : Type} {z x : α} (s : Set α) :
z ∈ s.erase x ↔ z ≠ x ∧ z ∈ s := by
  unfold Set.erase; aesop

theorem Set.erase_eq_of_not_mem {α : Type} {x : α} {s : Set α}
(h : x ∉ s) : s.erase x = s := by simpa [Set.erase]

theorem Set.insert_erase_eq_of_mem {α : Type} {x : α} {s : Set α}
(h : x ∈ s) : insert x (s.erase x) = s := by
  ext z; simp; apply Iff.intro <;> intro h₁
  rcases h₁ with rfl | ⟨h₁, h₂⟩ <;> assumption
  simp [h₁]; apply eq_or_ne

theorem ne_none_of_eq_some {α : Type} {m : Option α} {x : α}
(h : m = some x) : m ≠ none := by simp [h]

def List.snoc {α : Type} (xs : List α) (x : α) := xs ++ [x]

@[simp]
theorem Set.finite_erase_iff {α : Type} {x : α} {s : Set α} :
(s.erase x).Finite ↔ s.Finite := by
  by_cases hx : x ∈ s
  case neg => simp [Set.erase_eq_of_not_mem hx]
  symm; apply Iff.intro Finite.diff; intro h
  generalize hs' : s.erase x = s' at h
  have hs : s = insert x s' := by
    subst hs'; rw [Set.insert_erase_eq_of_mem hx]
  rw [←Set.erase, hs'] at h; rw [hs]
  apply Finite.insert; exact h

@[simp]
theorem Set.infinite_erase_iff {α : Type} {x : α} {s : Set α} :
(s.erase x).Infinite ↔ s.Infinite := by simp [Set.Infinite]