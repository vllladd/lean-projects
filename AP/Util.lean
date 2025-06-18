import Init.Coe
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Finset.Basic
-- import Mathlib.Data.Ordmap.Ordset
import Mathlib.Control.Monad.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section
open scoped Classical
open BigOperators

syntax:min term atomic(" #" ws) term:min : term

macro_rules
| `($f $args* # $a) => `($f $args* $a)
| `($f # $a) => `($f $a)

macro "nm " args:(ppSpace colGt Lean.binderIdent)+ : tactic =>
  `(tactic| rename_i $args*)

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
theorem forall_unit_iff {p : Unit → Prop} : (∀ u, p u) ↔ p () :=
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

theorem forall_spec {α β γ : Type} {p : α → Prop} (f : β → γ → α)
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

theorem Set.diff_upair {α : Type} (x y : α) (s : Set α) :
s \ {x, y} = (s \ {x}) \ {y} := by ext z; simp; tauto

@[simp]
theorem Set.univ_ne_univ_diff_insert {α : Type} {x : α} {s : Set α} :
Set.univ ≠ Set.univ \ (insert x s) := by
  simp [Set.ext_iff]; use x; simp

@[simp]
theorem Set.univ_ne_univ_diff_singleton {α : Type} {x : α} :
Set.univ ≠ Set.univ \ {x} := by simp [Set.ext_iff]

@[simp]
theorem Set.univ_ne_erase {α : Type} {x : α} :
Set.univ ≠ Set.univ.erase x := by simp [Set.erase]

theorem prop_bcs (P : Prop) {R : Prop} (h₁ : P → R)
(h₂ : (P → R) → ¬P → R) : R := by tauto

theorem eq_true_of {P : Prop} (h : P) : P = True := by simpa

theorem Set.diff_erase_self_eq_of_mem {α : Type} {x : α} {s : Set α}
(h : x ∈ s) : s \ s.erase x = {x} := by simpa [Set.erase]

theorem Set.eq_empty_iff {α : Type} {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  eq_empty_iff_forall_notMem

@[simp]
theorem Set.subsingleton_upair_iff {α : Type} {x y : α} :
({x, y} : Set _).Subsingleton ↔ x = y := by
  simp [Set.Subsingleton]; simp [eq_comm]

theorem ne_of_congr {α β : Type} {x y : α} (f : α → β)
(h : f x ≠ f y) : x ≠ y := by contrapose! h; rw [h]

theorem skolemize {α β : Type} [Nonempty β] {p : α → Prop} {q : α → β → Prop} :
(∀ x, p x → ∃ y, q x y) ↔ ∃ (f : α → β), ∀ x, p x → q x (f x) := by
  constructor
  · intro h; use λ x => Classical.epsilon λ y => p x → q x y
    intro x hx; specialize h x hx;
    convert Classical.epsilon_spec h; simp [hx]
  rintro ⟨f, h⟩ x hx; specialize h x hx; use f x

theorem and_intro (P : Prop) {Q : Prop} : P ∧ Q → Q := And.right

theorem nat_even_iff_exi {n : ℕ} : Even n ↔ ∃ k, n = k * 2 := by
  rw [Even]; ring_nf

theorem nat_odd_iff_exi {n : ℕ} : Odd n ↔ ∃ k, n = k * 2 + 1 := by
  rw [Odd]; ring_nf

theorem int_even_iff_exi {n : ℤ} : Even n ↔ ∃ k, n = k * 2 := by
  rw [Even]; ring_nf

theorem int_odd_iff_exi {n : ℤ} : Odd n ↔ ∃ k, n = k * 2 + 1 := by
  rw [Odd]; ring_nf

theorem nat_mod_2_ind {P : ℕ → Prop}
(h₁ : ∀ n, P (n * 2)) (h₂ : ∀ n, P (n * 2 + 1)) (n : ℕ) : P n := by
  rcases Nat.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := nat_even_iff_exi.mp h; apply h₁
  · obtain ⟨k, rfl⟩ := nat_odd_iff_exi.mp h; apply h₂

theorem int_mod_2_ind {P : ℤ → Prop}
(h₁ : ∀ n, P (n * 2)) (h₂ : ∀ n, P (n * 2 + 1)) (n : ℤ) : P n := by
  rcases Int.even_or_odd n with h | h
  · obtain ⟨k, rfl⟩ := int_even_iff_exi.mp h; apply h₁
  · obtain ⟨k, rfl⟩ := int_odd_iff_exi.mp h; apply h₂

theorem nat_not_even_mul_2_succ {n : ℕ} : ¬Even (n * 2 + 1) := by simp

@[simp]
theorem nat_not_odd_mul_2 {n : ℕ} : ¬Odd (n * 2) := by simp

theorem int_not_even_mul_2_succ {n : ℤ} : ¬Even (n * 2 + 1) := by simp

@[simp]
theorem int_not_odd_mul_2 {n : ℤ} : ¬Odd (n * 2) := by simp

@[simp]
theorem nat_even_succ_iff {n : ℕ} : Even (n + 1) ↔ Odd n := by
  simp [Nat.even_add_one]

@[simp]
theorem nat_odd_succ_iff {n : ℕ} : Odd (n + 1) ↔ Even n := by
  simp [Nat.odd_add_one]

theorem nat_even_of_succ_div_2_eq {n : ℕ}
(h : (n + 1) / 2 = n / 2) : Even n := by
  contrapose! h; simp [nat_odd_iff_exi] at h
  obtain ⟨n, rfl⟩ := h; rw [Nat.div_eq]
  simp; induction n; simp; nm n ih; contrapose! ih; ring_nf at ih ⊢
  have h₁ : (n * 2 + 1 + 2) / 2 = (n * 2 + 1) / 2 + 1 := by simp
  ring_nf at h₁; rw [h₁, add_comm] at ih; nth_rewrite 2 [add_comm] at ih
  rw [add_comm]; exact Nat.succ_inj.mp ih

theorem nat_odd_of_succ_div_2_eq {n : ℕ}
(h : (n + 1) / 2 = n / 2 + 1) : Odd n := by
  contrapose! h; simp [nat_even_iff_exi] at h;
  obtain ⟨n, rfl⟩ := h; rw [Nat.div_eq]; induction n; trivial
  nm n ih; cases n; trivial; nm n; simp [add_mul] at ih ⊢
  change (_ + (1 + 2)) / _ ≠ _; rw [←add_assoc]; simpa

theorem nat_le_one_iff {n : ℕ} : n ≤ 1 ↔ n = 0 ∨ n = 1 := by
  cases n; simp; nm n; cases n <;> simp

theorem iff_of_and {P Q : Prop} (hp : P) (hq : Q) : P ↔ Q := by
  simp [hp, hq]

theorem iff_of_not_and {P Q : Prop} (hp : ¬P) (hq : ¬Q) : P ↔ Q := by
  simp [hp, hq]

theorem int_le_one_iff {n : ℤ} (h : 0 ≤ n) : n ≤ 1 ↔ n = 0 ∨ n = 1 := by
  cases n; nm n; cases n; simp; nm n; cases n; simp; nm n; simp
  have h₁ := Int.ofNat_zero_le n; apply iff_of_not_and
  simp; simp; constructor <;> linarith; simp at h

theorem nat_of_between_succ {a b : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ a + 1) :
b = a ∨ b = a + 1 := by
  obtain ⟨k, rfl⟩ := exists_add_of_le h₁
  simp at h₂ ⊢; rw [nat_le_one_iff] at h₂; exact h₂

theorem int_of_between_succ {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a + 1) :
b = a ∨ b = a + 1 := by
  obtain ⟨k, rfl⟩ := exists_add_of_le h₁; simp at h₂ ⊢
  cases k; nm k; generalize hk : Int.ofNat k = k at *
  rw [int_le_one_iff] at h₂; exact h₂; simp [←hk]; simp at h₁

theorem nat_succ_div_2_eq_or_eq (n : ℕ) :
(n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1 := by
  have h₁ := Nat.add_div_le_add_div n 1 2
  have h₂ := Nat.add_div_le_add_div (n + 1) 1 2
  simp [add_assoc] at h₁ h₂; exact nat_of_between_succ h₁ h₂

@[simp]
theorem nat_succ_div_2_eq_div_iff {n : ℕ} :
(n + 1) / 2 = n / 2 ↔ Even n := by
  refine' ⟨nat_even_of_succ_div_2_eq, _⟩
  intro h; contrapose h; simp
  apply nat_odd_of_succ_div_2_eq
  rcases nat_succ_div_2_eq_or_eq n with h₃ | h₃
  contradiction; exact h₃

@[simp]
theorem nat_succ_div_2_eq_div_iff' {n : ℕ} :
n / 2 = (n + 1) / 2 ↔ Even n := by
  rw [eq_comm]; exact nat_succ_div_2_eq_div_iff

@[simp]
theorem nat_succ_div_2_eq_div_succ_iff {n : ℕ} :
(n + 1) / 2 = n / 2 + 1 ↔ Odd n := by
  cases n; simp; nm n; simp [add_assoc]

@[simp]
theorem nat_succ_div_2_eq_div_succ_iff' {n : ℕ} :
n / 2 + 1 = (n + 1) / 2 ↔ Odd n := by
  rw [eq_comm]; exact nat_succ_div_2_eq_div_succ_iff

theorem int_add_div_eq {a b : ℤ} (h : 0 < b) : (a + b) / b = a / b + 1 := by
  rw [Int.add_ediv_of_pos h]; have h₁ : b ≠ 0 := (Int.ne_of_lt h).symm
  simp [Int.ediv_self h₁]; exact Int.emod_lt_of_pos _ h

@[simp]
theorem int_negSucc_succ {n : ℕ} :
Int.negSucc (n + 1) = Int.negSucc n - 1 := by rfl

@[simp]
theorem int_even_succ_iff {n : ℤ} : Even (n + 1) ↔ Odd n := by
  simp [Int.even_add_one]

@[simp]
theorem int_odd_succ_iff {n : ℤ} : Odd (n + 1) ↔ Even n := by
  rw [←Int.not_even_iff_odd, int_even_succ_iff]; simp

theorem int_succ_div_2_eq_div_iff {n : ℤ} (hp : 0 ≤ n) :
(n + 1) / 2 = n / 2 ↔ Even n := by
  induction n using int_mod_2_ind <;> nm n
  · simp at hp ⊢; cases n; nm n; simp; induction n; rfl
    nm n ih; specialize ih (by simp); simp [add_mul]
    rw [add_assoc]; nth_rewrite 2 [add_comm]; rw [←add_assoc]
    have h₁ := @int_add_div_eq ((n : ℤ) * 2 + 1) 2 # Int.zero_le_ofNat _
    rw [h₁, ih]; simp at hp
  simp; rw [add_assoc]; simp
  rw [@int_add_div_eq ((n : ℤ) * 2) 2 # Int.zero_le_ofNat _]
  rw [eq_comm]; simp; cases n <;> nm n
  simp at hp ⊢; induction n; simp; nm n ih
  specialize ih (by linarith); simp; rw [add_mul, add_assoc]
  nth_rewrite 2 [add_comm]; rw [←add_assoc]; simp
  rw [@int_add_div_eq ((n : ℤ) * 2 + 1) 2 # Int.zero_le_ofNat _]
  simpa; have h₁ := Int.negSucc_lt_zero n; linarith

theorem int_succ_div_2_eq_div_succ_iff {n : ℤ} (hp : 0 ≤ n) :
(n + 1) / 2 = n / 2 + 1 ↔ Odd n := by
  by_cases hn : n = 0; simp [hn]; obtain ⟨k, hk⟩ := hv # n - 1
  replace hk := congrArg (· + 1) hk; simp at hk; subst hk
  replace hp : 0 ≤ k := by
    cases k <;> nm k; simp only [Int.ofNat_eq_coe, Nat.cast_nonneg,
      implies_true, imp_self]
    cases k; simp only [Int.reduceNegSucc, neg_add_cancel,
      implies_true, imp_self, not_true_eq_false] at hn
    nm k; rw [int_negSucc_succ] at hp
    have := Int.negSucc_lt_zero k; linarith
  rw [add_assoc]; simp
  rw [@int_add_div_eq k 2 # Int.zero_le_ofNat _]
  rw [eq_comm]; simp; exact int_succ_div_2_eq_div_iff hp

theorem int_succ_div_2_eq_or_eq {n : ℤ} (hp : 0 ≤ n) :
(n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1 := by
  rcases Int.even_or_odd n with h | h
  · rw [←int_succ_div_2_eq_div_iff hp] at h; left; exact h
  · rw [←int_succ_div_2_eq_div_succ_iff hp] at h; right; exact h

theorem int_succ_div_2_eq_div_iff' {n : ℤ} (hp : 0 ≤ n) :
n / 2 = (n + 1) / 2 ↔ Even n := by
  rw [eq_comm]; exact int_succ_div_2_eq_div_iff hp

@[simp]
theorem int_succ_div_2_eq_div_succ_iff' {n : ℤ} (hp : 0 ≤ n) :
n / 2 + 1 = (n + 1) / 2 ↔ Odd n := by
  rw [eq_comm]; exact int_succ_div_2_eq_div_succ_iff hp

@[simp]
theorem nat_mul_2_succ_div_2_eq (n : ℕ) : (n * 2 + 1) / 2 = n := by
  suffices (n * 2 + 1) / 2 = n * 2 / 2 by simp at this; assumption
  rw [nat_succ_div_2_eq_div_iff]; simp

theorem int_mul_2_succ_div_2_eq {n : ℤ}
(hp : 0 ≤ n) : (n * 2 + 1) / 2 = n := by
  suffices (n * 2 + 1) / 2 = n * 2 / 2 by simp at this; assumption
  rw [int_succ_div_2_eq_div_iff # by linarith]; simp

theorem choose_eq_epsilon {α : Type} [Nonempty α] {P : α → Prop} (h : ∃ x, P x) :
h.choose = Classical.epsilon P := by
  simp only [Exists.choose, Classical.choose, Classical.indefiniteDescription,
    Classical.epsilon, Classical.strongIndefiniteDescription]
  simp [h]

@[simp]
theorem snoc_ne_nil {α : Type} {xs : List α} {x : α} : xs.snoc x ≠ [] := by
  simp [List.snoc]

@[simp]
def List.init {α : Type} : List α → List α
| [] => []
| [_] => []
| (x :: ys) => x :: ys.init

theorem init_cons_of_ne_nil {α : Type} {x : α} {xs : List α}
(h : xs ≠ []) : (x :: xs).init = x :: xs.init := by
  cases xs; simp at h; rfl

@[simp]
theorem init_snoc {α : Type} {xs : List α} {x : α} : (xs.snoc x).init = xs := by
  unfold List.snoc
  induction xs; rfl
  nm y xs ih
  rw [List.cons_append, init_cons_of_ne_nil # by simp, ih]

@[simp]
theorem nil_snoc {α : Type} {x : α} : [].snoc x = [x] := rfl

@[simp]
theorem cons_snoc {α : Type} {x y : α} {xs : List α} :
(x :: xs).snoc y = x :: xs.snoc y := rfl

theorem and_of {P Q : Prop} (h₁ : P) (h₂ : P → Q) : P ∧ Q := by tauto

@[simp]
theorem snoc_inj {α : Type} {xs ys : List α} {x y : α} :
xs.snoc x = ys.snoc y ↔ xs = ys ∧ x = y := by
  symm; constructor; rintro ⟨rfl, rfl⟩; rfl
  intro h
  apply and_of
  · replace h := congrArg List.init h
    simp at h
    exact h
  · rintro rfl
    induction xs; simp at h; exact h
    nm z xs ih
    simp at h
    exact ih h

@[simp]
theorem snoc_ne_self {α : Type} {xs : List α} {x : α} : xs.snoc x ≠ xs := by
  simp [List.snoc]

theorem not_iff' {P Q : Prop} : ¬(P ↔ Q) ↔ (P ↔ ¬Q) := by tauto
theorem not_iff_comm' {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by tauto

theorem imp_cpos {P Q : Prop} : (P → Q) ↔ (¬Q → ¬P) := by tauto

def nat_find (P : ℕ → Prop) : ℕ :=
  if h : ∃ x, P x then Nat.find h else 0

theorem nat_find_spec' {P : ℕ → Prop} (h : ∃ n, P n) :
P (nat_find P) ∧ ∀ k, P k → nat_find P ≤ k := by
  simp [nat_find, h]
  use Nat.find_spec h
  intro k hk
  use k

theorem nat_find_spec {P : ℕ → Prop} (h : ∃ n, P n) : P (nat_find P) := by
  exact (nat_find_spec' h).1

theorem nat_find_eq_of {P : ℕ → Prop} {n}
(h₁ : P n) (h₂ : ∀ k < n, ¬P k) : nat_find P = n := by
  unfold nat_find
  split_ifs with h₃
  · rw [Nat.find_eq_iff]
    tauto
  simp at h₃
  specialize h₃ n
  contradiction

theorem nat_find_eq_zero_of {P : ℕ → Prop} (h : ∀ n, ¬P n) : nat_find P = 0 := by
  unfold nat_find
  split_ifs with h₁
  · contrapose! h
    exact h₁
  rfl

theorem nat_find_eq_iff {P : ℕ → Prop} {n} :
nat_find P = n ↔ ite (∃ n, P n) (P n ∧ ∀ k < n, ¬P k) (n = 0) := by
  split_ifs with h₁
  · unfold nat_find; simp [h₁, Nat.find_eq_iff]
  simp at h₁
  rw [nat_find_eq_zero_of h₁, eq_comm]

theorem nat_find_min {P : ℕ → Prop} {n} (h : n < nat_find P) : ¬P n := by
  unfold nat_find at h
  split_ifs at h with h₁
  · exact Nat.find_min h₁ h
  simp at h

theorem nat_find_eq_of_not_ap_zero {P : ℕ → Prop} (h₁ : ∃ n, P n) (h₂ : ¬P 0) :
nat_find P = nat_find (λ m => P (m + 1)) + 1 := by
  apply nat_find_eq_of
  · apply @nat_find_spec (P # · + 1)
    obtain ⟨n, hn⟩ := h₁
    cases n
    · contradiction
    nm n
    use n
  intro k hk
  cases k
  · exact h₂
  nm k
  simp at hk
  apply @nat_find_min (P # · + 1)
  exact hk

theorem nat_find_eq_of_not_ap_le {P : ℕ → Prop} (n : ℕ)
(h₁ : ∃ n, P n) (h₂ : ∀ k ≤ n, ¬P k) :
nat_find P = nat_find (λ m => P (n + m)) + n := by
  induction n generalizing P
  · simp
  nm n ih
  have h₃ : ¬P 0 :=
    by
      apply h₂; simp
  specialize @ih (P # · + 1) _ _ <;> try dsimp
  · obtain ⟨k, hk⟩ := h₁
    cases k
    · contradiction
    nm k
    use k
  · intro k hk
    apply h₂
    simpa
  rw [nat_find_eq_of_not_ap_zero h₁ h₃, ih]; clear ih
  ring_nf

theorem fn_set_same_value {α β : Type} {f : α → β} {a : α} : 
fn_set a (f a) f = f := by
  unfold fn_set; ext x; split_ifs with h
  rw [h]
  rfl

theorem fn_set_twice_same {α β : Type} {f : α → β} {a : α} {b₁ b₂ : β} :
fn_set a b₂ (fn_set a b₁ f) = fn_set a b₂ f := by
  unfold fn_set; ext x; split_ifs with h <;> rfl

theorem fn_set_comm {α β : Type} {f : α → β} {a₁ a₂ : α} {b₁ b₂ : β}
(h : a₁ ≠ a₂) : fn_set a₁ b₁ (fn_set a₂ b₂ f) = fn_set a₂ b₂ (fn_set a₁ b₁ f) := by
  unfold fn_set; ext x; split_ifs with h₁ h₂ h₂ <;> try rfl
  rw [h₁] at h₂
  contradiction

theorem fn_set_ext {α β : Type} {f g : α → β} {a : α} {b : β} :
(∀ x, fn_set a b f x = fn_set a b g x) ↔ (∀ x, x ≠ a → f x = g x) := by
  constructor <;> intro h x
  · intro h₁
    specialize h x
    simp only [fn_set_eq_of_ne h₁] at h
    exact h
  · unfold fn_set; split_ifs with h₁; rfl
    exact h _ h₁

@[simp]
theorem Option.failure_bind {α β : Type} {f : α → Option β} :
(failure : Option α).bind f = none := rfl

@[simp]
theorem Option.exists_eq_some_of_ne_none {α : Type} {x : Option α}
(h : x ≠ none) : ∃ y, x = some y := by rwa [←ne_none_iff_exists']

@[simp]
theorem Option.guard_bind_eq_some_iff {α : Type} {P : Prop} [Decidable P]
{f : Unit → Option α} {x} :
(_root_.guard P : Option Unit).bind f = some x ↔ P ∧ f () = some x := by
  by_cases h : P <;> simp [h]

theorem quot_lift_mk_of {α : Type} {P : α → α → Prop} {f : α → Prop} {a} (h₁)
(h₂ : (∀ (a₁ a₂ : α), P a₁ a₂ → f a₁ = f a₂) → f a) :
Quot.lift f h₁ (Quot.mk P a) := h₂ h₁

@[simp]
theorem Set.not_nonempty_iff {α : Type} {s : Set α} :
¬s.Nonempty ↔ s = ∅ := not_nonempty_iff_eq_empty

@[simp]
theorem Set.setOf_compl {α : Type} {P : α → Prop} :
{x | P x}ᶜ = {x | ¬P x} := rfl

-- @[simp]
-- theorem not_mem_ordset_empty {α : Type} [LinearOrder α] {x : α} :
-- x ∉ (∅ : Ordset α) := by
--   simp [Ordset.instEmptyCollection, Ordset.nil, Ordset.instMembership]; rfl

-- @[simp]
-- theorem Ordset.finite {α : Type} [hi : LinearOrder α] {s : Ordset α} :
-- {x | x ∈ s}.Finite := by
--   sorry

@[simp]
theorem option_get!_with_bot_some {α : Type} [Inhabited α] {x : α} :
(WithBot.some x).get! = x := rfl

theorem max_right_eq_of_max_eq_and_ne {α : Type} [LinearOrder α] {a b c : α}
(h₁ : max a b = c) (h₂ : a ≠ c) : b = c := by
  simp [max_eq_iff, h₂] at h₁; exact h₁.1

@[simp]
theorem list_not_mem_failure {α : Type} {x : α} :
x ∉ (failure : List α) := List.count_eq_zero.mp rfl

@[simp]
theorem list_unit_mem_guard_iff {P : Prop} [Decidable P] :
() ∈ (guard P : List Unit) ↔ P := by
  by_cases h : P <;> simp [h]

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

theorem not_forall_congr_iff : ¬∀ (α : Type) (P Q : α → Prop),
((∀ x, P x) ↔ (∀ x, Q x)) ↔ ∀ x, P x ↔ Q x := by
  push_neg
  use Prop, id, (¬.)
  dsimp
  decide

theorem not_exi_congr_iff : ¬∀ (α : Type) (P Q : α → Prop),
((∃ x, P x) ↔ (∃ x, Q x)) ↔ ∃ x, P x ↔ Q x := by
  push_neg
  use Prop, id, (¬.)
  dsimp
  decide

end