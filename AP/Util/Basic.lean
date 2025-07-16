import Init.Coe
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Infix
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Control.Monad.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.CompleteField
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

open BigOperators

syntax:min term atomic(" #" ws) term:min : term

macro_rules
| `($f $args* # $a) => `($f $args* $a)
| `($f # $a) => `($f $a)

macro "nm " args:(ppSpace colGt Lean.binderIdent)+ : tactic =>
  `(tactic| rename_i $args*)

def fn_set' {α : Type*} [DecidableEq α] (a b x : α) : α :=
if x = a then b else x

def fn_swap' {α : Type*} [DecidableEq α] (a b x : α) : α :=
if x = a then b else if x = b then a else x

def fn_set {α β : Type*} [DecidableEq α] (a : α) (b : β) (f : α → β) (x : α) : β :=
if x = a then b else f x

def fn_swap {α β : Type*} [DecidableEq α] (a b : α) (f : α → β) (x : α) : β :=
f # fn_swap' a b x

-----

theorem thm_let {α : Type*} (x : α) : ∃ y, y = x := by
  apply exists_apply_eq_apply

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

theorem nat_rec_const (n m : ℕ) : n.rec m (λ _ a => a) = m := by
  induction n with
  | zero => simp
  | succ n => simpa

theorem nat_rec_succ' {α : Type*} {z : α} (f : ℕ → α → α) {n : ℕ} :
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

theorem fn_set_eq_of_ne {α β : Type*} [DecidableEq α] {a : α} {b : β}
{f : α → β} {x : α} (hx : x ≠ a) : fn_set a b f x = f x := by
  simp [fn_set_eq, hx]

theorem nat_fn_set_add {a b : ℕ} {f : ℕ → ℕ} {x : ℕ} :
fn_set a (f a + b) f x = f x + if x = a then b else 0 := by
  rw [fn_set_eq]; aesop

theorem fn_set_fn_set_eq_fn_swap {α β : Type*} [DecidableEq α] {a b} {f : α → β} :
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

@[simp]
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
theorem ite_10_le_one {P : Prop} [Decidable P] : ite P 1 0 ≤ 1 := by
  split_ifs <;> simp

@[simp]
theorem ite_01_le_one {P : Prop} [Decidable P] : ite P 0 1 ≤ 1 := by
  split_ifs <;> simp

theorem hv {α : Type*} (x : α) : ∃ y, y = x := exists_eq

theorem forall_spec {α β γ : Type*} {p : α → Prop} (f : β → γ → α)
(h : ∀ x, p x) : ∀ y z, p (f y z) := by intro y z; apply h

class ListMem {α : Type*} [DecidableEq α] (x : α) (xs : List α) where
  i : ℕ

@[simp]
instance {α : Type*} [DecidableEq α] {x : α} {xs} :
ListMem x (x :: xs) := ⟨0⟩

@[simp]
instance {α : Type*} [DecidableEq α] {x y : α} {xs}
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

def Set.erase {α : Type*} (x : α) (s : Set α) := s \ {x}

@[simp]
theorem Set.mem_erase {α : Type*} {z x : α} (s : Set α) :
z ∈ s.erase x ↔ z ≠ x ∧ z ∈ s := by
  unfold Set.erase; aesop

theorem Set.erase_eq_of_not_mem {α : Type*} {x : α} {s : Set α}
(h : x ∉ s) : s.erase x = s := by simpa [Set.erase]

theorem Set.insert_erase_eq_of_mem {α : Type*} {x : α} {s : Set α}
(h : x ∈ s) : insert x (s.erase x) = s := by
  ext z; simp; apply Iff.intro <;> intro h₁
  rcases h₁ with rfl | ⟨h₁, h₂⟩ <;> assumption
  simp [h₁]; apply eq_or_ne

theorem ne_none_of_eq_some {α : Type*} {m : Option α} {x : α}
(h : m = some x) : m ≠ none := by simp [h]

def List.snoc {α : Type*} (xs : List α) (x : α) := xs ++ [x]

@[simp]
theorem Set.finite_erase_iff {α : Type*} {x : α} {s : Set α} :
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
theorem Set.infinite_erase_iff {α : Type*} {x : α} {s : Set α} :
(s.erase x).Infinite ↔ s.Infinite := by simp [Set.Infinite]

theorem Set.diff_upair {α : Type*} (x y : α) (s : Set α) :
s \ {x, y} = (s \ {x}) \ {y} := by ext z; simp; tauto

@[simp]
theorem Set.univ_ne_univ_diff_insert {α : Type*} {x : α} {s : Set α} :
Set.univ ≠ Set.univ \ (insert x s) := by
  simp [Set.ext_iff]; use x; simp

@[simp]
theorem Set.univ_ne_univ_diff_singleton {α : Type*} {x : α} :
Set.univ ≠ Set.univ \ {x} := by simp [Set.ext_iff]

@[simp]
theorem Set.univ_ne_erase {α : Type*} {x : α} :
Set.univ ≠ Set.univ.erase x := by simp [Set.erase]

theorem prop_bcs (P : Prop) {R : Prop} (h₁ : P → R)
(h₂ : (P → R) → ¬P → R) : R := by tauto

theorem eq_true_of {P : Prop} (h : P) : P = True := by simpa

theorem Set.diff_erase_self_eq_of_mem {α : Type*} {x : α} {s : Set α}
(h : x ∈ s) : s \ s.erase x = {x} := by simpa [Set.erase]

theorem Set.eq_empty_iff {α : Type*} {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  eq_empty_iff_forall_notMem

@[simp]
theorem Set.subsingleton_upair_iff {α : Type*} {x y : α} :
({x, y} : Set _).Subsingleton ↔ x = y := by
  simp [Set.Subsingleton]; simp [eq_comm]

theorem ne_of_congr {α β : Type*} {x y : α} (f : α → β)
(h : f x ≠ f y) : x ≠ y := by contrapose! h; rw [h]

theorem skolemize {α β : Type*} [Nonempty β] {p : α → Prop} {q : α → β → Prop} :
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

theorem choose_eq_epsilon {α : Type*} [Nonempty α] {P : α → Prop} (h : ∃ x, P x) :
h.choose = Classical.epsilon P := by
  simp only [Exists.choose, Classical.choose, Classical.indefiniteDescription,
    Classical.epsilon, Classical.strongIndefiniteDescription]
  simp [h]

@[simp]
theorem snoc_ne_nil {α : Type*} {xs : List α} {x : α} : xs.snoc x ≠ [] := by
  simp [List.snoc]

@[simp]
def List.init {α : Type*} : List α → List α
| [] => []
| [_] => []
| (x :: ys) => x :: ys.init

theorem init_cons_of_ne_nil {α : Type*} {x : α} {xs : List α}
(h : xs ≠ []) : (x :: xs).init = x :: xs.init := by
  cases xs; simp at h; rfl

@[simp]
theorem init_snoc {α : Type*} {xs : List α} {x : α} : (xs.snoc x).init = xs := by
  unfold List.snoc
  induction xs; rfl
  nm y xs ih
  rw [List.cons_append, init_cons_of_ne_nil # by simp, ih]

@[simp]
theorem nil_snoc {α : Type*} {x : α} : [].snoc x = [x] := rfl

@[simp]
theorem cons_snoc {α : Type*} {x y : α} {xs : List α} :
(x :: xs).snoc y = x :: xs.snoc y := rfl

theorem and_of {P Q : Prop} (h₁ : P) (h₂ : P → Q) : P ∧ Q := by tauto

theorem List.snoc_elim {α : Type*} {xs ys : List α} (x : α)
(h : xs ++ [x] = ys ++ [x]) : xs = ys := by
  replace h := congrArg reverse h
  simp at h
  exact h

@[simp]
theorem List.snoc_inj {α : Type*} {xs ys : List α} {x y : α} :
xs ++ [x] = ys ++ [y] ↔ xs = ys ∧ x = y := by
  symm; constructor; rintro ⟨rfl, rfl⟩; rfl
  intro h
  replace h := congrArg reverse h
  simp at h
  exact h.symm

@[simp]
theorem snoc_ne_self {α : Type*} {xs : List α} {x : α} : xs.snoc x ≠ xs := by
  simp [List.snoc]

theorem not_iff' {P Q : Prop} : ¬(P ↔ Q) ↔ (P ↔ ¬Q) := by tauto
theorem not_iff_comm' {P Q : Prop} : (¬P ↔ Q) ↔ (P ↔ ¬Q) := by tauto

theorem imp_cpos {P Q : Prop} : (P → Q) ↔ (¬Q → ¬P) := by tauto

noncomputable
def nat_find (P : ℕ → Prop) : ℕ := by
  classical
  exact if h : ∃ n, P n ∧ ∀ k < n, ¬P k then h.choose else 0

theorem nat_find_eq {P} : by classical exact (
nat_find P = if h : ∃ n, P n then Nat.find h else 0) := by
  classical
  unfold nat_find
  symm
  by_cases h₁ : ∃ n, P n
  · have h₂ : ∃ n, P n ∧ ∀ k < n, ¬P k :=
      by
        use Nat.find h₁
        rw [←Nat.find_eq_iff h₁]
    simp [h₁, h₂]
    generalize_proofs
    rw [Nat.find_eq_iff h₁]
    exact h₂.choose_spec
  split_ifs with h₂
  · simp at h₁
    obtain ⟨n, h₂⟩ := h₂
    cases h₁ n h₂.1
  rfl

theorem nat_find_spec' {P : ℕ → Prop} (h : ∃ n, P n) : P (nat_find P) ∧
∀ k, P k → nat_find P ≤ k := by
  classical
  simp [nat_find_eq, h]
  use Nat.find_spec h
  intro k hk
  use k

theorem nat_find_spec {P : ℕ → Prop} (h : ∃ n, P n) : P (nat_find P) := by
  exact (nat_find_spec' h).1

theorem nat_find_eq_of {P : ℕ → Prop} {n} (h₁ : P n) (h₂ : ∀ k < n, ¬P k) :
nat_find P = n := by
  classical
  rw [nat_find_eq]
  split_ifs with h₃
  · rw [Nat.find_eq_iff]
    tauto
  simp at h₃
  specialize h₃ n
  contradiction

theorem nat_find_eq_zero_of {P : ℕ → Prop} (h : ∀ n, ¬P n) : nat_find P = 0 := by
  rw [nat_find_eq]
  split_ifs with h₁
  · contrapose! h
    exact h₁
  rfl

theorem nat_find_eq_iff {P : ℕ → Prop} {n} : by classical exact (
nat_find P = n ↔ ite (∃ n, P n) (P n ∧ ∀ k < n, ¬P k) (n = 0)) := by
  split_ifs with h₁
  · rw [nat_find_eq]; simp [h₁, Nat.find_eq_iff]
  simp at h₁
  rw [nat_find_eq_zero_of h₁, eq_comm]

theorem nat_find_min {P : ℕ → Prop} {n} (h : n < nat_find P) : ¬P n := by
  classical
  rw [nat_find_eq] at h
  split_ifs at h with h₁
  · exact Nat.find_min h₁ h
  simp at h

theorem nat_find_eq_of_not_ap_zero {P : ℕ → Prop}
(h₁ : ∃ n, P n) (h₂ : ¬P 0) : nat_find P = nat_find (λ m => P (m + 1)) + 1 := by
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

theorem nat_find_eq_of_not_ap_le {P : ℕ → Prop}
(n : ℕ) (h₁ : ∃ n, P n) (h₂ : ∀ k ≤ n, ¬P k) :
nat_find P = nat_find (λ m => P (n + m)) + n := by
  classical
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
theorem Option.failure_bind {α β : Type*} {f : α → Option β} :
(failure : Option α).bind f = none := rfl

@[simp]
theorem Option.exists_eq_some_of_ne_none {α : Type*} {x : Option α}
(h : x ≠ none) : ∃ y, x = some y := by rwa [←ne_none_iff_exists']

@[simp]
theorem Option.guard_bind_eq_some_iff {α : Type*} {P : Prop} [Decidable P]
{f : Unit → Option α} {x} :
(_root_.guard P : Option Unit).bind f = some x ↔ P ∧ f () = some x := by
  by_cases h : P <;> simp [h]

theorem quot_lift_mk_of {α : Type*} {P : α → α → Prop} {f : α → Prop} {a} (h₁)
(h₂ : (∀ (a₁ a₂ : α), P a₁ a₂ → f a₁ = f a₂) → f a) :
Quot.lift f h₁ (Quot.mk P a) := h₂ h₁

@[simp]
theorem Set.not_nonempty_iff {α : Type*} {s : Set α} :
¬s.Nonempty ↔ s = ∅ := not_nonempty_iff_eq_empty

@[simp]
theorem Set.setOf_compl {α : Type*} {P : α → Prop} :
{x | P x}ᶜ = {x | ¬P x} := rfl

-- @[simp]
-- theorem not_mem_ordset_empty {α : Type*} [LinearOrder α] {x : α} :
-- x ∉ (∅ : Ordset α) := by
--   simp [Ordset.instEmptyCollection, Ordset.nil, Ordset.instMembership]; rfl

-- @[simp]
-- theorem Ordset.finite {α : Type*} [hi : LinearOrder α] {s : Ordset α} :
-- {x | x ∈ s}.Finite := by
--   sorry

@[simp]
theorem option_get!_with_bot_some {α : Type*} [Inhabited α] {x : α} :
(WithBot.some x).get! = x := rfl

theorem max_right_eq_of_max_eq_and_ne {α : Type*} [LinearOrder α] {a b c : α}
(h₁ : max a b = c) (h₂ : a ≠ c) : b = c := by
  simp [max_eq_iff, h₂] at h₁; exact h₁.1

@[simp]
theorem list_not_mem_failure {α : Type*} {x : α} :
x ∉ (failure : List α) := by classical
  exact List.count_eq_zero.mp rfl

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

theorem Nat.add_one_add {a b : ℕ} : a + 1 + b = a + b + 1 := by ring

theorem Nat.add_one_sub {a b : ℕ} (h : b ≤ a) : a + 1 - b = a - b + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ring_nf; simp [nat_thm_aux₃]

theorem List.eq_of_prefix_and_length_eq {α : Type*} {xs ys zs : List α}
(hx : xs <+: zs) (hy : ys <+: zs) (hn : xs.length = ys.length) : xs = ys := by
  induction ys generalizing xs zs
  · simp at hn; exact hn
  nm y ys ih
  cases xs
  · simp at hn
  nm x xs
  simp at hn ⊢
  cases zs
  · simp at hx
  nm z zs
  simp at hx hy
  constructor
  · rw [hx.1, hy.1]
  exact ih hx.2 hy.2 hn

theorem fintype_exi_iter_cycle {α : Type*} [ha : Fintype α]
{f : α → α} {x : α} : ∃ n m, n < m ∧ f^[n] x = f^[m] x := by
  obtain ⟨g, hg⟩ := hv # λ n => f^[n] x
  suffices h : ∃ n m, g n = g m ∧ n ≠ m by
    subst hg
    obtain ⟨n, m, h₁, h₂⟩ := h
    wlog h₃ : n < m with ih
    · symm at h₁ h₂
      apply @ih α _ f x m n h₁ h₂ _
      simp at h₃
      exact Nat.lt_of_le_of_ne h₃ h₂
    use n, m
  by_contra! h₁
  exact Fintype.false # Fintype.ofInjective g h₁

@[simp]
theorem list_take_prefix {α : Type*} {xs : List α} {k : ℕ} : xs.take k <+: xs := by
  apply List.take_prefix

theorem List.prefix_of_prefix_snoc_and_ne {α : Type*} {xs ys : List α} {y : α}
(h₁ : xs <+: ys ++ [y]) (h₂ : xs ≠ ys ++ [y]) : xs <+: ys := by
  induction ys generalizing xs y
  · cases xs; rfl
    nm x xs
    simp at h₁ h₂
    tauto
  nm z zs ih
  cases xs
  · simp
  nm x xs
  simp at h₁
  rcases h₁ with ⟨rfl, h₁⟩
  simp at h₂
  simp
  exact ih h₁ h₂

theorem List.right_induction {α : Type*} {P : List α → Prop}
(h₁ : P []) (h₂ : ∀ xs x, P xs → P (xs ++ [x])) (xs : List α) : P xs := by
  generalize h : xs.reverse = ys
  induction ys generalizing xs
  · simp at h
    rwa [h]
  nm y ys ih
  replace h := congrArg (·.reverse) h
  simp at h
  subst h
  apply h₂
  apply ih
  simp

@[simp]
theorem List.append_prefix_left_iff {α : Type*} {xs ys : List α} :
xs ++ ys <+: xs ↔ ys = [] := by
  symm
  constructor
  · rintro rfl; simp
  rintro ⟨zs, h⟩
  simp at h
  exact h.1

@[simp]
theorem List.prefix_snoc_iff {α : Type*} {xs ys : List α} {y : α} :
xs <+: ys ++ [y] ↔ xs <+: ys ∨ xs = ys ++ [y] := by
  induction xs generalizing ys y
  · simp
  nm x xs ih
  cases ys
  · simp
  nm z ys
  simp
  by_cases h : x = z <;> simp [h]
  exact ih

theorem List.prefix_antisymm {α : Type*} {xs ys : List α}
(h₁ : xs <+: ys) (h₂ : ys <+: xs) : xs = ys := by
  obtain ⟨ys, rfl⟩ := h₁
  obtain ⟨zs, h₂⟩ := h₂
  simp at h₂
  simp [h₂]

theorem List.take_length_eq_of_prefix {α : Type*} {xs ys : List α}
(h₁ : ys <+: xs) : xs.take ys.length = ys := by
  obtain ⟨xs, rfl⟩ := h₁; simp

@[simp]
theorem List.nodup_inits {α : Type*} {xs : List α} : xs.inits.Nodup := by
  induction xs
  · simp
  nm x xs ih
  simp
  rwa [List.nodup_map_iff]
  simp

noncomputable
instance {α : Type*} [h : Fintype α] {β : Type*} {f : α → β} :
Fintype # Set.range f := by apply Fintype.ofFinite

theorem Cardinal.mk_eq_of_fintype_card {α : Type*} [h : Fintype α] {n}
(h₁ : Fintype.card α = n) : Cardinal.mk α = n := by
  rw [Cardinal.mk_fintype, h₁]

noncomputable
def Finset.to_some_list {α : Type*} (s : Finset α) : List α := by
  classical
  exact Classical.epsilon # λ xs => xs.toFinset = s

def Finset.to_sorted_list {α : Type*} [h : LinearOrder α]
(s : Finset α) : List α := by
  apply s.val.lift # λ xs => xs.mergeSort
  intro xs ys hxy
  reduce at hxy
  dsimp
  generalize hx : xs.mergeSort (· ≤ ·) = xs'
  generalize hy : ys.mergeSort (· ≤ ·) = ys'
  obtain ⟨h₁, h₂⟩ : xs'.Sorted (· ≤ ·) ∧ ys'.Sorted (· ≤ ·) := by
    subst hx hy; constructor <;> apply List.sorted_mergeSort'
  have h₃ : xs'.Perm ys' := by
    subst hx hy
    trans xs
    · apply List.mergeSort_perm
    symm; trans ys
    · apply List.mergeSort_perm
    exact hxy.symm
  exact List.eq_of_perm_of_sorted h₃ h₁ h₂

@[simp]
theorem Finset.to_some_list_toFinset {α : Type*} [h : DecidableEq α]
{s : Finset α} : s.to_some_list.toFinset = s := by
  unfold to_some_list
  convert Classical.epsilon_spec (p := λ (xs : List α) => xs.toFinset = s) _
  rcases s with ⟨m, h₁⟩
  simp [Finset.ext_iff]
  apply m.ind
  intro xs
  use xs
  simp

@[simp]
theorem Finset.to_sorted_list_toFinset {α : Type*} [h : LinearOrder α]
{s : Finset α} : s.to_sorted_list.toFinset = s := by
  ext x
  unfold to_sorted_list
  rcases s with ⟨m, h₁⟩
  simp
  apply m.ind
  intro xs
  simp

noncomputable
def mk_finset {α β : Type*}
(f : α → β) : Finset β := by
  classical
  by_cases h : Infinite α
  · exact {}
  simp at h
  replace h := Fintype.ofFinite α
  exact (Fintype.elems.to_some_list.map f).toFinset

def mk_finset_comp {α β : Type*} [Fintype α] [LinearOrder α] [DecidableEq β]
(f : α → β) : Finset β :=
  (Fintype.elems.to_sorted_list.map f).toFinset

@[simp]
theorem Finset.mem_to_some_list_iff {α : Type*} {s : Finset α} {x} :
x ∈ s.to_some_list ↔ x ∈ s := by
  classical
  simp [←List.mem_toFinset]

@[simp]
theorem Finset.mem_to_sorted_list_iff {α : Type*} [LinearOrder α] {s : Finset α} {x} :
x ∈ s.to_sorted_list ↔ x ∈ s := by simp [←List.mem_toFinset]

@[simp]
theorem Fintype.complete' {α : Type*} [Fintype α] {x : α} : x ∈ Fintype.elems := by
  apply complete

theorem mk_finset_eq {α β : Type*}
[ha : Fintype α] [DecidableEq α] [DecidableEq β] {f : α → β} :
mk_finset f = (Fintype.elems.to_some_list.map f).toFinset := by
  simp [mk_finset]
  split_ifs with h₁
  · exfalso; exact ha.false
  ext x
  simp

@[simp]
theorem mem_mk_finset_iff {α β : Type*} [Fintype α]
{f : α → β} {b : β} : b ∈ mk_finset f ↔ ∃ a, f a = b := by
  classical
  simp [mk_finset_eq]

@[simp]
theorem mem_mk_finset_comp_iff {α β : Type*} [Fintype α] [LinearOrder α] [DecidableEq β]
{f : α → β} {b : β} : b ∈ mk_finset_comp f ↔ ∃ a, f a = b := by simp [mk_finset_comp]

@[simp]
theorem mk_finset_comp_eq_mk_finset {α β} [Fintype α] [LinearOrder α] [DecidableEq β]
{f : α → β} : mk_finset_comp f = mk_finset f := by ext x; simp

instance {α : Type*} [h : IsEmpty α] : Fintype α := ⟨{}, by simp⟩

@[simp]
theorem mk_finset_const_of_nonempty {α β : Type*}
[Fintype α] [Nonempty α] [DecidableEq α] [DecidableEq β] {b : β} :
mk_finset (λ (_ : α) => b) = {b} := by ext x; simp [eq_comm]

@[simp]
theorem mk_finset_const_of_empty {α β : Type*}
[IsEmpty α] [DecidableEq β] {b : β} : mk_finset (λ (_ : α) => b) = {} := by
  ext x; simp

theorem mk_finset_fin_succ_eq_insert {α : Type*}
[ha : DecidableEq α] {n} {f : Fin (n + 1) → α} : mk_finset f =
insert (f ⟨n, by linarith⟩) (mk_finset # λ (⟨k, hk⟩ : Fin n) => f ⟨k, by linarith⟩) := by
  ext x
  simp
  constructor
  · rintro ⟨⟨k, hk⟩, rfl⟩
    rw [Nat.lt_succ_iff, Nat.le_iff_lt_or_eq] at hk
    rcases hk with hk | rfl
    · right
      use ⟨_, hk⟩
    simp
  rintro (rfl | ⟨⟨k, hk⟩, h₁⟩)
  · simp
  use ⟨k, by linarith⟩

theorem mk_finset_card_le {α β} [ha₁ : Fintype α] {f : α → β} :
(mk_finset f).card ≤ Fintype.card α := by
  apply Finset.card_le_card_of_surjOn f
  simp [mk_finset_eq]
  intro y
  simp

@[simp]
theorem Set.univ_injOn_iff {α β : Type*} {f : α → β} :
(Set.univ : Set α).InjOn f ↔ f.Injective := by simp [Set.InjOn]; rfl

@[simp]
theorem Fintype.elems_eq_empty_iff {α : Type*} [ha : Fintype α] :
ha.elems = ∅ ↔ ∀ (_ : α), false := by simp [Finset.ext_iff]

theorem Finset.card_eq_card_iff_equiv.{u} {α β : Type u}
{sa : Finset α} {sb : Finset β} : sa.card = sb.card ↔ Nonempty (sa ≃ sb) := by
  simp [←Cardinal.eq]

set_option linter.unusedVariables false
@[simp]
theorem Cardinal.mk_subtype_const_true {α : Type*} :
Cardinal.mk {x : α // True} = Cardinal.mk α := by
  rw [Cardinal.eq]
  use λ ⟨x, _⟩ => x
  use λ x => ⟨x, trivial⟩
  · intro x; simp
  · intro x; simp
set_option linter.unusedVariables true

set_option linter.unusedVariables false
@[simp]
theorem nonempty_equiv_subtype_const_true_iff.{u} {α β : Type u} :
Nonempty (α ≃ {x : β // True}) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]
set_option linter.unusedVariables true

theorem nonempty_equiv_comm {α β : Type*} :
Nonempty (α ≃ β) ↔ Nonempty (β ≃ α) := by
  apply Nonempty.congr <;> exact λ h => h.symm

theorem mk_finset_toSet_eq {α β : Type*} [ha : Fintype α] {f : α → β} :
(mk_finset f).toSet = Set.range f := by ext x; simp

theorem Finset.card_eq_cardinal_mk_to_nat {α : Type*} {s : Finset α} :
s.card = (Cardinal.mk s).toNat := by simp

@[simp]
theorem nonempty_equiv_refl {α : Type*} : Nonempty (α ≃ α) := ⟨by rfl⟩

theorem Set.nonempty_equiv_empty_empty {α β : Type*} :
Nonempty ((∅ : Set α) ≃ (∅ : Set β)) := by
  refine' ⟨⟨_, _, _, _⟩⟩
  all_goals try rintro ⟨x, h⟩; simp at h

@[simp]
theorem Set.nonempty_equiv_empty_iff {α β : Type*} {s : Set α} :
Nonempty (s ≃ (∅ : Set β)) ↔ s = ∅ := by
  constructor
  · rintro ⟨h⟩
    ext x
    simp
    intro hx
    exact (h.toFun ⟨_, hx⟩).2
  · rintro rfl
    exact Set.nonempty_equiv_empty_empty

theorem nonempty_equiv_trans {α γ : Type*} (β : Type*)
(h₁ : Nonempty (α ≃ β)) (h₂ : Nonempty (β ≃ γ)) : Nonempty (α ≃ γ) := by
  rcases h₁ with ⟨a⟩
  rcases h₂ with ⟨b⟩
  exact ⟨a.trans b⟩

theorem nonempty_equiv_set_univ_self {α : Type*} :
Nonempty (α ≃ (Set.univ : Set α)) := by
  simp [←Cardinal.eq]

theorem nonempty_equiv_set_univ_self' {α : Type*} :
Nonempty ((Set.univ : Set α) ≃ α) := by
  simp [←Cardinal.eq]

theorem nonempty_equiv_set_univ_set_univ_iff.{u} {α β : Type u} :
Nonempty ((Set.univ : Set α) ≃ (Set.univ : Set β)) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

@[simp]
theorem nonempty_equiv_set_univ_iff.{u} {α β : Type u} :
Nonempty (α ≃ (Set.univ : Set β)) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

@[simp]
theorem nonempty_equiv_set_univ_iff'.{u} {α β : Type u} :
Nonempty ((Set.univ : Set α) ≃ β) ↔ Nonempty (α ≃ β) := by
  simp [←Cardinal.eq]

theorem Finset.card_eq_toSet_ncard {α : Type*} {s : Finset α} :
s.card = s.toSet.ncard := by simp

noncomputable
instance {α : Type*} [Fintype α] {s : Set α} : Fintype s := by
  exact Fintype.ofFinite ↑s

theorem mk_finset_card_eq_set_card_range {α β : Type*}
[ha : Fintype α] {f : α → β} :
(mk_finset f).card = (Set.range f).ncard := by
  classical
  simp [Finset.card_eq_cardinal_mk_to_nat]
  have h₁ : Cardinal.mk {x // ∃ a, f a = x} = Cardinal.mk (Set.range f) :=
    by
      rw [Cardinal.eq]
      exact nonempty_equiv_refl
  rw [h₁]
  clear h₁
  unfold Set.ncard
  apply congrArg Cardinal.toNat
  simp

@[simp]
theorem fintype_card_set_eq_ncard {α : Type*}
{s : Set α} [hs : Fintype s] : Fintype.card s = s.ncard := by
  unfold Fintype.card
  rw [Finset.card_eq_cardinal_mk_to_nat]
  apply congrArg Cardinal.toNat
  simp

@[simp]
theorem Cardinal.mk_eq_mk_iff_of_finite.{u} {α β : Type u}
[ha : Fintype α] [hb : Fintype β] :
Cardinal.mk α = Cardinal.mk β ↔ Fintype.card α = Fintype.card β := by
  rw [Cardinal.eq, Fintype.card_eq]

noncomputable
def Finite.to_fintype {α : Type*} (ha : Finite α) : Fintype α :=
  Fintype.ofFinite α

noncomputable
def Set.Finite.to_fintype {α : Type*}
{sa : Set α} (ha : sa.Finite) : Fintype sa := by
  unfold Set.Finite at ha; exact ha.to_fintype

theorem Finset.image_toSet_eq {α β : Type*} [DecidableEq β]
{s : Finset α} {f : α → β} :
f '' s.toSet = (s.image f).toSet := by
  symm; exact coe_image

theorem Finset.ncard_toSet {α : Type*} {s : Finset α} :
s.toSet.ncard = s.card := by simp

theorem Set.injOn_of_card_image_eq' {α : Type*} {s : Set α} {f : α → α}
(h₁ : s.Finite) (h₂ : Cardinal.mk (f '' s) = Cardinal.mk s) : s.InjOn f := by
  classical
  have h₃ := Set.Finite.image f h₁
  replace h₁ := h₁.to_fintype
  replace h₃ := h₃.to_fintype
  simp at h₂
  rename' s => s'
  generalize hs : s'.toFinset = s
  replace hs := congrArg (·.toSet) hs
  simp at hs
  subst hs
  clear h₁ h₃
  simp at h₂
  rw [Finset.image_toSet_eq, Finset.ncard_toSet, Finset.card_image_iff] at h₂
  exact h₂

theorem Set.card_image_eq_iff_injOn' {α : Type*} {s : Set α} {f : α → α}
(h₁ : s.Finite) : Cardinal.mk (f '' s) = Cardinal.mk s ↔ s.InjOn f := by
  classical
  use injOn_of_card_image_eq' h₁
  intro h
  rw [Cardinal.eq]
  constructor
  symm
  apply Equiv.ofBijective # λ ⟨x, hx⟩ => ⟨f x, by simp; use x⟩
  simp
  constructor
  · simpa [Function.Injective]
  · simp [Function.Surjective]

theorem Set.ncard_eq_ncard_iff_nonempty_equiv.{u} {α β : Type u}
{sa : Set α} {sb : Set β} (ha : sa.Finite) (hb : sb.Finite) :
sa.ncard = sb.ncard ↔ Nonempty (sa ≃ sb) := by
  classical
  rw [←Cardinal.eq]
  replace ha := ha.to_fintype
  replace hb := hb.to_fintype
  simp

theorem Set.ncard_image_eq_iff_injOn' {α : Type*} {s : Set α} {f : α → α}
(h₁ : s.Finite) : (f '' s).ncard = s.ncard ↔ s.InjOn f := by
  rw [ncard_eq_ncard_iff_nonempty_equiv (Set.Finite.image f h₁) h₁]
  rw [←Cardinal.eq]
  exact card_image_eq_iff_injOn' h₁

theorem nonempty_equiv_iff_bijective {α β : Type*} :
Nonempty (α ≃ β) ↔ ∃ (f : α → β), f.Bijective := by
  use λ ⟨e⟩ => ⟨_, e.bijective⟩
  use λ ⟨f, hf⟩ => ⟨Equiv.ofBijective f hf⟩

theorem Set.ncard_eq_ncard_iff_bijective.{u} {α β : Type u}
{sa : Set α} {sb : Set β} (ha : sa.Finite) (hb : sb.Finite) :
sa.ncard = sb.ncard ↔ ∃ (f : sa → sb), f.Bijective := by
  rw [ncard_eq_ncard_iff_nonempty_equiv ha hb]
  exact nonempty_equiv_iff_bijective

theorem Set.range_eq_image {α β : Type*} {f : α → β} :
Set.range f = f '' Set.univ := by simp

theorem Fintype.card_eq_finset_card {α : Type*} [ha : Fintype α] :
Fintype.card α = (Finset.univ : Finset α).card := by simp

theorem Set.univ_eq_finset_univ_of_fintype {α : Type*} [ha : Fintype α] :
(Set.univ : Set α) = Finset.univ.toSet := by simp

theorem fintype_card_range_eq_iff_injective {α β : Type*}
[ha : Fintype α] {f : α → β} :
Fintype.card (Set.range f) = Fintype.card α ↔ f.Injective := by
  classical
  refine' ⟨_, λ h => Set.card_range_of_injective h⟩
  intro h
  simp at h
  rw [Set.range_eq_image, Fintype.card_eq_finset_card,
    Set.univ_eq_finset_univ_of_fintype, Finset.image_toSet_eq,
    Finset.ncard_toSet] at h
  rw [Finset.card_image_iff] at h
  simp at h
  exact h

theorem Fintype.card_eq_set_ncard {α : Type*} [ha : Fintype α] :
Fintype.card α = (Set.univ : Set α).ncard := by
  rw [Set.ncard_eq_toFinset_card]; simp

theorem Set.finite_of_finite_and_bijective {α β : Type*}
{sa : Set α} {sb : Set β}
(h₁ : sa.Finite) (h₂ : ∃ (f : sa → sb), f.Bijective) : sb.Finite := by
  rw [←nonempty_equiv_iff_bijective] at h₂
  obtain ⟨e⟩ := h₂
  replace h₁ := h₁.to_fintype
  suffices h₃ : Fintype sb from Set.toFinite sb
  exact Fintype.ofEquiv _ e

theorem exi_bijective_symm {α β : Type*}
(h : ∃ (f : α → β), f.Bijective) : ∃ (f : β → α), f.Bijective := by
  obtain ⟨f, hf⟩ := h
  rw [Function.bijective_iff_has_inverse] at hf
  obtain ⟨g, h₁, h₂⟩ := hf
  use g
  exact Equiv.bijective ⟨g, f, h₂, h₁⟩

theorem exi_bijective_comm {α β : Type*} :
(∃ (f : α → β), f.Bijective) ↔ ∃ (f : β → α), f.Bijective := by
  constructor <;> exact exi_bijective_symm

theorem Set.finite_of_finite_and_bijective' {α β : Type*}
{sa : Set α} {sb : Set β}
(h₁ : sa.Finite) (h₂ : ∃ (f : sb → sa), f.Bijective) : sb.Finite := by
  rw [exi_bijective_comm] at h₂
  exact finite_of_finite_and_bijective h₁ h₂

theorem Set.ncard_image_eq_iff_injOn {α β : Type*} {s : Set α} {f : α → β}
(h₁ : s.Finite) : (f '' s).ncard = s.ncard ↔ s.InjOn f := ncard_image_iff h₁

theorem set_range_sum_inl_card_eq {α β : Type*} [ha : Fintype α] :
(Set.range # @Sum.inl α β).ncard = Fintype.card α := by
  rw [Fintype.card_eq_set_ncard, Set.range_eq_image]
  rw [Set.ncard_image_eq_iff_injOn Set.finite_univ]
  apply Set.injOn_of_injective Sum.inl_injective

theorem set_range_sum_inr_card_eq {α β : Type*} [hb : Fintype β] :
(Set.range # @Sum.inr α β).ncard = Fintype.card β := by
  rw [Fintype.card_eq_set_ncard, Set.range_eq_image]
  rw [Set.ncard_image_eq_iff_injOn Set.finite_univ]
  apply Set.injOn_of_injective Sum.inr_injective

theorem Set.nonempty_range_equiv_self_iff_injective.{u} {α β : Type u}
[ha : Fintype α] {f : α → β} : Nonempty (Set.range f ≃ α) ↔ f.Injective := by
  rw [←fintype_card_range_eq_iff_injective, ←Cardinal.eq]; simp

@[simp]
theorem mk_finset_card_eq_fintype_card_iff_injective.{u} {α β : Type u}
[ha : Fintype α] {f : α → β} :
(mk_finset f).card = Fintype.card α ↔ f.Injective := by
  classical
  by_cases h₁ : IsEmpty α
  · simp [Finset.eq_empty_iff_forall_notMem]
    exact Function.injective_of_subsingleton f
  simp at h₁
  change _ = Finset.univ.card ↔ _
  rw [←fintype_card_range_eq_iff_injective]
  rw [Finset.card_eq_card_iff_equiv, ←Cardinal.eq]
  simp [Set.range]
  simp only [←Finset.card_univ]
  simp only [Finset.card_eq_cardinal_mk_to_nat]
  simp
  constructor <;> intro h
  · simp [h]
  rwa [Cardinal.toNat_eq_iff] at h
  simp [Fintype.card_eq_zero_iff]

@[simp]
theorem Finset.card_le_fintype_card {α : Type*} [ha : Fintype α] {s : Finset α} :
s.card ≤ Fintype.card α := Finset.card_le_univ s

theorem inf_type : Infinite Type := by
  rw [Cardinal.infinite_iff]
  suffices h : Cardinal.aleph0 ≤ Cardinal.lift.{1, 1} (Cardinal.mk Type)
    by
      simp at h
      exact h
  rw [Cardinal.aleph0, Cardinal.lift_mk_le]
  refine' ⟨⟨Fin, _⟩⟩
  intro x y h
  replace h := congrArg Cardinal.mk h
  simp at h
  exact h

instance : Infinite Type := inf_type

theorem card_lt_pi {α : Type*} : Cardinal.mk α < Cardinal.mk (α → Prop) := by
  simp [Cardinal.mk_pi]; apply Cardinal.cantor

def Quotient.lift_out {α β : Type*} {s : Setoid α} (q : Quotient s) (f : α → β)
(h : ∀ (x y : α), s.r x q.out → s.r y q.out → f x = f y) : β := by
  induction q using Quotient.hrecOn
  · nm x
    use f x
  nm x y h
  clear! q
  apply Function.hfunext
  · simp
    rw [forall_congr]; intro a
    rw [forall_congr]; intro b
    ext
    constructor
    all_goals
      intro h₁ h₂ h₃
      apply h₁
      all_goals
        first | apply s.trans h₂ | apply s.trans h₃
        apply Quotient.out_equiv_out.mpr
        apply Quotient.sound
        first | exact s.symm h | exact h
  intro h₁ h₂ h₃
  clear h₂ h₃
  simp
  have h₂ : s (Quotient.mk s x).out (Quotient.mk s y).out :=
    by
      apply Quotient.out_equiv_out.mpr
      simpa
  apply h₁ x y
  · apply s.symm
    exact Quotient.eq_mk_iff_out.mp rfl
  · apply s.symm
    apply Quotient.eq_mk_iff_out.mp
    simpa

theorem List.length_takeWhile_le {α : Type*} {P : α → Bool} {xs : List α} :
(xs.takeWhile P).length ≤ xs.length := by
  induction xs
  · simp
  nm x xs ih
  simp [takeWhile]
  split; simpa; simp

theorem List.not_apply_of_takeWhile_append_cons_eq_self
{α : Type*} {xs ys : List α} {P : α → Bool} {y}
(h : xs.takeWhile P ++ y :: ys = xs) : P y = false := by
  induction xs using right_induction generalizing y ys
  · simp at h
  nm xs x ih
  rw [takeWhile_append] at h
  split_ifs at h with h₁
  · simp [takeWhile_cons] at h
    split_ifs at h with h₂ <;> simp at h
    simp [←h] at h₂
    exact h₂
  suffices h₂ : xs.takeWhile P ++ [y] <+: xs
    by
      obtain ⟨zs, h₂⟩ := h₂
      simp at h₂
      exact ih h₂
  rw [append_cons] at h
  induction ys using right_induction
  · rw [append_nil, snoc_inj] at h
    simp [h.1] at h₁
  nm ys z x; clear x
  rw [←append_assoc, snoc_inj] at h
  rcases h with ⟨h, rfl⟩
  use ys

theorem List.exists_takeWhile_eq {α : Type*} (xs : List α) (P : α → Bool) :
∃ k ≤ xs.length, xs.takeWhile P = xs.take k ∧ (∀ x ∈ xs.take k, P x) ∧
((h : k < xs.length) → P xs[k] = false) := by
  use (xs.takeWhile P).length
  use length_takeWhile_le
  use by rw [take_length_eq_of_prefix # takeWhile_prefix _]
  constructor
  · intro x hx
    induction xs using List.right_induction
    · simp at hx
    nm xs y ih
    rw [List.takeWhile_append] at hx
    split_ifs at hx with h₁
    · simp [List.take_append] at hx
      simp [h₁] at ih
      rcases hx with h₂ | h₂
      · exact ih h₂
      rw [List.takeWhile_cons] at h₂
      split_ifs at h₂ with h₃
      · simp at h₂
        rwa [h₂]
      simp at h₂
    rw [List.take_append_eq_append_take] at hx
    simp at hx
    rcases hx with h₂ | h₂
    · exact ih h₂
    have h₃ : (takeWhile P xs).length - xs.length = 0 :=
      by
        exact Nat.sub_eq_zero_of_le length_takeWhile_le
    simp [h₃] at h₂
  have h₁ : takeWhile P xs <+: xs := takeWhile_prefix P
  obtain ⟨ys, h₁⟩ := h₁
  rw [←h₁]
  cases ys
  · simp at h₁ ⊢
    rw [←List.takeWhile_eq_self_iff] at h₁
    simp [h₁]
  nm y ys
  have h₂ := List.not_apply_of_takeWhile_append_cons_eq_self h₁
  rw [append_cons, takeWhile_append, takeWhile_append, takeWhile_idem]
  simp [h₂]

@[simp]
theorem List.init_snoc {α : Type*} {xs : List α} {x} :
(xs ++ [x]).init = xs := by
  induction xs generalizing x
  · simp
  nm y ys ih
  simp
  exact ih

theorem List.ext {α : Type*} {xs ys : List α} : xs = ys ↔ xs.length = ys.length ∧
∀ {i} (_ : i < xs.length) (_ : i < ys.length), xs[i] = ys[i] := by
  constructor
  · rintro rfl; simp
  rintro ⟨h₁, h₂⟩
  ext i x
  have h₄ : i < xs.length ↔ i < ys.length := by rw [h₁]
  by_cases h₃ : i < xs.length <;> simp [h₃] at h₄
  · rw [List.getElem?_eq_getElem h₃]
    rw [List.getElem?_eq_getElem h₄]
    simp
    rw [h₂ h₃ h₄]
  simp at h₃
  rw [List.getElem?_eq_none h₃]
  rw [List.getElem?_eq_none h₄]

def Fin.next {n} (k : Fin n) : Fin n := by
  let k₁ := k.1 + 1
  use if k₁ = n then 0 else k₁
  split_ifs <;> omega

theorem Fin.toNat_next_eq {n} {k : Fin n} :
k.next.toNat = if k.toNat + 1 = n then 0 else k.toNat + 1 := by rfl

theorem List.suffix_cons_of_suffix {α : Type*} {xs ys : List α} {y}
(h : xs <:+ ys) : xs <:+ y :: ys := by
  simp [List.suffix_cons_iff, h]

@[simp]
theorem List.not_cons_suffix {α : Type*} {xs : List α} {x} : ¬(x :: xs <:+ xs) := by
  rintro ⟨ys, h⟩
  replace h := congrArg (·.length) h
  simp at h
  linarith

theorem Real.add_inv {a b : ℝ} (h : b ≠ 0) : a + b⁻¹ = (a * b + 1) / b := by
  field_simp

theorem pow_lt_iff {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ b < c ↔ a < c ^ (1 / b) := by
  iterate rw [Real.rpow_lt_iff_lt_log, Real.lt_rpow_iff_log_lt] <;>
    try linarith
  have h : Real.log c = b * ((1 / b) * Real.log c) := by
    rw [←mul_assoc, mul_div, mul_one, div_self # by linarith]
    simp
  nth_rw 1 [h]
  rw [mul_lt_mul_iff_of_pos_left hb]

theorem Real.add_inv_pow_lt_exp_one_of {a : ℝ} (h : 0 ≤ a) :
    (1 + a⁻¹) ^ a < Real.exp 1 := by
  rw [le_iff_eq_or_lt] at h; rcases h with rfl | h; simp
  rw [Real.rpow_def_of_pos # by positivity, Real.exp_lt_exp, (by simp : a = a⁻¹⁻¹),
    mul_inv_lt_iff₀' # by positivity, add_comm]; simp
  nth_rw 2 [(by simp : a⁻¹ = a⁻¹ + 1 - 1)]; apply Real.log_lt_sub_one_of_pos
  positivity; apply ne_of_congr (· - 1); simp; linarith

section card_type

universe u v w q

theorem nonempty_equiv_of_embed {α : Type u} {β : Type v}
(h₁ : Nonempty (α ↪ β)) (h₂ : Nonempty (β ↪ α)) : Nonempty (α ≃ β) := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  rw [nonempty_equiv_iff_bijective]
  exact Function.Embedding.schroeder_bernstein hf hg

theorem nonempty_embed_trans {α : Type u} {β : Type v} {γ : Type w}
(h₁ : Nonempty (α ↪ β)) (h₂ : Nonempty (β ↪ γ)) : Nonempty (α ↪ γ) := by
  obtain ⟨f, hf⟩ := h₁
  obtain ⟨g, hg⟩ := h₂
  exact ⟨_, Function.Injective.comp hg hf⟩

theorem nonempty_embed_iff_lift_left {α : Type v} {β : Type w} :
Nonempty (α ↪ β) ↔ Nonempty (ULift.{u} α ↪ β) := by
  constructor <;> rintro ⟨f, hf⟩
  all_goals
    refine' ⟨λ x => _, _⟩
    first | exact f x.down | exact f (.up x)
    intro x y h
    simp at h
    specialize hf h
    simp at hf
    exact hf

theorem nonempty_embed_iff_lift_right {α : Type v} {β : Type w} :
Nonempty (α ↪ β) ↔ Nonempty (α ↪ ULift.{u} β) := by
  constructor <;> rintro ⟨f, hf⟩
  all_goals
    refine' ⟨λ x => _, _⟩
    first | exact .up (f x) | exact (f x).down
    intro x y h
    simp at h
    specialize hf h
    exact hf

theorem isEmpty_embed_iff_lift_left {α : Type v} {β : Type w} :
IsEmpty (α ↪ β) ↔ IsEmpty (ULift.{u} α ↪ β) := by
  rw [←not_iff_not]; simp; exact nonempty_embed_iff_lift_left

theorem isEmpty_embed_iff_lift_right {α : Type v} {β : Type w} :
IsEmpty (α ↪ β) ↔ IsEmpty (α ↪ ULift.{u} β) := by
  rw [←not_iff_not]; simp; exact nonempty_embed_iff_lift_right

theorem nonempty_embed_iff_lift {α : Type w} {β : Type q} :
Nonempty (α ↪ β) ↔ Nonempty (ULift.{u} α ↪ ULift.{v} β) := by
  constructor <;> rintro ⟨f, hf⟩
  all_goals
    refine' ⟨λ y => _, _⟩
    first | exact .up (f y.down) | exact (f (.up y)).down
    intro x y h
    simp at h
    specialize hf h
    simp at hf
    exact hf

theorem isEmpty_embed_iff_lift {α : Type w} {β : Type q} :
IsEmpty (α ↪ β) ↔ IsEmpty (ULift.{u} α ↪ ULift.{v} β) := by
  rw [←not_iff_not]
  simp
  exact nonempty_embed_iff_lift

theorem nonempty_embed_of_empty_embed_rev {α : Type u} {β : Type v}
(h : IsEmpty (β ↪ α)) : Nonempty (α ↪ β) := by
  rw [isEmpty_embed_iff_lift.{u, v}] at h
  rw [nonempty_embed_iff_lift.{v, u}]
  rw [←Cardinal.le_def]
  contrapose! h
  simp
  rw [←Cardinal.le_def]
  exact le_of_lt h

theorem isEmpty_embed_of_isEmpty_of_nonempty {α : Type u} {β : Type v} {γ : Type w}
(h₁ : IsEmpty (β ↪ α)) (h₂ : Nonempty (β ↪ γ)) : IsEmpty (γ ↪ α) := by
  contrapose h₁
  simp at h₁ ⊢
  exact nonempty_embed_trans h₂ h₁

@[simp]
theorem isEmpty_set_embed {α : Type u} : IsEmpty (Set α ↪ α) := by
  by_contra h
  simp at h
  rw [←Cardinal.le_def] at h
  simp at h
  contrapose! h
  apply Cardinal.cantor

theorem nonempty_embed_type {α : Type u} : Nonempty (α ↪ Type u) := by
  use λ x => (embeddingToCardinal.1 x).out
  intro x y h
  simp at h
  exact embeddingToCardinal.2 h

theorem isEmpty_type_embed {α : Type u} : IsEmpty (Type u ↪ α) := by
  apply isEmpty_embed_of_isEmpty_of_nonempty isEmpty_set_embed
  exact nonempty_embed_type

theorem cardinal_embed_type : Nonempty (Cardinal.{u} ↪ Type u) := by
  use Quotient.out
  intro x y h
  simp at h
  exact h

theorem cardinal_embed_ordinal : Nonempty (Cardinal.{u} ↪ Ordinal.{u}) := by
  use Cardinal.ord
  intro x y h
  simp at h
  exact h

theorem ifEmpty_embed_trans {α : Type u} {β : Type v} {γ : Type w}
(h₁ : IsEmpty (α ↪ β)) (h₂ : IsEmpty (β ↪ γ)) : IsEmpty (α ↪ γ) := by
  apply isEmpty_embed_of_isEmpty_of_nonempty h₂
  exact nonempty_embed_of_empty_embed_rev h₁

@[simp]
theorem nonempty_lift_embed_iff {α : Type v} {β : Type w} :
Nonempty (ULift.{u} α ↪ β) ↔ Nonempty (α ↪ β) :=
  nonempty_embed_iff_lift_left.symm

@[simp]
theorem nonempty_embed_lift_iff {α : Type v} {β : Type w} :
Nonempty (α ↪ ULift.{u} β) ↔ Nonempty (α ↪ β) :=
  nonempty_embed_iff_lift_right.symm

@[simp]
theorem isEmpty_lift_embed_iff {α : Type v} {β : Type w} :
IsEmpty (ULift.{u} α ↪ β) ↔ IsEmpty (α ↪ β) :=
  isEmpty_embed_iff_lift_left.symm

@[simp]
theorem isEmpty_embed_lift_iff {α : Type v} {β : Type w} :
IsEmpty (α ↪ ULift.{u} β) ↔ IsEmpty (α ↪ β) :=
  isEmpty_embed_iff_lift_right.symm

theorem nonempty_embed_type_max {α : Type v} :
Nonempty (α ↪ Type (max v u)) := by
  rw [nonempty_embed_iff_lift_left.{max u v}]
  exact nonempty_embed_type

theorem isEmpty_type_max_embed {α : Type v} :
IsEmpty (Type (max v u) ↪ α) := by
  apply isEmpty_embed_of_isEmpty_of_nonempty isEmpty_set_embed
  exact nonempty_embed_type_max.{max u v}

@[simp]
theorem type_embed_type_succ : Nonempty (Type u ↪ Type (u + 1)) :=
  nonempty_embed_type_max.{u + 1}

@[simp]
theorem not_type_succ_embed_type : IsEmpty (Type (u + 1) ↪ Type u) :=
  isEmpty_type_max_embed.{u + 1}

end card_type

theorem List.perm_swap_left {α : Type*} {xs ys : List α} {x y} :
(x :: y :: xs).Perm ys ↔ (y :: x :: xs).Perm ys := by
  constructor <;> intro h
  · trans x :: y :: xs
    rotate_left; exact h
    apply List.Perm.swap
  · trans y :: x :: xs
    rotate_left; exact h
    apply List.Perm.swap

theorem List.perm_swap_right {α : Type*} {xs ys : List α} {x y} :
xs.Perm (x :: y :: ys) ↔ xs.Perm (y :: x :: ys) := by
  rw [List.perm_comm]
  nth_rw 2 [List.perm_comm]
  exact perm_swap_left

theorem List.mergeSort_attach {α : Type*} {xs : List α} {r} :
(xs.attach.mergeSort (r ·.1 ·.1)).unattach = xs.mergeSort r := by
  rw [List.ext_getElem?_iff]
  simp
  intro n
  induction n using Nat.strong_induction_on generalizing xs
  nm n ih
  generalize ha : xs.attach.mergeSort (r ·.1 ·.1) = as
  generalize hb : xs.mergeSort r = bs
  cases as
  · replace ha := congrArg (·.length) ha
    replace hb := congrArg (·.length) hb
    simp at ha hb
    symm at hb
    simp [ha] at hb
    simp [hb]
  nm a as
  cases bs
  · replace ha := congrArg (·.length) ha
    replace hb := congrArg (·.length) hb
    simp at hb
    simp [hb] at ha
  nm b bs
  have hab : a = b :=
    by
      sorry
  cases n
  · simpa
  nm n
  simp
  -- xs' := remove first `a` from xs
  -- use xs' in induction hypothesis
  sorry