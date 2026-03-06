import Projects.Paramodulator.Defs
import Projects.Paramodulator.Basic
import Projects.Paramodulator.Systems

set_option pp.fieldNotation false

namespace Paramodulator.Test

open Node

def Z := const 0
def S := const 1
def Nat := const 2
def Add := const 3

inductive P : Node → Prop where
  | r0 : P (!! Nat Z)
  | r1 {n} : P (!! Nat n) → P (!! Nat (S n))
  | r2 {n} : P (!! Nat n) → P (!! Add n Z n)
  | r3 {n m r} : P (!! Add n m r) → P (!! Add n (S m) (S r))

@[simp]
def ofNat (n : ℕ) : Node :=
  match n with
  | 0 => Z
  | n + 1 => pair S # ofNat n

def toNat (n : Node) : ℕ :=
  if n = Z then 0 else 1 + match n with
  | 0 => 0
  | pair _ n => toNat n

def IsNat (n : Node) : Prop :=
  P # !! Nat n

@[simp]
theorem toNat_Z : toNat Z = 0 := rfl

@[simp]
theorem toNat_S {n} : toNat (!! S n) = toNat n + 1 := by
  simp [toNat, Z, S]; omega

@[simp]
theorem toNat_ofNat {n} : toNat (ofNat n) = n := by
  induction n <;> simp_all

@[simp]
theorem isNat_Z : IsNat Z := P.r0

@[simp]
theorem isNat_S {n} : IsNat (!! S n) ↔ IsNat n := by
  symm; use P.r1; intro h; cases h; assumption

@[simp]
theorem isNat_ofNat {n} : IsNat (ofNat n) := by
  induction n <;> simp_all

theorem ofNat_toNat_of {n} (h : IsNat n) : ofNat (toNat n) = n := by
  generalize hk : toNat n = k; induction k generalizing n
  · rw [toNat.eq_def] at hk; simp_all
  nm k ih; simp; cases h <;> simp at hk
  nm n h; subst hk; simp; exact ih h rfl

@[simp]
theorem ofNat_toNat_iff {n} : ofNat (toNat n) = n ↔ IsNat n := by
  symm; use ofNat_toNat_of; intro h; rw [←h]; simp

theorem isNat_iff_exi {n} : IsNat n ↔ ∃ k, ofNat k = n := by
  constructor
  · intro h; use toNat n; simpa
  · rintro ⟨k, rfl⟩; simp

@[simp]
theorem P_nat_iff_isNat {n} : P (!! Nat n) ↔ IsNat n := by rfl

theorem Add_iff {n m r} : P (!! Add n m r) ↔ IsNat n ∧ IsNat m ∧ IsNat r ∧
toNat n + toNat m = toNat r := by
  symm; constructor
  · simp [isNat_iff_exi]; rintro n rfl m rfl r rfl; simp; rintro rfl
    induction m; apply P.r2; simp; nm m ih; exact P.r3 ih
  · intro h; generalize hx : (!! Add n m r) = x at h
    induction h generalizing n m r <;> cases hx; simpa
    nm n₁ m₁ r₁ h ih; simp [←add_assoc]; apply ih; simp