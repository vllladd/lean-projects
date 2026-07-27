import Projects.Util.Nat
import Projects.Util.Option
import Projects.Util.Algebra
import Projects.Util.Function

import Init.Data.List.Perm
import Mathlib.Data.List.Lex
import Init.Data.List.Sublist
import Mathlib.Data.List.Range
import Mathlib.Data.List.Intervals
import Mathlib.Data.List.TakeWhile

instance {α : Type*} [ha : LinearOrder α] : Std.LawfulOrderMax α where
  max_eq_or := by simp [le_total]
  max_le_iff := by simp

def mkList {α : Type*} (n : ℕ) (f : ℕ → α) : List α :=
  List.range n |>.map f

namespace List

variable {α β γ : Type*}

@[simp]
def init {α : Type*} : List α → List α
| [] => []
| [_] => []
| (x :: ys) => x :: ys.init

def combinations (xs : List α) (n : ℕ) : List (List α) :=
  sequence # replicate n xs

def atMostOne : List Bool → Bool
| [] => true
| b :: bs => if b then !bs.or else bs.atMostOne

@[simp]
def mapWith (xs : List α) (f : (x : α) → x ∈ xs → β) : List β :=
  match h : xs with
  | [] => []
  | x :: ys => f x (by simp) :: ys.mapWith (λ y h₁ => f y # by simp [h₁])

open Classical in noncomputable
def dfltMapWith {xs : List α} (f : (x : α) → x ∈ xs → β) (h : xs ≠ []) : β :=
  match h₁ : xs with
  | [] => by simp at h
  | x :: _ => Nonempty.some ⟨f x # by simp⟩

@[simp]
def foldlWith {β : Sort*} (xs : List α) (f : β → (x : α) → x ∈ xs → β) (z : β) : β :=
  match h : xs with
  | [] => z
  | x :: ys => ys.foldlWith (λ acc y h₁ => f acc y (by simp [h₁])) # f z x (by simp)

def toSet (xs : List α) : Set α := {x | x ∈ xs}

def toVec (xs : List α) : Fin xs.length → α :=
  (xs[·])

def min!! [Min α] [Top α] (xs : List α) : α :=
  xs.min?.getD ⊤

def max!! [Max α] [Bot α] (xs : List α) : α :=
  xs.max?.getD ⊥