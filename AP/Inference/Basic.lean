import AP.Util

namespace Inference

inductive Expr where
| var : ℕ → Expr
| not : Expr → Expr
| imp : Expr → Expr → Expr

inductive Proof : Expr → Prop where
| ax₁ : ∀ (P Q : Expr), Proof # .imp P # .imp Q P
| ax₂ : ∀ (P Q R : Expr), Proof # .imp
  (.imp P # .imp Q R) # .imp (.imp P Q) # .imp P R
| ax₃ : ∀ (P Q : Expr), Proof # .imp
  (.imp (.not P) (.not Q)) # .imp Q P
| mp : ∀ {P Q}, Proof (.imp P Q) → Proof P → Proof Q

open Proof

-----

theorem mp' {P Q} (h₁ : Proof P) (h₂ : Proof # .imp P Q) : Proof Q :=
  mp h₂ h₁

theorem imp_refl : Proof # .imp (.var 0) (.var 0) := by
  generalize Expr.var 0 = P
  apply mp' # ax₁ P P
  apply mp' # ax₁ P (.imp P P)
  exact ax₂ P (.imp P P) P