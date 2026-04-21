import Projects.Util

namespace SK

inductive Expr where
| K : Expr
| S : Expr
| App : Expr → Expr → Expr
deriving Inhabited, DecidableEq, Repr
open Expr

infixl:1000 " %% " => App

def I : Expr :=
  S %% K %% K

inductive Reduces : Expr → Expr → Prop where
| rfl {a} : Reduces a a
| trans {a b c} : Reduces a b → Reduces b c → Reduces a c
| app {a b a' b'} : Reduces a a' → Reduces b b' → Reduces (a %% b) (a' %% b')
| k {a b} : Reduces (K %% a %% b) a
| s {a b c} : Reduces (S %% a %% b %% c) (a %% c %% (b %% c))

attribute [simp] Reduces.rfl
attribute [refl] Reduces.rfl
attribute [trans] Reduces.trans
attribute [simp] Reduces.k
attribute [simp] Reduces.s

inductive ExprNe : Expr → Expr → Prop where
| comb : ExprNe K S
| reduce {a b a' b'} : Reduces a a' → Reduces b b' → ExprNe a' b' → ExprNe a b
| ext {a b c x y} : Reduces (a %% c) x → Reduces (b %% c) y → ExprNe x y → ExprNe a b

attribute [simp] ExprNe.comb

def ExprEq (a b : Expr) : Prop :=
  ¬ExprNe a b

class Reduced (a : Expr) : Prop where
  h {b} : Reduces a b → a = b

def KI : Expr :=
  K %% I

def KK : Expr :=
  K %% K