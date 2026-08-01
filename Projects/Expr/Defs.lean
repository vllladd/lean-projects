import Projects.Util

inductive Expr where
| nil : Expr
| pair : Expr → Expr → Expr
deriving Inhabited, DecidableEq

namespace Expr

variable {a b c : Expr}

def isNil (a : Expr) : Prop :=
  match a with | .nil => True | _ => False

def isPair (a : Expr) : Prop :=
  match a with | .nil => False | _ => True

instance : Decidable (isNil a) :=
  match a with
  | .nil => .isTrue # by simp [isNil]
  | pair _ _ => .isFalse # by simp [isNil]

instance : Decidable (isPair a) :=
  match a with
  | .nil => .isFalse # by simp [isPair]
  | pair _ _ => .isTrue # by simp [isPair]

instance : CoeSort Expr Prop := ⟨isPair⟩

def fst (a : Expr) : Expr :=
  match a with | .nil => .nil | .pair a _ => a

def snd (a : Expr) : Expr :=
  match a with | .nil => .nil | .pair _ b => b

def toPair (a : Expr) : Expr :=
  .pair a.fst a.snd

def ite (a b c : Expr) : Expr :=
  if a.isPair then b else c

def T : Expr := pair nil nil
def F : Expr := nil

def toProp (a : Expr) : Expr :=
  ite a T F

def not (a : Expr) : Expr :=
  ite a F T

def imp (a b : Expr) : Expr :=
  ite a (toProp b) T

def or (a b : Expr) : Expr :=
  ite a T (toProp b)

def and (a b : Expr) : Expr :=
  ite a (toProp b) F

def iff (a b : Expr) : Expr :=
  ite a (toProp b) (not b)

def eq (a b : Expr) : Expr :=
  if a = b then T else F

def sle (a b : Expr) : Expr :=
  if a = b then T else match a, b with
  | nil, _ => T
  | _, nil => F
  | _, pair x y => a.sle x |>.or # a.sle y
  
def slt (a b : Expr) : Expr :=
  match b with
  | nil => F
  | pair c d => (sle a c).or (sle a d)

def depth' (a : Expr) : ℕ :=
  match a with
  | nil => 0
  | pair x y => 1 + max x.depth' y.depth'

instance : LE Expr := ⟨λ a b => a.sle b⟩
instance : LT Expr := ⟨λ a b => a.slt b⟩

instance : DecidableLE Expr := λ a b => inferInstanceAs(Decidable # a.sle b)
instance : DecidableLT Expr := λ a b => inferInstanceAs(Decidable # a.slt b)