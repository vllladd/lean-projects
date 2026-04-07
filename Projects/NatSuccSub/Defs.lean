import Projects.Util

namespace NatSuccSub

inductive Expr : Type where
| arg : ℕ → Expr
| call : ℕ → (ℕ → Expr) → Expr
deriving Inhabited

@[ext]
structure Def : Type where
  arity : ℕ
  expr : Expr
deriving Inhabited

@[ext]
structure Prog : Type where
  defs : List Def
deriving Inhabited

-----

def Def.succ : Def where
  arity := 1
  expr := default

def Def.sub : Def where
  arity := 2
  expr := default

def Prog.def (prog : Prog) (i : ℕ) : Def :=
  match i with
  | 0 => Def.succ
  | 1 => Def.sub
  | i + 2 => prog.defs[i]!

def Prog.main (prog : Prog) : Def :=
  prog.def 0

def Prog.defsNum (prog : Prog) : ℕ :=
  prog.defs.length + 2

def Prog.HasDef (prog : Prog) (i : ℕ) : Prop :=
  i < prog.defsNum

def Prog.arity (prog : Prog) (i : ℕ) : ℕ :=
  prog.def i |>.arity

def Prog.expr (prog : Prog) (i : ℕ) : Expr :=
  prog.def i |>.expr

def Expr.WF (prog : Prog) (arity : ℕ) (e : Expr) : Prop :=
  match e with
  | .arg i => i ≤ arity
  | .call i args => prog.HasDef i ∧ ∀ ⦃j⦄,
    if prog.arity i ≤ j then args j = default
    else args j |>.WF prog arity

def Def.WF (prog : Prog) (d : Def) : Prop :=
  d.expr.WF prog d.arity

def Expr.eval (e : Expr) (prog : Prog) (fs : List (List ℕ → ℕ)) (args : List ℕ) : ℕ :=
  match e with
  | .arg i => args[i]!
  | .call i xs => fs[i]! # List.range (prog.arity i)
    |>.map λ i => xs i |>.eval prog fs args

structure Prog.Compatible (prog : Prog) (fs : List (List ℕ → ℕ)) : Prop where
  length_fs : fs.length = prog.defs.length
  eq_default_of_ne_arity ⦃i⦄ : i < prog.defs.length → ∀ ⦃xs : List ℕ⦄,
    xs.length ≠ prog.arity i → fs[i]! xs = default
  eval_eq ⦃i⦄ : i < prog.defs.length → ∀ ⦃xs : List ℕ⦄, xs.length = prog.arity i →
    (prog.expr i).eval prog fs xs = fs[i]! xs

class Prog.WF (prog : Prog) : Prop where
  defs_ne_nil : prog.defs ≠ []
  arity_main : prog.main.arity = 1
  wf_def ⦃d⦄ : d ∈ prog.defs → d.WF prog
  eq_of_compatible ⦃f g⦄ : prog.Compatible f → prog.Compatible g → f = g