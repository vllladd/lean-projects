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

def Expr.WF (prog : Prog) (arity : ℕ) (e : Expr) : Prop :=
  match e with
  | .arg i => i ≤ arity
  | .call i args => prog.HasDef i ∧ ∀ ⦃j⦄,
    if prog.arity i ≤ j then args j = default
    else args j |>.WF prog arity

def Def.WF (prog : Prog) (d : Def) : Prop :=
  d.expr.WF prog d.arity

class Prog.WF (prog : Prog) : Prop where
  defs_ne_nil : prog.defs ≠ []
  arity_main : prog.main.arity = 1
  wf_def ⦃d⦄ : d ∈ prog.defs → d.WF prog