import Projects.Util

namespace Esolangs.Lang_001

inductive Builtin : Type where
| succ : Builtin
| sub : Builtin
deriving Inhabited, Fintype, DecidableEq

inductive Target : Type where
| builtin : Builtin → Target
| custom : ℕ → Target
deriving Inhabited, DecidableEq

inductive Expr : Type where
| arg : ℕ → Expr
| call : Target → List Expr → Expr
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

def Prog.def (prog : Prog) (i : ℕ) : Def :=
  prog.defs[i]!

def Prog.main (prog : Prog) : Def :=
  prog.def 0

def Prog.HasDef (prog : Prog) (i : ℕ) : Prop :=
  i < prog.defs.length

def Prog.arity (prog : Prog) (i : ℕ) : ℕ :=
  prog.def i |>.arity

def Prog.expr (prog : Prog) (i : ℕ) : Expr :=
  prog.def i |>.expr

def Builtin.arity (bn : Builtin) : ℕ :=
  match bn with
  | .succ => 1
  | .sub => 2

def Target.arity (t : Target) (prog : Prog) : ℕ :=
  match t with
  | .builtin bn => bn.arity
  | .custom i => prog.arity i

def Prog.HasTarget (prog : Prog) (t : Target) : Prop :=
  match t with
  | .builtin _ => True
  | .custom i => prog.HasDef i

def Expr.WF (prog : Prog) (arity : ℕ) (e : Expr) : Prop :=
  match e with
  | .arg i => i < arity
  | .call t args => prog.HasTarget t ∧ args.length = t.arity prog ∧
    ∀ e ∈ args, e.WF prog arity

@[simp]
def Def.WF (prog : Prog) (d : Def) : Prop :=
  d.expr.WF prog d.arity

def Builtin.f (bn : Builtin) (args : List ℕ) : ℕ :=
  match bn with
  | .succ => args[0]! + 1
  | .sub => args[0]! - args[1]!

def Target.f (t : Target) (fs : List (List ℕ → ℕ)) : List ℕ → ℕ :=
  match t with
  | .builtin bn => bn.f
  | .custom i => fs[i]!

def Expr.eval (e : Expr) (prog : Prog) (fs : List (List ℕ → ℕ)) (args : List ℕ) : ℕ :=
  match e with
  | .arg i => args[i]!
  | .call t xs => t.f fs # xs.map λ x => x.eval prog fs args

structure Prog.Compatible (prog : Prog) (fs : List (List ℕ → ℕ)) : Prop where
  length_fs : fs.length = prog.defs.length
  eq_default_of_ne_arity ⦃i⦄ : i < prog.defs.length → ∀ ⦃xs : List ℕ⦄,
    xs.length ≠ prog.arity i → fs[i]! xs = default
  eval_eq ⦃i⦄ : i < prog.defs.length → ∀ ⦃xs : List ℕ⦄, xs.length = prog.arity i →
    fs[i]! xs = (prog.expr i).eval prog fs xs

class Prog.WF (prog : Prog) : Prop where
  defs_ne_nil : prog.defs ≠ []
  arity_main : prog.main.arity = 1
  wf_def ⦃d⦄ : d ∈ prog.defs → d.WF prog
  exiu_compatible : ∃! fs, prog.Compatible fs

open Classical in noncomputable
def Prog.fs (prog : Prog) : List (List ℕ → ℕ) :=
  τ fs, prog.Compatible fs

open Classical in noncomputable
def Prog.eval (prog : Prog) (i : ℕ) (xs : List ℕ) : ℕ :=
  prog.fs[i]! xs

open Classical in noncomputable
def Prog.run (prog : Prog) (n : ℕ) : ℕ :=
  prog.eval 0 [n]

def fn (arity : ℕ) (f : List ℕ → ℕ) (xs : List ℕ) : ℕ :=
  if xs.length ≠ arity then default else f xs

def Builtin.show (b : Builtin) : String :=
  match b with
  | .succ => "succ"
  | .sub => "sub"

def Target.show (t : Target) (defNames : Array String) : String :=
  match t with
  | .builtin b => b.show
  | .custom i => defNames[i - 1]!

def Expr.show (e : Expr) (defNames argNames : Array String) : String :=
  match e with
  | .arg i => argNames[i]!
  | .call t args =>
    t.show defNames ++ if args.length = 0 then "" else
      "(" ++ ", ".intercalate (args.map (·.show defNames argNames)) ++ ")"

def Def.show (d : Def) (defNames : Array String) (name : String) : String :=
  let argNames := List.range d.arity |>.map λ i => String.ofList [.ofNat # 97 + i]
  name ++ "".intercalate (argNames.map (" " ++ ·)) ++ " := " ++
    d.expr.show defNames ⟨argNames⟩

def Prog.show (prog : Prog) (defNames : Array String) : String :=
  match prog.defs with
  | mainDef :: defs =>
    let xs := defs.zipWith (Def.show · defNames) defNames.toList
    "\n".intercalate # xs ++ [mainDef.show defNames "main"]
  | _ => ""