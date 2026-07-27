import Projects.Util

def mkList {α : Type*} (n : ℕ) (f : ℕ → α) : List α :=
  List.range n |>.map f

instance : LinearOrder String where
  le_refl := by grind
  le_trans := by grind
  le_antisymm := by grind
  le_total := by grind
  toDecidableLE := inferInstance
  lt_iff_le_not_ge := by grind
  min_def := by
    intro a b; change ite _ _ _ = _; congr
    change (Ordering.isLE (ite _ _ _) = _) = _
    have h : (a < b) = ¬(b ≤ a); change _ = ¬¬_; simp
    simp [apply_ite (f := Ordering.isLE)]; grind
  max_def := by
    intro a b; change ite _ _ _ = _; congr
    change (Ordering.isLE (ite _ _ _) = _) = _
    have h : (a < b) = ¬(b ≤ a); change _ = ¬¬_; simp
    simp [apply_ite (f := Ordering.isLE)]; grind
  compare_eq_compareOfLessAndEq := by
    intro a b; change compareOfLessAndEq _ _ = _; congr

-- namespace List
-- 
-- variable {α β γ : Type*}
-- variable {xs ys zs : List α}
-- 
-- -- #check 0 #exit
-- 
-- end List

-- #check 0 #exit

namespace Finset

variable {α β γ : Type*}
variable {s s₁ s₂ s₃ : Finset α}

def fold' (s : Finset α) (f : β → α → β) (z : β)
(h : ∀ {acc x y}, f (f acc x) y = f (f acc y) x) : β :=
  haveI : RightCommutative f := ⟨@h⟩; s.val.foldl f z

-- #check 0 #exit

end Finset

-- namespace Map
-- 
-- open Std
-- 
-- universe u v w
-- variable {α : Type u} {β : Type v} {γ : Type w}
-- variable [hh₁ : DecidableEq α] [hh₂ : Hashable α]
-- variable {mp : Map α β}
-- variable [ha : LinearOrder α]
-- omit ha
-- 
-- def ofFinset (s : Finset (α × β)) : Map α β :=
--   s.fold' (z := ∅) (λ m ⟨k, v⟩ => m.insert k v) #
--     by
--       intro m x y
--       simp
--       rw [insert_comm]
-- 
-- #check 0 #exit
-- 
-- end Map

namespace Esolangs.Cornucopia

def mainName : String := "main"

inductive Builtin : Type where
| succ : Builtin
| sub : Builtin
deriving Inhabited, Fintype, DecidableEq

@[ext]
structure BuiltinInfo : Type where
  name : String
  arity : ℕ
  eval : List ℕ → ℕ
deriving Inhabited

inductive Expr : Type where
| arg : ℕ → Expr
| call : String → List Expr → Expr
deriving Inhabited

@[ext]
structure Def : Type where
  arity : ℕ
  expr : Expr
deriving Inhabited

@[ext]
structure Prog : Type where
  defs : Map String Def
deriving Inhabited

-----

-- #check 0 #exit

def fn (arity : ℕ) (f : List ℕ → ℕ) (xs : List ℕ) : ℕ :=
  if xs.length ≠ arity then 0 else f xs

def builtins : List Builtin :=
  [.succ, .sub]

def Builtin.info (b : Builtin) : BuiltinInfo :=
  match b with
  | .succ => {name := "succ", arity := 1, eval xs := xs[0]! + 1}
  | .sub => {name := "sub", arity := 2, eval xs := xs[0]! - xs[1]!}

def Builtin.name (b : Builtin) : String := b.info.name
def Builtin.arity (b : Builtin) : ℕ := b.info.arity
def Builtin.eval (b : Builtin) : List ℕ → ℕ := fn b.arity b.info.eval

def Builtin.expr (b : Builtin) : Expr :=
  .call b.name # mkList b.arity .arg

def Builtin.def (b : Builtin) : Def where
  arity := b.arity
  expr := b.expr

def Builtin.namesMap : Map String Builtin :=
  .ofList # builtins.map λ b => (b.name, b)

def IsBuiltin (name : String) : Prop :=
  ∃ (b : Builtin), b.name = name

def Prog.def? (prog : Prog) (name : String) : Option Def :=
  prog.defs.get? name

def Prog.def (prog : Prog) (name : String) : Def :=
  prog.defs.get! name

def builtinDefs : Map String Def :=
  .ofList # builtins.map (λ b => (b.name, b.def))

def builtinFs : Map String (List ℕ → ℕ) :=
  .ofList # builtins.map (λ b => (b.name, b.eval))

def Prog.ofDefs (defs : List (String × Def)) : Prog where
  defs := builtinDefs ∪ .ofList defs

def Prog.main (prog : Prog) : Def :=
  prog.def mainName

def Prog.HasDef (prog : Prog) (name : String) : Prop :=
  name ∈ prog.defs

def Prog.arity (prog : Prog) (name : String) : ℕ :=
  prog.def name |>.arity

def Prog.expr (prog : Prog) (name : String) : Expr :=
  prog.def name |>.expr

def Expr.WF (prog : Prog) (arity : ℕ) (e : Expr) : Prop :=
  match e with
  | .arg i => i < arity
  | .call t args => prog.HasDef t ∧ args.length = prog.arity t ∧
    ∀ e ∈ args, e.WF prog arity

@[simp]
def Def.WF (prog : Prog) (d : Def) : Prop :=
  d.expr.WF prog d.arity

def Expr.eval (e : Expr) (prog : Prog) (fs : Map String (List ℕ → ℕ)) (args : List ℕ) : ℕ :=
  match e with
  | .arg i => args[i]!
  | .call t xs => fs.get! t # xs.map λ x => x.eval prog fs args

structure Prog.Compatible (prog : Prog) (fs : Map String (List ℕ → ℕ)) : Prop where
  keys_fs : fs.keys = prog.defs.keys
  eval_of_ne_arity ⦃name⦄ : prog.HasDef name → ∀ ⦃xs : List ℕ⦄,
    xs.length ≠ prog.arity name → fs.get! name xs = 0
  eval_eq ⦃name⦄ : prog.HasDef name → ∀ ⦃xs : List ℕ⦄, xs.length = prog.arity name →
    fs.get! name xs = (prog.expr name).eval prog fs xs

class Prog.WF (prog : Prog) : Prop where
  def?_builtin {b : Builtin} : prog.def? b.name = some b.def
  has_main : prog.HasDef mainName
  arity_main : prog.main.arity = 1
  wf_def ⦃name d⦄ : prog.def? name = some d → d.WF prog
  exiu_compatible : ∃! fs, prog.Compatible fs

in noncomputable
def Prog.fs (prog : Prog) : Map String (List ℕ → ℕ) :=
  τ fs, prog.Compatible fs

in noncomputable
def Prog.eval (prog : Prog) (name : String) (xs : List ℕ) : ℕ :=
  prog.fs.get! name xs

in noncomputable
def Prog.run (prog : Prog) (n : ℕ) : ℕ :=
  prog.eval mainName [n]

def Expr.show (e : Expr) (argNames : Array String) : String :=
  match e with
  | .arg i => argNames[i]!
  | .call t args =>
    t ++ if args.length = 0 then "" else
    "(" ++ ", ".intercalate (args.map (·.show argNames)) ++ ")"

def Def.show (d : Def) (name : String) : String :=
  let argNamesList := mkList d.arity λ i => String.ofList [.ofNat # 97 + i]
  let argNames := .mk argNamesList
  let argsStr := if d.arity = 0 then "" else
    "(" ++ "".intercalate (argNamesList.map (", " ++ ·)) ++ ")"
  name ++ argsStr ++ " := " ++ d.expr.show argNames

def Prog.show (prog : Prog) (defNames : List String) : String :=
  if ¬defNames.Perm prog.defs.keys then "/" else
  "\n".intercalate # defNames.map # λ name => prog.def name |>.show name