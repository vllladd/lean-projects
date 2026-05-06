import Projects.Util

namespace Prover

inductive Univ where
| nat : ℕ → Univ
| var : String → Univ
| succ' : Univ → Univ
| max' : Univ → Univ → Univ
deriving Inhabited, DecidableEq

def Univ.zero : Univ :=
  .nat 0

instance : OfNat Univ 0 := ⟨.zero⟩

def Univ.succ (u : Univ) : Univ :=
  u.succ'

def Univ.max (u v : Univ) : Univ :=
  u.max' v

def Univ.ble (_u _v : Univ) : Bool :=
  true

instance : LE Univ := ⟨(Univ.ble · ·)⟩

instance {u v : Univ} : Decidable (u ≤ v) :=
  inferInstanceAs(Decidable # u.ble v)

inductive Expr where
| var : Univ → String → Expr
| lam : String → Expr → Expr
| app : Expr → Expr → Expr
| eq : Expr → Expr → Expr
deriving Inhabited, DecidableEq

def Expr.univ' (e : Expr) : StateT (Map String Univ) Option Univ := do
  let mp ← get
  match e with
  | var u name =>
    match mp.get? name with
    | none => set # mp.insert name u
    | some v => guard # u == v
    pure u
  | lam name e =>
    set # mp.erase name
    let u := mp.get? name |>.getD 0
    let v ← e.univ'
    pure # u.max v
  | app a b =>
    let u ← a.univ'
    let v ← b.univ'
    guard # v ≤ u
    pure u
  | eq a b =>
    let u ← a.univ'
    let v ← b.univ'
    pure # u.max v

def Expr.univ (e : Expr) : Option Univ :=
  e.univ'.run ∅ |>.map (·.1)