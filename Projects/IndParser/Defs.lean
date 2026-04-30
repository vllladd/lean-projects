import Projects.Util
import Projects.Temp

namespace IndParser

@[ext]
structure Word where
  (left word right : List ℕ)
deriving Inhabited, DecidableEq

@[ext]
structure Parser where
  words : Set Word
deriving Inhabited

def Word.succ (w : Word) : Word :=
  {w with word := w.word.map .succ}

def Parser.succ (p : Parser) : Parser where
  words := .succ '' p.words

instance : Membership Word Parser where
  mem p w := w ∈ p.words

def Parser.concat (p₁ p₂ : Parser) : Parser where
  words := setOf # λ w => ∃ w₁ ∈ p₁, ∃ w₂ ∈ p₂,
    w = ⟨w₁.left, w₁.word ++ w₂.word, w₂.right⟩ ∧
    w₁.left ++ w₁.word = w₂.left ∧
    w₂.word ++ w₂.right = w₁.right

inductive ExprType where
| par : ExprType
| var : ℕ → ExprType
| fn : ExprType → ExprType → ExprType
deriving Inhabited

inductive Expr where
| ref : String → List Expr → Expr
| ind : List Expr → Expr
| left : Expr
| right : Expr
| concat : Expr → Expr → Expr
deriving Inhabited

@[ext]
structure Ctor where
  types : List ExprType
  left : List Expr
  right : List Expr
deriving Inhabited

@[ext]
structure Def where
  types : List ExprType
  ctors : List Ctor
deriving Inhabited

@[ext]
structure Grammar where
  defs : Map String Def
deriving Inhabited

def ExprType.varsNum : ExprType → ℕ
| .par => 0
| .var i => i
| .fn a b => max a.varsNum b.varsNum

def ExprType.WF (t : ExprType) (mx : ℕ) : Bool :=
  t.varsNum ≤ mx

def specTypes (ts₁ ts₂ : List ExprType) : Option ExprType := do
  guard # ts₁.length = ts₂.length
  none

def Expr.type (mp : Map String (List ExprType)) (vars : List ExprType) : Expr → Option ExprType
| .ref name args => do
  let refTypes ← mp.get? name
  let argTypes ← args.mapM # Expr.type mp vars
  let _ ←  specTypes refTypes argTypes
  pure .par
| _ => none