import AP.Util

namespace Paramodulator

inductive Node where
| nil : Node
| pair : Node → Node → Node
deriving DecidableEq

open Node

declare_syntax_cat node

syntax num : node
syntax ident : node
syntax node node : node
syntax "(" node ")" : node
syntax "!!" node : term

macro_rules
  | `(!!$a:node $b:node) => `(pair (!!$a) (!!$b))
  | `(!!($a:node)) => `(!!$a)
  | `(!!$a:num) => `($a)
  | `(!!$a:ident) => `($a)

instance : Zero Node := ⟨nil⟩
instance : One Node := ⟨!!(0 0)⟩

@[simp]
def const (n : ℕ) : Node :=
  match n with
  | 0 => 1
  | n + 1 => pair 0 # const n

@[simp]
def Node.left (x : Node) : Node :=
  match x with
  | .pair x _ => x
  | _ => 0

@[simp]
def Node.right (x : Node) : Node :=
  match x with
  | .pair _ y => y
  | _ => 0