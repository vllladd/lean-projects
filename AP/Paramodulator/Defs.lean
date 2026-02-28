import AP.Util.Finset

namespace Paramodulator

inductive Node where
| nil : Node
| pair : Node → Node → Node
deriving DecidableEq

open Node

declare_syntax_cat node

syntax num : node
syntax ident : node
syntax "(" node node ")" : node
syntax "!!" node : term

macro_rules
  | `(!!($a:node $b:node)) => `(pair (!!$a) (!!$b))
  | `(!!$a:num) => `($a)
  | `(!!$a:ident) => `($a)

instance : Zero Node := ⟨nil⟩
instance : One Node := ⟨!!(0 0)⟩