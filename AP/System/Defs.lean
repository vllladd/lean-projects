import AP.Util

structure System (S T : Type) : Type where
  tr : S → T → Option S

namespace System

def valid_tr {S T} (sys : System S T) (s : S) (t : T) : Prop :=
  (sys.tr s t).isSome

def has_tr {S T} (sys : System S T) (s : S) : Prop :=
  ∃ t, sys.valid_tr s t

@[class]
structure DecidableHasTr {S T} (sys : System S T) : Type where
  h : Π s, Decidable # sys.has_tr s

@[class]
structure TrFn {S T} (sys : System S T) (f : S → T) : Prop where
  h : ∀ s, sys.has_tr s → sys.valid_tr s (f s)

def tr! {S T} (sys : System S T) (s : S) (t : T) : S :=
  (sys.tr s t).getD s

def trs {S T} (sys : System S T) (s : S) : List T → S × List T
| [] => (s, [])
| (t :: ts) => match sys.tr s t with
  | none => (s, t :: ts)
  | some s₁ => sys.trs s₁ ts

def simulate {S T} (sys : System S T) (f : S → T) (s : S) : ℕ → S × ℕ
| 0 => (s, 0)
| n + 1 => match sys.tr s # f s with
  | none => (s, n + 1)
  | some s₁ => sys.simulate f s₁ n

@[class]
inductive Reachable {S T} (sys : System S T) : S → S → Prop where
| refl : ∀ {a}, sys.Reachable a a
| step : ∀ {a b c t}, sys.tr b t = some c → sys.Reachable a b → sys.Reachable a c