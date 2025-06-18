import AP.Util

structure System (S T : Type) : Type where
  tr : S → T → Option S

namespace System

def valid_tr {S T} (sys : System S T) (s : S) (t : T) : Prop :=
  ∃ s₁, sys.tr s t = some s₁

def has_tr {S T} (sys : System S T) (s : S) : Prop :=
  ∃ t, sys.valid_tr s t

@[class]
structure DecidableHasTr {S T} (sys : System S T) : Type where
  h : Π s, Decidable # sys.has_tr s

@[class]
structure SimFn {S T} (sys : System S T) (f : S → T) : Prop where
  h : ∀ s, sys.has_tr s → sys.valid_tr s (f s)

def tr! {S T} (sys : System S T) (s : S) (t : T) : S :=
  (sys.tr s t).getD s

@[simp]
def trs {S T} (sys : System S T) (s : S) : List T → S × List T
| [] => (s, [])
| (t :: ts) => match sys.tr s t with
  | none => (s, t :: ts)
  | some s₁ => sys.trs s₁ ts

@[simp]
def simulate {S T} (sys : System S T) (f : S → T) (s : S) : ℕ → S × ℕ
| 0 => (s, 0)
| n + 1 => match sys.tr s # f s with
  | none => (s, n + 1)
  | some s₁ => sys.simulate f s₁ n

@[class]
inductive Reachable {S T} (sys : System S T) : S → S → Prop where
| refl : ∀ {a}, sys.Reachable a a
| step : ∀ {a b c t}, sys.tr a t = some b → sys.Reachable b c → sys.Reachable a c

@[class]
structure SimInj {S T} (sys : System S T) (s : S) : Prop where
  h : ∀ f [sys.SimFn f] n m,
    let (sn, n₁) := sys.simulate f s n
    let (sm, m₁) := sys.simulate f s m
    n₁ = 0 → m₁ = 0 → sn = sm → n = m