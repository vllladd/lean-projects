import AP.Util.Main

@[ext]
structure System.{u} (S T : Type u) where
  initial : Set S
  tr : S → T → Option S

namespace System

universe u
variable {S T : Type u} (sys : System S T)

@[simp]
def trTo (s : S) (t : T) (s₁ : S) : Prop :=
  sys.tr s t = some s₁

def validTr (s : S) (t : T) : Prop :=
  ∃ s₁, sys.trTo s t s₁

def hasTr (s : S) : Prop :=
  ∃ t, sys.validTr s t

@[class]
structure DecidableHasTr where
  h : Π s, Decidable # sys.hasTr s

@[class]
structure SimFn (f : S → T) : Prop where
  h : ∀ {s}, sys.hasTr s → sys.validTr s (f s)

def tr! (s : S) (t : T) : S :=
  (sys.tr s t).getD s

@[simp]
def trs {S T : Type u} (sys : System S T) (s : S) : List T → S × List T
| [] => (s, [])
| (t :: ts) => match sys.tr s t with
  | none => (s, t :: ts)
  | some s₁ => sys.trs s₁ ts

@[simp]
def simulate {S T : Type u} (sys : System S T) (f : S → T) (s : S) : ℕ → S × ℕ
| 0 => (s, 0)
| n + 1 => match sys.tr s # f s with
  | none => (s, n + 1)
  | some s₁ => sys.simulate f s₁ n

def simp_path' (sys : System S T) (a : S) (ts : List T) : Prop :=
  ∀ (xs ys : List T), xs <+: ts → ys <+: ts →
  (sys.trs a xs).1 = (sys.trs a ys).1 → xs = ys

def simp_path (sys : System S T) (a : S) (ts : List T) (b : S) : Prop :=
  sys.simp_path' a ts ∧ sys.trs a ts = (b, [])

@[class]
inductive Reachable {S T : Type u} (sys : System S T) : S → S → Prop where
| refl : ∀ {a}, sys.Reachable a a
| step : ∀ {a b c t}, sys.trTo a t b → sys.Reachable b c → sys.Reachable a c

@[class]
structure Acyclic (s : S) : Prop where
  h : ∀ {a b t}, sys.Reachable s a → sys.trTo a t b → ¬sys.Reachable b a

@[class]
structure Tree (s : S) : Prop where
  h : ∀ {ts₁ ts₂}, sys.trs s ts₁ = sys.trs s ts₂ → ts₁ = ts₂

@[class]
structure Initial (s : S) : Prop where
  h : s ∈ sys.initial

@[class]
inductive Valid (s' : S) : Prop where
| mk : ∀ {s} [sys.Initial s], sys.Reachable s s' → Valid s'