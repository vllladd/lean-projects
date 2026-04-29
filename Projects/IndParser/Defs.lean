import Projects.Util

namespace IndParser

@[ext]
structure Word where
  xs : List ℕ
deriving Inhabited, DecidableEq

@[ext]
structure Parser where
  words : Set Word
deriving Inhabited

def Word.succ (w : Word) : Word where
  xs := w.xs.map .succ

def Parser.succ (par : Parser) : Parser where
  words := .succ '' par.words

@[class]
inductive ParType : Type → Type 1 where
| par : ParType Parser
| fn {α β} : ParType α → ParType α → ParType (α → β)

def Word.concat (w₁ w₂ : Word) : Word where
  xs := w₁.xs ++ w₂.xs

def Parser.concat (par₁ par₂ : Parser) : Parser where
  words := {w | ∃ w₁ ∈ par₁.words, ∃ w₂ ∈ par₂.words, w₁.concat w₂ = w}

def Parser.inter (par₁ par₂ : Parser) : Parser where
  words := par₁.words ∩ par₂.words

def Parser.univ : Parser where
  words := Set.univ

def FinFn.{u, v} {n : ℕ} (α : Fin n → Type u) (β : Type v) : Type (max u v + 1) :=
  match n with
  | 0 => ULift.{max u v + 1} β
  | n + 1 => α 0 → FinFn (λ (k : Fin n) => α ⟨k + 1, by omega⟩) β

def mkFinFn.{u, v} {n : ℕ} {α : Fin n → Type u} {β : Type v}
(f : (∀ n, α n) → β) : FinFn α β := by
  induction n
  · exact .up # f nofun
  nm n ih
  intro x
  specialize @ih _ _
  · rintro ⟨k, hk⟩
    exact α ⟨k + 1, by omega⟩
  · intro ps
    apply f
    rintro ⟨k, hk⟩
    cases k
    · exact x
    nm k
    specialize ps ⟨k, by omega⟩
    convert ps
  exact ih

def callFinFn.{u, v} {n : ℕ} {α : Fin n → Type u} {β : Type v}
(f : FinFn α β) (ps : ∀ n, α n) : β :=
  match n with
  | 0 => f.down
  | n + 1 => callFinFn (f (ps 0)) (λ (k : Fin n) => ps ⟨k + 1, by omega⟩)

@[ext]
structure IndSpec : Type 1 where
  (tn cn : ℕ)
  ts : Fin tn → Type
  ctns : Fin cn → ℕ
  cts : ∀ n, Fin (ctns n) → Type
  cs : FinFn ts Parser → ∀ n, FinFn (cts n) (List Parser) × ∀ n, ts n
  H₁ : ∀ n, ParType (ts n) := by infer_instance
  H₂ : ∀ n k, ParType (cts n k) := by infer_instance

inductive IndSpec.Ind (spec : IndSpec) : (∀ n, spec.ts n) → Word → Prop where
| mk (n : Fin spec.cn) (ps : ∀ k, spec.cts n k) (xs : List Parser) (ys : ∀ n, spec.ts n) 
  (part : (∀ n, spec.ts n) → Word → Prop) (ind : FinFn spec.ts Parser) (w : Word) :
  (∀ ps w, part ps w → Ind spec ps w) → mkFinFn (λ ps => .mk {w | part ps w}) = ind →
  callFinFn (spec.cs ind n |>.1) ps = xs → (spec.cs ind n).2 = ys →
  w ∈ (xs.foldr Parser.inter Parser.univ).words → Ind spec ys default

def IndSpec.toParser (spec : IndSpec) : FinFn spec.ts Parser :=
  mkFinFn λ ps => .mk {w | spec.Ind ps w}