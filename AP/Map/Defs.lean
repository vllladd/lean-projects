import AP.Util

@[simp]
def Map.listCnd.{u} {ι α : Type u} [LinearOrder ι] [DecidableEq α] : List (ι × α) → Prop
| (x :: y :: xs) => x.1 < y.1 ∧ Map.listCnd (y :: xs)
| _ => True

@[ext]
structure Map.{u} (ι α : Type u) [LinearOrder ι] [DecidableEq α] : Type u where
  toList : List (ι × α)
  h : Map.listCnd toList

namespace Map

set_option linter.unusedVariables false
universe u
variable {ι α : Type u} [hhι : LinearOrder ι] [hhα : DecidableEq α]
set_option linter.unusedSectionVars true

def empty : Map ι α :=
  ⟨[], trivial⟩

instance : EmptyCollection (Map ι α) := ⟨Map.empty⟩

def insert' (x : ι × α) : List (ι × α) → List (ι × α)
| [] => [x]
| (y :: xs) => match compare x.1 y.1 with
  | .eq => x :: xs
  | .lt => x :: y :: xs
  | .gt => y :: insert' x xs

@[simp]
def ofList' (xs : List (ι × α)) : List (ι × α) → List (ι × α)
| [] => xs
| (y :: ys) => ofList' (insert' y xs) ys

def lookup' (i : ι) : List (ι × α) → Option α
| [] => none
| ((j, x) :: xs) => if i == j then some x else lookup' i xs