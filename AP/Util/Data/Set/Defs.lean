import AP.Util

universe u
variable {ι : Type u} {α : ι → Type u} [hhι : LinearOrder ι]

@[simp]
def DMap.listCnd : List (Σ i, α i) → Prop
| (x :: y :: xs) => x.1 < y.1 ∧ listCnd (y :: xs)
| _ => True

@[ext]
structure DMap (ι : Type u) (α : ι → Type u) [LinearOrder ι] : Type u where
  toList : List (Σ i, α i)
  h : DMap.listCnd toList

abbrev Map (ι : Type u) (α : Type u) [LinearOrder ι] : Type u :=
  DMap ι # λ _ => α

namespace DMap

def empty : DMap ι α :=
  ⟨[], trivial⟩

instance : EmptyCollection (DMap ι α) := ⟨DMap.empty⟩

end DMap namespace Map

def empty {α : Type u} : Map ι α := ∅

end Map namespace DMap

def insert' (x : Σ i, α i) : List (Σ i, α i) → List (Σ i, α i)
| [] => [x]
| (y :: xs) => match compare x.1 y.1 with
  | .eq => x :: xs
  | .lt => x :: y :: xs
  | .gt => y :: insert' x xs

@[simp]
def ofList' (xs : List (Σ i, α i)) : List (Σ i, α i) → List (Σ i, α i)
| [] => xs
| (y :: ys) => ofList' (insert' y xs) ys

@[simp]
def get' (i : ι) : List (Σ i, α i) → Option (α i)
| [] => none
| (⟨j, x⟩ :: xs) => if h : i = j then some # h ▸ x else get' i xs

@[simp]
def mem' (i : ι) : List (Σ i, α i) → Bool
| [] => false
| (⟨j, _⟩ :: xs) => if i = j then true else mem' i xs