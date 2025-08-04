import AP.Util.Function

namespace Option

@[simp]
theorem failure_bind {α β : Type*} {f : α → Option β} :
(failure : Option α).bind f = none := rfl

@[simp]
theorem exists_eq_some_of_ne_none {α : Type*} {x : Option α}
(h : x ≠ none) : ∃ y, x = some y := by rwa [←ne_none_iff_exists']

@[simp]
theorem guard_bind_eq_some_iff {α : Type*} {P : Prop} [Decidable P]
{f : Unit → Option α} {x} :
(_root_.guard P : Option Unit).bind f = some x ↔ P ∧ f () = some x := by
  by_cases h : P <;> simp [h]

@[simp]
theorem get!_with_bot_some {α : Type*} [Inhabited α] {x : α} :
(WithBot.some x).get! = x := rfl

theorem eq_iff_of_subsingleton {α : Type*} [ha : Subsingleton α]
{x y : Option α} : x = y ↔ (x.isSome ↔ y.isSome) := by
  rcases x with ⟨⟩ | x <;> rcases y with ⟨⟩ | y <;> simp
  apply ha.1

@[simp]
theorem bind_eq_some_iff' {α β : Type*} {x : Option α} {y} {f : α → Option β} :
x.bind f = some y ↔ ∃ a, x = some a ∧ f a = some y :=
  bind_eq_some_iff

theorem bind_dite {α β : Type*} {P} [hp : Decidable P]
{f : P → Option α} {g : ¬P → Option α} {r : α → Option β} :
(if h : P then f h else g h).bind r = if h : P then (f h).bind r else (g h).bind r := by
  split_ifs <;> simp

theorem bind_ite {α β : Type*} {P} [hp : Decidable P]
{x y : Option α} {f : α → Option β} :
(if P then x else y).bind f = if P then x.bind f else y.bind f := by
  split_ifs <;> simp