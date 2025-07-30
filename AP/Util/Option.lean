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