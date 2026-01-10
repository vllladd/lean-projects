import AP.Util.Function

namespace Option

variable {α β γ : Type*}

def getd [Inhabited α] (x : Option α) :=
  match x with
  | .none => default
  | some x => x

-----

@[simp]
theorem failure_bind {f : α → Option β} :
(failure : Option α).bind f = none := rfl

@[simp]
theorem exists_eq_some_of_ne_none {x : Option α}
(h : x ≠ none) : ∃ y, x = some y := by rwa [←ne_none_iff_exists']

@[simp]
theorem guard_bind_eq_some_iff {P : Prop} [Decidable P]
{f : Unit → Option α} {x} :
(_root_.guard P : Option Unit).bind f = some x ↔ P ∧ f () = some x := by
  by_cases h : P <;> simp [h]

@[simp]
theorem get!_with_bot_some [Inhabited α] {x : α} :
(WithBot.some x).get! = x := rfl

theorem eq_iff_of_subsingleton [ha : Subsingleton α]
{x y : Option α} : x = y ↔ (x.isSome ↔ y.isSome) := by
  rcases x with ⟨⟩ | x <;> rcases y with ⟨⟩ | y <;> simp
  apply ha.1

@[simp]
theorem bind_eq_some_iff' {x : Option α} {y} {f : α → Option β} :
x.bind f = some y ↔ ∃ a, x = some a ∧ f a = some y :=
  bind_eq_some_iff

theorem bind_dite {P} [hp : Decidable P]
{f : P → Option α} {g : ¬P → Option α} {r : α → Option β} :
(if h : P then f h else g h).bind r = if h : P then (f h).bind r else (g h).bind r := by
  split_ifs <;> simp

theorem bind_ite {P} [hp : Decidable P]
{x y : Option α} {f : α → Option β} :
(if P then x else y).bind f = if P then x.bind f else y.bind f := by
  split_ifs <;> simp

theorem ne_none_of_eq_some {m : Option α} {x : α}
(h : m = some x) : m ≠ none := by simp [h]

theorem map_elim_fn_some {f : α → β} {x y : Option α} :
(x.elim y some).map f = (x.map f).elim (y.map f) some := by
  cases x <;> rfl

@[simp]
theorem elim_init_bool_false_eq_true_iff {m : Option α} {f : α → Bool} :
m.elim false f = true ↔ ∃ x, m = some x ∧ f x := by
  cases m <;> simp

@[simp]
theorem elim_init_false_iff {m : Option α} {f : α → Prop} :
m.elim False f ↔ ∃ x, m = some x ∧ f x := by
  cases m <;> simp

@[simp] theorem getd_none [ha : Inhabited α] : (none : Option α).getd = default := rfl
@[simp] theorem getd_some [ha : Inhabited α] {x : α} : (some x).getd = x := rfl

theorem getd_eq_getD [ha : Inhabited α] {x : Option α} : x.getd = x.getD default := by
  cases x <;> rfl