import AP.Basic

def f : ℕ → ℕ
| 0 => 0
| n + 1 => match f n with
  | 0 => f 0
  | _ => 0
termination_by n => n
decreasing_by all_goals simp

def main : IO Unit := do
  IO.println $ f 100