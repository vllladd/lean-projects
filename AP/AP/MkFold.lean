import AP.AP.King

namespace AP

variable {α : Type}

def AStrat.mkFold' (s : State) (z : α) (fa : State → α → PointZ × α)
(fd : State → PointZ → α → α) : List PointZ → Option PointZ
| [] => some # fa s z |>.1
| p :: ps => do
  let z₁ := if s.aTurn then fa s z |>.2 else fd s p z
  let s₁ ← sys.tr s p
  mkFold' s₁ z₁ fa fd ps

def AStrat.mkFold (s₀ : State) (z : α) (fa : State → α → PointZ × α)
(fd : State → PointZ → α → α) : AStrat := mk # λ s =>
  AStrat.mkFold' s₀ z fa fd # s.hist.reverse.drop s₀.hist.length

def DStrat.mkFold' (s : State) (z : α) (fa : State → PointZ → α → α)
(fd : State → α → PointZ × α) : List PointZ → Option PointZ
| [] => some # fd s z |>.1
| p :: ps => do
  let z₁ := if s.aTurn then fa s p z else fd s z |>.2
  let s₁ ← sys.tr s p
  mkFold' s₁ z₁ fa fd ps

def DStrat.mkFold (s₀ : State) (z : α) (fa : State → PointZ → α → α)
(fd : State → α → PointZ × α) : DStrat := mk # λ s =>
  DStrat.mkFold' s₀ z fa fd # s.hist.reverse.drop s₀.hist.length