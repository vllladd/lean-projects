import AP.AP.Defense

namespace AP

def dKingOp' : DStrat := .mk # λ s => List.head? # do
  let p ← Box.interior.toList
  guard # p ≠ s.aPos ∧ p ∉ s.taken
  return p

def dKingOp : DStrat :=
  Box.defense.st dKingOp'