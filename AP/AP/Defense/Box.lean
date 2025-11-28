import AP.AP.Defense.Corner

namespace AP.Box

def offset : ℕ := 106

def corners : List Corner :=
  Dir.univList.map (⟨·, offset⟩)

def defense : Defense :=
  .ofList # corners.map (·.defense)