import AP.Map.Defs

namespace Map

set_option linter.unusedVariables false
universe u
variable {ι α : Type u} [hhι : LinearOrder ι] [hhα : DecidableEq α] {mp : Map ι α}
set_option linter.unusedSectionVars true