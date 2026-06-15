import Projects.IO.Defs

namespace VerifiedIO

variable {α β γ : Type}

@[instance, simp]
theorem ProgM.wf_pure {x : α} : (pure x : ProgM α).WF := by
  constructor <;> simp