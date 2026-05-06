import Projects.Prover.Defs

namespace Prover

theorem Univ.zero_def : (0 : Univ) = .zero := rfl
theorem Univ.ble_def {u v : Univ} : u ≤ v ↔ u.ble v := by rfl