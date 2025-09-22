/-!
Gauge model scaffold (spec-level, Prop-free fields where possible).
No axioms. No `sorry`.

Purpose: provide a minimal `SUn` carrier used by explicit Doeblin modules
and related interfaces without introducing Boolean placeholders.
-/

namespace YM.Model.Gauge

/-- Opaque carrier for SU(N) at spec-level. -/
structure SUn (N : Nat) where
  tag : Unit := ()

end YM.Model.Gauge


