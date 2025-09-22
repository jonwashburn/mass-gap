import Mathlib
import IndisputableMonolith.Constants
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.Verification

/‑!
Reality adapters for YM (scale and units hooks).

Exports:
- `phiValue` (selection scale φ)
- Minimal normalization/units hooks re‑exported for YM integration

References: the Reality/RS stack (φ selection; K‑gate invariance).
-/ 

namespace YM.RealityAdapters

open IndisputableMonolith

/-- Canonical selection scale φ exported for YM integration. -/
def phiValue : ℝ := Constants.phi

/-- K‑gate identity (route A/B equality) re‑exported as a normalization hook. -/
theorem k_gate_bridge : ∀ U : Constants.RSUnits,
  Verification.BridgeEval Verification.K_A_obs U
    = Verification.BridgeEval Verification.K_B_obs U :=
  Verification.K_gate_bridge

/-- Units rescaling invariance hook for a generic display. -/
theorem anchor_invariance
  {obs : Verification.Observer} {U U' : Constants.RSUnits}
  (h : Verification.UnitsRescaled U U') :
  Verification.BridgeEval obs U = Verification.BridgeEval obs U' :=
  Verification.anchor_invariance _ h

/-- Framework uniqueness (pairwise isomorphism up to units) at φ. -/
def frameworkUniquenessAtPhi : Prop :=
  RH.RS.FrameworkUniqueness phiValue

theorem framework_uniqueness_holds : frameworkUniquenessAtPhi :=
  RH.RS.framework_uniqueness _

end YM.RealityAdapters


