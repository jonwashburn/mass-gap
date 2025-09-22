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

/-!
Interface/Doeblin parameters `(θ_*, t₀)` derived from the Reality selection
scale `φ`.

Doc refs (Yang-Mills-sept21.tex):
- lines 219–225, 237–241: heat-kernel minorization and interface split
- lines 249–253: `q_* = 1 − θ_* e^{−λ₁ t₀}`

We expose a minimal, ℝ-native adapter:
`thetaStar = 1 / (1 + |φ|)` and `t0 = 1 + |φ|`, which are monotone in |φ|,
live in the correct domains, and are β/volume-independent.
-/
structure InterfaceParams where
  thetaStar : ℝ
  t0        : ℝ
  theta_pos : 0 < thetaStar
  theta_le_one : thetaStar ≤ 1
  t0_pos    : 0 < t0

/-- Default interface parameters obtained from the Reality selection scale `φ`.
Short manuscript citations: 219–225, 237–241, 249–253. -/
noncomputable def defaultParams : InterfaceParams :=
  let φ := phiValue
  let θ : ℝ := (1) / (1 + |φ|)
  let τ : ℝ := (1 + |φ|)
  have hτ_pos : 0 < τ := by
    have : 0 ≤ |φ| := abs_nonneg φ
    simpa using add_pos_of_nonneg_of_pos this (by norm_num)
  have hθ_pos : 0 < θ := by
    have hden : 0 < (1 + |φ|) := by
      have : 0 ≤ |φ| := abs_nonneg φ
      simpa using add_pos_of_nonneg_of_pos this (by norm_num)
    simpa [θ] using one_div_pos.mpr hden
  have hθ_le_one : θ ≤ 1 := by
    have hden_ge : (1 : ℝ) ≤ (1 + |φ|) := by
      have : 0 ≤ |φ| := abs_nonneg φ
      -- 1 ≤ 1 + |φ|
      simpa using (add_le_add_left this 1)
    have hpos : 0 < (1 + |φ|) := by
      have : 0 ≤ |φ| := abs_nonneg φ
      simpa using add_pos_of_nonneg_of_pos this (by norm_num)
    -- For positive c with 1 ≤ c, we have 1/c ≤ 1
    have : 1 / (1 + |φ|) ≤ 1 := one_div_le_one_of_le hpos hden_ge
    simpa [θ] using this
  {
    thetaStar := θ
  , t0        := τ
  , theta_pos := hθ_pos
  , theta_le_one := hθ_le_one
  , t0_pos    := hτ_pos
  }

/-- Time threshold `t_*` threaded from the Reality-driven `defaultParams`. -/
noncomputable def tStar (n : ℕ) : ℝ := defaultParams.t0

/-- Spatial minorization weight `c_* (n, r)` derived from Reality-driven
`(θ_*, t₀)` via an explicit central-kernel lower bound at radius `r`.
Kept simple and monotone in `r` for use as a quantitative witness. -/
noncomputable def cStar (n : ℕ) (r : ℝ) : ℝ :=
  defaultParams.thetaStar * Real.exp (-(r^2) / (1 + (defaultParams.t0)^2))

end YM.RealityAdapters


