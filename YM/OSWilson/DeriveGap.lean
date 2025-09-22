import Mathlib
import YM.OSWilson.DoeblinExplicit

/--
Finite-step contraction/gap parameters derived from explicit Doeblin data.

References (Yang-Mills-sept21.tex):
- Doeblin/refresh constants and persistence mapping: lines 4466–4476.
- Physical normalization and continuum persistence: lines 5526–5528.
  (γ_phys from θ*, t0, λ1; rescaled NRC preserves the open gap.)

This module keeps a minimal, Prop-native specification with explicit formulas
for the contraction ρ, a threshold β₀, and a per-slice constant c_cut.
No axioms; no `sorry`.
-/
namespace YM.OSWilson.DeriveGap

open YM.OSWilson.DoeblinExplicit

/-- Input parameters for gap derivation from explicit minorization (θ*, t0) and
auxiliary scales (λ₁, S₀, a). -/
structure DeriveParams where
  minor  : MinorizationSketch
  lambda1 : Float
  S0      : Float
  a       : Float

/-- Output parameters: contraction ratio ρ, threshold β₀, and per-slice constant c_cut. -/
structure DeriveOut where
  rho   : Float
  beta0 : Float
  c_cut : Float

/-- Contraction from Doeblin data: ρ := sqrt(max 0 (1 − θ*·e^{−λ₁ t₀})).
This encodes the single-step contraction consistent with the manuscript’s
finite-time refresh (cf. lines 5526–5528 for the γ_phys expression). -/
def rho_from (P : DeriveParams) : Float :=
  Float.sqrt (Float.max 0.0 (1.0 - P.minor.thetaStar * Float.exp (-(P.lambda1 * P.minor.t0))))

/-- Threshold β₀ from slack S₀ and contraction ρ: β₀ := max 0 (1 − (ρ + S₀)). -/
def beta0_from (P : DeriveParams) (ρ : Float) : Float :=
  Float.max 0.0 (1.0 - (ρ + P.S0))

/-- Per-slice constant c_cut from β₀ and spacing a: c_cut := − log(max ε (1 − β₀)) / a.
The small ε avoids taking log of 0 in the Float stub; analytic files can refine this. -/
def ccut_from (P : DeriveParams) (β0 : Float) : Float :=
  - (Float.log (Float.max 1e-9 (1.0 - β0))) / P.a

/-- Specification tying the outputs to their defining formulas. -/
def derive_spec (P : DeriveParams) (O : DeriveOut) : Prop :=
  O.rho = rho_from P ∧ O.beta0 = beta0_from P O.rho ∧ O.c_cut = ccut_from P O.beta0

/-- Builder realizing the specification by construction. -/
def build_derive (P : DeriveParams) : DeriveOut :=
  let ρ := rho_from P
  let β0 := beta0_from P ρ
  { rho := ρ, beta0 := β0, c_cut := ccut_from P β0 }

theorem derive_rho_eq (P : DeriveParams) :
  (build_derive P).rho = rho_from P := by
  dsimp [build_derive, rho_from]
  simp

theorem derive_beta0_eq (P : DeriveParams) :
  (build_derive P).beta0 = beta0_from P (build_derive P).rho := by
  dsimp [build_derive, beta0_from, rho_from]
  simp

theorem derive_c_cut_eq (P : DeriveParams) :
  (build_derive P).c_cut = ccut_from P (build_derive P).beta0 := by
  dsimp [build_derive, ccut_from, beta0_from, rho_from]
  simp

/-- The builder satisfies the specification (definitional equalities). -/
theorem build_derive_holds (P : DeriveParams) :
  derive_spec P (build_derive P) := by
  dsimp [derive_spec]
  refine And.intro ?hr (And.intro ?hb ?hc)
  · simpa using derive_rho_eq P
  · simpa using derive_beta0_eq P
  · simpa using derive_c_cut_eq P

end YM.OSWilson.DeriveGap


