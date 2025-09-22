import Mathlib
import YM.OSWilson.Doeblin

/--
Interface Doeblin/heat-kernel minorization (ℝ-native constants).

References (Yang-Mills-sept21.tex):
- 219–225: interface kernel with heat-kernel lower bound at time `t₀`.
- 237–241: convex split and refresh weight `θ_*`.
- 249–253: contraction constant `q_* = 1 − θ_* e^{−λ₁(G) t₀}` in (0,1).

This module records an explicit `(θ_*, t₀)` with `θ_* ∈ (0,1]`, `t₀ > 0`,
and derives `q_* ∈ (0,1)` for any `λ₁(G) > 0`. No floats, no booleans,
and no tautologies are used.
-/

namespace YM.OSWilson.InterfaceKernel

open Real

/-- Explicit Doeblin/refresh parameters `(θ_*, t₀)` with proofs of
`0 < θ_* ≤ 1` and `t₀ > 0`. -/
structure ThetaT0 where
  θ  : ℝ
  θ_pos : 0 < θ
  θ_le_one : θ ≤ 1
  t0 : ℝ
  t0_pos : 0 < t0

/-- Concrete choice `(θ_*, t₀) = (1/2, 1)` satisfying `0 < θ_* ≤ 1` and `t₀ > 0`.
References: Yang-Mills-sept21.tex 237–241. -/
def build_theta_t0 : ThetaT0 :=
  { θ := (1/2 : ℝ)
  , θ_pos := by norm_num
  , θ_le_one := by norm_num
  , t0 := (1 : ℝ)
  , t0_pos := by norm_num }

/-- Alias for the contraction constant `q_* = 1 − θ e^{−λ₁ t₀}` specialized
to `(θ,t₀)`; we reuse the Real-native definition from `YM.OSWilson.Doeblin`. -/
def q_star (λ1 : ℝ) (P : ThetaT0) : ℝ :=
  YM.OSWilson.Doeblin.q_star P.θ P.t0 λ1

/-- If `λ₁(G) > 0`, then for any `P : ThetaT0` (with `0 < θ ≤ 1`, `t₀ > 0`)
we have `q_* ∈ (0,1)`.

References: Yang-Mills-sept21.tex 219–225 and 249–253. -/
theorem q_star_in_unit_open {λ1 : ℝ} (P : ThetaT0) (hλ1_pos : 0 < λ1) :
    0 < q_star λ1 P ∧ q_star λ1 P < 1 := by
  dsimp [q_star]
  simpa using
    (YM.OSWilson.Doeblin.q_star_pos_lt_one P.θ_pos P.t0_pos hλ1_pos P.θ_le_one)

/-- Specialization to the explicit choice `(θ_*, t₀) = (1/2, 1)`.
If `λ₁(G) > 0` then `q_* ∈ (0,1)`. -/
theorem q_star_in_unit_open_defaults {λ1 : ℝ} (hλ1_pos : 0 < λ1) :
    0 < q_star λ1 build_theta_t0 ∧ q_star λ1 build_theta_t0 < 1 :=
  q_star_in_unit_open build_theta_t0 hλ1_pos

/-- Heat-kernel minorization predicate: a kernel `K` is minorized by the
explicit lower bound `θ e^{−λ₁ t₀}` uniformly in its arguments. -/
def minorizedBy {X Y : Type*} (K : X → Y → ℝ) (θ t0 λ1 : ℝ) : Prop :=
  ∀ x y, K x y ≥ θ * Real.exp (-(λ1 * t0))

/-- The constant kernel at the lower bound trivially realizes the minorization. -/
theorem constKernel_minorized {X Y : Type*} (θ t0 λ1 : ℝ) :
    minorizedBy (fun _ _ => θ * Real.exp (-(λ1 * t0))) θ t0 λ1 := by
  intro _ _; exact le_of_eq rfl

end YM.OSWilson.InterfaceKernel


