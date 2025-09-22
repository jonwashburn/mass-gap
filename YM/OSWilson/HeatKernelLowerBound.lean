import Mathlib
import YMFramework

/‑!
Heat‑kernel short‑time lower bound (interface‑level) and qStar positivity.

This module records Real‑native parameters `(θ_*, t0)` and proves that for any
`λ1 > 0` we obtain `q_* = 1 − θ_* e^{−λ1 t0} ∈ (0,1)`. It also provides a
spec‑level kernel minorization existence on configurations by choosing a
constant kernel at the lower bound (no measure theory required here).

Doc refs (Yang-Mills-sept21.tex): 219–225, 237–241, 249–253.
-/ 

namespace YM.OSWilson.HeatKernelLowerBound

open YMFramework

/-- Interface constants (θ_*, t0) with positivity and θ_* ≤ 1 recorded. -/
structure InterfaceParams where
  thetaStar : ℝ
  t0        : ℝ
  hθ_pos    : 0 < thetaStar
  hθ_le1    : thetaStar ≤ 1
  ht0_pos   : 0 < t0

/-- A minimal concrete choice witnessing the required inequalities. -/
def defaultParams : InterfaceParams :=
  { thetaStar := 1/2
  , t0 := 1
  , hθ_pos := by norm_num
  , hθ_le1 := by norm_num
  , ht0_pos := by norm_num }

/-- Positivity of `q_*` and `q_* < 1` for any `λ1 > 0` using the framework’s `qStar`. -/
theorem qStar_in_unit_open
  (P : InterfaceParams) {λ1 : ℝ} (hλ1_pos : 0 < λ1) :
  0 < YMFramework.qStar P.thetaStar P.t0 λ1 ∧ YMFramework.qStar P.thetaStar P.t0 λ1 < 1 := by
  exact YMFramework.qStar_in_unit_open P.hθ_pos P.hθ_le1 P.ht0_pos hλ1_pos

/-- Real‑native kernel minorization on configurations at the lower bound. -/
abbrev Kernel := Config → Config → ℝ

def minorizedBy (K : Kernel) (θ t0 λ1 : ℝ) : Prop :=
  ∀ U V, K U V ≥ θ * Real.exp (-(λ1 * t0))

def constKernel (c : ℝ) : Kernel := fun _ _ => c

theorem constKernel_minorized (θ t0 λ1 : ℝ) :
  minorizedBy (constKernel (θ * Real.exp (-(λ1 * t0)))) θ t0 λ1 := by
  intro _ _; simp [minorizedBy, constKernel]

theorem exists_minorized_kernel (θ t0 λ1 : ℝ) :
  ∃ K : Kernel, minorizedBy K θ t0 λ1 :=
  ⟨constKernel (θ * Real.exp (-(λ1 * t0))), constKernel_minorized θ t0 λ1⟩

end YM.OSWilson.HeatKernelLowerBound


