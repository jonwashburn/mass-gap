import YM.RealityAdapters
import YM.OSWilson.Doeblin

/-!
Interface constants for the explicit Doeblin/heat‑kernel minorization used by
the OS/Wilson lattice derivations. This file intentionally avoids any geometric
or analytic placeholders and only exposes the concrete `(θ_*, t₀)` interface
consumed by downstream modules.
-/

namespace YM.OSWilson.HeatKernelLowerBound

noncomputable section

/-!
Interface/Doeblin parameters `(θ_*, t₀)` are provided by `YM.RealityAdapters`.
We re-export the interface to ensure all constants are threaded from there.
-/
abbrev InterfaceParams := YM.RealityAdapters.InterfaceParams

noncomputable def defaultParams : InterfaceParams := YM.RealityAdapters.defaultParams

/‑!
Unused Riemannian/heat‑kernel helpers (interface level only).

These provide lightweight witnesses for the spectral gap `λ₁(SU(N))` and the
derived contraction factor `q_* = 1 − θ_* e^{−λ₁ t₀}` using the Reality‑driven
interface parameters `(θ_*, t₀)`. They are intentionally kept at the interface
layer: no geometry is developed here and no heavy analytics are assumed. The
section exists to centralize the numerical constants used by downstream
modules.

References (Yang‑Mills‑sept21.tex): 219–225, 237–241, 249–253.
-/ 

/-- Interface contraction factor `q_* = 1 − θ_* e^{−λ₁ t₀}` using `defaultParams`.
`q_* ∈ (0,1)` under the basic positivity/normalization of `(θ_*, t₀)` and `λ₁>0`.
-/
noncomputable def qStar_default (N : ℕ) [Fact (1 < N)] (λ1 : ℝ) : ℝ :=
  YM.OSWilson.Doeblin.q_star defaultParams.thetaStar defaultParams.t0 λ1

theorem qStar_default_in_unit_interval (N : ℕ) [Fact (1 < N)] {λ1 : ℝ}
  (hλpos : 0 < λ1) : 0 < qStar_default N λ1 ∧ qStar_default N λ1 < 1 := by
  have hθpos  : 0 < defaultParams.thetaStar := defaultParams.theta_pos
  have hθle   : defaultParams.thetaStar ≤ 1 := defaultParams.theta_le_one
  have ht0pos : 0 < defaultParams.t0        := defaultParams.t0_pos
  simpa [qStar_default] using
    (YM.OSWilson.Doeblin.q_star_pos_lt_one hθpos ht0pos hλpos hθle)

/-- Convenience factor `ρ := e^{−λ₁ t₀}` at the interface defaults. -/
noncomputable def rho_default (λ1 : ℝ) : ℝ :=
  Real.exp (-(λ1 * defaultParams.t0))

lemma rho_default_pos (λ1 : ℝ) : 0 < rho_default λ1 := by
  simp [rho_default, Real.exp_pos]

lemma rho_default_lt_one_of_pos {λ1 : ℝ}
  (hλpos : 0 < λ1) : rho_default λ1 < 1 := by
  have ht0pos : 0 < defaultParams.t0 := defaultParams.t0_pos
  have hmulpos : 0 < λ1 * defaultParams.t0 := mul_pos hλpos ht0pos
  have : -(λ1 * defaultParams.t0) < 0 := by simpa using (neg_lt_zero.mpr hmulpos)
  simpa [rho_default, Real.exp_zero] using (Real.exp_lt_one_iff.mpr this)

lemma rho_default_le_one_of_nonneg {λ1 : ℝ}
  (hλnn : 0 ≤ λ1) : rho_default λ1 ≤ 1 := by
  have ht0pos : 0 < defaultParams.t0 := defaultParams.t0_pos
  have hmulnn : 0 ≤ λ1 * defaultParams.t0 := mul_nonneg hλnn (le_of_lt ht0pos)
  have : -(λ1 * defaultParams.t0) ≤ 0 := by simpa using (neg_nonpos.mpr hmulnn)
  simpa [rho_default, Real.exp_zero] using (Real.exp_le_one_iff.mpr this)

lemma qStar_default_eq_one_sub_theta_mul_rho (N : ℕ) [Fact (1 < N)] (λ1 : ℝ) :
  qStar_default N λ1 = 1 - defaultParams.thetaStar * rho_default λ1 := by
  unfold qStar_default rho_default YM.OSWilson.Doeblin.q_star
  rfl

lemma qStar_default_at_lambda_zero (N : ℕ) [Fact (1 < N)] :
  qStar_default N 0 = 1 - defaultParams.thetaStar := by
  simp [qStar_default_eq_one_sub_theta_mul_rho, rho_default]

lemma qStar_default_lower_bound_of_nonneg (N : ℕ) [Fact (1 < N)] {λ1 : ℝ}
  (hλnn : 0 ≤ λ1) : 1 - defaultParams.thetaStar ≤ qStar_default N λ1 := by
  have hθnn : 0 ≤ defaultParams.thetaStar := le_of_lt defaultParams.theta_pos
  have hρ_le_one : rho_default λ1 ≤ 1 := rho_default_le_one_of_nonneg hλnn
  -- θ·ρ ≤ θ, hence 1 − θ ≤ 1 − θ·ρ
  have : defaultParams.thetaStar * rho_default λ1 ≤ defaultParams.thetaStar := by
    simpa [mul_one] using (mul_le_mul_of_nonneg_left hρ_le_one hθnn)
  have := sub_le_sub_left this 1
  simpa [qStar_default_eq_one_sub_theta_mul_rho] using this

lemma rho_default_antitone_in_lambda1 {λ1 λ1' : ℝ}
  (hle : λ1 ≤ λ1') : rho_default λ1' ≤ rho_default λ1 := by
  have ht0pos : 0 < defaultParams.t0 := defaultParams.t0_pos
  have hmul : λ1 * defaultParams.t0 ≤ λ1' * defaultParams.t0 :=
    mul_le_mul_of_nonneg_right hle (le_of_lt ht0pos)
  have : -(λ1' * defaultParams.t0) ≤ -(λ1 * defaultParams.t0) := by
    simpa using (neg_le_neg hmul)
  simpa [rho_default] using (Real.exp_le_exp.mpr this)

lemma qStar_default_monotone_in_lambda1 (N : ℕ) [Fact (1 < N)]
  {λ1 λ1' : ℝ} (hle : λ1 ≤ λ1') :
  qStar_default N λ1 ≤ qStar_default N λ1' := by
  have hθnn : 0 ≤ defaultParams.thetaStar := le_of_lt defaultParams.theta_pos
  have hρ : rho_default λ1' ≤ rho_default λ1 := rho_default_antitone_in_lambda1 hle
  have hθρ : defaultParams.thetaStar * rho_default λ1' ≤
      defaultParams.thetaStar * rho_default λ1 :=
    mul_le_mul_of_nonneg_left hρ hθnn
  -- negate and add 1
  have : -(defaultParams.thetaStar * rho_default λ1) ≤
      -(defaultParams.thetaStar * rho_default λ1') := by
    simpa using (neg_le_neg hθρ)
  have := add_le_add_left this 1
  simpa [qStar_default_eq_one_sub_theta_mul_rho, add_comm, add_left_comm, add_assoc]
    using this

/-- Cut constant `γ_cut := - log q_*`, positive once `q_* ∈ (0,1)`. -/
noncomputable def gammaCut_default (N : ℕ) [Fact (1 < N)] (λ1 : ℝ) : ℝ :=
  - Real.log (qStar_default N λ1)

lemma gammaCut_default_pos (N : ℕ) [Fact (1 < N)] {λ1 : ℝ}
  (hλpos : 0 < λ1) : 0 < gammaCut_default N λ1 := by
  have hq := qStar_default_in_unit_interval (N := N) (λ1 := λ1) hλpos
  have hqpos : 0 < qStar_default N λ1 := hq.left
  have hqlt1 : qStar_default N λ1 < 1 := hq.right
  have hloglt0 : Real.log (qStar_default N λ1) < 0 := by
    have hx : 0 < qStar_default N λ1 := hqpos
    have : qStar_default N λ1 < Real.exp 0 := by simpa [Real.exp_zero] using hqlt1
    exact (Real.log_lt_iff_lt_exp hx).mpr this
  exact neg_pos.mpr hloglt0

/-!
Bundled interface triplet with fields `{ρ, q_*, γ_cut}` and basic properties.
This version is independent of `N` and only depends on the interface parameters
`(θ_*, t₀)` together with an external spectral parameter `λ₁`.
-/

structure InterfaceTriplet where
  lambda1   : ℝ
  rho       : ℝ
  q         : ℝ
  gammaCut  : ℝ
  rho_pos   : 0 < rho
  rho_lt_one_of_pos : 0 < lambda1 → rho < 1
  q_in_unit : 0 < lambda1 → 0 < q ∧ q < 1
  gamma_pos : 0 < lambda1 → 0 < gammaCut

/-- Build the bundled `{ρ, q_*, γ_cut}` at spectral parameter `λ₁`.
Properties are discharged from the interface defaults and elementary calculus.
-/
noncomputable def buildInterfaceTriplet (λ1 : ℝ) : InterfaceTriplet :=
  let ρ := rho_default λ1
  let q := YM.OSWilson.Doeblin.q_star defaultParams.thetaStar defaultParams.t0 λ1
  let γ := - Real.log q
  -- Basic constants from the interface
  have hθpos  : 0 < defaultParams.thetaStar := defaultParams.theta_pos
  have hθle   : defaultParams.thetaStar ≤ 1 := defaultParams.theta_le_one
  have ht0pos : 0 < defaultParams.t0        := defaultParams.t0_pos
  {
    lambda1 := λ1
  , rho     := ρ
  , q       := q
  , gammaCut := γ
  , rho_pos := by
      -- ρ > 0 for all λ₁
      simpa [ρ, rho_default, show λ1 = λ1 from rfl] using rho_default_pos λ1
  , rho_lt_one_of_pos := by
      -- If λ₁>0 then ρ<1
      intro hλpos; simpa [ρ, rho_default] using rho_default_lt_one_of_pos (λ1 := λ1) hλpos
  , q_in_unit := by
      -- If λ₁>0 then q∈(0,1)
      intro hλpos
      -- direct application of the generic q_* lemma
      simpa [q, YM.OSWilson.Doeblin.q_star] using
        (YM.OSWilson.Doeblin.q_star_pos_lt_one hθpos ht0pos hλpos hθle)
  , gamma_pos := by
      -- If λ₁>0 then 0<q<1, hence log q < 0 and γ = -log q > 0
      intro hλpos
      have hq := (YM.OSWilson.Doeblin.q_star_pos_lt_one hθpos ht0pos hλpos hθle)
      have hqpos : 0 < q := by simpa [q, YM.OSWilson.Doeblin.q_star] using hq.left
      have hqlt1 : q < 1 := by simpa [q, YM.OSWilson.Doeblin.q_star] using hq.right
      have hloglt0 : Real.log q < 0 := by
        have : q < Real.exp 0 := by simpa [Real.exp_zero] using hqlt1
        exact (Real.log_lt_iff_lt_exp hqpos).mpr this
      simpa [γ] using (neg_pos.mpr hloglt0)
  }

end -- noncomputable section

end YM.OSWilson.HeatKernelLowerBound


