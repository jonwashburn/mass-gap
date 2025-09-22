import Mathlib.Analysis.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.SpecialUnitaryGroup
import YM.OSWilson.DoeblinExplicit

/-!
Heat-kernel short-time lower bound on SU(N).

This file will contain the formalization of the short-time lower bound for the
heat kernel on SU(N), as described in `Yang-Mills-sept21.tex`, Lemma
`lem:hk-lower-explicit`.

The main steps are:
1.  Define the geometric structures on SU(N) (manifold, Riemannian metric).
2.  Define the heat kernel on a Riemannian manifold.
3.  Prove the short-time lower bound for the heat kernel on SU(N).
4.  Derive the constants `t₀` and `θ_*` from the RS parameters.
-/

namespace YM.OSWilson.HeatKernelLowerBound

-- We will start by defining the necessary geometric structures on SU(N).
-- Mathlib provides the SpecialUnitaryGroup, which we can use as our starting point.

noncomputable section

-- Alias for SU(N) for convenience.
alias SU_N := Matrix.specialUnitaryGroup

section ManifoldStructure

variable {n : ℕ}

-- Mathlib provides the Lie group structure on SU(N).
-- The instance `Matrix.specialUnitaryGroup.lieGroup` is available, making SU(N)
-- a real Lie group.
instance : LieGroup 𝓘(ℝ) (SU_N (Fin n) ℂ) :=
  Matrix.specialUnitaryGroup.lieGroup

-- We assume a metric space structure induced by a bi-invariant Riemannian metric.
-- A full construction requires defining the metric from the Lie algebra inner
-- product and showing it induces the standard topology.
instance : MetricSpace (SU_N (Fin n) ℂ) := sorry

end ManifoldStructure

section HeatKernel

variable {n : ℕ} [Fact (0 < n)]

def heatKernel (t : ℝ) (g : SU_N (Fin n) ℂ) : ℝ := sorry

-- For the proof of the lower bound, we can use Varadhan's formula:
-- p_t(g) ~ (4πt)^(-d/2) * exp(-d(e, g)² / (4t))
-- where d is the dimension and d(e, g) is the Riemannian distance.

-- TODO: Formalize the Laplace-Beltrami operator.
-- TODO: Formalize the heat kernel.
-- TODO: State Varadhan's formula or a similar asymptotic result.
theorem heat_kernel_asymptotics (g : SU_N (Fin n) ℂ) (t : ℝ) (ht : 0 < t) :
  let d := finrank ℝ (lieAlg_su n)
  let dist_sq := dist (1 : SU_N (Fin n) ℂ) g ^ 2
  let p_t_g := heatKernel t g
  -- Using a placeholder for asymptotic equivalence.
  p_t_g - (4 * π * t)^(-d / 2) * Real.exp (-dist_sq / (4 * t)) < 1 :=
  sorry

-- TODO: Use this to prove the lower bound from `lem:hk-lower-explicit`.
theorem heat_kernel_lower_bound (g : SU_N (Fin n) ℂ) (t : ℝ) (r : ℝ)
    (ht : 0 < t) (hr : 0 < r) (h_t_small : t < t_star n) :
  let d := finrank ℝ (lieAlg_su n)
  let p_t_g := heatKernel t g
  p_t_g ≥ c_star n r * t^(d / 2) * (Metric.ball (1 : SU_N (Fin n) ℂ) r).indicator 1 g :=
  sorry

/-- A temporary assumption that balls in a normed space are preconnected,
    using the available `isConnected_ball` lemma. -/
lemma temporary_isPreconnected_assumption {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : E) {r : ℝ} (hr : 0 < r) :
  IsPreconnected (Metric.ball x r) :=
  (isConnected_ball x hr).isPreconnected

end HeatKernel

section ConstantsFromRS

variable {n : ℕ}

-- The constants `t₀` and `θ_*` from the tex file need to be derived from
-- the RS parameters.
-- The tex file states:
-- t₀ = t₀(G)
-- θ_* = κ₀ = c_geo * (α_ref * c_*)^m_cut
-- These depend on geometric properties of the lattice and the group G = SU(N).
-- The RS framework provides a way to handle physical units and fundamental
-- constants. The derivation of these constants will involve connecting the
-- geometric setup of the YM model to the RS framework.

def t_star (n : ℕ) : ℝ :=
  -- This should be a function of the RS parameters. For now, a placeholder.
  1

def c_star (n : ℕ) (r : ℝ) : ℝ :=
  -- This should also be a function of the RS parameters. For now, a placeholder.
  1 / (r ^ (n^2 - 1))

-- The final `MinorizationSketch` should be derived from these.
def derivedInterfaceParams (n : ℕ) : MinorizationSketch :=
  { thetaStar := 1/2,
    t0 := t_star n / 2,
    theta_pos := by norm_num,
    theta_le_one := by norm_num,
    t0_pos := by norm_num [t_star] }

end ConstantsFromRS

section BiInvariantMetric

variable {n : ℕ} [Fact (0 < n)]

-- The tangent space at the identity of SU(N) is the space of skew-Hermitian
-- trace-zero matrices, su(n).
local notation "M_n" => Matrix (Fin n) (Fin n) ℂ

-- We define su(n) as a real submodule of the space of n x n complex matrices.
def lieAlg_su (n : ℕ) : Submodule ℝ M_n where
  carrier := {X | Xᴴ = -X ∧ Matrix.trace X = 0}
  add_mem' {X Y} hX hY := by
    simp_all only [Set.mem_setOf_eq, Matrix.conjTranspose_add, Matrix.trace_add, add_zero]
    exact ⟨by simp, by simp⟩
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.conjTranspose_zero, Matrix.trace_zero]
    exact ⟨rfl, rfl⟩
  smul_mem' c X hX := by
    simp_all only [Set.mem_setOf_eq, Matrix.conjTranspose_smul, smul_neg,
      Matrix.trace_smul, mul_zero]
    rw [Complex.star_ofReal]
    exact ⟨rfl, rfl⟩

-- The standard Ad-invariant inner product on su(n) is (X, Y) ↦ -Re(tr(XY)).
-- This gives rise to a bi-invariant Riemannian metric on SU(N).
def lieAlgInnerProduct (X Y : M_n) : ℝ :=
  - (Matrix.trace (X * Y)).re

lemma lieAlgInnerProduct_symm (X Y : M_n) :
  lieAlgInnerProduct X Y = lieAlgInnerProduct Y X := by
  simp [lieAlgInnerProduct, Matrix.trace_mul_comm]

lemma lieAlgInnerProduct_nonneg_def (X : lieAlg_su n) :
    0 ≤ lieAlgInnerProduct X.val X.val ∧ (lieAlgInnerProduct X.val X.val = 0 ↔ X = 0) := by
  let X_val := X.val
  have hX : X_valᴴ = -X_val := X.property.1
  let tr_re := (Matrix.trace (X_val * X_val)).re
  have tr_eq_neg_sum_sq : Matrix.trace (X_val * X_val) = -Matrix.trace (X_val * X_valᴴ) := by
    rw [hX, mul_neg, Matrix.trace_neg]
  have tr_sum_sq : Matrix.trace (X_val * X_valᴴ) =
      ∑ i j, X_val i j * (Matrix.conjTranspose X_val) j i := by
    simp [Matrix.trace, Matrix.mul_apply]
  have : (Matrix.trace (X_val * X_valᴴ)).re =
    (∑ i j, ‖X_val i j‖^2 : ℂ).re := by
    simp_rw [tr_sum_sq, Matrix.conjTranspose_apply, star_def, Complex.mul_conj,
      Complex.normSq_eq_abs_sq_real, ← Complex.ofReal_pow,
      map_sum, Complex.ofReal_re]
  rw [lieAlgInnerProduct, tr_eq_neg_sum_sq, map_neg, neg_neg, tr_re, this]
  constructor
  · apply Finset.sum_nonneg
    intros
    apply sq_nonneg
  · simp_rw [sum_eq_zero_iff_of_nonneg, pow_eq_zero_iff_of_nonneg (norm_nonneg _),
      norm_eq_zero, Submodule.ext_iff, Subtype.val_inj, Matrix.ext_iff]
    intros; apply Finset.mem_univ
    exact fun i j => Iff.rfl

instance : InnerProductSpace ℝ (lieAlg_su n) :=
  InnerProductSpace.ofCore (lieAlg_su n) {
    inner := fun X Y => lieAlgInnerProduct X.val Y.val,
    nonneg_def := lieAlgInnerProduct_nonneg_def,
    bilin := fun X Y Z => by
      simp [lieAlgInnerProduct, Matrix.trace_add, Complex.add_re, Matrix.add_mul],
    smul := fun c X Y => by
      simp [lieAlgInnerProduct, Matrix.trace_smul, Complex.smul_re, Matrix.mul_smul_comm],
    conj_symm := fun X Y => lieAlgInnerProduct_symm X.val Y.val,
  }

-- TODO: Extend this to a left-invariant metric on the whole group.
-- TODO: Show that the metric is also right-invariant, hence bi-invariant.
-- TODO: Define the Laplace-Beltrami operator.
-- TODO: Define the heat kernel.
-- TODO: Prove the lower bound.

-- We equip SU(N) with a bi-invariant Riemannian metric, which is unique up to
-- a constant scaling factor. The metric is induced from the inner product on
-- the Lie algebra su(n).
instance : RiemannianMetric 𝓘(ℝ) (SU_N (Fin n) ℂ) :=
  let inner_product : InnerProductSpace.Core ℝ (lieAlg_su n) := {
    inner := fun X Y => lieAlgInnerProduct X.val Y.val,
    nonneg_def := lieAlgInnerProduct_nonneg_def,
    bilin := fun X Y Z => by
      simp [lieAlgInnerProduct, Matrix.trace_add, Complex.add_re, Matrix.add_mul],
    smul := fun c X Y => by
      simp [lieAlgInnerProduct, Matrix.trace_smul, Complex.smul_re, Matrix.mul_smul_comm],
    conj_symm := fun X Y => lieAlgInnerProduct_symm X.val Y.val,
  }
  biinvariantMetric inner_product

end BiInvariantMetric

end -- noncomputable section

end YM.OSWilson.HeatKernelLowerBound


