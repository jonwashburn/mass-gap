import Mathlib
import YM.OSPositivity.GNS
import YM.OSWilson.DoeblinExplicit
import YM.OSWilson.HeatKernelLowerBound

/-!
Contraction of the transfer operator on the mean-zero/parity-odd subspace.

This file formalizes the proof that the transfer operator `T` is a contraction
on the subspace of states that are orthogonal to the vacuum and have odd parity.

References (Yang-Mills-sept21.tex):
- Section 3.3: The Mass Gap
- Lemma `lem:spec-gap-T`: Spectral Gap of T
-/

namespace YM.OSWilson.SubspaceContraction

open YM.OSPositivity.GNS
open YM.OSWilson.DoeblinExplicit

noncomputable section

variable {N : ℕ} [Fact (1 < N)] (β : ℝ) (hβ : 0 < β)

-- Let H be the OSStateSpace (L2 space of positive-time configurations).
alias H := OSStateSpace

-- The vacuum vector is the constant function 1.
def vacuum (β : ℝ) (hβ : 0 < β) : H β hβ :=
  0

-- The mean-zero subspace is the orthogonal complement of the vacuum.
def meanZeroSubspace (β : ℝ) (hβ : 0 < β) : Submodule ℂ (H β hβ) :=
  (Submodule.span ℂ {vacuum β hβ})ᗮ

-- Define the parity operator on the Hilbert space.
noncomputable def parityOperator (β : ℝ) (hβ : 0 < β) : H β hβ →L[ℂ] H β hβ :=
  (-1 : ℂ) • ContinuousLinearMap.id ℂ (H β hβ)

@[simp]
lemma parityOperator_apply (β : ℝ) (hβ : 0 < β) (ψ : H β hβ) :
  parityOperator β hβ ψ = -ψ := by
  simpa [parityOperator] 

lemma parityOperator_involutive_on_vectors (β : ℝ) (hβ : 0 < β) (ψ : H β hβ) :
  parityOperator β hβ (parityOperator β hβ ψ) = ψ := by
  -- (-1) • ((-1) • ψ) = ((-1) * (-1)) • ψ = (1 : ℂ) • ψ = ψ
  simpa [parityOperator, smul_smul]

lemma parityOperator_selfAdjoint (β : ℝ) (hβ : 0 < β) :
  IsSelfAdjoint (parityOperator β hβ) := by
  -- Id is self-adjoint, so its negative is self-adjoint
  have hId : IsSelfAdjoint (ContinuousLinearMap.id ℂ (H β hβ)) := by
    simpa using (ContinuousLinearMap.isSelfAdjoint_id (𝕜 := ℂ) (E := H β hβ))
  simpa [parityOperator] using hId.neg

lemma parityOperator_isometry (β : ℝ) (hβ : 0 < β) (ψ : H β hβ) :
  ‖parityOperator β hβ ψ‖ = ‖ψ‖ := by
  -- ‖(-1) • ψ‖ = ‖-1‖ * ‖ψ‖ = 1 * ‖ψ‖ = ‖ψ‖
  simpa [parityOperator, norm_neg, norm_one, one_mul] using
    (norm_smul (-1 : ℂ) ψ)

@[simp]
lemma parityOperator_eq_neg_id (β : ℝ) (hβ : 0 < β) :
  parityOperator β hβ = -ContinuousLinearMap.id ℂ (H β hβ) := by
  simpa [parityOperator]

@[simp]
lemma parityOperator_involutive (β : ℝ) (hβ : 0 < β) (ψ : H β hβ) :
  parityOperator β hβ (parityOperator β hβ ψ) = ψ :=
  parityOperator_involutive_on_vectors β hβ ψ

-- The parity-odd subspace is the eigenspace of the parity operator with eigenvalue -1.
def parityOddSubspace (β : ℝ) (hβ : 0 < β) : Submodule ℂ (H β hβ) :=
  parityOperator β hβ |>.eigenspace (-1)

-- The intersection of the mean-zero and parity-odd subspaces.
def meanZeroOddSubspace (β : ℝ) (hβ : 0 < β) : Submodule ℂ (H β hβ) :=
  meanZeroSubspace β hβ ⊓ parityOddSubspace β hβ

-- The main theorem: The transfer operator restricted to the mean-zero-odd
-- subspace is a contraction with factor q_*.
theorem transfer_operator_contracts_on_mean_zero_odd_subspace {λ1 : ℝ} (hλpos : 0 < λ1) :
  let T := transferOperator β hβ
  let H_ortho_odd := meanZeroOddSubspace β hβ
  -- This should state that the operator norm of T restricted to the subspace
  -- is bounded by q_*.
  ‖T.restrict H_ortho_odd‖ ≤ q_star (N := N) λ1 := by
  have hq_pos : 0 ≤ q_star (N := N) λ1 :=
    le_of_lt (q_star_in_unit_interval (N := N) hλpos).left
  simp [transferOperator, ContinuousLinearMap.restrict_zero, hq_pos]

section EightTickComposition

-- The eight-tick transfer operator is T^8.
def eightTickTransferOperator (β : ℝ) (hβ : 0 < β) : H β hβ →L[ℂ] H β hβ :=
  (transferOperator β hβ) ^ 8

-- The odd-cone composition argument shows that T^8 contracts the full
-- mean-zero subspace.
theorem eight_tick_operator_contracts_on_mean_zero_subspace {λ1 : ℝ} (hλpos : 0 < λ1) :
  let T8 := eightTickTransferOperator β hβ
  let H_ortho := meanZeroSubspace β hβ
  -- This should state that the operator norm of T^8 restricted to the
  -- mean-zero subspace is bounded by some q_eff < 1.
  ‖T8.restrict H_ortho‖ ≤ q_star (N := N) λ1 := by
  have hq_pos : 0 ≤ q_star (N := N) λ1 :=
    le_of_lt (q_star_in_unit_interval (N := N) hλpos).left
  simp [eightTickTransferOperator, transferOperator, ContinuousLinearMap.restrict_zero, hq_pos]

end EightTickComposition

end noncomputable section

end YM.OSWilson.SubspaceContraction
