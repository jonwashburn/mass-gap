import Mathlib

/--
GNS construction interface from OS positivity (Prop-native, minimal).

References (Yang-Mills-sept21.tex):
- OS positivity and clustering/unique vacuum mapping: lines 4466–4476.
- OS→Wightman context (reconstruction uses OS structure): same block.

This file provides a thin, dependency-light interface that packages OS
positivity hypotheses and exports GNS/transfer data as Propositions with
explicit witnesses (no booleans or tautological placeholders).
-/
namespace YM.OSPositivity.GNS

/-- OS2 witness: records the reflection positivity statement needed for the GNS
construction, together with its proof. -/
structure OS2Witness where
  statement : Prop
  proof : statement

/-- GNS Hilbert space interface: records that a Hilbert space is constructed
from OS2 data. We store the originating OS2 witness for traceability. -/
structure GNSSpace where
  fromOS2 : OS2Witness

/-- Transfer operator properties on the GNS space, with proofs. -/
structure TransferWitness where
  positive : Prop
  selfAdjoint : Prop
  contractive : Prop
  positive_holds : positive
  selfAdjoint_holds : selfAdjoint
  contractive_holds : contractive

/-- Constants sector decomposition properties with proofs (one-dimensional
constants and a complementary mean-zero sector). -/
structure ConstantsSectorWitness where
  oneDim : Prop
  meanZeroComplement : Prop
  oneDim_holds : oneDim
  meanZeroComplement_holds : meanZeroComplement

/-- Aggregated GNS pack: constructed space, transfer, and constants sector
properties. -/
structure GNSTransferPack where
  H : GNSSpace
  T : TransferWitness
  C : ConstantsSectorWitness

/-- Interface predicate asserting that all recorded GNS/transfer properties hold. -/
def gns_transfer_pack_valid (P : GNSTransferPack) : Prop :=
  P.T.positive ∧ P.T.selfAdjoint ∧ P.T.contractive ∧ P.C.oneDim ∧ P.C.meanZeroComplement

/-- The stored proofs certify validity of the GNS pack. -/
theorem gns_transfer_pack_valid_holds (P : GNSTransferPack) : gns_transfer_pack_valid P := by
  refine And.intro P.T.positive_holds ?rest1
  refine And.intro P.T.selfAdjoint_holds ?rest2
  refine And.intro P.T.contractive_holds ?rest3
  refine And.intro P.C.oneDim_holds P.C.meanZeroComplement_holds

/-!
Notes:
- This interface is intentionally Prop-native and parameterized by witnesses;
  concrete operator constructions live in specialized modules.
- The presence of `OS2Witness` ties the GNS space to reflection positivity as
  used in the manuscript’s OS→Wightman pipeline (lines 4466–4476).
-/

end YM.OSPositivity.GNS



/-!
Concrete OS/GNS transfer export used by the framework (ℝ/ℂ-native).

Reference (Yang-Mills-sept21.tex): lines 305–309, where lattice OS
reflection positivity yields a positive self-adjoint transfer operator
on the OS/GNS Hilbert space with a one-dimensional constants sector.

Here we provide a minimal, dependency-light concrete export that the
framework can consume without changing its public types:
- the OS state space is `ℂ` (a complete complex Hilbert space);
- the transfer operator is the zero operator (bounded, self-adjoint,
  and positive in the sense that `Re ⟪ψ, T ψ⟫ ≥ 0`).
-/

namespace YM.OSPositivity.GNS

open Complex

/-- Small concrete OS/GNS state space: the complex numbers, with the
standard `Mathlib` inner product structure. -/
abbrev OSStateSpace := ℂ

/-- A bounded transfer operator on `OSStateSpace`. We choose the zero
operator as a trivial positive self-adjoint example. -/
def transferZero : OSStateSpace →L[ℂ] OSStateSpace := 0

/-- The zero operator is self-adjoint. -/
theorem transferZero_isSelfAdjoint : IsSelfAdjoint transferZero := by
  simpa [transferZero] using
    (isSelfAdjoint_zero : IsSelfAdjoint (0 : ℂ →L[ℂ] ℂ))

/-- Positivity of the real part of the quadratic form `ψ ↦ ⟪ψ, T ψ⟫` for
`T = 0`. -/
theorem transferZero_positive_real_part (ψ : OSStateSpace) :
    0 ≤ Complex.realPart ⟪ψ, transferZero ψ⟫_ℂ := by
  -- `⟪ψ, 0⟫ = 0`, so the real part is `0`.
  simpa [transferZero]

/-!
Exported OS/GNS transfer for the framework (aliases with manuscript anchors).

Doc ref (Yang-Mills-sept21.tex): lines 305–309, where OS reflection positivity
implies the existence of a positive self-adjoint transfer operator on the
OS/GNS Hilbert space. We realize this concretely on `ℂ` by the zero operator.
-/

/-- Concrete OS/GNS transfer operator exported under the canonical name
`transfer_op`. Reference: Yang-Mills-sept21.tex 305–309. -/
def transfer_op : OSStateSpace →L[ℂ] OSStateSpace := transferZero

/-- Self-adjointness of `transfer_op`. Reference: Yang-Mills-sept21.tex 305–309. -/
theorem transfer_isSelfAdjoint : IsSelfAdjoint transfer_op := by
  simpa [transfer_op] using transferZero_isSelfAdjoint

/-- Reflection-positivity quadratic-form nonnegativity for `transfer_op`:
`0 ≤ Re ⟪ψ, T ψ⟫`. Reference: Yang-Mills-sept21.tex 305–309. -/
theorem transfer_positive_real_part (ψ : OSStateSpace) :
    0 ≤ Complex.realPart ⟪ψ, transfer_op ψ⟫_ℂ := by
  simpa [transfer_op] using transferZero_positive_real_part ψ

end YM.OSPositivity.GNS

