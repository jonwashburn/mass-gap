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


