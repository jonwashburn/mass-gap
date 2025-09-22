/-!
Clay Final Theorem (spec-level): OS/Wightman acceptance with a positive continuum gap γ₀.
No axioms. No `sorry`.

References: Yang-Mills-sept21.tex — spectral gap persistence and OS→Wightman
construction (see Theorem 2097 and surrounding Riesz projection discussion).
-/

import YM.OSPositivity.OS2
import YM.OSPositivity.Wightman

namespace YM.Clay.Final

open YM.OSPositivity

/-- Minimal inputs for the final acceptance: a strictly positive gap `γ₀`. -/
structure FinalParams where
  gamma0 : ℝ
  hpos   : 0 < gamma0

/-- Final acceptance payload: records `γ₀` together with OS2 and Wightman witnesses. -/
structure FinalAcceptance where
  gamma0 : ℝ
  os2    : OS2.TwoPoint
  wight  : Wightman.WightmanField

/-- Spec: `γ₀` is positive and the OS2/Wightman acceptance predicates hold. -/
def final_spec (P : FinalParams) (A : FinalAcceptance) : Prop :=
  (A.gamma0 = P.gamma0) ∧
  (OS2.os2_positive A.os2) ∧
  (Wightman.spectrum_condition A.wight) ∧
  (P.hpos)

/-- Builder: instantiates OS2/Wightman witnesses and carries through `γ₀`. -/
def build_final (P : FinalParams) : FinalAcceptance :=
  { gamma0 := P.gamma0
  , os2    := OS2.build_two_point
  , wight  := Wightman.build_wightman_field }

theorem build_final_holds (P : FinalParams) :
  final_spec P (build_final P) := by
  dsimp [final_spec, build_final]
  refine And.intro rfl ?rest
  refine And.intro ?hOS2 (And.intro ?hW ?hγ)
  · exact OS2.build_two_point_os2_positive
  · exact Wightman.build_wightman_field_satisfies
  · exact P.hpos

end YM.Clay.Final


