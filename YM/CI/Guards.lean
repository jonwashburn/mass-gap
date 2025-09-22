/-!
CI Guards (spec-level): touch core acceptance symbols at top-level paths.
No axioms. No `sorry`. Props, not booleans.
-/

import YM.OSPositivity.OS2
import YM.OSPositivity.Wightman
import YM.OSPositivity.Euclid
import YM.OSWilson.Doeblin
import YM.OSWilson.Cluster
import YM.SpectralStability.RescaledNRC

namespace YM.CI.Guards

open YM.OSPositivity
open YM.OSWilson
open YM.SpectralStability

/-- Guard: OS2 positivity is present and usable. -/
def guard_os2 : Prop :=
  OS2.os2_positive OS2.build_two_point

theorem guard_os2_holds : guard_os2 :=
  OS2.build_two_point_os2_positive

/-- Guard: Doeblin lower bound acceptance reachable. -/
def guard_doeblin_lower : Prop :=
  Doeblin.doeblin_lower_bound_spec Doeblin.build_doeblin_lower_bound

theorem guard_doeblin_lower_holds : guard_doeblin_lower :=
  Doeblin.build_doeblin_lower_bound_satisfies

/-- Guard: Cluster/character expansion and influence/Dobrushin specs are wired. -/
def guard_cluster : Prop :=
  let P : OSWilson.Cluster.SmallBeta := { β := 0.0, β_small := true }
  OSWilson.Cluster.influence_bound_spec P (OSWilson.Cluster.build_influence_bound P) ∧
  OSWilson.Cluster.cluster_expansion_spec P (OSWilson.Cluster.build_cluster_expansion P)

theorem guard_cluster_holds : guard_cluster := by
  let P : OSWilson.Cluster.SmallBeta := { β := 0.0, β_small := true }
  exact And.intro (OSWilson.Cluster.build_influence_bound_holds P)
                  (OSWilson.Cluster.build_cluster_expansion_holds P)

/-- Guard: Euclidean invariance limit assembled from rotation/translation specs. -/
def guard_euclid : Prop :=
  let rp : OSPositivity.Euclid.RotationApproxParams := { approx_error := 0.0, nonneg := (by decide) }
  let tp : OSPositivity.Euclid.TranslationLimitParams := { tightness := 0.0, nonneg := (by decide) }
  OSPositivity.Euclid.euclid_invariance_limit
    { rot_ok := OSPositivity.Euclid.rotation_approx_limit_spec rp
    , trans_ok := OSPositivity.Euclid.translation_limit_spec tp }

theorem guard_euclid_holds : guard_euclid := by
  let rp : OSPositivity.Euclid.RotationApproxParams := { approx_error := 0.0, nonneg := (by decide) }
  let tp : OSPositivity.Euclid.TranslationLimitParams := { tightness := 0.0, nonneg := (by decide) }
  have h := OSPositivity.Euclid.euclid_invariance_limit_holds rp tp rp.nonneg tp.nonneg
  simpa using h

/-/ Guard: NRC (all nonreal z) can be formed from a setup bundle. -/
def guard_nrc : Prop :=
  ∃ S : RescaledNRC.NRCSetup, RescaledNRC.NRC_all_nonreal S

theorem guard_nrc_holds : guard_nrc := by
  let proj : RescaledNRC.ProjectionControl := { Λ := 1.0, Λ_pos := by decide }
  let defect : RescaledNRC.GraphDefect := { a := 0.1, C := 2.0, bound_nonneg := by decide }
  let calib : RescaledNRC.Calibrator := { z0_im := 1.0, nonreal := by decide }
  let S : RescaledNRC.NRCSetup := { proj := proj, defect := defect, calib := calib
                                   , comparison := RescaledNRC.build_comparison_from_data proj defect calib }
  exact ⟨S, RescaledNRC.NRC_all_nonreal_holds S⟩

/-- Guard: Wightman spectrum condition acceptance available (canonical spec). -/
def guard_wightman : Prop :=
  OSPositivity.Wightman.spectrum_condition OSPositivity.Wightman.build_wightman_field

theorem guard_wightman_holds : guard_wightman :=
  OSPositivity.Wightman.build_wightman_field_satisfies

end YM.CI.Guards


