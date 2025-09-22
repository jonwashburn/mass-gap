/-!
Export variants and real wiring (spec-level): spectral, real, interface.
References: Yang-Mills-sept21.tex — NRC (lines 5339–5357), interface γ_cut exports (around lines 740–758, 1543 ff.).
No axioms. No `sorry`.
-/

import YM.SpectralStability.RescaledNRC
import YM.Transfer.PhysicalGap
import YM.OSWilson.Doeblin

namespace YM.Export.Variants

open YM.SpectralStability.RescaledNRC
open YM.Transfer.PhysicalGap

/-- Spectral variant export using NRC setup (spec-level; Prop-based). -/
structure SpectralVariant where
  /-- Placeholder payload; the acceptance is the NRC proposition itself. -/
  unit : Unit := ()

/-- Spec: spectral export holds exactly when NRC(all nonreal z) holds for the setup. -/
def spectral_export_spec (S : NRCSetup) (_V : SpectralVariant) : Prop :=
  NRC_all_nonreal S

/-- Builder for the spectral export payload (spec-level). -/
def build_spectral_export (_S : NRCSetup) : SpectralVariant :=
  { unit := () }

/-- The built spectral export satisfies the NRC-based spec. -/
theorem build_spectral_export_holds (S : NRCSetup) :
  spectral_export_spec S (build_spectral_export S) := by
  simpa [spectral_export_spec] using NRC_all_nonreal_holds S

/-- Real/physical variant export via Doeblin-driven γ_phys (spec-level). -/
structure RealVariant where
  gamma_phys : Float

/-- Spec: the exported physical gap equals that built from Doeblin data. -/
def real_export_spec (G : GapFromDoeblinOut) (V : RealVariant) : Prop :=
  V.gamma_phys = G.gamma_phys

/-- Builder: copy out γ_phys from the Doeblin gap aggregator. -/
def build_real_export (G : GapFromDoeblinOut) : RealVariant :=
  { gamma_phys := G.gamma_phys }

theorem build_real_export_holds (G : GapFromDoeblinOut) :
  real_export_spec G (build_real_export G) := rfl

/-- Interface variant export via Wilson interface γ_cut (spec-level). -/
structure InterfaceVariant where
  gamma_cut : Float

/-- Spec: the exported cut gap equals the interface export γ_c. -/
def interface_export_spec (I : YM.OSWilson.Doeblin.WilsonGibbsInterface) (V : InterfaceVariant) : Prop :=
  V.gamma_cut = (YM.OSWilson.Doeblin.export_from_interface I).gamma_c

/-- Builder: copy out γ_c from the interface export. -/
def build_interface_export (I : YM.OSWilson.Doeblin.WilsonGibbsInterface) : InterfaceVariant :=
  { gamma_cut := (YM.OSWilson.Doeblin.export_from_interface I).gamma_c }

theorem build_interface_export_holds (I : YM.OSWilson.Doeblin.WilsonGibbsInterface) :
  interface_export_spec I (build_interface_export I) := rfl

end YM.Export.Variants


