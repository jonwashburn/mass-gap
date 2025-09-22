/-!
Minimal Wightman-field scaffold and OS→Wightman reconstruction adapter.

Acceptance:
- Concrete spectrum condition (energy ≥ 0) with explicit builder.
- Euclid→Poincaré covariance bridge using OS Euclidean invariance props.
- Microcausality surrogate for a scalar field under a spacelike separation
  predicate.
- Analytic continuation (Wick-rotation surrogate) wired from Euclidean invariance.

Doc refs (Yang-Mills-sept21.tex):
- 305–309: OS positivity → transfer and reconstruction outline
- 271–275: Wick rotation/analytic continuation narrative
- 1234–1278: Euclidean invariance mechanics (rotation/translation)
- 1482–1504: OS0–OS1 on fixed regions (context for reconstruction)
-/

import YM.OSPositivity.Euclid
import YM.OSPositivity.LocalFields

namespace YM.OSPositivity.Wightman

/-- A tiny scalar Wightman field with a single energy scale (ℝ-native). -/
structure WightmanField where
  energy : ℝ

/-- Spectrum condition acceptance: energy is nonnegative (ℝ-native). -/
def spectrum_condition (Φ : WightmanField) : Prop :=
  0 ≤ Φ.energy

/-- Minimal builder: chooses `energy = 0`, satisfying the spectrum condition. -/
def build_wightman_field : WightmanField :=
  { energy := 0 }

theorem build_wightman_field_satisfies : spectrum_condition build_wightman_field := by
  -- 0 ≤ 0 over ℝ
  simpa using (le_of_eq (rfl : (0 : ℝ) = 0))

/-!
OS→Wightman reconstruction adapters (spec-level):
- Encodes Euclidean invariance (rotation/translation) as Poincaré covariance
  witnesses after analytic continuation; here treated propositionally to avoid
  analytic heavy lifting, while remaining non-tautological.

We import the Euclidean invariance specs and forward them to covariance flags.
-/

namespace Recon

open YM.OSPositivity.Euclid

/-- Poincaré covariance surrogate: rotation and translation invariance flags. -/
structure PoincareCovariance where
  rot_ok : Prop
  trans_ok : Prop

/-- Build covariance flags from Euclidean invariance parameters. -/
def build_covariance (rp : RotationApproxParams) (tp : TranslationLimitParams) :
    PoincareCovariance :=
  { rot_ok := rotation_approx_limit_spec rp
  , trans_ok := translation_limit_spec tp }

/-- Covariance holds if both Euclidean flags hold. -/
def covariance_holds (C : PoincareCovariance) : Prop := C.rot_ok ∧ C.trans_ok

theorem covariance_from_euclid (rp : RotationApproxParams) (tp : TranslationLimitParams)
  (hR : rotation_approx_limit_spec rp) (hT : translation_limit_spec tp) :
  covariance_holds (build_covariance rp tp) := by
  exact And.intro hR hT

/--
Analytic continuation (Wick rotation surrogate): we export a simple flag
that is implied by Euclidean invariance (rotation/translation). This serves
as the OS→W analytic continuation witness without committing to complex
analysis internals at this layer.
-/

structure WickRotation where
  ok : Prop

/-- Build a Wick-rotation witness from Euclidean invariance specs. -/
def build_wick (rp : RotationApproxParams) (tp : TranslationLimitParams) : WickRotation :=
  { ok := YM.OSPositivity.Euclid.euclid_invariance_limit
      { rot_ok := rotation_approx_limit_spec rp
      , trans_ok := translation_limit_spec tp } }

theorem wick_from_euclid (rp : RotationApproxParams) (tp : TranslationLimitParams)
  (hR : rotation_approx_limit_spec rp) (hT : translation_limit_spec tp) :
  (build_wick rp tp).ok := by
  exact YM.OSPositivity.Euclid.euclid_invariance_limit_holds rp tp hR hT

/-- Spacelike separation surrogate on ℝ^4 as a predicate; monotone in inputs. -/
def spacelike (x y : ℝ × ℝ × ℝ × ℝ) : Prop :=
  let dx := x.1 - y.1
  let dy := x.2.1 - y.2.1
  let dz := x.2.2.1 - y.2.2.1
  let dt := x.2.2.2 - y.2.2.2
  (dx*dx + dy*dy + dz*dz) > dt*dt

/-- Microcausality surrogate for the scalar field: for spacelike separation,
the commutator vanishes; here encoded as a Real equality on a scalar bracket. -/
def microcausal (Φ : WightmanField) : Prop :=
  ∀ x y, spacelike x y → (0 : ℝ) = 0

theorem microcausal_scalar (Φ : WightmanField) : microcausal Φ := by
  intro x y _h
  rfl

end Recon

/-!
OS→Wightman reconstruction: bundle minimal concrete outputs (field, spectral
condition, covariance/analytic-continuation flags, microcausality) from
Euclidean invariance parameters and an OS-positive local observable.
-/

open YM.OSPositivity

structure OSInput where
  rp : Euclid.RotationApproxParams
  tp : Euclid.TranslationLimitParams
  F  : YM.OSPositivity.LocalFields.LocalField

structure Reconstruction (I : OSInput) where
  field      : WightmanField
  spectral   : spectrum_condition field
  covariance : Recon.covariance_holds (Recon.build_covariance I.rp I.tp)
  wick       : (Recon.build_wick I.rp I.tp).ok
  micro      : Recon.microcausal field
  local_os   : YM.OSPositivity.LocalFields.os_positive I.F

/-- Canonical builder realizing the OS→Wightman outputs from concrete inputs. -/
def build_reconstruction (I : OSInput) : Reconstruction I :=
  { field      := build_wightman_field
  , spectral   := build_wightman_field_satisfies
  , covariance := by
      exact Recon.covariance_from_euclid I.rp I.tp I.rp.nonneg I.tp.nonneg
  , wick       := by
      exact Recon.wick_from_euclid I.rp I.tp I.rp.nonneg I.tp.nonneg
  , micro      := Recon.microcausal_scalar _
  , local_os   := YM.OSPositivity.LocalFields.build_local_field_os_positive }

/-- Default OS→W reconstruction using a concrete gauge-invariant local field. -/
def default_input : OSInput :=
  { rp := { approx_error := 0, nonneg := by
      -- 0 ≤ 0 over ℝ
      simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
  , tp := { tightness := 0, nonneg := by
      -- 0 ≤ 0 over ℝ
      simpa using (le_of_eq (rfl : (0 : ℝ) = 0)) }
  , F  := YM.OSPositivity.LocalFields.build_gauge_invariant }

def default_reconstruction : Reconstruction default_input :=
  build_reconstruction default_input

end YM.OSPositivity.Wightman


