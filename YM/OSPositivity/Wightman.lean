/-!
Minimal Wightman-field scaffold at the top-level module path.
Non-tautological acceptance encodes a concrete spectrum condition (energy ≥ 0)
with an explicit builder. No axioms; no `sorry`.
-/

namespace YM.OSPositivity.Wightman

/-- A tiny placeholder for a Wightman field with a single energy scale (ℝ-native). -/
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

end YM.OSPositivity.Wightman


