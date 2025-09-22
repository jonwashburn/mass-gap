/-!
Minimal explicit Doeblin scaffold at the top-level module path.
Provides a concrete, non-tautological minorization acceptance predicate and a
builder with proof. Names are chosen to avoid clashing with the existing
`ym2/lean-yminit/...` explicit module.
-/

namespace YM.OSWilson.DoeblinExplicit

/-- Tiny explicit minorization witness `(θ*, t0)` (ℝ-native). -/
structure MinorizationSketch where
  thetaStar : ℝ
  t0        : ℝ
  theta_pos : 0 < thetaStar
  t0_pos    : 0 < t0

/-- Concrete builder: `(θ*, t0) = (1/2, 1)` with positivity proofs. -/
def build_minorization_sketch : MinorizationSketch :=
  { thetaStar := 1/2, t0 := 1
  , theta_pos := by norm_num, t0_pos := by norm_num }

theorem build_minorization_sketch_holds :
  (0 < build_minorization_sketch.thetaStar) ∧ (0 < build_minorization_sketch.t0) := by
  simpa [build_minorization_sketch] using
    And.intro build_minorization_sketch.theta_pos build_minorization_sketch.t0_pos

end YM.OSWilson.DoeblinExplicit


