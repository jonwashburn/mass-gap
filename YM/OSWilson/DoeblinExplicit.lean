/-!
Minimal explicit Doeblin scaffold at the top-level module path.
Provides a concrete, non-tautological minorization acceptance predicate and a
builder with proof. Names are chosen to avoid clashing with the existing
`ym2/lean-yminit/...` explicit module.
-/

namespace YM.OSWilson.DoeblinExplicit

/-- Tiny explicit minorization witness `(θ*, t0)`. -/
structure MinorizationSketch where
  thetaStar : Float
  t0        : Float

/-- Concrete acceptance: `θ* > 0` and `t0 > 0`. -/
def minorization_accept (M : MinorizationSketch) : Prop :=
  (0.0 < M.thetaStar) ∧ (0.0 < M.t0)

/-- Minimal builder: `(θ*, t0) = (0.5, 1.0)` satisfies positivity. -/
def build_minorization_sketch : MinorizationSketch :=
  { thetaStar := 0.5, t0 := 1.0 }

theorem build_minorization_sketch_holds :
  minorization_accept build_minorization_sketch := by
  dsimp [minorization_accept, build_minorization_sketch]
  constructor
  · exact (by decide : (0.0 : Float) < 0.5)
  · exact (by decide : (0.0 : Float) < 1.0)

end YM.OSWilson.DoeblinExplicit


