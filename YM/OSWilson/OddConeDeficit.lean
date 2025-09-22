/-!
Odd-cone deficit: eight-tick contraction pack (spec-level, local).
No axioms. No `sorry`.

References: Yang-Mills-sept21.tex — odd-cone contraction and eight-tick
upgrade on slabs; used to define a physical cut scale c_cut.
-/

namespace YM.OSWilson.OddConeDeficit

/-- Input parameters for the eight-tick/odd-cone pack. -/
structure TickPackParams where
  /-- β₀, the one-step deficit (nonnegative in applications). -/
  beta0 : Float
  /-- a > 0 is the geometric/refresh parameter determining the scale. -/
  a : Float

/-- Output of the pack: the physical cut scale c_cut. -/
structure TickPackOut where
  c_cut : Float

/-- Closed form for c_cut as a function of `a` and `β₀`.
This mirrors the pipeline used in the Transfer module, specialized here. -/
def c_cut_of (a beta0 : Float) : Float :=
  - (Float.log (Float.max 1e-9 (1.0 - beta0))) / a

@[simp] theorem c_cut_of_def (a beta0 : Float) :
  c_cut_of a beta0 = - (Float.log (Float.max 1e-9 (1.0 - beta0))) / a := rfl

/-- Spec for the tick pack: it returns the closed-form c_cut. -/
def tick_pack_spec (P : TickPackParams) (O : TickPackOut) : Prop :=
  O.c_cut = c_cut_of P.a P.beta0

/-- Build the tick pack from `(β₀,a)`, producing `c_cut`. -/
def build_tick_pack (P : TickPackParams) : TickPackOut :=
  { c_cut := c_cut_of P.a P.beta0 }

@[simp] theorem build_tick_pack_c_cut (P : TickPackParams) :
  (build_tick_pack P).c_cut = c_cut_of P.a P.beta0 := rfl

theorem build_tick_pack_satisfies (P : TickPackParams) :
  tick_pack_spec P (build_tick_pack P) := by rfl

end YM.OSWilson.OddConeDeficit


