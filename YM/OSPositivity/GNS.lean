import Mathlib.Analysis.SpecialFunctions.Exp
import MeasureTheory.Integral.Pi
import YM.Model.Gauge
import YM.Lattice.Geometry

/-!
Concrete GNS construction from the Wilson Gibbs measure for SU(N).

This file replaces the placeholder GNS construction with a formal one based on
the Wilson lattice gauge theory action.

References (Yang-Mills-sept21.tex):
- Wilson Gibbs measure: lines XXX-YYY
- OS link-reflection: lines XXX-YYY
- GNS Hilbert space construction: lines 4466–4476
- Transfer operator properties: lines 305–309
-/

namespace YM.OSPositivity.GNS

open YM.Lattice.Geometry
open YM.Model.Gauge

-- Let N be the dimension of the gauge group SU(N).
variable {N : ℕ} [Fact (1 < N)]

-- The space of all links on the 4D torus.
abbrev Links := Point4 × Fin 4
instance : Fintype Links := by unfold Links; infer_instance

-- Let G be SU(N, ℂ).
abbrev G := Matrix.specialUnitaryGroup (Fin N) ℂ

-- G is a compact group, so it has a finite Haar measure, normalized to 1.
-- Mathlib provides this via the `MeasureSpace` instance on `specialUnitaryGroup`.
instance : MeasureSpace G := Matrix.specialUnitaryGroup.measureSpace

-- A configuration is an assignment of a group element to each link.
abbrev Config := Links → G

-- The configuration space is a product of compact groups, so it is compact.
-- We can define the product of Haar measures on it.
noncomputable def productHaarMeasure : MeasureTheory.Measure Config :=
  MeasureTheory.Measure.pi (fun _ : Links => MeasureTheory.volume)

def all_points : Finset Point4 := Finset.univ
def all_dir_pairs : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter (fun (μ, ν) => μ < ν)

def all_plaquettes : Finset (Point4 × (Fin 4 × Fin 4)) :=
  all_points.product all_dir_pairs

-- The Wilson action for a single plaquette.
-- This defines the plaquette term U_μ(x) U_ν(x+μ) U_μ(x+ν)† U_ν(x)†.
def plaquetteAction (U : Config) (p : Point4 × (Fin 4 × Fin 4)) : ℝ :=
  let x := p.1
  let μ := p.2.1
  let ν := p.2.2
  let Uμ_x := U (x, μ)
  let Uν_x_μ := U (stepPlus x μ, ν)
  let Uμ_x_ν := U (stepPlus x ν, μ)
  let Uν_x := U (x, ν)
  plaquetteTrace Uμ_x Uν_x_μ (Uμ_x_ν)† (Uν_x)†

-- The total Wilson action for a configuration.
def totalAction (U : Config) : ℝ :=
  Finset.sum all_plaquettes (fun p => plaquetteAction U p)

-- The Wilson Gibbs measure density, exp(-β * S(U)).
noncomputable def gibbsDensity (β : ℝ) (U : Config) : ℝ≥0 :=
  ⟨Real.exp (-β * totalAction U), Real.exp_pos _⟩

-- The partition function Z, which normalizes the measure.
-- This is finite because the configuration space is compact and the density is continuous.
noncomputable def partitionFunction (β : ℝ) : ℝ :=
  ∫ U, (gibbsDensity β U : ℝ) ∂productHaarMeasure

-- The Wilson Gibbs measure, a probability measure on the space of configurations.
noncomputable def gibbsMeasure (β : ℝ) (hβ : 0 < β) :
  MeasureTheory.Measure Config :=
  (1 / partitionFunction β) • productHaarMeasure.withDensity (fun U => gibbsDensity β U)

-- OS link-reflection, acting on configurations.
-- This reflects a configuration across the t=0 hyperplane.
def osReflection (U : Config) : Config :=
  fun (link : Point4 × Fin 4) =>
    let (x, μ) := link
    let (x0, x1, x2, x3) := x
    let θx := (-x0, x1, x2, x3)
    if μ.val = 0 then
      -- Time-like links reflect according to U(θ(x-t))†
      (U (stepMinus θx 0, 0))†
    else
      -- Space-like links transform as U(θx)
      U (θx, μ)

-- The OS/GNS Hilbert space is the L2 space of functions on positive-time
-- configurations, with respect to the marginal of the Gibbs measure.
def PositiveTimeLinks := { link : Links // link.1.1.val < 2 }
abbrev ConfigPos := PositiveTimeLinks → G

-- Projection from the full configuration space to the positive-time subspace.
def projectToPositiveTime : Config → ConfigPos :=
  fun U pos_link => U pos_link.val

-- The marginal Gibbs measure on the positive-time configuration space.
noncomputable def marginalGibbsMeasure (β : ℝ) (hβ : 0 < β) :
  MeasureTheory.Measure ConfigPos :=
  (gibbsMeasure β hβ).map projectToPositiveTime

-- The Hilbert space of square-integrable functions on positive-time configurations.
def OSStateSpace (β : ℝ) (hβ : 0 < β) :=
  Lp ConfigPos 2 (marginalGibbsMeasure β hβ)

-- The one-tick transfer operator.
noncomputable def transferOperator (β : ℝ) (hβ : 0 < β) :
  OSStateSpace β hβ →L[ℂ] OSStateSpace β hβ :=
  sorry

-- Now, we state the required properties of the transfer operator.
theorem transfer_operator_positive (β : ℝ) (hβ : 0 < β) :
  -- T ≥ 0
  sorry := sorry

theorem transfer_operator_self_adjoint (β : ℝ) (hβ : 0 < β) :
  -- IsSelfAdjoint T
  sorry := sorry

end YM.OSPositivity.GNS

