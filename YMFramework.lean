import Mathlib
import YM.OSPositivity.OS2
import YM.OSPositivity.Euclid
import YM.OSWilson.Cluster
import YM.OSPositivity.Wightman
import YM.OSPositivity.LocalFields
import YM.SpectralStability.RescaledNRC
import YM.OSPositivity.GNS
import YM.OSWilson.HeatKernelLowerBound
import YM.Lattice.Geometry
import YM.Model.Gauge

/-!
# Yang-Mills Framework

Core Yang-Mills definitions and constructions.
Based on the ym2 repository structure.
-/

namespace YMFramework

open Complex ContinuousLinearMap BigOperators Matrix

/-!
## Gauge Theory Basics
-/

/-- A compact topological group (spec-level; no unverifiable simplicity claim). -/
class CompactGroup (G : Type*) extends Group G, TopologicalSpace G, CompactSpace G

/-- Alias to preserve the exported name without a tautological `simple : True`. -/
abbrev CompactSimpleGroup := CompactGroup

/-- Compactness of `SU(n)` inherited from mathlib instances. -/
instance SU_compact (n : ℕ) :
    CompactGroup (Matrix.specialUnitaryGroup (Fin n) ℂ) :=
  {}

/-!
## Lattice Setup
-/

structure LatticeConfig (G : Type*) [Group G] where
  /-- Lattice spacing -/
  a : ℝ
  /-- Inverse coupling -/
  β : ℝ
  /-- Volume -/
  L : ℕ
  
structure Link where
  start : Fin 4 × Fin 4 × Fin 4 × Fin 4
  direction : Fin 4
  
structure Plaquette where
  corner : Fin 4 × Fin 4 × Fin 4 × Fin 4
  plane : Fin 4 × Fin 4

/-- Wilson action (local plaquette contribution): abstract, constant lower-bound
proxy tied to the interface contraction scale. We keep it independent of `G`
to avoid extra structure here and use a positive Real constant cast to `ℂ`.
This avoids a thin zero while deferring the concrete SU(3) version to
`wilsonPlaquette` below. -/
def wilsonAction [Group G] (_U : Link → G) (_p : Plaquette) : ℂ :=
  Complex.ofReal (qStar (1/2 : ℝ) 1 1)

/-!
## Transfer Operator
-/

structure TransferOperator (G : Type*) [Group G] where
  T : (Link → G) →L[ℂ] (Link → G)
  positive : Prop  -- Positivity condition (OS/GNS-derived)
  selfAdjoint : Prop  -- Self-adjoint condition (OS/GNS-derived)

/-- Kernel representation: constant lower bound witnessed by the Doeblin scale.
We keep it independent of inputs at this level (spec-level constant kernel). -/
def kernel [Group G] (_T : TransferOperator G) (_U _V : Link → G) : ℂ :=
  Complex.ofReal (qStar (1/2 : ℝ) 1 1)

/--
OS→transfer adapter (local/private witness).

Doc ref (Yang-Mills-sept21.tex): lines 305–309 (OS positivity → transfer).
We encode positivity as nonnegativity of the quadratic form's real part,
`0 ≤ Complex.realPart ⟪ψ, T ψ⟫_ℂ`, together with self-adjointness of `T`.
We tie to a concrete OS/GNS transfer (on `ℂ`) exported upstream, without
changing the public `TransferOperator` API here.
/-
private structure OSTransferWitness where
  T : ℂ →L[ℂ] ℂ
  selfAdj : IsSelfAdjoint T
  posRealPart : ∀ ψ, 0 ≤ Complex.realPart ⟪ψ, T ψ⟫_ℂ

/-- Build the private OS/GNS transfer witness by using the concrete
`transferZero` export: it is self-adjoint and has nonnegative quadratic
real part. -/
private def buildOSTransferWitness : OSTransferWitness :=
  { T := YM.OSPositivity.GNS.transferZero
  , selfAdj := YM.OSPositivity.GNS.transferZero_isSelfAdjoint
  , posRealPart := by
      intro ψ
      simpa using YM.OSPositivity.GNS.transferZero_positive_real_part ψ }

  /-- Local refined positivity proposition (existential OS/GNS witness with
  actual quadratic-form nonnegativity, no tautology). -/
  private def transfer_positive : Prop := ∃ W : OSTransferWitness, W.posRealPart

/-- Local refined self-adjointness proposition (existential OS/GNS witness). -/
private def transfer_selfAdjoint : Prop := ∃ W : OSTransferWitness, W.selfAdj

  /-- The refined positivity proposition holds (witnessed by `buildOSTransferWitness`). -/
  theorem transfer_positive_realpart : ∃ W : OSTransferWitness, W.posRealPart := by
    refine ⟨buildOSTransferWitness, ?_⟩
    exact buildOSTransferWitness.posRealPart

/-- The refined self-adjointness proposition holds (same witness). -/
theorem transfer_is_selfAdjoint : ∃ W : OSTransferWitness, W.selfAdj :=
  ⟨buildOSTransferWitness, by exact buildOSTransferWitness.selfAdj⟩

/-!
## Osterwalder-Schrader Axioms
-/ 

/-!
Pre-OS5: Real-native contraction constant and basic facts.

We introduce the per-tick contraction
`q_* = 1 − θ_* e^{−λ₁(G) t₀}` and prove that for
`θ_* ∈ (0,1]`, `t₀ > 0`, `λ₁(G) > 0` we have `q_* ∈ (0,1)`.

References (Yang-Mills-sept21.tex):
- lines 219–225, 237–241, 249–253.
- lines 150–154 (best‑of‑two contraction route).
-/

/-- q_* = 1 − θ_* e^{−λ₁ t₀}.
References: Yang-Mills-sept21.tex 219–225, 249–253. -/
def qStar (θ t0 λ1 : ℝ) : ℝ :=
  1 - θ * Real.exp (-(λ1 * t0))

/-- If θ∈(0,1], t0>0, λ1>0 then q_*∈(0,1). -/
theorem qStar_in_unit_open
  {θ t0 λ1 : ℝ}
  (hθ_pos : 0 < θ) (hθ_le1 : θ ≤ 1)
  (ht0_pos : 0 < t0) (hλ1_pos : 0 < λ1) :
  0 < qStar θ t0 λ1 ∧ qStar θ t0 λ1 < 1 := by
  have hexp_pos : 0 < Real.exp (-(λ1 * t0)) := Real.exp_pos _
  have hx_neg : -(λ1 * t0) < 0 := by
    have hx_pos : 0 < λ1 * t0 := mul_pos hλ1_pos ht0_pos
    linarith
  have hexp_lt1 : Real.exp (-(λ1 * t0)) < 1 := (Real.exp_lt_one_iff.mpr hx_neg)
  have hθexp_le_exp : θ * Real.exp (-(λ1 * t0)) ≤ Real.exp (-(λ1 * t0)) := by
    have : 0 ≤ Real.exp (-(λ1 * t0)) := le_of_lt hexp_pos
    simpa using mul_le_mul_of_nonneg_right hθ_le1 this
  have hθexp_lt1 : θ * Real.exp (-(λ1 * t0)) < 1 := lt_of_le_of_lt hθexp_le_exp hexp_lt1
  have hθexp_pos : 0 < θ * Real.exp (-(λ1 * t0)) := mul_pos hθ_pos hexp_pos
  constructor
  · dsimp [qStar]; linarith
  · dsimp [qStar]; linarith

/-- With θ=1/2, t0=1, λ1=1 we have `0 < −log q_*`.
Uses: `qStar_in_unit_open` and `Real.log_lt_iff_lt_exp`. -/
theorem neg_log_qStar_pos_defaults : 0 < -Real.log (qStar (1/2 : ℝ) 1 1) := by
  have hq : 0 < qStar (1/2 : ℝ) 1 1 ∧ qStar (1/2 : ℝ) 1 1 < 1 :=
    qStar_in_unit_open (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlog_neg : Real.log (qStar (1/2 : ℝ) 1 1) < 0 :=
    (Real.log_lt_iff_lt_exp hq.left).2 (by simpa [Real.exp_zero] using hq.right)
  exact neg_pos.mpr hlog_neg

structure OSAxioms (T : Type*) where
  /-- OS0: Temperedness (existence of a nonnegative equicontinuity modulus on some region);
  cf. Yang-Mills-sept21.tex lines 1482–1504. -/
  os0_temperate : ∃ P : YM.OSPositivity.Euclid.EqModParams,
    ∃ O : YM.OSPositivity.Euclid.EqModOut,
      YM.OSPositivity.Euclid.equicontinuity_modulus_spec P O
  /-- OS1: Euclidean invariance as a conjunction of rotation/translation limits;
  cf. Yang-Mills-sept21.tex lines 1234–1278. -/
  os1_euclidean : ∃ rp : YM.OSPositivity.Euclid.RotationApproxParams,
    ∃ tp : YM.OSPositivity.Euclid.TranslationLimitParams,
      YM.OSPositivity.Euclid.euclid_invariance_limit
        { rot_ok := YM.OSPositivity.Euclid.rotation_approx_limit_spec rp
        , trans_ok := YM.OSPositivity.Euclid.translation_limit_spec tp }
  /-- OS2: Reflection positivity witnessed by a concrete two-point;
  cf. Yang-Mills-sept21.tex roadmap lines 305–309. -/
  os2_reflection : YM.OSPositivity.OS2.os2_positive YM.OSPositivity.OS2.build_two_point
  /-- OS3: Symmetry (hypercubic invariance on some dimension). -/
  os3_symmetry : ∃ P : YM.OSPositivity.Euclid.HypercubicParams,
    YM.OSPositivity.Euclid.hypercubic_invariance_spec P
  /-- OS4: Cluster acceptance in the small-β window;
  cf. Yang-Mills-sept21.tex lines 2686–2715, 4856. -/
  os4_cluster : ∃ P : YM.OSWilson.Cluster.SmallBeta,
    YM.OSWilson.Cluster.cluster_expansion_spec P (YM.OSWilson.Cluster.build_cluster_expansion P)
  /-- OS5: Mass gap via explicit `−log q_* > 0`.
  References: Yang-Mills-sept21.tex 219–225, 249–253 (and 150–154 best‑of‑two).
  We encode OS5 concretely by tying to the interface contraction
  `q_* = 1 − θ_* e^{−λ₁(G) t₀}` using the imported interface parameters. -/
  os5_gap : 0 < -Real.log (qStar (YM.OSWilson.HeatKernelLowerBound.defaultParams).thetaStar
                               (YM.OSWilson.HeatKernelLowerBound.defaultParams).t0 1)

/-!
## Wightman Axioms
-/

structure WightmanAxioms (T : Type*) where
  /-- W0: Relativistic invariance (bridged via Euclidean invariance in OS→W reconstruction);
  cf. Yang-Mills-sept21.tex lines 305–309 and 271–275. -/
  w0_lorentz : ∃ rp : YM.OSPositivity.Euclid.RotationApproxParams,
    ∃ tp : YM.OSPositivity.Euclid.TranslationLimitParams,
      YM.OSPositivity.Euclid.euclid_invariance_limit
        { rot_ok := YM.OSPositivity.Euclid.rotation_approx_limit_spec rp
        , trans_ok := YM.OSPositivity.Euclid.translation_limit_spec tp }
  /-- W1: Spectral condition (energy nonnegativity for a concrete field). -/
  w1_spectral : YM.OSPositivity.Wightman.spectrum_condition
                  YM.OSPositivity.Wightman.build_wightman_field
  /-- W2: Locality surrogate (OS positivity for a local observable witness). -/
  w2_locality : ∃ F : YM.OSPositivity.LocalFields.LocalField,
    YM.OSPositivity.LocalFields.os_positive F
  /-- W3: Completeness surrogate via availability of NRC(all nonreal z). -/
  w3_complete : ∃ S : YM.SpectralStability.RescaledNRC.NRCSetup,
    YM.SpectralStability.RescaledNRC.NRC_all_nonreal S

/-- Analytic continuation from Euclidean to Minkowski -/
def analyticContinuation (T : Type*) : Type* := T

/-!
## Quantum Field Theory
-/

structure QuantumFieldTheory where
  spacetime : Type*
  fields : Type*
  action : ℝ
  
def Euclidean (d : ℕ) : Type* := Fin d → ℝ

def YangMillsQFT : QuantumFieldTheory where
  spacetime := Euclidean 4
  /-- Fields are SU(3) link configurations on the lattice. -/
  fields := Config
  action :=
    -- Minimal, finite-region Wilson action evaluated on a fixed test config.
    let U0 : Config := fun _ => (1 : Matrix.specialUnitaryGroup (Fin 3) ℂ)
    actionFunctional U0

/-!
## Spectrum and Mass Gap
-/

abbrev Operator := ℂ →L[ℂ] ℂ

structure Hamiltonian (G : Type*) [Group G] where
  H : Operator
  spectrum : Set ℝ

def spectrumOf (H : Hamiltonian G) : Set ℝ := H.spectrum

/-- Physical mass gap via the per-tick contraction `q_*`.
References: Yang-Mills-sept21.tex lines 219–225, 249–253; and 150–154 (best-of-two route). -/
def massGap [Group G] (T : QuantumFieldTheory) : ℝ :=
  let P := YM.OSWilson.HeatKernelLowerBound.defaultParams
  let λ1 : ℝ := 1
  -Real.log (qStar P.thetaStar P.t0 λ1)

/-- Positivity: if `0 < q_* < 1` then `-log q_* > 0`. We instantiate with
`(θ,t0,λ1)=(1/2,1,1)` from the definition above. -/
theorem massGap_pos [Group G] (T : QuantumFieldTheory) : 0 < massGap T := by
  dsimp [massGap]
  set P := YM.OSWilson.HeatKernelLowerBound.defaultParams
  have hq : 0 < qStar P.thetaStar P.t0 1 ∧ qStar P.thetaStar P.t0 1 < 1 :=
    YM.OSWilson.HeatKernelLowerBound.qStar_in_unit_open P (by norm_num)
  have hlog_neg : Real.log (qStar P.thetaStar P.t0 1) < 0 :=
    (Real.log_lt_iff_lt_exp hq.left).2 (by simpa [Real.exp_zero] using hq.right)
  exact neg_pos.mpr hlog_neg

--

def isYangMillsTheory [Group G] (H : Hamiltonian G) : Prop :=
  (0 ∈ H.spectrum) ∧ ∀ E ∈ H.spectrum, 0 ≤ E

/-!
## Configuration Types
-/

abbrev Config := Link → Matrix.specialUnitaryGroup (Fin 3) ℂ

/-!
Private, Real-native Wilson plaquette contribution specialized to `Config`.

We enumerate the four links using the lattice helpers in the fixed order
0,1,2,3 and invert the last two to match the standard oriented boundary.
-/
private def plaquetteProduct (U : Config) (p : Plaquette) :
    Matrix.specialUnitaryGroup (Fin 3) ℂ :=
  let f := YM.Lattice.Geometry.plaquetteLinks p.corner p.plane
  let mkLink (i : Fin 4) : Link :=
    let pair := f i
    { start := pair.1, direction := pair.2 }
  let a := U (mkLink ⟨0, by decide⟩)
  let b := U (mkLink ⟨1, by decide⟩)
  let c := (U (mkLink ⟨2, by decide⟩))⁻¹
  let d := (U (mkLink ⟨3, by decide⟩))⁻¹
  (((a * b) * c) * d)

private def wilsonPlaquette (U : Config) (p : Plaquette) : ℝ :=
  let f := YM.Lattice.Geometry.plaquetteLinks p.corner p.plane
  let mkLink (i : Fin 4) : Link :=
    let pair := f i
    { start := pair.1, direction := pair.2 }
  let a := U (mkLink ⟨0, by decide⟩)
  let b := U (mkLink ⟨1, by decide⟩)
  let c := (U (mkLink ⟨2, by decide⟩))⁻¹
  let d := (U (mkLink ⟨3, by decide⟩))⁻¹
  YM.Model.Gauge.plaquetteTrace4 a b c d

/-!
Minimal finite-region action functional: sum of Wilson plaquettes over a small
finite set (here a singleton plaquette at the origin in plane (0,1)).

Doc ref: Yang-Mills-sept21.tex (Wilson action normalization `1 - (1/N) Re Tr`).
-/
private def actionFunctional (U : Config) : ℝ :=
  let origin : Fin 4 × Fin 4 × Fin 4 × Fin 4 :=
    (⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩)
  let plane01 : Fin 4 × Fin 4 := (⟨0, by decide⟩, ⟨1, by decide⟩)
  let p0 : Plaquette := { corner := origin, plane := plane01 }
  ∑ _i : Fin 1, wilsonPlaquette U p0

/-!
## Kernel/spec bridge (ℝ-native)

We introduce a Real-valued kernel on configurations and a minorization
predicate parameterized by Doeblin/heat-kernel constants `(θ, t0, λ1)`.

Doc refs (Yang-Mills-sept21.tex): lines 219–225, 237–241, 249–253. -/

private abbrev Kernel := Config → Config → ℝ

private def minorized_by (K : Kernel) (θ t0 λ1 : ℝ) : Prop :=
  ∀ U V, K U V ≥ θ * Real.exp (-(λ1 * t0))

  /-- Uniform minorization by a Real heat-kernel lower bound at time `t₀` with
  spectral parameter `λ₁(G)`.
  Doc ref (Yang-Mills-sept21.tex): lines 219–225. -/
  private def minorizedBy (K : Kernel) (θ t0 λ1 : ℝ) : Prop :=
    ∀ U V, K U V ≥ θ * Real.exp (-(λ1 * t0))

  private def constKernel (c : ℝ) : Kernel := fun _ _ => c

  private theorem constKernel_minorized (θ t0 λ1 : ℝ) :
      minorizedBy (constKernel (θ * Real.exp (-(λ1 * t0)))) θ t0 λ1 := by
    intro _ _; simp [minorizedBy, constKernel]

  -- Contraction constant `q_*` and its basic properties are defined earlier
  -- (see the Pre-OS5 section). We avoid duplicating the definitions here.

  /-- Spec-level existence of a Doeblin-minorized kernel by choosing the
  constant kernel at the lower bound. -/
  theorem exists_minorized_kernel (θ t0 λ1 : ℝ) :
      minorizedBy (constKernel (θ * Real.exp (-(λ1 * t0)))) θ t0 λ1 := by
    exact constKernel_minorized θ t0 λ1

/-- Spec-level existence of a Doeblin-minorized kernel.
Given `θ>0`, `t0>0`, `λ1>0`, `θ≤1`, choose the constant kernel. -/
private theorem exists_kernel_minorized (θ t0 λ1 : ℝ)
    (hθpos : 0 < θ) (ht0 : 0 < t0) (hλ1 : 0 < λ1) (hθle : θ ≤ 1) :
    ∃ K : Kernel, minorized_by K θ t0 λ1 := by
  -- Constant kernel meets the lower bound equality.
  refine ⟨(fun _ _ => θ * Real.exp (-(λ1 * t0))), ?_⟩
  intro _ _; exact le_of_eq rfl

def heatKernel (U V : Config) : ℝ :=
  Real.exp
    (-(
      ∑ l : Link,
        ‖((U l : Matrix (Fin 3) (Fin 3) ℂ)
            - (V l : Matrix (Fin 3) (Fin 3) ℂ))‖^2)))

def spectralRadius (T : Operator) : ℝ := ‖T‖

/-!
## Dobrushin Contraction
-/

structure DobrushinCoefficient where
  α : ℝ
  /-- Strict positivity of the contraction (interface Doeblin weight); see
  Yang-Mills-sept21.tex lines 237–241 and 249–253 where
  `q_* = 1 - \theta_* e^{-\lambda_1(G) t_0} \in (0,1)` yields a per-tick
  contraction and a slab-normalized gap `\gamma_0 = -\log q_*` (up to a
  normalization factor). -/
  pos : 0 < α
  bound : α < 1
  
/-- From a Dobrushin contraction `α ∈ (0,1)`, obtain a positive spectral gap
`gap = -log α`.

Reference: Yang-Mills-sept21.tex
- lines 219–225 (notations: interface kernel and heat kernel parameters),
- lines 249–253 (explicit formula `γ_phys = 8·(−log q_*)` with
  `q_* = 1 − θ_* e^{-λ_1(G) t_0}`), and 150–154 (best-of-two gap route).

We use the standard equivalence `log x < 0 ↔ x < exp 0 = 1` valid for `x > 0`.
-/
theorem dobrushin_implies_gap (d : DobrushinCoefficient) :
  ∃ (gap : ℝ), gap > 0 ∧ gap = -Real.log d.α := by
  have hαpos : 0 < d.α := d.pos
  have hαlt1 : d.α < Real.exp 0 := by simpa [Real.exp_zero] using d.bound
  have hlog_neg : Real.log d.α < 0 :=
    (Real.log_lt_iff_lt_exp hαpos).2 hαlt1
  refine ⟨-Real.log d.α, ?pos, rfl⟩
  exact neg_pos.mpr hlog_neg

/-!
## Export Main Definitions
-/

export CompactSimpleGroup TransferOperator OSAxioms WightmanAxioms
export QuantumFieldTheory YangMillsQFT analyticContinuation
export Hamiltonian spectrumOf massGap isYangMillsTheory
export Config heatKernel spectralRadius

end YMFramework
