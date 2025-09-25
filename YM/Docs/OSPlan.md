# OS Positivity → Wightman Blueprint

## Scope
- Audit spec-level scaffolding across `YM/OSPositivity/*` and identify the
  analytic ingredients needed for a full OS0–OS5 proof.
- Map the reconstruction pipeline from Schwinger data to Wightman fields and
  record external dependencies (transfer, NRC, heat kernel, clustering, continuum limit).
- Align the Clay certificate with the documented chain of lemmas and TODO items.

Key literature hooks: Yang-Mills-sept21.tex §§3–5 (citations below),
Osterwalder–Schrader (1973/75), Glimm–Jaffe Ch. VI.

## OS Axiom Modules — Current Gaps

- `YM/OSPositivity/Euclid.lean`
  - Placeholders: `EqModParams`, `RotationApproxParams`, `TranslationLimitParams`, and `EuclidAggregate*` only record radii/errors.
  - Needed proofs: UEI equicontinuity (Lemma E1-tightness, Prop. OS0-poly), rotation/translation commutator control (Lemma commutator-Oa2, Cor. resolvent-commutator), and $E(4)$ invariance (Thm. global-OS01).
  - Dependencies: `YM/OSWilson/HeatKernelLowerBound.lean`, `YM/Transfer/OSGNS.lean`, `YM/SpectralStability/RescaledNRC.lean`, `YM/SpectralStability/Persistence.lean`.
  - References: Yang-Mills-sept21.tex lines 1200–1314, 1482–1504, 1551–1560.

- `YM/OSPositivity/OS2.lean`
  - Placeholders: scalar `TwoPoint`, simple positivity predicate, trivial builder.
  - Needed proofs: Schwinger reflection geometry (Prop. os0os2-closure), limit stability (Lemma “OS2 preserved under limits”), implementation of the reflection map $\theta$.
  - Dependencies: `YM/OSPositivity/LocalFields.lean`, `YM/Transfer/OSGNS.lean`, `YM/OSWilson/HeatKernelLowerBound.lean`.
  - References: Yang-Mills-sept21.tex lines 271–331, 1200–1219, 1551–1560.

- `YM/OSPositivity/Clustering.lean`
  - Placeholders: `Params` without smearing/cylinder metadata, clustering defined as mere gap positivity.
  - Needed proofs: exponential decay bound from eight-tick contraction (Thm. eight-tick-uniform) and gap persistence (Thm. gap-persist-cont), Doeblin minorization (Cor. hk-convex-split-explicit).
  - Dependencies: `YM/OSWilson/Doeblin.lean`, `YM/OSWilson/Cluster.lean`, `YM/OSWilson/DeriveGap.lean`, `YM/SpectralStability/Persistence.lean`.
  - References: Yang-Mills-sept21.tex lines 1200–1319, 4466–4476, 5085–5101.

- `YM/OSPositivity/LocalFields.lean`
  - Placeholders: scalar `LocalField`, positivity as nonnegativity, trivial builders.
  - Needed proofs: smeared gauge-invariant observables via kernels $\kappa_\rho$ and embeddings $E_{a,R}$ (Lemma graph-defect-core, Prop. embedding-independence) and reflection-compatible time-zero cores.
  - Dependencies: `YM/OSPositivity/Euclid.lean`, `YM/Transfer/OSGNS.lean`, `YM/OSWilson/HeatKernelLowerBound.lean`.
  - References: Yang-Mills-sept21.tex lines 1214–1220, 1278–1279, 1497–1508.

- `YM/OSPositivity/Wightman.lean`
  - Placeholders: scalar `WightmanField`, propositional covariance/analytic continuation, simplified reconstruction outputs.
  - Needed proofs: full OS→W reconstruction (Thm. os-to-wightman), Hilbert completion, Hamiltonian extraction, analytic continuation, microcausality from OS4.
  - Dependencies: `YM/OSPositivity/Euclid.lean`, `YM/OSPositivity/OS2.lean`, `YM/OSPositivity/LocalFields.lean`, `YM/OSPositivity/Clustering.lean`, `YM/OSPositivity/GNS.lean`, `YM/Transfer/OSGNS.lean`, `YM/SpectralStability/RescaledNRC.lean`.
  - References: Yang-Mills-sept21.tex lines 271–309, 390ff, 1200–1268, 1482–1504, 1551–1560, 4466–4476.

## Reconstruction Pipeline Sketch

1. **Schwinger Input**
   - Families `{S_n}` with OS0–OS5 (Theorem global-OS0-5) built from smeared,
     gauge-invariant observables.
   - Dependencies: UEI bounds, NRC/heat-kernel convergence, transfer contraction.

2. **Pre-Hilbert Space Construction**
   - Define `𝒟` via finite linear combinations of cylinder insertions at positive
     Euclidean times; quotient by null space from OS2.
   - Needs formal encoding of reflection map `θ` and semi-definite form
     `⟨F,G⟩ = S_{m+n}(θF, G)`.

3. **Hilbert Completion & Vacuum**
   - Complete `𝒟` to Hilbert space `ℋ_OS`; vacuum vector comes from the unit observable.
   - Requires transport of gap bounds to show spectral radius estimates.

4. **Hamiltonian and Transfer Operator**
   - Extract positive self-adjoint generator `H` from time translations, using
     NRC convergence and eight-tick contraction (ensures `spec(H) ⊂ [0,∞)` with gap `γ_*`).

5. **Field Operators**
   - Define smeared fields `Φ(f)` via insertions; check domain stability and
     covariance under Euclidean transformations.
   - Requires formal smearing framework and control of local cores.

6. **Analytic Continuation / Poincaré Covariance**
   - Extend time parameter to complex strip using Schwinger analyticity; obtain
     unitary representation of Poincaré from Euclidean invariance.
   - Dependencies: commutator bounds (Lemma commutator-Oa2), resolvent control,
     NRC analytic continuation (Cor. nrc-allz-fixed).

7. **Locality (Microcausality)**
   - Translate OS4 permutation symmetry to vanishing commutators for spacelike
     separation after Wick rotation (Thm. microcausality-poincare).

8. **Mass Gap Persistence**
   - Show the Minkowski Hamiltonian retains gap `γ_*` via spectral stability
     results (Thm. gap-persist-cont) and transfer contraction.

## Clay Certificate Alignment

- `YM/Clay/Final.lean` (spec-level): currently exports `FinalParams`, `FinalAcceptance`, and
  `build_final`. The final theorem should certify a mass gap once OS0–OS5 and
  reconstruction are mechanized.
  - Outstanding proofs: genuine OS2 witness (`YM/OSPositivity/OS2.lean`),
    reconstruction of the Wightman field (`YM/OSPositivity/Wightman.lean`),
    persistence of the spectral gap (`YM/SpectralStability/Persistence.lean`).
  - TODOs record dependencies on transfer contraction (`YM/OSWilson/DeriveGap.lean`),
    heat-kernel bounds (`YM/OSWilson/HeatKernelLowerBound.lean`), and clustering
    (`YM/OSPositivity/Clustering.lean`).

- Roadmap for completion:
  1. Implement UEI/OS1 in `Euclid.lean` with explicit modulus witnesses.
  2. Formalize the reflection-positive local core in `LocalFields.lean` and feed
     it into `OS2.lean`.
  3. Derive exponential clustering and microcausality via `Clustering.lean` and
     `Wightman.lean`.
  4. Assemble the OS→W reconstruction, track the Hamiltonian, and propagate the
     gap into the Clay certificate.
  5. Replace spec-level builders in `Final.lean` with the actual mass-gap proof.

## Dependency Summary

- Transfer and contraction: `YM/OSWilson/Doeblin.lean`, `YM/OSWilson/SubspaceContraction.lean`,
  `YM/OSWilson/DeriveGap.lean`, `YM/OSWilson/HeatKernelLowerBound.lean`.
- Heat-kernel & NRC: `YM/SpectralStability/RescaledNRC.lean`, `YM/SpectralStability/Persistence.lean`.
- Continuum limit & embeddings: `Yang-Mills-sept21.tex` §§3.4–3.6, plus
  references to Mosco convergence (appendix) for cross-checks.
- Clustering & spectrum: `YM/OSPositivity/Clustering.lean`, `YM/OSWilson/Cluster.lean`.
- Reflection positivity & local fields: `YM/OSPositivity/OS2.lean`, `YM/OSPositivity/LocalFields.lean`.

## Outstanding Lemmas / Tasks

1. **Equicontinuity modulus lemma** — formalize UEI bound tying lattice and
   continuum Schwinger functions (Euclid module).
2. **Rotation/translation convergence** — implement the commutator estimates
   yielding $O(a^2)$ Euclidean invariance errors.
3. **Reflection positivity closure** — encode OS2 limit lemma from the text.
4. **Exponential clustering** — derive explicit decay bounds from transfer gap.
5. **Analytic continuation lemma** — show Schwinger functions extend to strip
   and produce unitary Minkowski time evolution.
6. **Microcausality transport** — formalize the OS→W locality argument using
   permutation symmetry and support separation.
7. **Gap persistence theorem** — connect lattice gap `γ_*` to Minkowski gap in Lean.

These lemmas must be implemented before the Clay certificate can certify an
unconditional mass gap. Each TODO in the OS positivity modules references the
specific analytic components needed to complete the chain.


