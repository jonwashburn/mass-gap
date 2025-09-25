### YM-Plus: Scope to Finish the Unconditional Proof

## Build/Health
- Current status: repository builds cleanly (`lake build`). No `sorry`/`admit` in YM code.

## What’s Already Solid (Real-native, compiles)
- Reality integration and constants wiring (`YM/RealityAdapters.lean`).
- Doeblin interface and `q_*` positivity (`YM/OSWilson/Doeblin.lean`, `DoeblinExplicit.lean`).
- Heat-kernel minorization interface (probability kernel and inequality with Haar at r=0) (`YM/OSWilson/HeatKernelLowerBound.lean`).
- Gap derivation numerics and golden-gap corollary (`YM/OSWilson/DeriveGap.lean`, `GoldenGap.lean`).
- Spec-level OS axioms scaffolding (`YM/OSPositivity/*`).
- NRC interface and trivial convergence witness (`YM/SpectralStability/RescaledNRC.lean`).

## Remaining Work to Reach Unconditional (no placeholders, end-to-end)
1) OS/GNS: Concrete Transfer Operator (Step 1)
   - Replace `transferOperator := id` with the actual one-tick OS/GNS transfer built from the Wilson Gibbs measure on the slab (Markov operator via conditional expectation top|bottom).
   - Prove: `IsSelfAdjoint T` and quadratic-form positivity on `OSStateSpace`.
   - Status helpers already present: continuity of `totalAction`, positivity of `partitionFunction`.

2) Doeblin/Heat-Kernel Minorization (Step 2)
   - Upgrade `heat_kernel_lower_bound` from the Haar r=0 inequality to a genuine short-time heat-kernel lower bound on `SU(N)` (Varadhan/Minakshisundaram–Pleijel, small-time Gaussian lower bounds, injectivity radius control).
   - Thread explicit `(θ_*, t₀)` from Reality into the slab kernel split, independent of β and volume.

3) Subspace Contraction (Step 3)
   - Implement the contraction proof on the mean-zero, parity-odd subspace using the Doeblin split and first eigenvalue `λ₁(G)` to obtain `‖T‖ ≤ q_* < 1` on that sector.
   - Prove eight-tick contraction on the entire mean-zero subspace (odd-cone composition).

4) Spectral Identification (Step 3)
   - Connect the lattice contraction to the spectral radius on the restricted space and identify the mass gap as `γ₀ := −log q_*` rigorously.

5) Continuum Limit and Persistence (Step 4)
   - Replace the trivial operator family with the actual lattice transfer operators `T_a` (van Hove nets on fixed regions).
   - Prove strong/norm-resolvent convergence to a continuum operator; show spectral semicontinuity/persistence of a positive gap.

6) OS→Wightman Stack (Step 5)
   - Replace spec-level acceptance with unconditional proofs: OS0–OS5 on limiting Schwinger functions, reconstruction, Poincaré covariance, microcausality.

## File-Level Deltas
- `YM/OSPositivity/GNS.lean`: implement interface kernel and transfer; prove self-adjointness/positivity.
- `YM/OSWilson/HeatKernelLowerBound.lean`: add small-time lower bound for `SU(N)` heat kernel; quantify `t₀` and constants.
- `YM/OSWilson/SubspaceContraction.lean`: replace spec proof with Doeblin-based contraction proofs.
- `YM/OSWilson/DeriveGap.lean`: add spectral radius identification proof (currently numeric corollary is present).
- `YM/SpectralStability/RescaledNRC.lean` (and `Persistence.lean` if added): replace trivial operator family with `T_a`, prove resolvent/semigroup convergence and spectral gap persistence.
- `YM/OSPositivity/*`: strengthen Euclid/OS2/Clustering/LocalFields from spec to unconditional theorems.

## Suggested Execution Order (incremental, buildable after each step)
1. GNS transfer operator (minimal conditional-expectation construction on the slab) with self-adjointness and positivity.
2. Heat-kernel lower bound (Varadhan-type, SU(N)), thread `(θ_*, t₀)`.
3. Mean-zero/odd contraction and eight-tick contraction; bind `q_*`.
4. Spectral radius = `q_*` on the sector; define `γ₀` and connect to OS5.
5. NRC and persistence using actual `T_a` family (fixed regions).
6. Finalize OS→Wightman and `Clay/Final.lean` acceptance.

## Acceptance Criteria
- No axioms; no `sorry`; proofs Real-native; `(θ_*, t₀, λ₁(G))` threaded from Reality; `lake build` passes.

## References
- Mass-Gap repo plan: `https://github.com/jonwashburn/mass-gap`
- Reality framework and certificates: `https://github.com/jonwashburn/reality`


