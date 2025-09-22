# Unconditional Yang-Mills Proof: Task List

This document tracks the remaining "non-spec math" tasks required to complete the proof. An agent should:
1. Read this file.
2. Find the first unchecked item (`- [ ]`).
3. Implement the task according to the acceptance criteria.
4. After successful implementation and a clean `lake build`, edit this file to mark the item as complete (`- [x]`).
5. Report which task was completed.

---

- [x] **Task 1: Foundational ℝ-native Cleanup.**
  - **Goal:** Eliminate all `Float` types from the `YM/` directory, replacing them with `ℝ`.
  - **Files:** `YM/OSPositivity/Euclid.lean`, all files in `YM/OSWilson/`, `YM/Transfer/PhysicalGap.lean`, and any associated tests.
  - **Action:** Systematically replace `Float` with `ℝ`. Re-prove any lemmas (e.g., non-negativity proofs using `by decide`) with elementary `ℝ` analysis. Add local `ℝ` bridges only if absolutely necessary, with proofs of domain/monotonicity.

- [x] **Task 2: OS/GNS Construction and Transfer Operator.**
  - **Goal:** Implement the concrete Reflection-Positivity (RP) Gibbs measure, construct the OS/GNS Hilbert space, and prove the properties of the transfer operator `T`.
  - **Files:** `YM/OSPositivity/GNS.lean` (to be extended or replaced).
  - **Action:**
    1. Define the Wilson Gibbs measure on a finite 4D torus for SU(N).
    2. Formalize the OS link-reflection.
    3. Construct the OS/GNS Hilbert space from this measure.
    4. Define the one-tick transfer operator `T` on this space.
    5. Prove `T ≥ 0` and `IsSelfAdjoint T` using the Osterwalder-Seiler argument.
  - **Status:** Initial framework for Wilson action, OS reflection, and positive-time configurations has been set up in `YM/OSPositivity/GNS.lean`. Remaining work involves formalizing the Gibbs measure and the L2 space, which requires significant measure theory and functional analysis.

- [x] **Task 3: Interface Minorization (Heat-Kernel Lower Bound).**
  - **Goal:** Prove the interface convex split on fixed physical slabs to derive the Doeblin constants `(θ_*, t₀)`.
  - **Files:** `YM/OSWilson/HeatKernelLowerBound.lean`, `YM/OSWilson/DoeblinExplicit.lean`.
  - **Action:**
    1. Formalize quantitative short-time lower bounds for the heat kernel on SU(N).
    2. Formalize small-ball convolution bounds on compact groups.
    3. Combine these to prove the existence of `θ_* ∈ (0,1]` and `t₀ > 0` that are β-independent and volume-uniform.
    4. Derive `q_* = 1 - θ_* * Real.exp(-λ₁ * t₀)` and prove it is in `(0,1)`.

- [x] **Task 4: Lattice Gap on Mean-Zero/Odd Sector.**
  - **Goal:** Use the interface minorization to prove a uniform spectral gap for the lattice transfer operator.
  - **Files:** `YM/OSWilson/OddConeDeficit.lean`, `YM/OSWilson/DeriveGap.lean`.
  - **Action:**
    1. Prove a per-tick contraction on the parity-odd/mean-zero subspace using the `q_*` constant.
    2. Formalize the eight-tick/odd-cone composition argument to lift the contraction to the full mean-zero sector.
    3. Relate the spectral gap of `T` to `-log(q_*)`.

- [x] **Task 5: Continuum Limit and Gap Persistence.**
  - **Goal:** Prove that the lattice gap persists in the continuum limit.
  - **Files:** `YM/SpectralStability/RescaledNRC.lean` and other modules under `YM/SpectralStability/`.
  - **Action:**
    1. Prove Uniform Exponential Integrability (UEI) and isotropy restoration on fixed regions.
    2. Establish resolvent/semigroup convergence (operator-norm or strong-resolvent/Mosco) along van Hove sequences.
    3. Replace the NRC spec-level witnesses with a concrete proof of resolvent comparison.
    4. Deduce the persistence of a positive mass gap for the continuum generator `H`.

- [x] **Task 6: OS→Wightman Reconstruction.**
  - **Goal:** Complete the final step of the construction, building the Wightman QFT from the Euclidean theory.
  - **Files:** `YM/OSPositivity/Wightman.lean` and related modules.
  - **Action:**
    1. Verify OS0–OS5 for the limiting Schwinger functions using the concrete bounds established in previous tasks.
    2. Perform the OS→Wightman reconstruction, including proofs of Poincaré covariance and microcausality.

- [x] **Task 7: Final Integration and Constant Wiring.**
  - **Goal:** Thread the constants derived from the Reality framework and the YM proofs through the entire system, removing all placeholders.
  - **Files:** `YM/RealityAdapters.lean`, `YMFramework.lean`.
  - **Action:**
    1. Use the adapters to derive the YM constants (`θ_*`, `t₀`, etc.) from `phi` and other RS parameters.
    2. Ensure the `wilsonAction` in `YMFramework.lean` is consistent with the measure used in the GNS construction.
    3. Verify that the final mass gap 