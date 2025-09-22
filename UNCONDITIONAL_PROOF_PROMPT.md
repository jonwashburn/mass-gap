### Mission
Your primary mission is to complete the unconditional, machine-verified proof of the Yang-Mills mass gap. You will achieve this by systematically working through the task list below, replacing all spec-level placeholders, `sorry`s, and `admit`s with rigorous, formal proofs in Lean.

### Context
The project synthesizes two repositories:
1.  **`reality/`**: A foundational framework providing core physical and mathematical constants, intended as the meta-spine for the proof.
2.  **`YM/`**: The formalization of the Yang-Mills theory and the mass gap proof, which is currently "spec-level"—the structure is present, but the difficult analytical proofs are placeholders.

Your work must follow the strategy outlined in `YM_REALITY_INTEGRATION_PLAN.md`. The final proof must be fully "Real-native," deriving its constants from the `reality` framework and containing no shortcuts.

### Rules of Engagement
1.  **No Shortcuts**: You must not use `sorry`, `admit`, axioms, or placeholder implementations (e.g., defining operators as `0`, using toy kernels, or returning trivial values like `True` or `0` to satisfy a `Prop`). All proofs must be fully constructive and machine-verified.
2.  **One Task at a Time**: Address only the first task in the "Remaining Tasks" list. Do not proceed to the next task.
3.  **Indefinite Requeue**: After you successfully complete a task, I will remove it from the list and requeue this prompt for you to begin the next one.
4.  **Adhere to the Plan**: Your proofs must align with the six-step workflow described in `YM_REALITY_INTEGRATION_PLAN.md`.

---

## Unconditional Proof Task List

Please begin with Task 1.

### Remaining Tasks:

**1. Formalize the OS/GNS Framework and Lattice Measure (Integration Plan: Step 1)**
*   **File Path**: `YM/OSPositivity/GNS.lean`
*   **Current State**: This file is a major structural placeholder.
    *   The `transferOperator` is defined as the zero operator (`0`).
    *   It contains `sorry`s for proving the continuity of the total action and the positivity of the partition function.
*   **Task**:
    1.  Replace the `transferOperator := 0` definition with the actual, non-trivial transfer operator derived from the Wilson Gibbs measure and the lattice structure.
    2.  Prove that this operator is self-adjoint and positive (`IsSelfAdjoint T` and `T ≥ 0`).
    3.  Complete the `sorry` proofs for `continuous_totalAction` and `partitionFunction_pos` to ensure the underlying Gibbs measure is well-defined and a valid probability measure.

**2. Prove the Doeblin/Heat-Kernel Minorization (Integration Plan: Step 2)**
*   **File Path**: `YM/OSWilson/HeatKernelLowerBound.lean`
*   **Current State**: This file has no `sorry`s but its central proof, `heat_kernel_lower_bound`, is a stub. It assumes the key mathematical inequalities rather than proving them. It also contains several `TODO`s for formalizing the Laplace-Beltrami operator and the heat kernel itself.
*   **Task**:
    1.  Formalize the necessary geometric objects on SU(N), including the Laplace-Beltrami operator.
    2.  Replace the placeholder logic in `heat_kernel_lower_bound` with a rigorous, unconditional proof of the short-time lower bound for the heat kernel on SU(N), likely using Varadhan's formula or a similar result.
    3.  Ensure the constants `t₀` and `θ_*` are correctly derived from the Reality framework parameters as intended.

**3. Establish the Uniform Lattice Gap (Integration Plan: Step 3)**
*   **File Path**: `YM/OSWilson/SubspaceContraction.lean`
*   **Current State**: This file contains two critical `sorry`s that are placeholders for the core mass gap argument. The `parityOperator` is also `opaque`.
*   **Task**:
    1.  Implement the `parityOperator`.
    2.  Complete the proof for `transfer_operator_contracts_on_mean_zero_odd_subspace`. This requires proving that the transfer operator `T` contracts states in the mean-zero, parity-odd subspace by a factor `q_* < 1`.
    3.  Complete the proof for `eight_tick_operator_contracts_on_mean_zero_subspace`. This requires proving that the eight-tick operator `T^8` contracts the entire mean-zero subspace.

**4. Connect the Lattice Gap to the Spectral Radius (Integration Plan: Step 3)**
*   **File Path**: `YM/OSWilson/DeriveGap.lean`
*   **Current State**: Contains a `sorry` in the `mass_gap_eq_gamma0` theorem.
*   **Task**: Complete the proof of `mass_gap_eq_gamma0`. This involves formally demonstrating that the spectral radius of the transfer operator, when restricted to the mean-zero subspace, is equal to the contraction factor `q_*`, thus connecting the abstract definition of the mass gap to the concrete value `gamma0`.

**5. Prove Continuum Limit and Gap Persistence (Integration Plan: Step 4)**
*   **File Path**: `YM/SpectralStability/RescaledNRC.lean` and `YM/SpectralStability/Persistence.lean`
*   **Current State**: These are spec-level files that outline the *requirements* for the continuum limit via Norm-Resolvent Convergence (NRC) and spectral persistence. They use trivial builders (e.g., a zero-operator family) to satisfy the specs.
*   **Task**:
    1.  Replace the placeholder structures in `RescaledNRC.lean` with the actual transfer operators for a sequence of lattice spacings `a`.
    2.  Prove that this sequence of operators converges in the strong or norm-resolvent sense to a continuum operator.
    3.  In `Persistence.lean`, replace the abstract `rieszSemicontinuity` proposition with a rigorous proof, likely based on Riesz projections or spectral semicontinuity, showing that the spectral gap does not close in the continuum limit.

**6. Complete the OS-to-Wightman Reconstruction (Integration Plan: Step 5)**
*   **File Paths**: `YM/OSPositivity/Euclid.lean`, `YM/OSPositivity/LocalFields.lean`, `YM/OSPositivity/OS2.lean`, `YM/OSPositivity/Clustering.lean`, `YM/Clay/Final.lean`
*   **Current State**: These files are all spec-level placeholders that use trivial builders (returning `0` or `True`) to satisfy the required OS axioms.
*   **Task**: Systematically replace the placeholder implementations in these files with unconditional proofs demonstrating that the constructed continuum theory satisfies:
    *   **OS1 (Euclidean Invariance)** in `Euclid.lean`.
    *   **OS2 (Positivity)** in `OS2.lean`.
    *   **OS3 (Clustering)** in `Clustering.lean`.
    *   Construct proper, non-trivial smeared field operators in `LocalFields.lean`.
    *   Once all axioms are proven, the `Final.lean` certificate will represent a valid, unconditional result.

**7. Remove the Proof Shortcut (Integration Plan: Final Cleanup)**
*   **File Path**: `SHORTCUT_PROOF.lean`
*   **Current State**: This file bypasses the entire proof structure by directly asserting the final answer using constants from the `reality` framework. Its central theorem, `mass_gap_is_golden_gap`, contains a `sorry`.
*   **Task**: Once all previous steps are complete and the mass gap has been formally derived through the YM framework, this file should be deleted or its main theorem should be proven, which would then be a simple corollary of the completed proof. The `sorry` within it represents the gap between the entire YM framework and the claims of the `reality` framework.
