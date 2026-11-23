# BranchingProcess

A Lean 4 / Mathlib library for branching processes, branching random walks,
selection, and random-walk small deviations. The tables below list principal
objects and results. Every theorem retains its hypotheses in its Lean signature;
proof-support declarations are documented in their owning modules.

## Trees and stopping lines

| Object | Main properties available | Lean entry |
| --- | --- | --- |
| Ulam–Harris trees and marked trees | Locally finite tree spaces, completeness and density, equivalent tree metrics and their Borel sigma algebras | [`Tree`](Combinatorics/UlamHarris/Tree/) |
| Lines in a forest | Ancestry antichains; meeting every infinite path is a separate property. Ancestral precedence orders lines, and distinct line members have disjoint descendant subtrees | [`Line/Basic`](Combinatorics/UlamHarris/Line/Basic.lean), [`Line/Order`](Combinatorics/UlamHarris/Line/Order.lean) |
| First-entrance and truncated lines | First entrance consists of ancestry-minimal target nodes. Generation truncations are increasing cuts of bounded depth and meet every infinite address path | [`FirstEntrance`](Combinatorics/UlamHarris/Line/FirstEntrance.lean), [`Truncation`](Combinatorics/UlamHarris/Line/Truncation.lean) |
| Optional random lines | Optionality tests `{L ≼ ℓ} ∈ F_ℓ`; countable ancestral suprema remain optional. Ancestrally observable first-entrance rules give optional lines; along a fixed path their entrance events equal Mathlib hitting-time events | [`Optional`](Probability/Process/Tree/Line/Optional.lean), [`Supremum`](Probability/Process/Tree/Line/Supremum.lean), [`FirstEntrance`](Probability/Process/Tree/Line/FirstEntrance.lean), [`PathHitting`](Probability/Process/Tree/Line/PathHitting.lean) |
| Information at an optional line | `L ≼ M` implies `F_L ⊆ F_M`; stopping at a deterministic line recovers its past. Ordered optional lines form a native filtration, admitting conditional-expectation martingales and Lévy upward convergence to the generated stopped information. Ordered pasting has an exact stopped-information decomposition on its decision cells | [`Stopped`](Probability/Process/Tree/Line/Information/Stopped.lean), [`Pasting`](Probability/Process/Tree/Line/Pasting.lean), [`Information/Pasting`](Probability/Process/Tree/Line/Information/Pasting.lean) |
| Strong branching at optional lines | Given `F_L`, observed distinct boundary vertices have complete descendant-tree law `⊗ᵢ P_(X_(Rᵢ))`. Localized identities cover empty lines and random cardinality; conditional integration allows nonnegative infinite payoffs depending on the stopped information, with arbitrary measurable states, state-dependent offspring kernels and jointly distributed initial roots | [`State/StrongBranching`](Probability/BranchingProcess/State/StrongBranching.lean) |
| Adapted node many-to-one | For any nonnegative payoff known at each node's generation, `E[∑_u W_u F_u] = E_spine[∑_(u∈spine) F_u]`; active nodes need not form a line | [`Density/AdaptedPayoff`](Probability/BranchingProcess/Spine/Tree/Density/AdaptedPayoff.lean) |
| Random-line mass | For measurable mean-harmonic ancestral weights, `E[W_L] = P_spine(spine hits L) ≤ 1`; equality to one is equivalent to almost-sure entrance. Membership may use the entire current generation; no separate optionality assumption is imposed | [`StoppingLine/ManyToOne`](Probability/BranchingProcess/Spine/StoppingLine/ManyToOne.lean) |
| Generation-truncated line mass | The frozen boundary mass `S_n = ∑_(k<n) A_k + U_n` is a native nonnegative martingale with `E[S_n]=1` and an almost-sure limit. The ordinary generation-density martingale is its empty-line special case | [`StoppingLine/Martingale`](Probability/BranchingProcess/Spine/StoppingLine/Martingale.lean), [`Density/Martingale`](Probability/BranchingProcess/Spine/Tree/Density/Martingale.lean) |
| First-entrance exponential mass | For an i.i.d. BRW with boundary-normalized tilt, `E[W_B] = P̂(∃ n, S_n ∈ B) ≤ 1`; expectation is one exactly when the tilted spine enters `B` almost surely | [`Spine/StoppingLine/FirstEntrance`](Probability/BranchingRandomWalk/Spine/StoppingLine/FirstEntrance.lean) |

Life records and child marks are ordinary measurable observations. States are
computed from marks and a measurable update; observing a state can discard
information. Reversible measurable coding preserves the line's information.
The library distinguishes birth-state information from the individual's own
reproduction information.

**Boundary:** strong branching is proved for the canonical discrete
offspring-kernel model. The full-family law requires each observed address to
have countable range; the optional line itself needs no countable-range,
bounded-depth or path-coverage assumption. Continuous-time life-history
models, many-to-one for line rules using information beyond the node's generation, line-indexed optional
sampling and identification of the truncated-mass limit with `W_L` remain
separate obligations. The latter identification needs expectation preservation. The
first-entrance mass identity above is the additive BRW specialization.
Optionality of generation
truncation is currently proved for ancestrally observable membership rules;
it is not asserted for arbitrary optional lines. Source results and remaining
obligations are recorded in the [formalization checklist](FORMALIZATION_CHECKLIST.md#stopping-and-optional-lines).

## Branching processes and selection

| Object | Main results available | Lean entry |
| --- | --- | --- |
| State-dependent branching process | A native offspring kernel `Q(s)` and measurable update `F(s,e)` induce the offspring-state kernel. The process admits arbitrary joint initial states; generation and stopping-generation conditional product laws follow from optional-line strong branching | [`Offspring/Kernel`](Probability/BranchingProcess/Offspring/Kernel.lean), [`State/StrongBranching`](Probability/BranchingProcess/State/StrongBranching.lean), [`State/Descendants/Observed`](Probability/BranchingProcess/State/Descendants/Observed.lean) |
| Harmonic spine bias | For a general mean-harmonic state kernel, the joint law is `Q(s,dξ) h(ξ_i)/h(s)`. Its family marginal has total-weight density; its selected-state marginal is the Doob transform. Conditional child weights are `h(ξ_i)/∑_j h(ξ_j)` | [`Family/Marginals`](Probability/BranchingProcess/Spine/Family/Marginals.lean), [`Family/Conditional`](Probability/BranchingProcess/Spine/Family/Conditional.lean) |
| Measurable state factors | If `K(s).map (Step.map f) = L(f(s))`, mapping every state by `f` preserves the complete path and tree laws, including arbitrary joint initial states; `f` may be noninjective | [`State/Map`](Probability/BranchingProcess/State/Map.lean) |
| Branching random walk and tilted path | Endpoint, ancestral-path and first-entry formulas derive from the general state-tree many-to-one theorem via complete pre-sampled-field law transport | [`EndpointManyToOne`](Probability/BranchingRandomWalk/Spine/ManyToOne/EndpointManyToOne.lean), [`Path/ManyToOne/Identity`](Probability/BranchingRandomWalk/Spine/Path/ManyToOne/Identity.lean) |
| Selection and capacity `N` | Threshold-count domination gives an injective order-preserving matching. Adapted selection and first-`N` populations admit pathwise and probabilistic coupling | [`ThresholdCount`](Combinatorics/Matching/ThresholdCount.lean), [`SelectedPopulation`](Combinatorics/Selection/NSelection/Matching/SelectedPopulation.lean), [`Causal/Restarted/Coupling`](Probability/BranchingRandomWalk/Selection/NSelection/Law/Causal/Restarted/Coupling.lean) |
| Selected-population endpoint | From `⌊Nᵃ⌋` initial particles, `a ∈ [0,1]`, at times `n_N/log³ N → t > 0`, the normalized minimum converges in `L²` to `−a + π²σ²t/2`, under the stated branching and moment conditions | [`L2Limit`](Probability/BranchingRandomWalk/Selection/NSelection/EndpointDeviation/Endpoint/Sequence/L2Limit.lean) |
| Asymptotic speed | For each positive capacity, every deterministic nonempty initial cloud of size at most `N` has the same almost-sure and `L¹` speed; `v_N log² N → π²σ²/2` under the theorem's first-moment assumptions | [`Limit/Speed`](Probability/BranchingRandomWalk/Selection/NSelection/Frontier/AsymptoticSpeed/Limit/Speed.lean) |

For a mean-harmonic state kernel, the canonical distinguished tree has one
measurably observed realized spine. Its complete untyped tree law is uniquely
identified by the finite-generation densities
`P_spine(Hₙ∈dx,wₙ=z) = W_z(x) P(Hₙ∈dx)`.
Given the whole untyped finite tree, the spine address has probabilities
`W_z/∑_u W_u`; its state path has the canonical Doob-chain law.
See [`Density/FiniteGeneration`](Probability/BranchingProcess/Spine/Tree/Density/FiniteGeneration.lean),
[`Density/Conditional`](Probability/BranchingProcess/Spine/Tree/Density/Conditional.lean),
[`Tree/Observation`](Probability/BranchingProcess/Spine/Tree/Observation.lean),
and [`Tree/PathLaw`](Probability/BranchingProcess/Spine/Tree/PathLaw.lean).
Ordinary descendant trees retain their original conditional product laws,
including zero-weight branches:
[`Tree/Normal`](Probability/BranchingProcess/Spine/Tree/Normal.lean).
These are finite-generation Radon–Nikodym identities; an infinite-horizon
density requires additional uniform integrability. The [checklist](FORMALIZATION_CHECKLIST.md#shis-general-spinal-decomposition)
records the remaining optional-line obligations.
The additive BRW specialization now transports the complete field and spine
path laws; its endpoint and first-entry formulas are corollaries of
[`Density/PathPayoff`](Probability/BranchingProcess/Spine/Tree/Density/PathPayoff.lean),
with no parallel branching-expectation induction.

The endpoint and speed results formalize Theorems 1.1 and 1.2 (including the
first-moment formulation) in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (Fudan University, 2026). The abstract
branching and selection interfaces do not require that reference's boundary
normalization or additive state space.

## Random walks and small deviations

| Object | Main results available | Lean entry |
| --- | --- | --- |
| Finite-variance random walks | Horizontal and inclined tube estimates, drawdown estimates, and the linear mean exit-time bound from the boundary, `E[τ_w] ≤ Cw` | [`SmallDeviation`](Probability/Process/RandomWalk/SmallDeviation/), [`ExitTime`](Probability/Process/RandomWalk/Path/Corridor/Horizontal/ExitTime.lean) |
| Mogul'skii small deviations | Discrete stable-domain, stable-process and finite-variance path-class rates, with explicit approximation and measurability hypotheses. In the finite-variance case the energy coefficient is `−π²σ²/2` | [`Mogulskii/Theorems`](Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Theorems.lean) |

The Mogul'skii entry identifies Theorems 1–3 of A. A. Mogul'skii, *Small
Deviations in a Space of Trajectories*, DOI
[10.1137/1119081](https://doi.org/10.1137/1119081). Theorem 4 for the full
source process remains open; a theorem for its discrete skeleton is not
counted as that result.

## Build and contribute

Lean and dependencies are pinned in [`lean-toolchain`](lean-toolchain),
[`lakefile.toml`](lakefile.toml) and [`lake-manifest.json`](lake-manifest.json).

```sh
git submodule update --init --recursive
lake exe cache get
lake build
python3 scripts/run-all-lean-tests.py --jobs 2
```

Keep `.lake/build` for incremental builds. A missing fork download cache
means uncached modules must be built locally; it does not invalidate existing
local build artifacts. Refresh dependency revisions only intentionally.

Import the narrow owning module. Reusable objects and theorems live in their
mathematical domain; `Lemmas/` contains only theorem-specific proof support.
See [architecture](ARCHITECTURE.md), [contributing](CONTRIBUTING.md), the
[proof checklist](FORMALIZATION_CHECKLIST.md), and [release checks](RELEASE.md).
Questions and contributions are welcome through GitHub issues and pull
requests, or **wang_yi_yang@foxmail.com**.

The Lean library uses [Apache 2.0](LICENSE). Dependencies retain their own
licenses; the surrounding LaTeX template is separately licensed.
