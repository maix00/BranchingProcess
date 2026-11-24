# Weak spinal reproductive tails: implementation and proof boundary

Audit date: 2026-11-25. The task follows `audit-20261124.txt`.
Pinned Mathlib: `26573066084e6e2aa8526ea358bc43b66d96f970`.

## Mathematical target and sources checked

B. Mallein, *N-branching random walk with α-stable spine* (2015),
Theorem 1.1, conditions (1.9)–(1.10), and §2.1:
<https://arxiv.org/abs/1503.03762>;
<https://www.math.univ-toulouse.fr/~bmallein/publications/brwalphaspine.pdf>.

B. Mallein, *Necessary and sufficient conditions for the convergence of the
consistent maximal displacement of the branching random walk*,
arXiv:1510.00602v2, condition (1.4), Theorem 2.3 and proof of Lemma 2.4:
<https://arxiv.org/pdf/1510.00602>.

Both primary texts were checked. In the repository's leftmost-selection
convention, put `W = ∑ᵢ exp(-Ξᵢ)`, let `μ̂(dξ,i) = exp(-Ξᵢ) μ(dξ)`
on present slots, and write `X = Ξᵢ`. The requested reproductive assumption is

`x² μ̂{log W + X > x} → 0`.

It is a weak tail condition, not integrability of `(log₊ W)²` under the
biased law. Under `E W = 1` and finite spinal second moment, it is equivalent
to `x² (μ.withDensity W){log W > x} → 0`. For endpoint means and speed the
target retains a first moment of the positive part of the leftmost child;
it retains the spinal second moment which determines the small-deviation rate.

## Native and existing interfaces reused

The pinned Mathlib tree has no weak-L²-vanishing-tail or enriched-Mogulskii
interface. Its dominated convergence, `setIntegral_ge_of_const_le_real`,
`measureReal_biUnion_finset_le`, `HasLaw.measureReal_eq`, density measures,
measure pushforwards, product measures, and measurable maps provide the
measure-level operations used here. The official module documentation and
the pinned source were compared; no conditional-probability or independent
mark construction is added.

Existing `Probability/Sequence/IID/Basic.lean` owns the IID law, coordinate
laws and finite union bound. Tests use that law on a *joint* displacement/mark
space. Dependence within one increment is preserved.

The state-tree `Spine.LocalBias.familyChildKernel` is a state-dependent
offspring-state kernel. The scalar BRW increment law alone loses the raw
offspring family. The new BRW joint family/child measure has the same raw
step and potential semantics as the existing scalar increment law.
`Tilted/Law.lean` now defines the scalar law as its displacement pushforward
and derives its cancellation formula from the joint formula. It does not
maintain an independent second scalar tilt or a second branching-tree law.

## Completed results and owners

* `MeasureTheory/Measure/Tails/Quadratic.lean` owns the condition
  `Tail₂(f): x² μ{f > x} → 0`, pushforward invariance, positive rescaling of
  thresholds, clipping below a constant, addition, finite-second-moment
  sufficiency, and `Tail₂(f+g) ↔ Tail₂(f)` if `g²` is integrable.
  The two observations can be dependent and the measure is finite.
* `Probability/Sequence/Maximal/QuadraticTail.lean` proves a maximal-mark
  bound using only common marginal laws, with no independence. If
  `Lₙ → ∞`, `mₙ ≤ C Lₙ²` eventually and `α > 0`, then
  `P(∃j<mₙ, Bⱼ>αLₙ) → 0`. For every `p>0`, eventually and uniformly over
  *all* events `A` with `P(A)≥p`, the probability of `A` with all marks
  accepted is at least `p/2`. This is the local diffusion-block step.
* `Combinatorics/BranchingWalk/Step/Measure/ExponentialWeight.lean` owns the
  deterministic log-total-weight observable and `crossPotentialWeight ≤ W²`.
* `Probability/BranchingRandomWalk/Spine/Tilted/FamilyChild.lean` owns
  the joint bias, exact weighted and compensated integrals, present-child
  support, the family marginal `μ.withDensity W`, and normalization.
* `BranchingProcess/Spine/LocalBias/ManyToOne.lean` proves
  `lintegral_generationPayoff_eq` for arbitrary observed-tree payoffs at the
  selected generation, retaining entire ancestral reproduction families.
  The previous ancestral-state-path formula in `LocalBias/Path.lean` now
  derives from it and the realized spine. No extra admissibility or moment
  assumption is introduced.
* `Tilted/Marked.lean` reads `(X, mark(ξ,i))` from that same joint bias.
  Marks can take values in any measurable space. The displacement marginal
  is exactly the original scalar law. Marked one-generation many-to-one
  is derived from the joint compensation theorem.
* `Spine/Path/ManyToOne/Marked.lean` now identifies the original BRW
  generation sum with finite products of the existing joint family/child law
  (`familyPathManyToOne`), and with the existing IID sequence law of correlated
  displacement/marks (`markedPathManyToOne`). Every strict ancestor's complete
  family and selected slot are retained. No moment, finite-offspring-count or
  within-step independence hypothesis is added. The original scalar
  `weightedPathManyToOneCore` is derived by forgetting these records and
  cancelling the exponential factors; its dedicated state-tree representation
  proof has been removed. General state-tree spine results remain available
  for state-dependent branching kernels.
* `Combinatorics/UlamHarris/Mark/Path.lean` defines only the deterministic
  record `(field(z|j),zⱼ)`. `Probability/Process/Tree/Path/WeightedRecords.lean`
  integrates these records in an independent address field using injective
  ancestral-coordinate reindexing. These owners carry no BRW survival model.
* `MeasureTheory/Measure/Pi/WeightedPairs.lean` expands a finite product of
  countably weighted marked measures. It uses native product-measure
  uniqueness, integration and pushforward APIs rather than adding a new
  product measure or recursive branching-law construction.
* `Assumptions/SpinalWeightTail.lean` defines the actual Mallein condition,
  proves that its relative mark is nonnegative almost surely, and proves the
  equivalence with the total-weight tail condition using finite spinal
  second moment. No log-square moment or independent mark is assumed.
* `Tilted/FamilyCutoff.lean` proves `C_K = ∫_(W≤K) C dμ ≤ K E W`,
  hence `C_K ≤ K` under boundary normalization, for arbitrary countable
  offspring slots. It also identifies restriction of the original joint
  bias to a family event with the bias of the restricted raw law.
  This is distinct from `Tilted/Truncation.lean`, which continues to own
  truncation to the first finitely many ordered child slots.
* `Tube/Corridor/SecondMoment/FiniteVariance.lean` now retains the
  untruncated cross coefficient explicitly. Its threshold depends on the
  original scalar tube estimate, not on the cross coefficient:
  `E Z² ≤ C exp(3Δᵛ+2U-2d(H−1)/Δ²) ∑_(s<H) exp(ds/Δ²-r_s)`
  `+ exp(U+Δᵛ-dH/Δ²)`.
  No finite-cross-moment hypothesis is needed for this extended-real bound.
  The previous finite-cross version is derived by absorbing `C` into one
  extra exponential error. Its proof is not maintained in parallel.

Each public result is a complete reusable measure, tail, bias or corridor
statement. Single-module tactical helpers are private. No model-specific
unfinished theorem is promoted by placing its conclusion in an assumption.

## Remaining proof obligations

These are still open, not consequences already supplied by a new hypothesis:

1. The centered affine-corridor survival lower bound is now proved for
   arbitrary positive horizon sequences `Hₙ`, real widths `Lₙ→∞` and
   `Lₙ²/Hₙ→0`, with correlated marks accepted on *every* step. The native
   first-moment chain still needs the prescribed endpoint-window and general
   initial-fraction adapters before it can replace all current endpoint
   inputs. The full continuous-moving-boundary statement of Mallein's
   Theorem 2.3 is not asserted by this affine-corridor theorem.
2. Combine those marked first-moment inputs with the now proved actual
   family-cutoff MRCA second moment and capacity comparison to replace the
   positive-initial-exponent upper-tail input. Then transport the weak
   assumption through ordering and assemble the existing endpoint-mean,
   continuation-mean, restart-mean and speed comparisons.

The existing final endpoint and speed theorems therefore still take
`HasFiniteCrossWeight`. They have not been relabeled as weak-tail results.
A family cutoff generally changes both boundary normalization and centering;
the cutoff law cannot be inserted into those final theorems as though its
spine were the original centered law.

## Regression and axiom review

`BranchingProcessTest/Branching/SpinalWeightTail.lean` checks the exact weak
assumption, a perfectly correlated displacement/mark law, the exponential
cutoff bound with no untruncated cross assumption, and uniform mark retention
for arbitrary events of a joint IID sequence. Its explicit axiom inventory
covers all new theorem chains and both corridor second-moment statements.

Validated on 2026-11-25:

* `LEAN_NUM_THREADS=2 lake build`: successful (12001 jobs).
* New weak-tail regression: compiled; all 34 configured axiom reports passed.
* `ManyToOneLawTransport`, `SpinalBias`, `SpineDisintegration`: compiled;
  all 57 configured downstream axiom reports passed.
* Mathlib style lint, the import-boundary audit and all 32 Python unit tests
  passed. No new axiom or proof placeholder is introduced.

## Complete-record law transport review (2026-11-25)

The independent-field calculation reads distinct strict-ancestor coordinates
for each fixed finite address, then sums over addresses. Finite time is
arbitrary, including zero; countably many child labels and possibly infinitely
many offspring are allowed. It does not replace the original offspring law
by a normalized cutoff law. Family cutoffs are tests of the recorded marks.
The scalar and marked statements share this calculation, with no compatibility
aliases or independently maintained scalar branching expectation proof.

Mathlib revision `26573066084e6e2aa8526ea358bc43b66d96f970` and the current
official documentation were checked:

* [finite products](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Pi.html):
  `Measure.pi_eq`, `Measure.pi_pi` and `Measure.pi_map_pi` provide the
  rectangle uniqueness and coordinatewise pushforwards used directly;
* [independent integration](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Integration.html):
  `lintegral_prod_eq_prod_lintegral_of_indepFun` integrates the product of
  independent coordinate functions;
* pinned `Mathlib/Probability/Independence/InfinitePi.lean`:
  `Measure.map_infinitePi_infinitePi_of_inj` identifies any fixed address's
  distinct ancestral field coordinates with the finite IID product.

These APIs do not already state the countable weighted-pair expansion or the
address-sum identity. The new finite-measure identity is measure-level; its
base coordinates have probability laws and its weighted joint measures are
finite, without requiring their normalization or independence within a pair.
Single-file sum rearrangement, coordinate integration and exponential
cancellation helpers remain private. The record and law identities are
complete reusable results outside `Lemmas/`.

Reference alignment: B. Mallein, *N-branching random walk with α-stable spine*,
§2.1, Proposition 2.1, Lemma 2.2 and proof of Lemma 3.4,
[arXiv:1503.03762v2](https://arxiv.org/html/1503.03762v2), uses the reflected
spatial convention. The repository keeps its existing bias `exp(-X)`.
The family-mark use also follows the proof of Lemma 3.4 in B. Mallein,
*Necessary and sufficient conditions for the convergence of the consistent
maximal displacement of the branching random walk*,
[arXiv:1510.00602v2](https://arxiv.org/pdf/1510.00602).

Complete-record validation on 2026-11-25:

* Full `LEAN_NUM_THREADS=2 lake build` passed (12009 jobs), including the
  downstream corridor, endpoint and asymptotic-speed modules.
* `SpinalWeightTail.lean` additionally checks the actual all-ancestor
  family-cutoff count on the original raw field and the empty-address count
  without a nonempty child-label type. All 41 registered axiom reports use
  only `propext`, `Classical.choice` and `Quot.sound`.
* Mathlib style lint, the import-boundary audit (including the three new
  non-BRW owners) and all 32 Python tests passed.

## Long-horizon marks and actual cutoff MRCA (2026-11-25)

`Probability/Process/RandomWalk/SmallDeviation/Marked/FiniteVarianceLower.lean`
proves, for the original IID **joint** law of `(X,B)`,

`exp(-d Hₙ/Lₙ²) ≤ P(-Lₙ/2 ≤ S_k-ck/Lₙ² ≤ Lₙ/2 (1≤k≤Hₙ), Bⱼ≤αLₙ (j<Hₙ))`

eventually, when `EX=0`, `EX²=σ²>0`, `t²P(B>t)→0`, `c≥0`, `α>0`,
`d>π²σ²/2`, `Lₙ→∞`, `Hₙ>0` eventually and `Lₙ²/Hₙ→0`. The horizon
sequence is arbitrary and need not be strictly monotone. In particular real
widths and the time scales used by the BRW are allowed. There is no moment
assumption on `B` and no independence assumption within `(X,B)`.

`Kernel/Step/Noise/Map.lean` transports the existing partial-step execution
and kernel through a measurable noise map. `Noise/Restriction.lean` identifies
rejection exactly with killing at the first unaccepted noise value.
`Kernel/Survival/Return/NoiseRestriction.lean` applies the previously proved
weak-tail union bound only to blocks of order `L²` and then uses the existing
return-kernel iteration for **arbitrary total horizons**. At the random-walk
layer, the seven unmarked window estimates are derived from the existing
finite-variance endpoint-window theorem, including the `c/L²` drift; no local
return estimate is assumed in the final finite-variance theorem. Increasing
the fixed diffusion-block constant absorbs the blockwise factor `1/2`.
The general rounded block-count limit belongs in
`Analysis/Asymptotics/Scale/Block/Count.lean` and has no probability dependency.
The fixed seven-band geometry and parameter assembly are under
`Marked/Lemmas/`; each is specific proof support, not a reusable public API.

Whole-family selection uses the existing optional Step representation:
`Step.selectFamily A ξ = ξ` on `A` and is the all-absent family otherwise.
`Combinatorics/BranchingWalk/Selection/Family/Path.lean` proves that surviving
paths are precisely original surviving paths with `field(u|j)∈A` at every
**strict** ancestor. All retained displacements are identical, for arbitrary
mark maps into an additive monoid. `Spine/Path/FamilySelection.lean` transports
the independent-field law and proves path-count domination for arbitrary
nonnegative measurable history tests. The actual count keeps the acceptance
condition on every ancestor; acceptance of the generation-`N` endpoint's own
family is not imposed.

`Spine/Tube/MRCA/FamilySelection.lean` now bounds the actual selected-process
MRCA term by the original spine's continuation and prefix bounds, retaining
`C_A=∫_A crossWeight dμ`. The selected offspring law is a probability, but no
boundary normalization or centering is asserted for it. The exact corridor
square decomposition was weakened to arbitrary probability offspring laws,
deriving directly from the existing pathwise MRCA identity; the unnecessary
finite-first-moment cancellation route is avoided for this square identity.
The separate existing distinct-pair comparison retains its own assumptions.

`Tube/Corridor/SecondMoment/FamilySelection.lean` gives the actual count bound

`E_(μ_A) Z_N² ≤ C_A exp(3Δᵛ+2U-2d(N-1)/Δ²) ∑_(m<N) exp(dm/Δ²-r_m)`
`+ exp(U+Δᵛ-dN/Δ²)`,

where `μ_A=μ.map (Step.selectFamily A)` and `r_m=l+cm/Δ²`. Its width threshold
is uniform over all measurable `A`. For `A={W≤K}`, the **actual selected-law**
cross coefficient equals the restricted original integral and is at most `K`.
The corollary is uniform in `K`, in particular `K=exp(αΔ)`, without a finite
untruncated cross moment. The previous unselected finite-variance second
moment now derives from `A=univ`; its dedicated proof was removed. The old
finite-cross-moment absorption is still a corollary of that unselected result.

Mathlib overlap review used revision
`26573066084e6e2aa8526ea358bc43b66d96f970`, in particular native
`Measure.infinitePi_map_pi`, `Measure.map_apply`, `Kernel.comp_apply'`,
`Kernel.pow_add_apply_eq_lintegral` and their
[official composition documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html).
The existing local `ofPartialStep`, endpoint-law, return-kernel, prefix-factor
and normalized child-pair APIs are reused. No second Markov-chain definition,
branching recursion, normalized cutoff-spine law or compatibility alias is
introduced. The literature comparison is Mallein, arXiv:1510.00602v2,
§2.2, Theorem 2.3 and proof of Lemma 2.5, and the family-cutoff second moment
in the proof of Lemma 3.4 of arXiv:1503.03762v2 and arXiv:1510.00602v2.


Validation of the long-horizon and actual-cutoff additions (2026-11-25):

* Full `lake build`: successful (12033 jobs).
* All 154 working-tree Lean regression modules compiled successfully.
* `MarkedCorridorCutoff.lean` checks arbitrary horizon sequences, correlated
  increment/mark assumptions, actual strict-ancestor family selection,
  generation zero, and the second-moment signature without a finite original
  cross moment. All 31 configured new or affected axiom reports passed the
  reviewed allowlist.
* Mathlib style lint passed on 1826 production modules; the import-boundary
  audit and all 32 Python unit tests passed.
* No LaTeX source, bibliography or PDF was changed.
