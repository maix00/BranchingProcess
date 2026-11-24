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

1. Concatenate the marked diffusion-block estimates, with the necessary
   uniform return and endpoint-window bounds, to prove the full marked
   affine-corridor small-deviation lower bound. A single unmarked
   small-deviation probability minus the full-horizon bad-mark probability
   is insufficient. The new maximal theorem applies at order `L²`, not `L³`.
2. Identify the concrete BRW ancestral-family observations under the general
   observed-generation many-to-one formula with the joint IID marked-increment
   law. The full observed-generation compensation is proved, but this
   BRW/IID law transport has not yet been assembled. The one-generation
   marked compensation alone is not claimed to establish that transport.
3. Apply MRCA decomposition to the *family-cutoff path count*, retaining the
   cutoff at every reproducing ancestor and the corridor restriction at
   child birth. The coefficient is then `C_K`. The new unmarked corridor
   theorem has coefficient `C`; substituting `C_K` into that theorem
   without changing its random count would be invalid.
4. Use the marked first and second moments and capacity comparison to replace
   the positive-initial-exponent upper-tail input. Only then transport the
   new assumption through ordering and assemble the existing endpoint-mean,
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
