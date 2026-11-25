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

1. The actual finite-root causal capacity bridge, independent-root amplification,
   and the original first-`N` endpoint bound with an explicit affine budget are
   proved. Choose the internal window, tail cutoff and rate gaps on the target
   `log N` scales and turn that budget into the polynomial upper tail for
   `mₙ=⌊Nₙ^A⌋`, `0<A<1`.
2. Replace the positive-initial-exponent upper-tail input with that weak-tail
   polynomial result. Transport the weak assumption through ordering and
   assemble the endpoint-mean, continuation-mean, restart-mean and speed
   comparisons. These final interfaces still retain finite cross weight.

The full continuous-moving-boundary statement of Mallein's Theorem 2.3 is
outside the present affine-corridor coverage; it is not assumed in these
completed count and success results.

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


## Internal starts and terminal windows (2026-11-25)

`Marked/FiniteVarianceLower.lean` now proves the endpoint version first. For
`a,b∈(-1/2,1/2)`, `ρ>0` and `d>π²σ²/2`, put

`Eₙ={-Lₙ/2≤aLₙ+S_k-ck/Lₙ²≤Lₙ/2 (1≤k≤Hₙ),`
`aLₙ+S_Hₙ-cHₙ/Lₙ²∈[(b-ρ)Lₙ,(b+ρ)Lₙ], Bⱼ≤αLₙ (j<Hₙ)}`.

Then `exp(-dHₙ/Lₙ²)≤P(Eₙ)` eventually under the same centered finite-variance
and weak quadratic mark-tail hypotheses. For every `θ≥0`, its direct corollary is

`exp(θ((b-ρ-a)Lₙ+cHₙ/Lₙ²)-dHₙ/Lₙ²)≤E[exp(θS_Hₙ); Eₙ]`.

The former centered survival theorem now follows by forgetting the endpoint;
its separate proof was removed. The unmarked estimates still call Wang
Yiyang's Lemma 3.1(ii) through the existing real-width endpoint-window API.
The added mark retention and concatenation follow B. Mallein, *Necessary and
sufficient conditions for the convergence of the consistent maximal
displacement of the branching random walk*, §2.2, proof of Lemma 2.5,
equations (2.5)–(2.7), arXiv:1510.00602v2. No new offspring-law normalization,
centering or untruncated cross-moment hypothesis is introduced.

The exact horizon is an entrance block, `q` return blocks, and a final block
of length between `bₙ` and `2bₙ`. The final block absorbs the remainder.
Fixed entrance and terminal probabilities disappear after multiplication of
the logarithm by `Lₙ²/Hₙ`; the middle blocks retain the sharp rate. The
fixed seven-band transition geometry remains internal in `Marked/Lemmas/`.

The generic finite-transition restriction theorem belongs in
`Kernel/Step/Noise/QuadraticTail.lean`: it is uniform over every transition
time below a diffusive maximum and all measurable targets. The existing
return-survival theorem derives its local estimate from this interface.
`Kernel/Survival/Return/Basic.lean` combines entrance, repeated returns and
terminal kernels using the native Chapman–Kolmogorov inequality and the
existing return-kernel domination. It assumes no random-walk structure.
Mathlib overlap was checked against revision
`26573066084e6e2aa8526ea358bc43b66d96f970`, including
`Kernel.pow_add_apply_eq_lintegral` and `setLIntegral_mono'`.
The latter directly proves the weighted-payoff corollary; no separate
integration-bound framework was added.


Endpoint-window validation (2026-11-25): full `LEAN_NUM_THREADS=2 lake build`
passed (12035 jobs); all 154 working-tree Lean test modules passed; the
marked-corridor regression passed all 37 configured axiom reports; Mathlib
style lint passed on 1827 production modules; import boundaries and all 32
Python unit tests passed. The regression includes prescribed terminal windows
and the exact horizon-zero endpoint semantics. LaTeX was unchanged.


## Actual selected-count first moments and success (2026-11-25)

`Spine/Path/ManyToOne/FamilySelection.lean` proves the exact identity

`E_(μ_A) Zₙ(F,x)=E_ν̂[exp(Sₙ) F(x+S₀,…,x+Sₙ); Bⱼ∈A, j<n]`,

where `μ_A=μ.map (Step.selectFamily (mark⁻¹A))` and `ν̂` is the original
joint displacement/family-mark law. Marks may take values in any measurable
space. The count is the existing `pathGeneration`, with selection at every
strict ancestor; the endpoint's own family is not inspected. No moment,
nonextinction or finite offspring assumption is used. The proof uses the
existing marked many-to-one identity and original-field pushforward, rather
than a second branching induction or normalized selected spine.

`Path/Decomposition/Generation.lean` owns the finite-address enumeration of
that same count, using Mathlib's `List.equivSigmaTuple.symm.tsum_eq` and
`tsum_sigma'`. The general list/tuple operations are reused directly;
no new generic list-summation module is introduced. Ordinary
`pathManyToOneCore` now follows by accepting every family and forgetting the
unit mark, using native coordinatewise IID pushforward. The weighted formula
then follows by terminal exponential cancellation. The old independent
scalar-record transport proof and private reindex/measurability helpers have
been removed. The existing general `Fin.measurable_partialSum` supplies finite
history measurability in the selected-count proof.

`Tube/Corridor/FirstMoment/FamilySelection.lean` connects the original weak
spinal tail to the joint `log₊W` mark and the marked affine estimate. With
`μₙ=μ.map(selectFamily {W≤exp(αLₙ)})`, it proves

`Mₙ=exp((b-ρ-a)Lₙ+(c-dLower)Hₙ/Lₙ²) ≤ E_(μₙ) Z_Hₙ`,

for the corridor with lower edge `-(a+1/2)Lₙ`, slope `c/Lₙ²`, width `Lₙ`
and terminal upper bound `Uₙ=(b+ρ-a)Lₙ+cHₙ/Lₙ²`. The original centered
spine has variance `σ²>0`, `dLower>π²σ²/2`, the start and target centers
are internal, and the original weak spinal weight-tail condition is the only
reproductive tail hypothesis. Finite spinal square integrability follows
from the positive second moment in the existing centered-moment predicate.
The raw boundary normalization implies `W<∞` almost surely. This handles
the totalized real logarithm at infinite weight without adding a finiteness
assumption; equivalence of the actual cutoff and log cutoff is only needed
almost surely. Its one-use map lemma remains private in the first-moment file.

`Tube/Corridor/FamilySelection.lean` combines this mean with the existing
actual family-cutoff MRCA bound and the existing Paley--Zygmund interface:

`Mₙ²/Sₙ ≤ P_(μₙ)(hasPathHistoryIn φ Hₙ 0 corridorₙ)`,

where `Sₙ` is the explicit second-moment bound with
`Kₙ=exp(αLₙ)` and any `0<dUpper<π²σ²/2`. Its width threshold is uniform
in `Kₙ`, so the cutoff can grow with `Lₙ`. Both moments and the success
event use the same actual process. No separate success event, counted
process or public budget definition is introduced.

The three new modules expose complete reusable count or probability results;
all single-use proof support is local/private. The touched directories have
6 direct public files in `Path/ManyToOne/`, 2 in `Path/Decomposition/`,
7 in `Tube/Corridor/`, and 1 in `Corridor/FirstMoment/`.

The reference is B. Mallein, *N-branching random walk with α-stable spine*,
proof of Lemma 3.4, arXiv:1503.03762v2, and *Necessary and sufficient
conditions for the convergence of the consistent maximal displacement of
the branching random walk*, §2.1, §2.2 and proof of Lemma 3.4,
arXiv:1510.00602v2. The affine second-moment input is the extension of Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 3, Lemma 3.6, equation (3.7).
Pinned Mathlib revision `26573066084e6e2aa8526ea358bc43b66d96f970` and the
[official list/finite-tuple documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/OfFn.html)
were checked; the implementation uses the native equivalence, product
pushforward, `Measure.map_congr`, and ENNReal finite-sum/quotient bounds.


Actual-count validation (2026-11-25): full `LEAN_NUM_THREADS=2 lake build`
passed (12041 jobs), including all existing endpoint and speed clients of the
refactored scalar many-to-one identities. All 155 working-tree Lean tests
passed. `FamilyCutoffMoments.lean` verifies the distinction between counting
a child and inspecting its own reproduction, and positivity of the actual
cutoff corridor mean under the weak tail alone. Its 8 new/affected named
axiom reports passed the reviewed allowlist. Mathlib style lint passed on
1830 production modules; import boundaries and all 32 Python tests passed.
LaTeX source, bibliographies and PDFs were unchanged.


## Cubic-scale success and cumulative population (2026-11-25)

The existing actual-count Paley–Zygmund ratio now has an exponential
consequence in `Tube/Corridor/FamilySelection.lean`. Write `κ=π²σ²/2`,
let `Lₙ→∞`, `Hₙ/Lₙ³→t>0`, and assume
`0<dUpper<κ<dLower`, `c≥dUpper`, `α,ρ>0`, and internal start and target
centers `a,b∈(-1/2,1/2)`. Under the original boundary normalization,
centered finite spinal variance and weak spinal weight tail, every

`β>Γ := α+4ρ+a+1/2+2(dLower-dUpper)t`

gives `exp(-βLₙ)≤P_(μₙ)(hasPathHistoryIn φ Hₙ 0 corridorₙ)` eventually.
Here `μₙ=μ.map(selectFamily {W≤exp(αLₙ)})` and the corridor is exactly the
one in the actual first/second moment statements above. No normalization
or centering of `μₙ` is assumed. The sum in the MRCA denominator is bounded
by `Hₙ exp(-lowerₙ)` since `c≥dUpper`; the diagonal term fits the same
exponential bound. Dividing the resulting exponent by `Lₙ` leaves `Γ`.
The `√Lₙ`, `Lₙ⁻²` and `log(Hₙ+1)` errors vanish after division by `Lₙ`.
The finite-horizon algebra and this particular exponent assembly are
non-reusable proof support under `Corridor/Lemmas/FamilySelection/`.
No separate public budget object is defined.

`FirstMoment/FamilySelection.lean` also gives, uniformly over measurable
family events `A`, horizons `H`, and `lower∈[-L,0]`, for sufficiently large
real `L`,

`E_(μ.map(selectFamily A)) ∑_(j≤H) Zⱼ(prefix)`
`≤ (H+1) exp(lower+L+√L+max(c-d,0)H/L²)`,

where `c≥0`, `0<d<κ`, and `prefix` has lower edge
`lower+cj/L²` and width `L`. This upper bound needs boundary normalization
and the original centered finite spinal variance, without a weak-tail or
finite-cross-weight assumption. It follows by actual selected-count
domination, the existing many-to-one upper bound, the uniform drifted-tube
estimate, and finite summation. It is a reusable cumulative-count theorem,
so it remains outside `Lemmas/`.

The deterministic inclusion from affine finite histories to positive-time
drifted-tube events now belongs to `DriftedTube/Event.lean`. It holds for
arbitrary initial position and real parameters, with no sign or moment
hypotheses. First and second moments use that same inclusion; the previous
private measure-level copy in the second-moment module was removed.

Abstraction review: the pinned Mathlib revision listed above and the
[official power-asymptotics documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.html)
provide `tendsto_rpow_neg_atTop`, real-power subtraction and quotient
limits. They do not state the combined normalized-power implication
`L→∞`, `H/L^q→t≠0`, `p<q` ⇒ `L^p/H→0`. Its reusable version allows
any filter, real exponents and signed `H`, and belongs in
`Analysis/Asymptotics/Scale/Power/Basic.lean`. The existing intermediate-block
power-ratio helper now derives from it instead of maintaining another
negative-power proof. Cubic-scale integer-horizon facts remain private to
the corridor proof chain. Existing logarithmic power-bound limits are used
directly.

The proof follows the cutoff moment and population-budget steps in
B. Mallein, *N-branching random walk with α-stable spine*, proof of Lemma 3.4,
[arXiv:1503.03762v2](https://arxiv.org/html/1503.03762v2), with the repository's
reflected spatial convention. These results supply the numerical success
estimate and a capacity input; the actual finite-root causal capacity bridge,
positive-initial-exponent replacement and final weak-tail endpoint/speed
assembly remain open. No LaTeX changes are part of this step.


Cubic-scale/cumulative validation (2026-11-25): full
`LEAN_NUM_THREADS=2 lake build` passed (12045 jobs), including all existing
endpoint and speed clients. All 155 working-tree Lean tests compiled, with
the configured axiom allowlist checks passing. `FamilyCutoffMoments.lean`
now checks actual cutoff success positivity from the weak tail and cubic
scale alone, and audits 12 named declarations. Mathlib style lint passed on
1832 production modules. Import boundaries, all 32 Python unit tests, and
`git diff --check` passed. No proof placeholder, new axiom, dependency-version
change or LaTeX edit was introduced.

The final visibility review made the finite-horizon exponent comparison
private: it is used only inside its own proof-support module and appears
only in proof terms. Cross-file helpers retain ordinary lemma visibility.
The principal success entry and its regression were rebuilt after this
change; all 12 configured axiom reports passed again.


## Actual finite-root capacity and endpoint transfer (2026-11-25)

`Population/Processes/Causal/Capacity/FirstMoment.lean` now separates the
finite-root actual-count inequality

`E size(P_R,j) ≤ ∑_(r∈R) E pathGeneration(φ,j,Ψ,xᵣ)`

from its spinal specialization. The count bridge uses no boundary or moment
condition. Both previous one-root and finite-root spinal estimates derive
from this common bridge, using existing root-marginal integration and
many-to-one; their previous independent integration proofs were removed.

`Capacity/FamilySelection.lean` applies it under
`μA=μ.map(selectFamily A)` and the existing cumulative selected-count bound.
For the existing relative affine-corridor population, with original centered
spinal variance `σ²>0`, `c≥0`, `0<d<κ=π²σ²/2`, large `L`, and
`lower∈[-L,0]`,

`P_μA(Cap(N,H)ᶜ)`
`≤ |R|(H+1)exp(lower+L+√L+max(c-d,0)H/L²)/(N+1)`.

The same width threshold works for all measurable family events, root-label
types with the stated countability/measurability, root sets, initial positions,
horizons and capacities. In particular it supports varying root counts.
This estimate uses neither the reproductive weak tail nor finite cross weight.
Its original-law case is obtained by accepting every family.

`Path/Survival.lean` transfers a measurable single-root history success event
to the actual finite-root causal population. For a compatible history set
whose endpoints are in `B`, and `q≤P_μ(hasPathHistoryIn φ H 0 C)`,

`P_μ(∀p∈P_H, position(p)∉B)≤exp(-m q)`.

Only almost-sure finite negative-exponential family weight is needed to
activate the totalized population's guard. Boundary normalization, variance,
nonempty offspring, and time positivity are absent from this generic theorem.
The independent-root avoidance theorem and existing path-to-population
inclusion supply the argument, without another branching law or population.

`Spine/Path/ManyToOne/Event.lean` now proves that whole-family selection only
decreases arbitrary measurable history-success probabilities. The cubic-scale
success entry in `Spine/Tube/Corridor/FamilySelection.lean` consequently
supplies the original BRW's `exp(-βLₙ)` bound from the cutoff bound. All
retained positions agree pathwise. Thus the original comparison population
and the original first-`N` field law can be used throughout the capacity and
endpoint comparison; no filtered-field coupling is needed.

`Selection/NSelection/Law/Causal/Restarted/Overflow.lean` derives

`P(min NSelected_H>x)`
`≤ P(∀p∈P_H, position(p)>x)+P(Cap(N,H)ᶜ)`

from its existing stopped-minimum lower-tail domination. It reuses the
same private finite-minimum measurability calculation and constructs no new
coupling. The generic transfer assumes left local finiteness, positive
capacity and an initial dominating injection, without boundary or moment
conditions. Empty minima are `+∞`. The real totalized endpoint minimum is
bounded by this extended minimum, including the empty case.

The complete application is
`EndpointDeviation/Endpoint/Sequence/UpperTail/SpinalWeight.lean`, theorem
`eventually_measure_endpointMinimum_gt_le_affineBudget_of_spinalWeightTail`.
Under the original boundary normalization, centered finite spinal variance,
and `HasSpinalWeightTail`, let `Lₙ→∞`, `Hₙ/Lₙ³→t>0`,
`0<dUpper<κ<dLower`, `c≥dUpper`, `α,ρ>0`, and internal centers `a,b`.
For `β>α+4ρ+a+1/2+2(dLower-dUpper)t`, write
`lowerₙ=-(a+1/2)Lₙ`, `Uₙ=(b+ρ-a)Lₙ+cHₙ/Lₙ²` and
`Bₙ=lowerₙ+Lₙ+√Lₙ+max(c-dUpper,0)Hₙ/Lₙ²`. Then the original
first-`Nₙ` real endpoint minimum from arbitrary `mₙ` zero-position roots obeys

`P(Mₙ>Uₙ) ≤ exp(-mₙ exp(-βLₙ)) + mₙ(Hₙ+1)exp(Bₙ)/(Nₙ+1)`

eventually, assuming only eventual positivity of `Nₙ`. The actual finite-root
law is used on both sides. Finite cross weight, a logarithmic square moment,
and nonempty offspring are not extra assumptions. This is a proved explicit
endpoint bound; optimization of its logarithmic parameters and final weak-tail
speed assembly are still open.

Abstraction/native review: pinned Mathlib
`26573066084e6e2aa8526ea358bc43b66d96f970` and its
[Markov documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.html)
were checked. The existing capacity theorem already calls
`meas_ge_le_lintegral_div`; existing finite-root expectations and independent
root avoidance supply the root operations. Native `Measure.map_apply`,
`prob_compl_eq_one_sub`, `tsub_le_tsub_left`, and finite-infimum inequalities
are used directly for the endpoint transfer. None of these native results is
reimplemented. The finite-root count, capacity, avoidance and endpoint-law
bridges are complete reusable mathematical statements outside `Lemmas/`.
Single-file affine-history algebra remains private.

Reference alignment: the cutoff moments follow B. Mallein, *N-branching
random walk with α-stable spine*, Lemma 3.4; independent-root amplification
appears in §4.4, proof of Lemma 4.8, arXiv:1503.03762v2. The original spatial
convention is reflected. The capacity budget extends Wang Yiyang, *Asymptotic
Speed of the N-Branching Random Walk with Infinite Offspring* (Fudan University,
2026), Chapter 4, proof of Theorem 1.1, using Chapter 3, Lemma 3.4. The coupling
is the existing implementation of Chapter 3, Lemma 3.15. The explicit fixed-
horizon endpoint bound combines these ingredients; it is not claimed to be
Mallein's interval-in-time statement of Lemma 4.8. No LaTeX changes are included.

Directory review: the former nine direct sequence files would become ten.
The two existing complete upper-tail entries `PositiveInitialExponent` and
`SingleRoot`, together with the new weak-tail entry `SpinalWeight`, are grouped
in `Sequence/UpperTail/`. Seven direct sequence files remain. Imports and
recorded paths are migrated directly; old paths and compatibility aliases are
absent. These are public results, so they are outside `Lemmas/`.


The remaining logarithmic choice can be stated precisely. For
`mₙ=⌊Nₙ^A⌋`, `Lₙ=w log Nₙ`, `Hₙ/(log Nₙ)³→T>0` and
`lowerₙ=-b₀ log Nₙ`, the displayed bound is polynomially small once

`βw<A`,
`A+w-b₀+(c-dUpper)T/w²<1`,

and the terminal coefficient
`-b₀+(b+1/2+ρ)w+cT/w²` is below the desired endpoint coefficient.
The success theorem additionally requires
`αw+4ρw+b₀+2(dLower-dUpper)T/w²<βw`.
Formalizing this joint parameter choice, its floor-root asymptotics, and
transport to the final endpoint/speed interfaces remains the next obligation;
these inequalities are explanatory parameter targets, not additional proved
asymptotic theorems in this entry.


Finite-root/endpoint validation (2026-11-25): `LEAN_NUM_THREADS=2 lake build`
passed (12051 jobs), including the renamed upper-tail entries and all existing
endpoint and speed clients. All 156 working-tree Lean tests passed with the
configured axiom allowlists. The new `EndpointDeviation/SpinalWeight.lean`
regression tests zero-horizon terminal success under finite family weight,
without boundary normalization, positive variance or nonextinction; its 7
named bridge/application axiom reports passed. Mathlib style lint passed on
1835 production modules, import-boundary checks passed including the new
weak-entry/strong-route separation guards, and all 32 Python tests passed.
`git diff --check` passed. No axiom, placeholder, dependency change or LaTeX
edit is introduced.
