# Proof review and formalization status

## Theorems 1.1 and 1.2

The two statements have been checked against the arguments in Chapters 3–4, but
this is **not** a complete independent verification of every probabilistic
lemma. Three concrete errors in the written deductions were repaired:

1. In the proof of Theorem 1.1, squaring the endpoints of
   `[ζ, ζ′]` did not preserve their order when the limiting trajectory was
   negative. The second-moment sandwich now uses the infimum of `x²` on the
   interval and the maximum of the squared endpoints.
2. The appendix had `E[(V¹_n)₊] ≤ E[V¹_n]`, which is false for a signed
   position. It now uses `E[|V¹_n|] ≤ n E[|Ξ₁|]`.
3. The `a = 1` right-tail proof compared against `a = 1/2`, which does not
   work for every threshold just above the `a = 1` limit. It now chooses
   `b < 1` close enough to `1` for the given threshold.

The negative exponential moment bound `E[exp(-M_n)] ≤ 1` applies to a
single initial particle. For `m` initial particles it is `≤ m`. Theorem
1.1's fourth-moment step now shifts by `log N` and yields the uniform bound
`E[(M_n)₋⁴] = O(1 + (log N)⁴)` for `m ≤ N`.

**The `E₀` entrance estimate now has a finite-variance Lean proof.** The
all-offset cyclic-rotation transfer, including the moving-boundary drift
identity, is compiled and included in the 24-declaration axiom audit in
`BranchingProcessTest/Mogulskii/LinearTubeAxioms.lean`. `NormalDomain.lean`
constructs the Gaussian clock-process law internally from the raw centered
second-moment assumption and proves the uniform entrance lower bound
`q / floor(Delta^2)` for every initial point in the corridor. The new
`ExponentialLoss.lean` proves that this polynomial loss is at least
`exp(-δ L / Delta^2)` once `L ≥ floor(Delta^(2+ε))`; its focused test and
axiom check pass. The event is the normalized finite-prefix form of the
paper's `E₀`, including the central endpoint window and moving boundary.
This closes that entrance estimate under the paper's finite-variance spine
assumption. It does not assert the analogous raw-source estimate under
infinite-variance normal attraction or close the separate branching-walk
restart and Theorem 1.3 gaps below.

The proof of Theorem 1.2 originally applied the appendix's moment bound for
an ordinary selected walk directly to the **restarted** process `Vᵇ`. The
revised text gives a separate bound: the coupling handles the negative part,
while a designated lineage bounds the positive part by `Mn + Σ(R_j)₊`, with
fresh copies `R_j` of `Ξ₁`. This repairs the stated inference, but the
designated-lineage coupling has not been machine-checked. Theorem 1.2 is
therefore not fully certified by this review.

The restart section also asserted that $\tau=\tau_\kappa+\ell$ is a stopping
time solely because the trial times increase. That implication is invalid.
The revised bilingual text states the needed generationwise measurability of
success declarations. A generic first-success theorem has been checked in
Lean. The new measurable-candidate and causal-recursion interfaces are also
kernel-checked. `Restart/Trial.lean` now instantiates the first growth
candidate along a supplied pre-sampled lineage: it proves the selected-child
relation, the endpoint-band and earlier nonempty/cap event, measurability in
the generation filtration, and the exact clock identity `σ + ℓ - 1 = τ + ℓ`.
The recursive pre-sampled first/second-sibling construction and its finite
all-failure product law are formalized in
`Restart/RootedTrial/RecursiveReserve.lean`. The finite-completion premise is
proved generically in `Restart/RootedTrial/FiniteSplitCompletion.lean` from
nonempty selected offspring a.s. and positive split probability;
`RestartSiblingTrial.lean` contains its concrete
`BasicBranchingAssumptions`/`GoodSplit` instantiation. `Restart/RootedTrial/CausalReserve.lean`
defines generation-enabled, fixed-start cap-stopped first-child candidates on
one pre-sampled reserve spine and packages their union with the reserve
singleton as an adapted, parent-closed causal source process.

The target-side endpoint bridge has since been verified. In
`Restart/RootedTrial/Coupling.lean`, the endpoint time is a stopping time, the
actual rank-installed endpoint vector is measurable in its stopped domain
filtration, and its descendant field has the independent product law on the
finite-endpoint event. The joint law with any stopped-measurable endpoint
position vector then transfers to the first-`N` target population at every
fixed finite horizon. The endpoint-specialized theorem
`selectedReserveSpineRestartEndpointPopulation_law_on_finite` now composes
the stopping-time rank vector, fresh-field law, and fixed-horizon population
law for the thesis reserve endpoint. `RestartCausalReserveCoupling.lean`
compiles and audits 24 declarations; each has only
`[propext, Classical.choice, Quot.sound]`.
This is not a random remaining-horizon theorem. The C0 gap remains the
source-side identification: the causal candidate source is not yet identified
with the thesis's actual restarted population/frontier, and later reserve
candidate freshness has not been proved relative to the actual explored
domain. The quantitative finite-time candidate-success and spatial estimates
needed by the right-tail bound also remain open.

An audit of the source definitions rules out one proposed identification:
the generation-enabled causal source is generally larger than the
retrospectively restarted frontier before the first successful candidate.
For example, a later reserve sibling may split while an earlier candidate
window is still running, so its root and partial descendant segment already
belong to the pre-sampled causal source while the retrospective rule has not
yet enabled that trial. The source and retrospective frontier therefore
should not be required to agree pathwise. The next formal bridge must prove a
one-sided inclusion sufficient for the population comparison, or use the
adapted causal source directly as the killed population. A split completion
`σᵢ` is the correct stopping time for the full fresh sibling fields; at an
earlier overlapping candidate completion the later reserve subtree has
already been partly exposed, so it cannot be treated as an independent fresh
field there. These are proof obligations, not established Lean results yet.

The source [Aïdékon--Hu, arXiv:2512.23266, p. 19, Lemma 4.8](https://arxiv.org/pdf/2512.23266)
defines a killed walk immediately before the lemma through a selection rule
adapted to the natural filtration. The lemma itself then states a minimum
comparison through the first population-size excess time. The earlier
thesis wording required only the *population size* to be adapted, which is
weaker than an adapted rule identifying retained parents. The revised
bilingual lemma makes the latter explicit. Lean now verifies a finite
counterexample: adapted count does not imply adapted identity.

The source's $a=0$ argument on p. 21 grows an always-binary process whose
offspring law consists of its two leftmost children. It does **not** use the
retrospective reserve-branch restart written in this thesis. The source
proposition as restated here explicitly includes
`assumption:at-least-one-child`; the $a=0$ clause adds an exponential moment
but inherits this nonempty-a.s. hypothesis. The general point-process and
selected-step APIs must still allow empty offspring, and a candidate growth
trial may have zero, one, or two children after truncation. The reserve
selector retains the first selected child without a cutoff and retains
additional selected children only when their potential is at most $M$. Thus a
single-child continuation may have an unbounded first-child displacement.
However, on a reserve split the selected second child's potential is at most
$M$, and the ordered realization makes the first child's potential no larger;
both edges at the split are therefore bounded. The remaining spatial issue is
to connect this split/failure decomposition to the actual candidate positions:
Theorem 1.1 uses an exponential-moment bound for the unbounded first-child
increments on failed generations, while the L¹ version needs its independent
exceptional-event estimate. The growth estimate and causal comparison also
remain open.

The finite-split product-law theorem in
`Restart/RootedTrial/RecursiveReserve.lean` takes an explicit `hfinite`
input, and `Restart/RootedTrial/FiniteSplitCompletion.lean` proves this input
from almost-sure nonempty selected offspring and positive one-step split
probability. `GoodSplit` supplies these hypotheses for its concrete reserve
selector under `BasicBranchingAssumptions`; `RestartSiblingTrial.lean` contains
the concrete bridge. The source nonempty-a.s. premise is essential to this
argument. If it is removed and the offspring law has positive extinction
probability, then with positive probability the first root has no children
and no descendants at any later time. Under the convention
$\min\emptyset=+\infty$, the one-root right-tail event then has probability
at least that extinction mass for every $N$, contradicting the asserted
decay. Thus the general empty-capable model is retained, while a theorem
without the nonempty-a.s. premise would need a different conclusion or an
additional conditioning/restart source.

There is a second, sharper timing issue: $\tau_k$ is defined by the size of
generation $\tau_k+1$, so $\tau_k$ is generally not a stopping time for the
generation filtration. The observable candidate is $\sigma_k=\tau_k+1$.
`lean/ThesisSpeed/Probability/TimingCounterexample.lean` contains a
kernel-checked two-outcome counterexample to the original inference.
There is also a direct counterexample in the thesis model whenever
$0<p_0<1$: $\mathcal F_0$ is trivial, but
$\{\tau_1\le0\}=\{\#\Xi^{(M)b}_{\emptyset}\ge2\}$ has probability $p_0$.
This case is compatible with all stated moment assumptions. For example, let
the number of children be one or two with equal probability, independently of
i.i.d. Gaussian child displacements with mean and variance both
$2\log(3/2)$. Then $\psi(0)=\log(3/2)>0$,
$\psi(1)=\psi'(1)=0$, all needed moments are finite, and a finite $M$ with
$p_0>0$ has $p_0<1$ because half of births have only one child. This example
proves non-stopping for $\tau_1$, not for the final successful completion time
$\tau$; the latter still needs a separate measurability proof.

**Can one replace $\tau_i$ by $\sigma_i=\tau_i+1$?** For the first split,
yes. For later splits this works only if all candidate reserve lineages and
their $\sigma_i$ are defined on the pre-sampled tree *regardless of whether an
earlier growth trial succeeds*. Then the next reserve lineage is chosen from
offspring observed at $\sigma_i$, and its next split is a hitting time of an
adapted process. The abstract recursive stopping-time step is now formalized
in `Timing/CausalSchedule.lean`.  The concrete cardinality readiness event for
the root-indexed selected population is instantiated in
`Population/Processes/StepSelection/SplitSchedule/Basic.lean`. Put
$T_i=\sigma_i+\ell-1$. Each candidate success event $A_i$ can then
be tested at $T_i$; the identity
$\{\tau\le n\}=\bigcup_i\{T_i\le n,A_i,A_1^c,\ldots,A_{i-1}^c\}$
is represented by `Timing/OrderedCandidates.lean`; its split-schedule
specialization is in `SplitSchedule/Completion.lean` and proves the final
successful completion time is a generation stopping time. Population-size
success and its equivalence with the assigned root's fixed-age population are
formalized in `SplitSchedule/Success.lean`. For injectively assigned
pre-sampled roots, `SplitSchedule/Law.lean` proves mutual independence of the
fixed-age success indicators, equality of their marginal probabilities, and
the exact finite-family all-failure probability. `SplitSchedule/Geometric.lean`
proves the resulting first-success point law and identifies the causal ordered
declaration with the global-clock completion of that first successful trial.
`SplitSchedule/Roots.lean` constructs the measurable family of roots supplied
by the first successful population, and `SplitSchedule/FreshField.lean` proves
that their descendant field has the complete product law and is independent
of the selecting generation domain flow. `FreshPool.lean` and `Iteration.lean`
extend this to an active/reserve root pool and prove the complete product law
after every finite number of concrete restart stages.
`SelectedSubtrees/Coordinates.lean` tracks every iterated root back to its
original root/address and proves exact equality of the rebased step field and
of all absolute positions in an arbitrary additive position space. The
generic and split-schedule coupling files use this coordinate map to embed
every finite restarted population injectively into the original field with
identical spatial positions. The recursive rank-matched construction now
compares that embedded population with the target selected walk and composes
the two domination relations pathwise. The former product-law blocker is now
closed: `Coupling/Field/Ranked/Law.lean` proves by induction that every finite
predictable rank-installation stage preserves the complete product field
law; `Selection/NSelection/Law/SelectedPopulation.lean` specializes this to
the concrete first-`N` target; and `Selection/NSelection/Law/CausalPopulation.lean`
packages the recursively matched fields as a coupling with both marginals
verified. `Selection/NSelection/Law/Restarted.lean` instantiates that
coupling for the real-valued restarted killed population and proves the
capacity-event spatial injection. The remaining thesis-specific work is to
identify the reserve-lineage exploration and final frontier with these
interfaces, then prove the quantitative window estimates consumed by the
first-moment bound.

If instead $\sigma_{i+1}$ is defined only after trial $i$ has failed, this
argument fails. For example, let $\sigma_1=1$, let trial 1 be decided at
generation 4, and suppose its reserve sibling splits at generation 2. The
event that the second trial's $\sigma_2$ equals 2 then depends on the
generation-4 outcome, so need not be in $\mathcal F_2$. Defining auxiliary
candidate times unconditionally removes this anticipation from the times,
but does not remove it from the retrospectively selected process
$\mathcal Z_n^{\mathrm b}$.
The original proof calls $\tau_1$ a stopping time and uses
$\mathscr F_{\tau_k}$ for a submartingale. Those passages have been changed
to identify the correct candidate filtration. The i.i.d. fixed-age success
events, the complete geometric point law, and their connection to the causal
completion declaration are verified on distinct pre-sampled roots. For this
original split-schedule route, identifying the success events with the
spatially coupled target process at random completion remains a separate
open bridge; the recursive target product law itself is proved as described
above. The right-tail bound for $a=0$ and hence Theorems 1.1–1.2 cannot yet be
certified.

There are **two different information structures** in the reboot argument.
The generation filtration $\mathcal F_n$ from Chapter 2 reveals every offspring
mark through generation $n-1$. At the end of the first trial it already reveals
marks inside the unused sibling subtree, so conditioning on
$\mathcal F_{\tau_1+\ell}$ cannot make that sibling subtree fresh. The needed
conditional independence is relative to an exploration sigma algebra
$\mathscr H_j$ that records only revealed marks; the unexplored frontier is a
candidate stopping line. Jagers' optional-line branching theorem is relevant
to this step, but its hypotheses have not been verified for this construction.

Even a correct stopping-line argument does **not** make the retrospectively
defined generation process $\mathcal Z_n^{\mathrm b}$ adapted to
$\mathcal F_n$. Lemma 4.8 explicitly assumes that adaptedness, so its use to
obtain $\mathcal Z_n^{\mathrm b}\succcurlyeq\mathcal Z_n^{N|0}$ is invalid as
written. The address-free pathwise induction and its specialization to a
labelled single-root selected trial are now verified in
`Selection/Coupling/StepSelection.lean`. The causal coupled target field is
now constructed measurably and shares the exact source step only at the
canonical matched parents. It preserves the complete product law at every
finite recursively installed stage. The remaining gap for the current proof
of the $a=0$ right tail is the thesis-specific identification of the
trial-frontier construction together with its quantitative one-dimensional
estimates.

The original moment generating function incorrectly treated the waiting
displacement $\Xi_1$ as independent of the non-split event. With
$B=\{\#\Xi^{(M)b}\ge2\}$, the failure contribution is
$A_\lambda=E[e^{\lambda\Xi_1}1_{B^c}]$. In the chosen spatial decomposition,
$X_k$ sums only the first-child displacements on failed generations; the
successful split edge is accounted for separately by the bounded
$(\kappa-1)M$ term. Thus the failure-only cycle transform is
$E[e^{\lambda X_k}]=p_0/(1-A_\lambda)$, where $p_0=P(B)$. The expression
$E[e^{\lambda\Xi_2}1_B]/(1-A_\lambda)$ would instead correspond to a
different cycle variable that includes the successful split edge and must
not be used with the present spatial decomposition. The revised bilingual
thesis text records the failure-only transform and uses a union bound instead
of an unjustified submartingale. Independence across recursive trials and
the causal population comparison remain to be instantiated.
`lean/ThesisSpeed/Probability/GeometricTrial.lean` checks only the abstract
geometric-series identity, not this marked spatial increment law.

## Proposed first-moment Theorem 1.3

The bilingual statement is in `contents/introduction/main-results.tex` and
retains the cross-term assumption. It removes only the fourth moment of the
positive part of `Ξ₁`. The original Theorem 1.1 remains an `L²` theorem with
its original moment assumptions.

**Theorem 1.3 is not yet proved in the thesis or Lean.** A pointwise
first-moment truncation inequality and the final analytic speed-limit step
are machine-checked in
`lean/Probability/BranchingRandomWalk/Analytic/SpeedLimit.lean`. They do not supply
the one-sided `L¹` position estimates or the coupling on exceptional events.
`Restart/GeometricFirstMoment.lean` now states a concrete one-cycle estimate:
the expected positive leftmost displacement accumulated on failed generations
before the first bounded split is at most the one-step positive first moment
divided by the split probability. Its focused test and axiom audit have not
been run; moreover, the estimate is for an i.i.d. reserve sequence and does
not establish freshness or a bound for the actual restarted frontier.
The missing chain is concrete: connect the actual restart declaration to a
reserve subtree disjoint from the inspected domain; prove the pathwise bound
on the exceptional minimum by the reserve continuation; transfer its
`O((\log N)^3)N^{-\varepsilon}=o(\log N)` estimate; and replace the remaining
good-event position estimates that currently use the `L^2` trajectory result.
In particular, simply replacing Cauchy--Schwarz by uniform integrability of
an `O((log N)³)`-step one-particle walk only gives `o((log N)³)`;
the proof needs `o(log N)` at that point. A sharper one-sided argument is
required before calling this a proved strengthening.

## Potential weakening of the cross-term condition

The current pair expectation directly controls the two-descendant term in
the second-moment proof. No moment condition on `Ξ₁` alone can imply its
finiteness: this remains true even if `Ξ₁` has
compact support, so in particular all of its polynomial and exponential
moments are finite.

Here is a point-process counterexample that also satisfies the boundary,
centering, and finite-spine-variance assumptions. Let `N ≥ 3` have law
`P(N=n)=c n^(-9/4)`, where `c` normalizes the probabilities. Then
`E[N] < ∞` but `E[N^(3/2)] = ∞`. For a realization with `N=n`, set the
relative child locations to
`y₁=0` and `yᵢ=(1/4) log n + i/n²` for `2 ≤ i ≤ n`. Put
`Aₙ=Σᵢ exp(-yᵢ)` and `Bₙ=Σᵢ yᵢ exp(-yᵢ)`, and write
`a=E[Aₙ]` and `m=E[Bₙ]/a`. These constants are finite, with `a>1` and
`m>0`. Let `d>0` satisfy `cosh d = a exp(m)`. Let `Q` be uniform on
`{-m-d,-m+d}` and define the law of `Z` by
`P(Z∈dz)=exp(z) Q(dz)/a`, independently of `N`. This is a probability
law, and it gives `E[exp(-Z)]=1/a` and
`E[Z exp(-Z)]=-m/a`. Finally set `Ξᵢ=Z+yᵢ`.

The children are ordered, never absent, and `Ξ₁=Z` has finite support.
Direct calculation gives
`E[Σᵢ exp(-Ξᵢ)]=E[exp(-Z)]a=1` and
`E[Σᵢ Ξᵢ exp(-Ξᵢ)]=E[Z exp(-Z)]a+E[exp(-Z)]E[Bₙ]=0`.
Also `E[N]>1`, and the spine second moment is finite because its integrand
is bounded in expectation by a constant times
`E[N^(3/4)(log N)²] < ∞`. In contrast, the sibling-sibling terms give, for
all `n ≥ 3`,
`Σ_{2≤i≠j≤n} exp(-(yᵢ+yⱼ)) ≥ e^(-1)(n-1)(n-2)n^(-1/2)`.
Because `Z` is independent of `N` and `0 < E[exp(-2Z)] < ∞`, this gives
`E[Σ_{i≠j} exp(-(Ξᵢ+Ξⱼ))]=∞`. Thus neither a condition on `(Ξ₁)₊` nor
a condition on `exp(λ Ξ₁)` or `exp(-λ Ξ₁)` can replace the pair assumption
by implication. Even the rightmost child `Ξₙ=Z+(1/4)log n+1/n` has finite
moments of every polynomial order in this example.

A simple **sufficient** condition involving the leftmost child and the
offspring count is available for finite offspring configurations. If
`K=#Ξ<∞` and `Ξᵢ≥Ξ₁` for every child, then pointwise
`Σ_{i≠j} exp(-(Ξᵢ+Ξⱼ)) ≤ K(K-1) exp(-2Ξ₁)`.
Hence `E[K(K-1)exp(-2Ξ₁)]<∞` implies the pair assumption. This is not an
equivalent reformulation or a demonstrated weakening: it can be strictly
stronger and excludes infinite offspring configurations even when their
exponential pair sum is finite (for example, the deterministic configuration
`Ξᵢ=i`, `i≥1`, has a finite pair sum but infinite `K`).

Mallein's speed theorem uses a different pair of assumptions, not a
first-child moment implication. In his notation, equation (1.9) is a
logarithmic, spine-weighted offspring-cluster tail condition; after the sign
change `ℓ=-Ξᵢ`, it reads in the present notation
`x² E[Σᵢ exp(-Ξᵢ) 1{log(Σⱼ exp(-Ξⱼ)) > x-Ξᵢ}] → 0`
in the finite-variance (`α=2`) case, up to the slowly varying normalization
`L*(x)→σ²`. His separate equation (1.10) is
`E[(max_{ℓ∈L} ℓ)²]<∞`, which becomes `E[Ξ₁²]<∞` under this sign change.
These are hypotheses for a different speed-proof route; (1.10) is not the
cluster-tail condition (1.9), and neither condition is a pointwise bound on
the pair sum. The counterexample above also satisfies (1.9): its indicator
reduces to `log Aₙ+yᵢ>x`, which forces `N≥c exp(x)`, while the weighted sum
is at most `Aₙ=O(N^(3/4))`; hence the weighted tail is `O(exp(-x/2))` and the
left side of (1.9) is `O(x² exp(-x/2))`. It satisfies (1.10) as well, while
its pair expectation is infinite.
Mallein's theorem can therefore provide a separate speed theorem under its
own assumptions, but it does not establish the thesis's `L²` trajectory
Theorem 1.1 or the stated first-moment-only Theorem 1.3. See equations
(1.9)–(1.11) of the [primary paper](https://www.math.univ-toulouse.fr/~bmallein/publications/brwalphaspine.pdf).

## The `a = 1` endpoint under first moments

The lower-speed argument's endpoint at `a = 1` does not need the `L²`
trajectory conclusion. Under the hypotheses of Theorem 1.3, the previously
proved polynomial left-tail estimate (4.16) says, for every
`ζ < c_t := -1 + (π²/2) σ² t`, that
`p_N := P(M^{N|1}_{ℓ_N} ≤ ζ log N) ≤ N^(−ε)` for some `ε > 0`, when
`ℓ_N/log³ N → t`. The additive-martingale estimate gives
`E[exp(−M^{N|1}_{ℓ_N})] ≤ N`; the first-moment lemmas give
`E|M^{N|1}_{ℓ_N}| < ∞`. Splitting at this lower-tail event and using
`x ≥ −exp(−x)` after shifting by `log N` yields the explicit finite-`N`
bound
`E[M^{N|1}_{ℓ_N}] ≥ ζ log N − (max{ζ,0}+1)(log N)p_N − 1`.
In particular the `max{ζ,0}` is essential: for negative `ζ`, the good-event
contribution is at least `ζ log N`, rather than `ζ log N(1−p_N)`. Divide by
`log N`, let `N → ∞`, and then let `ζ ↑ c_t` to obtain
`liminf E[M^{N|1}_{ℓ_N}]/log N ≥ c_t`. Since the lower-speed cycle comparison
only needs this one-sided endpoint estimate, it yields
`liminf (log N)² v_N ≥ −1/t + (π²/2)σ²` for every `t > 0`, and hence the
first-moment hypotheses suffice for the matching lower speed bound after
`t → ∞`.

The generic finite-`N` integral inequality is formalized in
`lean/Probability/BranchingRandomWalk/Analytic/LowerTailExpectation.lean` as
`integral_ge_of_lower_bound_off_event_exp_neg`. It assumes a probability
measure, measurability of the bad event, integrability of `X` and
`exp(−X)`, a pointwise lower bound for `X` off the event, and explicit bounds
on the event probability and exponential moment. The focused Lake module build
passed. The same module now contains
`target_le_liminf_integral_div_log_of_polynomial_lower_tail`: for a sequence
of probability measures and integrable random variables, it proves the
extended-real normalized liminf from an eventual `E[exp(−Xₙ)] ≤ n` bound and a
polynomial lower-tail bound at every threshold below the target; the extended
liminf avoids assuming a uniform upper bound on these expectations. Its
focused build and axiom audit pass. The declarations
`neg_exp_neg_le_self` and
`integral_ge_of_lower_bound_off_event_exp_neg`, and
`target_le_liminf_integral_div_log_of_polynomial_lower_tail` passed the
repository's axiom allowlist check in
`lean/BranchingProcessTest/Probability/BranchingRandomWalk/LowerTailExpectationAxioms.lean`.
The current modules do not yet formalize or instantiate the branching-random-
walk estimate (4.16). `Analytic/LeftTailAtAOne.lean` proves and axiom-audits
the fixed-generation, one-root many-to-one bound for an endpoint below a level
together with a finite-horizon union bound. The shared
`Spectral/Range/BlockBound.lean` provides an eventual fixed-cover
horizontal-tube bound uniform over offsets in `[0,1]`; its focused test and
four-declaration axiom audit pass. The deterministic running-maximum binning,
fixed-pattern product law, finite union estimate, and parameter selection are
formalized in `Path/Drawdown.lean` and `Analytic/DrawdownSlicing.lean`. In
particular,
`exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp`
proves the uniform AH no-large-drawdown bound for centered i.i.d. increments
of variance one: for every endpoint ratio `c > 0`, growth slack `p > 0`, and
`0 < target < blockTarget < π²/2`, there is `delta₀ > 0` such that whenever
`delta ≥ delta₀` and `horizon ≥ delta^(2+p)`, the no-large-drop event with
endpoint threshold `delta/c` has probability at most
`exp(-target * horizon / delta²)`. Its focused module build and axiom audit
pass, with only `[propext, Classical.choice, Quot.sound]`. This statement is
explicitly normalized to variance one and uses the proved Brownian
finite-cover block bound. `DrawdownNormalization.lean` now transports both the
sequential and uniform versions to centered positive finite variance, with the
exponent scaled by the variance. This closes the random-walk estimate at that
normalization, not the branching-random-walk estimate (4.16).

This closes the random-walk drawdown estimate, not the branching-random-walk
estimate (4.16). That estimate still requires controlling large drawdowns
across selected particles and transferring the complementary event to the
population started from `floor(N^a)`. Thus the `a = 1` endpoint argument is
closed on paper conditional on (4.16), while its Lean bridge from the BRW
hypotheses to the polynomial-tail premise remains open. The `a = α`
random-remaining-time good-event estimate, the post-endpoint restart law, the
zero-start tube estimate, and the full Theorem 1.3 are also still open.

## Reuse in Lean

The pinned mathlib checkout provides filters, real limits, integration,
stochastic-process and martingale infrastructure. A search of that checkout
found no existing branching random walk, Galton--Watson, many-to-one, or
Mogul'skii module. Public search also found no ready-to-import Lean
formalization of this specific model. The related
[LeanLevy](https://github.com/slink/LeanLevy) and
[Stat-Lean](https://github.com/StatLean/Stat-Lean) libraries cover adjacent
probability machinery, not the missing branching-selection theorem.
The local Lean library reuses mathlib's stopping-time theorem and proves only
the missing finite size-bias algebra. Its full dependency audit is in
`lean/FORMALIZATION_CHECKLIST.md`.
