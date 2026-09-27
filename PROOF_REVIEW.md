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

**Remaining audit issue:** the transition estimate in the proof of the
tilted-tube lower bound (`contents/part-2-eng.tex`, event `E₀`) calls the
probability `O(1/Δ)` and then needs `≥ C/Δ`. The displayed lower bound
requires a stated lower local-limit or ballot theorem with its hypotheses
verified for the moving tube; weak convergence of the conditioned endpoint
alone does not supply the survival probability. This affects a key input to
both main theorems and still needs a complete reference or proof.

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
Lean. The new measurable-candidate and causal-recursion interfaces are also kernel-checked. The marked-tree instance, its identification with $\tau$, and branching at $\tau$ remain unproved.

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
retrospective reserve-branch restart written in this thesis. A possible
general-law replacement is a causal one-or-two-child process that always
retains $\Xi_1$ and retains $\Xi_2$ when it is at most a fixed $M$.
It has no extinction and a positive binary-split probability, but its
population-growth and spatial bounds must be proved under this thesis's
assumptions before it can replace the current $a=0$ proof. The speed proof
also invokes the old restart without an exponential moment, so it needs a
separate replacement.

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
formalized in `SplitSchedule/Success.lean`. The remaining obligation here is
the theorem-specific spatial coupling to the target selected walk.

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
to identify the correct candidate filtration, but the required random-time
independence and the geometric i.i.d. claims remain unverified. The right-tail
bound for $a=0$ and hence Theorems 1.1–1.2 cannot yet be certified.

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
written. The bilingual text now makes this comparison conditional on a new
causal coupling or an independent comparison proof. This is a blocking gap for
the current proof of the $a=0$ right tail.

The original moment generating function also incorrectly treated the waiting
displacement $\Xi_1$ as independent of the non-split event. The correct joint
transform is $A_\lambda=E[e^{\lambda\Xi_1}1_{B^c}]$, yielding
$E[e^{\lambda X_k}]=p_0/(1-A_\lambda)$ after the trial independence is proved.
The revised text uses a union bound instead of an unjustified submartingale.
`lean/ThesisSpeed/Probability/GeometricTrial.lean` checks only the resulting
geometric-series identity.

## Proposed first-moment Theorem 1.3

The bilingual statement is in `contents/introduction/main-results.tex` and
retains the cross-term assumption. It removes only the fourth moment of the
positive part of `Ξ₁`. The original Theorem 1.1 remains an `L²` theorem with
its original moment assumptions.

**Theorem 1.3 is not yet proved in the thesis or Lean.** A pointwise
first-moment truncation inequality and the final analytic speed-limit step
are machine-checked in `lean/ThesisSpeed/Analytic.lean`. They do not supply
the one-sided `L¹` position estimates or the coupling on exceptional events.
In particular, simply replacing Cauchy--Schwarz by uniform integrability of
an `O((log N)³)`-step one-particle walk only gives `o((log N)³)`;
the proof needs `o(log N)` at that point. A sharper one-sided argument is
required before calling this a proved strengthening.

## Potential weakening of the cross-term condition

The current pair expectation directly controls the two-descendant term in
the second-moment proof. A condition only on the first child `Ξ₁` does not
control this expectation if the offspring count has a heavy tail. The
precise replacement condition therefore remains undecided. Mallein's
original speed theorem uses a different logarithmic weighted-offspring tail
condition, equation (1.9), rather than this pair moment; see the
[primary paper](https://arxiv.org/html/1503.03762v2). Its separate
assumption (1.10) controls the extremal child, and should not be confused
with (1.9). Neither has yet been shown sufficient for Theorem 1.1 here.

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
