# Formalization checklist

The statuses below refer to kernel-checked Lean proofs in this repository.
The LaTeX proof is not counted as a Lean proof.

| Order | Obligation | Status | Reusable source / next step |
|---|---|---|---|
| 1 | Real limit and two-sided speed squeeze | **Done** | `ThesisSpeed/Analytic.lean` |
| 2 | First-moment pointwise truncation inequality | **Done** | `ThesisSpeed/Analytic.lean`; integration and the required `o(log N)` bound are still missing |
| 3 | Finite or countable offspring point process and selected $N$-BRW | Missing | Build on mathlib measures, countable products, and finite multisets |
| 4 | Generation filtration, unconditional candidate bifurcation times $\sigma_k=\tau_k+1$, and exploration information $\mathscr H_j$ | Missing | Define reserve lineages even after success; a time defined only after a later failure may anticipate that failure |
| 5 | First success of an adapted process or measurable declaration, including after a stopping start, is a stopping time | **Done, generic** | `ThesisSpeed/Probability/Stopping.lean`, reusing mathlib's `hittingAfter_isStoppingTime`; model-specific reserve observables remain missing |
| 6 | Prove the final $\tau=\tau_\kappa+\ell$ is a generation stopping time | **Generic declaration theorem done; model instance missing** | `ThesisSpeed/Probability/Measurability.lean` proves that stopping candidate completions and adapted generation tests give a stopping first-success time; the marked-tree model must still verify the hypotheses and identify this time with the thesis’s $\tau$ |
| 7 | Branching property at deterministic times | Missing | Prove from independence of offspring laws in the marked tree |
| 8 | Branching at the final time $\tau$ and at intermediate exploration frontiers | Missing | The former may use a generation stopping time; the latter needs a stopping-line theorem relative to $\mathscr H_j$ |
| 9 | Both directions of the many-to-one formula | **Finite one-step algebra done; probabilistic theorem missing** | `ThesisSpeed/Spine/FiniteKernel.lean` proves weighted and unweighted cancellation. Next: random/countable offspring, normalized measure, product independence and induction, following Shi §1.3 |
| 10 | Mogul'skiĭ small-deviation theorem for the finite-variance spine | Missing | No Lean formalization found in the checked mathlib tree or public search; would require a substantial invariance/small-ball development |
| 11 | Horizontal and tilted tube estimates, including the entrance lower bound | Missing | Depends on orders 9–10; the LaTeX entrance estimate also needs a lower local-limit theorem |
| 12 | Killed-BRW pair estimate and Paley–Zygmund step | Missing | Depends on orders 7, 9, 11; this is where the cross-term assumption is used |
| 13 | Couplings of selected, killed, and restarted walks | **Generic causal-adaptation theorem done; blocking model gap** | `ThesisSpeed/Probability/Measurability.lean` proves adaptedness for a measurable recursion using only currently observed marks. Retrospective restart need not satisfy this recursion or Lemma 4.8; construct a causal coupling or another comparison proof |
| 14 | Theorem 1.1, $L^2$ trajectory limit | Missing | Depends on orders 3–13 |
| 15 | Existence of the selected-walk speed | Missing | Formalize the subadditive process and apply an ergodic theorem |
| 16 | Theorem 1.2, speed under fourth moment | Missing | Depends on the preceding estimates and the analytic closure in order 1 |
| 17 | Theorem 1.3, proposed speed under first moment | Missing | Needs a separate one-sided $L^1$ argument; order 2 alone is insufficient |

The immediate next model-specific target is order 4, followed by order 6.
Only after those are proved can the stopping-time branching property in order 8
be invoked without an additional hypothesis.

## Local dependency layout

- `ThesisSpeed/Probability/Stopping.lean` contains only the thesis-specific
  adaptation of mathlib's `hittingAfter_isStoppingTime`. It does not redefine
  filtration, measurable space or stopping time.
- `ThesisSpeed/Probability/TimingCounterexample.lean` gives a kernel-checked
  counterexample to the original look-ahead stopping-time claim. In the thesis
  model itself, $\{\tau_1\le0\}$ has probability $p_0\in(0,1)$ in an allowed
  parameter case, whereas $\mathcal F_0$ is trivial. This does not settle
  whether the final successful completion time $\tau$ is a stopping time.
- `ThesisSpeed/Probability/Measurability.lean` proves the measurable candidate declaration and causal recursion interfaces. It does not construct the marked tree, reserve candidates, or coupling.
- `ThesisSpeed/Spine/FiniteKernel.lean` contains the finite offspring algebra
  for **both** many-to-one variants. It is not the expectation identity for
  random offspring and is not marked as the full theorem.
- `ThesisSpeed/Analytic.lean` contains the final deterministic speed squeeze
  and an elementary first-moment truncation inequality.

Shi, *Branching Random Walks*, §1.3, Theorem 1.1 proves the unweighted
many-to-one formula by induction: the one-generation weighted law is followed
by conditioning on the first generation and the branching property. The
weighted variant in the thesis follows by choosing a weighted test function.
The reference is at
<https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf>.

## Additional deductions that must not be hidden

1. A random countable offspring point process must admit the weighted sum and
   its expectation in the extended nonnegative reals. Normalization and any
   conversion to finite real expectations need their own integrability lemmas.
2. The one-step tilted law needs a constructed probability measure. Across
   generations, the tilted increments must be proved independent and identically
   distributed before the random-walk identity is used.
3. The many-to-one induction needs measurability of path tests and a Tonelli
   or conditional-expectation interchange for the offspring sums.
4. The restart schedule must be observable generation by generation, including
   failed trials, truncated descendants, and the generation at which the
   decision is announced. Its increasing trial times alone do not prove this.
   In particular $\tau_k$ looks at generation $\tau_k+1$; the candidate
   stopping time is $\sigma_k=\tau_k+1$. For $k\ge2$, this requires defining
   candidate reserve lineages independently of preceding trial outcomes.
5. The stopped branching property requires independence of all descendant
   subtrees from the stopped sigma algebra, with countably many possible
   generations and a random surviving particle set.
   The intermediate reboot trials instead require an exploration sigma
   algebra $\mathscr H_j$ and an optional/stopping line of unexposed roots.
6. Mogul'skiĭ must be stated with the exact centering, variance, scaling,
   tube regularity and endpoint conditions used later. The tilted entrance
   lower bound additionally needs a local or ballot lower estimate.
7. The selected and restarted walk moment estimates require separate proofs;
   ordinary selected-walk estimates do not automatically transfer to restart.
   Waiting displacements are coupled to non-split events; their joint
   transform, rather than a product of marginal transforms, is required.
8. Every use of a limit interchange, monotone convergence, Fatou, or uniform
   integrability in the $L^2$ and proposed $L^1$ closures remains a separate
   proof obligation.
