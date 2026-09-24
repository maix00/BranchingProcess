# Formalization checklist

The statuses below refer to kernel-checked Lean proofs in this repository.
The LaTeX proof is not counted as a Lean proof.

| Order | Obligation | Status | Reusable source / next step |
|---|---|---|---|
| 1 | Real limit and two-sided speed squeeze | **Done** | `ThesisSpeed/Analytic.lean` |
| 2 | First-moment pointwise truncation inequality | **Done** | `ThesisSpeed/Analytic.lean`; integration and the required `o(log N)` bound are still missing |
| 3 | Finite or countable offspring point process and selected $N$-BRW | **Countable raw mark space and i.i.d. law done; selected $N$-BRW missing** | `ThesisSpeed/Probability/OffspringMarks.lean` encodes one guaranteed child and countably many optional children. `OffspringLaw.lean` uses mathlib's infinite product measure and proves each mark has the prescribed marginal and all marks are independent. The assumptions connecting this encoding to the thesis's ordered point process, and the selected population, remain missing |
| 4 | Generation filtration, unconditional candidate bifurcation times $\sigma_k=\tau_k+1$, and exploration information $\mathscr H_j$ | **Generation filtration and first causal split done; reserve recursion and $\mathscr H_j$ missing** | `ThesisSpeed/Probability/MarkedTree.lean` proves fixed and selected-node mark measurability and first observable split stopping. Define all reserve lineages even after success |
| 5 | First success of an adapted process or measurable declaration, including after a stopping start, is a stopping time | **Done, generic** | `ThesisSpeed/Probability/Stopping.lean`, reusing mathlib's `hittingAfter_isStoppingTime`; model-specific reserve observables remain missing |
| 6 | Prove the final $\tau=\tau_\kappa+\ell$ is a generation stopping time | **Generic declaration theorem done; model instance missing** | `ThesisSpeed/Probability/Measurability.lean` proves that stopping candidate completions and adapted generation tests give a stopping first-success time; the marked-tree model must still verify the hypotheses and identify this time with the thesis’s $\tau$ |
| 7 | Branching property at deterministic times | **I.i.d. coordinate marks done; subtree theorem missing** | `OffspringLaw.lean` proves joint independence using mathlib's `iIndepFun_infinitePi`; next identify descendant subtrees by address prefix and prove their independence from the generation information |
| 8 | Branching at the final time $\tau$ and at intermediate exploration frontiers | Missing | The former may use a generation stopping time; the latter needs a stopping-line theorem relative to $\mathscr H_j$ |
| 9 | Both directions of the many-to-one formula | **Finite one-step algebra done; probabilistic theorem missing** | `ThesisSpeed/Spine/FiniteKernel.lean` proves weighted and unweighted cancellation. Next: random/countable offspring, normalized measure, product independence and induction, following Shi §1.3 |
| 10 | Mogul'skiĭ small-deviation theorem for the finite-variance spine | Missing | No Lean formalization found in the checked mathlib tree or public search; would require a substantial invariance/small-ball development |
| 11 | Horizontal and tilted tube estimates, including the entrance lower bound | Missing | Depends on orders 9–10; the LaTeX entrance estimate also needs a lower local-limit theorem |
| 12 | Killed-BRW pair estimate and Paley–Zygmund step | Missing | Depends on orders 7, 9, 11; this is where the cross-term assumption is used |
| 13 | Couplings of selected, killed, and restarted walks | **Concrete retained-set adaptation done; probability and comparison gaps remain** | `ThesisSpeed/Probability/RetainedPopulation.lean` constructs a causal one-or-two-child finite genealogical population. Its full labelled set, each membership event, each second-child decision, and its size are adapted to the generation filtration. It proves $1\le Z_n\le2^n$ without a binary-branching assumption. The i.i.d. marked-tree law is in `OffspringLaw.lean`; high-probability lower growth, spatial bound, selected-$N$ process, and pathwise comparison still need proofs. The retrospective restart is not validated by this result. |
| 14 | Theorem 1.1, $L^2$ trajectory limit | Missing | Depends on orders 3–13 |
| 15 | Existence of the selected-walk speed | Missing | Formalize the subadditive process and apply an ergodic theorem |
| 16 | Theorem 1.2, speed under fourth moment | Missing | Depends on the preceding estimates and the analytic closure in order 1 |
| 17 | Theorem 1.3, proposed speed under first moment | Missing | Needs a separate one-sided $L^1$ argument; order 2 alone is insufficient |

The immediate next model-specific target is the full reserve-lineage recursion in order 4, followed by the completion-time identification in order 6.
Only after those are proved can the stopping-time branching property in order 8
be invoked without an additional hypothesis.

## Local dependency layout

- `ThesisSpeed/Probability/Stopping.lean` contains only the thesis-specific
  adaptation of mathlib's `hittingAfter_isStoppingTime`. It does not redefine
  filtration, measurable space or stopping time.
- `ThesisSpeed/Probability/TimingCounterexample.lean` gives kernel-checked
  counterexamples to the original look-ahead stopping-time claim and to automatic
  adaptedness of a generation-one state chosen from a generation-two outcome.
  It also proves that an adapted population count need not make the retained
  particle identity adapted. In the thesis
  model itself, $\{\tau_1\le0\}$ has probability $p_0\in(0,1)$ in an allowed
  parameter case, whereas $\mathcal F_0$ is trivial. This does not settle
  whether the final successful completion time $\tau$ is a stopping time.
- `ThesisSpeed/Probability/Measurability.lean` proves the measurable candidate declaration and causal recursion interfaces. It does not construct the marked tree, reserve candidates, or coupling.
- `ThesisSpeed/Probability/MarkedTree.lean` defines the generation filtration on the pre-sampled Ulam--Harris tree (including the trivial generation-zero σ-algebra) and proves fixed-node, dynamically selected-node, causal-lineage, and first-split measurability.
- `ThesisSpeed/Probability/OffspringMarks.lean` gives one guaranteed first child, countably many optional child slots, and measurable first-bifurcation and truncated-second-child events. `ThesisSpeed/Probability/OneOrTwoGrowth.lean` proves deterministic nonextinction and the upper size bound $Z_n\le2^n$. `OffspringLaw.lean` supplies the i.i.d. tree law, but no binomial lower-tail estimate has yet been proved for the retained population; reuse mathlib's generic Chernoff bounds if applicable.
- `ThesisSpeed/Probability/RetainedPopulation.lean` instantiates the causal recursion as a finite set of labelled particles. It proves the complete set and its cardinality are adapted, proves each membership and second-child choice event measurable at the required generation, and derives $1\le Z_n\le2^n$ for the actual recursion. This only handles a causal killed comparison process; no selected-$N$ walk or probability estimate has been defined yet.
- `ThesisSpeed/Probability/OffspringLaw.lean` reuses mathlib's `Measure.infinitePi`, `infinitePi_map_eval`, and `iIndepFun_infinitePi` for a pre-sampled i.i.d. family at every genealogical address. The random law is parametrized; no moment or ordering hypothesis is silently imposed.
- `ThesisSpeed/Spine/FiniteKernel.lean` contains the finite offspring algebra
  for **both** many-to-one variants. It is not the expectation identity for
  random offspring and is not marked as the full theorem.
- `ThesisSpeed/Analytic.lean` contains the final deterministic speed squeeze
  and an elementary first-moment truncation inequality.

Shi, *Branching Random Walks*, §1.3, Theorem 1.1 proves the unweighted
many-to-one formula by induction: the one-generation weighted law is followed
by conditioning on the first generation and the branching property. The
weighted variant in the thesis follows by choosing a weighted test function.
This is a paper proof, not reusable Lean code: it assumes the independent BRW
subtrees and the normalized tilted law rather than establishing their
measurability. Shi §1.4, Lemma 1.5 also gives the elementary exponential
minimum bound using Jensen and max $\le$ sum; no new probability construction
is needed for that deduction once the many-to-one identity is formalized.
The reference is at
<https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf>.

## Dependency version audit (2026-09-25)

The previous project configuration used a local path dependency at commit
`de43fbb3c6cbf629cdb6805e24c258f76538689b` (2025-12-01), with Lean
`v4.26.0-rc2`. The project now pins the official upstream mathlib commit
`b3b63681020779dc7e14866c0b2afbd84e0722e4`, which was upstream HEAD
when checked again on 2026-09-25, together with its Lean `v4.35.0-rc2` toolchain.
The local user-fork checkout was not modified. Elan itself was updated to
`4.2.4`. `lake update mathlib` downloaded its cache and `lake build ThesisSpeed`
passes against this pinned revision. A moving upstream branch cannot be
guaranteed to remain current forever; the pinned revision makes the proof
check reproducible.

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
