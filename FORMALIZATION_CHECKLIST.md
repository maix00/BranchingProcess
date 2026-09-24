# Formalization checklist

The statuses below refer to kernel-checked Lean proofs in this repository.
The LaTeX proof is not counted as a Lean proof.

| Order | Obligation | Status | Reusable source / next step |
|---|---|---|---|
| 1 | Real limit and two-sided speed squeeze | **Done** | `ThesisSpeed/Analytic.lean` |
| 2 | First-moment pointwise truncation inequality | **Done** | `ThesisSpeed/Analytic.lean`; integration and the required `o(log N)` bound are still missing |
| 3 | Finite or countable offspring point process and selected $N$-BRW | **Adapted multi-root selected process and full countable-child equivalence done under ordered-mark support; measurable raw-slot enumeration in progress; full abstract point-process representation missing** | `Tree/MultiRoot.lean` models $m$ initial particles by `Fin m`, proves positions and realization measurable, and transfers ordered support from one mark to all roots and addresses almost surely. `Population/SelectedPopulation.lean` defines common globally ranked selection, proves the labelled set adapted, nonempty for $m,N>0$, and of size $\le N$ after one step. `Population/FullCandidateTruncation.lean` proves that, under ordered marks, every recursive step equals ranking all realized children of all selected parents, including ties, and gives the almost-sure all-generation version. `Tree/MeasurableNextAtom.lean` and `Tree/MeasurableEnumeration.lean` measurably choose successive raw slots with an explicit terminal value and prove no repeats, terminal persistence, and displacement order. Full coverage and ordered-mark law transfer remain missing. Set $m=\lfloor N^\alpha\rfloor$ for the thesis |
| 4 | Generation filtration, unconditional candidate bifurcation times $\sigma_k=\tau_k+1$, and exploration information $\mathscr H_j$ | **Generation filtration and first causal split done; reserve recursion and $\mathscr H_j$ missing** | `ThesisSpeed/Probability/Tree/MarkedTree.lean` proves fixed and selected-node mark measurability and first observable split stopping. Define all reserve lineages even after success |
| 5 | First success of an adapted process or measurable declaration, including after a stopping start, is a stopping time | **Done, generic** | `ThesisSpeed/Probability/Timing/Stopping.lean`, reusing mathlib's `hittingAfter_isStoppingTime`; model-specific reserve observables remain missing |
| 6 | Prove the final $\tau=\tau_\kappa+\ell$ is a generation stopping time | **Generic declaration theorem done; model instance missing** | `ThesisSpeed/Probability/Timing/Measurability.lean` proves that stopping candidate completions and adapted generation tests give a stopping first-success time; the marked-tree model must still verify the hypotheses and identify this time with the thesis’s $\tau$ |
| 7 | Branching property at deterministic times | **Selected-population branching on every finite-set cell and measurable current-position tests done; a single dependent random-size law and translated descendant process missing** | `Branching/MultiRootBranching.lean` proves joint past/future independence and product law for distinct labelled roots across initial ancestors. `Branching/MultiRootRandomSubtrees.lean` proves the fixed-size random-vector version. `Branching/SelectedPopulationBranching.lean` proves that each event specifying the actual selected set is generation-domain measurable, constructs its duplicate-free enumeration, and gives the joint product factorization on that event, including events testing all current particle positions. Next package all cardinalities into one dependent random-size law and define descendants translated by those positions |
| 8 | Branching at the final time $\tau$ and at intermediate exploration frontiers | Missing | The former may use a generation stopping time. For the latter, prove unused reserve subtrees are independent of exploration information $\mathscr H_j$ by a countable partition over selected labelled roots and independence of disjoint marks; a general stopping-line theorem is sufficient but not necessary |
| 9 | Both directions of the many-to-one formula | **Finite one-step algebra done; probabilistic theorem missing** | `ThesisSpeed/Spine/FiniteKernel.lean` proves weighted and unweighted cancellation. Next: random/countable offspring, normalized measure, product independence and induction, following Shi §1.3 |
| 10 | Mogul'skiĭ small-deviation theorem for the finite-variance spine | Missing | No Lean formalization found in the checked mathlib tree or public search; would require a substantial invariance/small-ball development |
| 11 | Horizontal and tilted tube estimates, including the entrance lower bound | Missing | Depends on orders 9–10; the LaTeX entrance estimate also needs a lower local-limit theorem |
| 12 | Killed-BRW pair estimate and Paley–Zygmund step | Missing | Depends on orders 7, 9, 11; this is where the cross-term assumption is used |
| 13 | Couplings of selected, killed, and restarted walks | **Concrete retained-set adaptation done; causal comparison for the retrospective restart missing** | `ThesisSpeed/Probability/Population/RetainedPopulation.lean` constructs a causal one-or-two-child finite genealogical population. Its full labelled set, each membership event, each second-child decision, and its size are adapted to the generation filtration. It proves $1\le Z_n\le2^n$ without a binary-branching assumption. The selected-$N$ process is now defined in `Population/SelectedPopulation.lean`, but no joint coupled law or rankwise comparison with the killed process has been proved. The retrospective reserve restart is not itself a causal generation process and cannot yet use Aïdékon--Hu Lemma 4.8. |
| 14 | Theorem 1.1, $L^2$ trajectory limit | Missing | Depends on orders 3–13 |
| 15 | Existence of the selected-walk speed | Missing | Formalize the subadditive process and apply an ergodic theorem |
| 16 | Theorem 1.2, speed under fourth moment | Missing | Depends on the preceding estimates and the analytic closure in order 1 |
| 17 | Theorem 1.3, proposed speed under first moment | Missing | Needs a separate one-sided $L^1$ argument; order 2 alone is insufficient |

The next model-specific targets are the ordered point-process representation in order 3, full reserve-lineage recursion in order 4, and completion-time identification in order 6.
Only after those are proved can the stopping-time branching property in order 8
be invoked without an additional hypothesis.

## Local dependency layout

The Lean probability modules are arranged by role:

- `Probability/Tree/`: raw offspring marks, their law, ordered point-process interface, the marked Ulam--Harris tree, and path positions.
- `Probability/Branching/`: fixed and generation-measurably selected subtree product laws, including the multi-root versions.
- `Probability/Population/`: causal retained-set recursion, multi-root finite candidate construction, measurable global finite-rank selection, and elementary growth bounds.
- `Probability/Timing/`: generic stopping-time and measurability lemmas, timing counterexamples, and geometric trials.

All of these are imported by `ThesisSpeed.lean`; `Spine/` and `Analytic.lean` remain separate because they are proof layers rather than probability-space definitions. Within one initial ancestor, a *single* i.i.d. pre-sampled marked tree supplies every reserve branch. A finite vector of same-generation roots indexes descendant marked trees in `Branching/RandomSubtreeVector.lean`; their joint product law is proved there. The vector length is fixed at the theorem interface. Random population size, stopped generations, position offsets, and stopping-line frontiers are not covered by that theorem.

For the theorem with $m_N=\lfloor N^\alpha\rfloor$ **initial particles**, `Tree/MultiRoot.lean` uses $m_N$ labelled initial roots, each with its own pre-sampled Ulam--Harris tree. The initial positions are supplied as `Fin m_N → ℝ`, so all-zero starts and later common shifts are representable. `Branching/MultiRootBranching.lean` and `Branching/MultiRootRandomSubtrees.lean` prove deterministic-generation branching across these roots, including roots selected using the entire multi-root domain filtration. `Population/SelectedPopulation.lean` defines one common selection pool, proves its labelled set adapted, proves it stays nonempty for positive initial and carrying capacities, and bounds its size by $N$ after the first generation. The earlier single-tree statements concern descendants of one initial ancestor and cannot substitute for this multi-root process.
`Population/MultiRootCandidates.lean` makes the finite step explicit. `Population/MultiRootCandidateAdapted.lean` proves that an adapted finite parent set produces a measurable candidate set at the next generation, by partitioning over the countable parent-set values. `Tree/OrderedOffspring.lean` proves local prefix and displacement witnesses for later slots. `Population/FiniteLeftmost.lean` proves a deterministic rank rule and its cardinal bound. Its tie key compares parent identity, then the child's slot number, then a full-address fallback; `candidateEarlier_ordered_siblings` proves earlier siblings beat later siblings even at equal displacement. The first version's arbitrary full-address code did not have this property and was corrected. `Population/FullCandidateTruncation.lean` proves exact equality between finite first-$N$-slot selection and full countable-child selection under ordered marks, pointwise at every generation and almost surely under an ordered-support mark law. The remaining gap at this layer is constructing that mark law as a measurable ordered enumeration of the thesis's original offspring point process. `Branching/SelectedPopulationBranching.lean` adds a product descendant-tree law on every cell specifying the actual finite selected set. A single dependent random-size law and stopped/stopping-line branching theorem remain open.

The raw mark type does not order optional children. `Tree/OrderedOffspring.lean` proves measurability of the subset on which slot zero is leftmost, optional realized slots form an initial segment, and successive displacements are nondecreasing. It also supplies a checked mark outside that subset. Thus the current `firstDisplacement` and `keepSecond` refer to $\Xi_1$ and $\Xi_2$ only after an ordered-support hypothesis. The thesis derives left-local finiteness from a finite exponential moment, but a measurable sorted enumeration and proof that its law is supported on `orderedOffspring` still need to be formalized. This representation step must not be skipped or treated as an extra moment assumption.
`Tree/LocalFiniteness.lean` now proves the deterministic first step: a finite total exponential atom weight gives finitely many labelled atoms below each real threshold and, when at least one atom exists, a leftmost atom. It reuses mathlib's cofinite convergence of a finite `ENNReal` sum and the finite-set minimal-element theorem. The subsequent measurable sorting and law correspondence remain missing.
`Tree/MeasurableFirstAtom.lean` defines a unique tie-resolving first-atom index on the existing raw countably indexed mark. Its value and displacement are measurable, and finite expected total exponential weight makes the selector correct almost surely. On `orderedOffspring` support it agrees with slot zero, as assumed by the current selected-walk code. `Tree/MeasurableNextAtom.lean` defines the unique next unused realized atom and proves its optional raw index jointly measurable in the mark and finite used-slot set. Under finite exponential weight, `none` is equivalent to there being no unused realized child. `Tree/MeasurableEnumeration.lean` recursively selects optional slots and proves measurability at each rank, distinctness of successful slots, persistence of `none`, and nondecreasing displacements. The remaining steps are full coverage of every realized atom, construction of an ordered `OffspringMark` from these choices, and transfer of the original point-process law. The original thesis point-process law still needs an explicit measurable coding into this raw mark space.
`Tree/OrderedLaw.lean` proves that if the one-node mark law gives this ordered subset probability one, then every address in the entire pre-sampled tree has an ordered mark simultaneously almost surely. This uses mathlib's countable almost-everywhere intersection and the proved one-node marginals; it does not itself establish the antecedent from the abstract offspring point process.

- `ThesisSpeed/Probability/Timing/Stopping.lean` contains only the thesis-specific
  adaptation of mathlib's `hittingAfter_isStoppingTime`. It does not redefine
  filtration, measurable space or stopping time.
- `ThesisSpeed/Probability/Timing/TimingCounterexample.lean` gives kernel-checked
  counterexamples to the original look-ahead stopping-time claim and to automatic
  adaptedness of a generation-one state chosen from a generation-two outcome.
  It also proves that an adapted population count need not make the retained
  particle identity adapted. In the thesis
  model itself, $\{\tau_1\le0\}$ has probability $p_0\in(0,1)$ in an allowed
  parameter case, whereas $\mathcal F_0$ is trivial. This does not settle
  whether the final successful completion time $\tau$ is a stopping time.
- `ThesisSpeed/Probability/Timing/Measurability.lean` proves the measurable candidate declaration and causal recursion interfaces. It does not construct the marked tree, reserve candidates, or coupling.
- `ThesisSpeed/Probability/Tree/MarkedTree.lean` defines the generation filtration on the pre-sampled Ulam--Harris tree (including the trivial generation-zero σ-algebra) and proves fixed-node, dynamically selected-node, causal-lineage, and first-split measurability.
- `ThesisSpeed/Probability/Tree/OffspringMarks.lean` gives one guaranteed first child, countably many optional child slots, and measurable first-bifurcation and truncated-second-child events. `ThesisSpeed/Probability/Population/OneOrTwoGrowth.lean` proves deterministic nonextinction and the upper size bound $Z_n\le2^n$. `Tree/OffspringLaw.lean` supplies the i.i.d. tree law, but no binomial lower-tail estimate has yet been proved for the retained population; reuse mathlib's generic Chernoff bounds if applicable.
- `ThesisSpeed/Probability/Population/RetainedPopulation.lean` instantiates the causal recursion as a finite set of labelled particles. It proves the complete set and its cardinality are adapted, proves each membership and second-child choice event measurable at the required generation, and derives $1\le Z_n\le2^n$ for the actual recursion. This only handles a causal killed comparison process; no selected-$N$ walk or probability estimate has been defined yet.
- `ThesisSpeed/Probability/Tree/OffspringLaw.lean` reuses mathlib's `Measure.infinitePi`, `infinitePi_map_eval`, and `iIndepFun_infinitePi` for a pre-sampled i.i.d. family at every genealogical address. The random law is parametrized; no moment or ordering hypothesis is silently imposed.
- `ThesisSpeed/Probability/Branching/BranchingProperty.lean` reuses mathlib's `indep_iSup_of_disjoint` and `Measure.map_infinitePi_infinitePi_of_inj`. It proves the actual generation domain is independent of all future raw marks, each fixed descendant subtree has the original i.i.d. law, and two distinct same-depth descendant domains are independent. It does not yet cover the joint random surviving set or positions.
- `ThesisSpeed/Probability/Branching/RandomSubtree.lean` proves the selected subtree is measurable for a generation-domain-measurable root; if that root has the current depth, a countable measurable partition gives the exact past/subtree event factorization, the original subtree law, and independence from the generation domain. The proof uses no look-ahead choice.
- `ThesisSpeed/Probability/Branching/JointSubtrees.lean` uses a prefix-address injection and mathlib's curry theorem for infinite product measures to prove the joint product law for any finite vector of distinct same-generation roots. It also proves the vector of subtrees reads only future marks and gives its past/future event factorization.
- `ThesisSpeed/Probability/Branching/RandomSubtreeVector.lean` partitions by the countable finite vector of selected addresses. It proves measurability, the event factorization, the joint i.i.d. product law, and independence from the generation domain for a measurable vector of $k$ distinct generation-$n$ roots. It does not yet identify such a vector with the actual selected or killed BRW population.
- `ThesisSpeed/Probability/Tree/Positions.lean` defines displacement of every child slot, the finite-path position sum, and realization of an address by all its ancestor presence flags. The latter two are measurable at the address's generation; the position of a measurably selected current-generation address is adapted. The position function is deliberately total on non-realized addresses, so later particle-system theorems must explicitly require `realizedNode`.
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
   algebra $\mathscr H_j$ and a proof that the selected unused reserve subtree
   is fresh. A direct countable-coordinate partition could replace a general
   stopping-line theorem, but still needs the same no-look-ahead property.
6. Mogul'skiĭ must be stated with the exact centering, variance, scaling,
   tube regularity and endpoint conditions used later. The tilted entrance
   lower bound additionally needs a local or ballot lower estimate.
7. The selected and restarted walk moment estimates require separate proofs;
   ordinary selected-walk estimates do not automatically transfer to restart.
   Waiting displacements are coupled to non-split events; their joint
   transform, rather than a product of marginal transforms, is required.
9. Aïdékon--Hu Lemma 4.8 applies to a killed process selected by a rule
   adapted to the natural generation filtration. Its separate $a=0$ shortcut
   uses the always-binary offspring law of that paper and does not extend to
   the present general point process. The current retrospective reserve
   construction is not a verified instance of Lemma 4.8. Starting trials
   sequentially only after failures would consume $K\ell=O((\log N)^2)$
   generations for $K,\ell=O(\log N)$ and loses the stated $O(\log N)$
   restart-time budget. A concurrent causal-backbone construction is a
   possible repair, but its population bound, spatial estimate, and
   measurable coupling must be proved before invoking the lemma.
8. Every use of a limit interchange, monotone convergence, Fatou, or uniform
   integrability in the $L^2$ and proposed $L^1$ closures remains a separate
   proof obligation.
