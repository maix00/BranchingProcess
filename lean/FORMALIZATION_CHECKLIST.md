# Formalization checklist

The statuses below refer to kernel-checked Lean proofs in this repository.
The LaTeX proof is not counted as a Lean proof.

| Order | Obligation | Status | Reusable source / next step |
|---|---|---|---|
| 1 | Real limit and two-sided speed squeeze | **Done** | `ThesisSpeed/Analytic.lean` |
| 2 | First-moment pointwise truncation inequality | **Done** | `ThesisSpeed/Analytic.lean`; integration and the required `o(log N)` bound are still missing |
| 3 | Finite or countable offspring point process and selected $N$-BRW | **Done at the construction, measurability, representation, and multi-root-law level** | `PointProcess/Basic.lean` admits zero offspring. `Enumeration/FromMeasure.lean` measurably enumerates ranked atoms from rational cumulative counts, proves finite ordered optional slots, the rank/CDF equivalence, and exact equality of the reconstructed Dirac sum with the original measure. It therefore constructs `canonicalOrderedSlotRepresentation` for every abstract offspring point process. `Law/MultiRootRepresentation.lean` transfers the original point-process law to every address of every labelled root. `Population/Processes/Selected.lean` gives the adapted selected process and size bound; nonextinction additionally uses the thesis's at-least-one-child assumption. |
| 4 | Generation filtration, unconditional candidate bifurcation times $\sigma_k=\tau_k+1$, and exploration information $\mathscr H_j$ | **Countable pre-sampled reserve recursion and every $\sigma_i$ done; model-specific reserve geometry and $\mathscr H_j$ missing** | `Genealogy/Reserve.lean` defines every causal reserve lineage on the same pre-sampled tree independently of earlier outcomes, proves each path adapted, and proves every visible split completion $\sigma_i$ and the first successful tested completion are stopping times. The thesis coupling must instantiate the reserve paths and define its exploration information. |
| 5 | First success of an adapted process or measurable declaration, including after a stopping start, is a stopping time | **Done, generic** | `ThesisSpeed/Probability/Timing/Stopping.lean`, reusing mathlib's `hittingAfter_isStoppingTime`; model-specific reserve observables remain missing |
| 6 | Prove the final $\tau=\tau_\kappa+\ell$ is a generation stopping time | **Generic declaration theorem done; model instance missing** | `ThesisSpeed/Probability/Timing/Measurability.lean` proves that stopping candidate completions and adapted generation tests give a stopping first-success time; the marked-tree model must still verify the hypotheses and identify this time with the thesis’s $\tau$ |
| 7 | Branching property at deterministic times | **Selected-population branching on every finite-set cell and measurable current-position tests done; a single dependent random-size law and translated descendant process missing** | `Branching/MultiRootBranching.lean` proves joint past/future independence and product law for distinct labelled roots across initial ancestors. `Branching/MultiRootRandomSubtrees.lean` proves the fixed-size random-vector version. `Branching/SelectedPopulationBranching.lean` proves that each event specifying the actual selected set is generation-domain measurable, constructs its duplicate-free enumeration, and gives the joint product factorization on that event, including events testing all current particle positions. Next package all cardinalities into one dependent random-size law and define descendants translated by those positions |
| 8 | Branching at the final time $\tau$ and at intermediate exploration frontiers | **Single root, fixed-cardinality vector, every finite-population cell at a finite stopping time, and the selected-population stopping-cell interface done; dependent packaging and coupling instance missing** | `Branching/StoppingTime.lean` handles one stopped-measurable root. `Branching/StoppingVector.lean` handles a fixed-length random vector. `Branching/MultiRootStoppingPopulation.lean` partitions a stopped finite population by its set value and stopping generation, enumerates each cell without duplicates, and proves the multi-root product subtree law, including the empty cell. It also defines the concrete `selectedPopulationAt`, proves its stopping-cell measurability and depth interface, and instantiates the abstract theorem as `selectedPopulation_stopped_cell_branches`. `Branching/Exploration.lean` handles a random unused reserve selected through $\mathscr H_j$. It remains to package all cardinalities in one dependent object and instantiate the concrete coupling. |
| 9 | Both directions of the many-to-one formula | **Finite algebra, exponential specialization, measurable monotone truncations, exact supremum limit, normalized offspring PMF, nonzero weight, and coordinate measurability done; probabilistic theorem missing** | `ThesisSpeed/Spine/FiniteKernel.lean` proves weighted and unweighted cancellation, specializes the weighted direction to exponential weights, and proves the exponential normalizer is nonzero for every nonempty finite family. `Spine/TruncatedWeights.lean` defines the first-$n$ slot exponential weight, proves measurability, monotonicity, domination, and `⨆ n, truncatedChildWeight n = totalChildWeight`. `Spine/TiltedOffspring.lean` reuses mathlib's `PMF.normalize`, proves its mass-one and weighted tsum identities, shows a nonempty offspring mark has nonzero total weight, and proves the normalized coordinate weight is measurable on the whole mark space (with zero fallback outside the finite-positive domain). Next: establish random-law measurability and product independence across generations, then induction, following Shi §1.3 |
| 10 | Mogul'skiĭ small-deviation theorem for the finite-variance spine | Missing | No Lean formalization found in the checked mathlib tree or public search; would require a substantial invariance/small-ball development |
| 11 | Horizontal and tilted tube estimates, including the entrance lower bound | Missing | Depends on orders 9–10; the LaTeX entrance estimate also needs a lower local-limit theorem |
| 12 | Killed-BRW pair estimate and Paley–Zygmund step | Missing | Depends on orders 7, 9, 11; this is where the cross-term assumption is used |
| 13 | Couplings of selected, killed, and restarted walks | **Both causal truncated populations and their adaptation done; causal comparison for the retrospective restart missing** | `Population/Processes/Retained.lean` models the backbone law $\Xi^{(M)\mathrm b}$ and proves nonextinction only under an explicit first-child hypothesis. `Population/Processes/Truncated.lean` models $\Xi^{(M)}$, where both children are truncated and extinction is possible. Both processes are adapted and satisfy $Z_n\le2^n$. No joint coupled law or rankwise comparison with the selected process has been proved. |
| 14 | Theorem 1.1, $L^2$ trajectory limit | Missing | Depends on orders 3–13 |
| 15 | Existence of the selected-walk speed | Missing | Formalize the subadditive process and apply an ergodic theorem |
| 16 | Theorem 1.2, speed under fourth moment | Missing | Depends on the preceding estimates and the analytic closure in order 1 |
| 17 | Theorem 1.3, proposed speed under first moment | Missing | Needs a separate one-sided $L^1$ argument; order 2 alone is insufficient |

The next model-specific targets are the full reserve-lineage recursion in order 4 and completion-time identification in order 6.
Only after those are proved can the stopping-time branching property in order 8
be invoked without an additional hypothesis.

The assumptions themselves are formalized separately under
`ThesisSpeed/Assumptions/`. `Structural.lean` contains the ordered-support,
nonempty, supercritical, and boundary-normalization predicates;
`Moments.lean` contains the leftmost and cross-weight moment predicates and
proves that the fourth leftmost moment implies the first moment;
`Bundles.lean` records the current theorem-specific groupings. Centering and
finite variance will be stated on the spine law once that probability measure
has been constructed. The possible weakening of the cross-weight assumption
has not yet been asserted as a theorem.

## Local dependency layout

The Lean probability modules are arranged by role:

- `Probability/PointProcess/`: abstract random point measures, empty-capable slot encodings, Dirac-sum measures, enumeration, and point-process laws. Enumeration algorithms live in `Enumeration/`; probability laws live in `Law/`.
- `Probability/Genealogy/`: marked Ulam--Harris trees, the generation domain filtration, positions, first observable splits, and multiple initial roots.
- `Probability/Branching/`: fixed and generation-measurably selected subtree product laws, including the multi-root versions.
- `Probability/Population/`: `Candidates/` for finite ranking and truncation, `Processes/` for selected and retained recursions, and `Growth/` for deterministic size lemmas.
- `Probability/Timing/`: generic stopping-time and measurability lemmas, timing counterexamples, and geometric trials.

All of these are imported by `ThesisSpeed.lean`; `Spine/` and `Analytic.lean` remain separate because they are proof layers rather than probability-space definitions. Within one initial ancestor, a *single* i.i.d. pre-sampled marked tree supplies every reserve branch. A finite vector of same-generation roots indexes descendant marked trees in `Branching/RandomSubtreeVector.lean`; their joint product law is proved there. The vector length is fixed at the theorem interface. Random population size, stopped generations, position offsets, and stopping-line frontiers are not covered by that theorem.

For the theorem with $m_N=\lfloor N^\alpha\rfloor$ **initial particles**, `Genealogy/MultiRoot.lean` uses $m_N$ labelled initial roots, each with its own pre-sampled Ulam--Harris tree. The initial positions are supplied as `Fin m_N → ℝ`, so all-zero starts and later common shifts are representable. `Branching/MultiRootBranching.lean` and `Branching/MultiRootRandomSubtrees.lean` prove deterministic-generation branching across these roots, including roots selected using the entire multi-root domain filtration. `Population/Processes/Selected.lean` defines one common selection pool, proves its labelled set adapted, bounds its size by $N$ after the first generation, and proves nonextinction under an explicit pathwise first-child hypothesis. `PointProcess/Law/OrderedSupport.lean` derives that hypothesis almost surely from ordered support together with the thesis's at-least-one-child assumption. The earlier single-tree statements concern descendants of one initial ancestor and cannot substitute for this multi-root process.
`Population/Candidates/MultiRoot.lean` makes the finite step explicit. `Population/Candidates/Adapted.lean` proves that an adapted finite parent set produces a measurable candidate set at the next generation, by partitioning over the countable parent-set values. `PointProcess/Enumeration/Order.lean` proves local prefix and displacement witnesses for later slots. `Population/Candidates/FiniteLeftmost.lean` proves a deterministic rank rule and its cardinal bound. Its tie key compares parent identity, then the child's slot number, then a full-address fallback; `candidateEarlier_ordered_siblings` proves earlier siblings beat later siblings even at equal displacement. The first version's arbitrary full-address code did not have this property and was corrected. `Population/Candidates/FullTruncation.lean` proves exact equality between finite first-$N$-slot selection and full countable-child selection under ordered marks, pointwise at every generation and almost surely under an ordered-support mark law. The remaining gap at this layer is constructing that mark law as a measurable ordered enumeration of the thesis's original offspring point process. `Branching/SelectedPopulationBranching.lean` adds a product descendant-tree law on every cell specifying the actual finite selected set. `Branching/MultiRootStoppingPopulation.lean` proves the analogous cellwise statement for any stopped-measurable finite population under the multi-root filtration, supplies `selectedPopulationAt`, its cell measurability and stopped-depth implication, and instantiates the concrete theorem `selectedPopulation_stopped_cell_branches` for the selected process. It also proves the countable population-cell partition and its measure sum. It partitions by the finite population value and the stopping generation, so no stopping-line abstraction is needed for this theorem. A single dependent random-size law and the concrete coupling instance remain open.

`PointProcess/Law/MultiRootRepresentation.lean` lifts any completed ordered
representation to all $m$ labelled initial roots. It proves that the offspring
point measure at every root/address has the original abstract law, and that
ordered support and the at-least-one-child property hold simultaneously over
all roots almost surely. Thus the remaining representation-existence proof is
shared by the single-root and $m=\lfloor N^\alpha\rfloor$ models; no separate
independence assumption is introduced for the multi-root theorem.

`Branching/MultiRootExploration.lean` uses labelled coordinates
`Fin m × TreeNode` for exploration information. It proves that a reserve
subtree under any initial root is independent of the joint exploration domain
whenever its labelled descendant coordinates have not been inspected. Equal
local addresses under two different initial roots remain distinct coordinates.

The raw mark type does not order optional children. `PointProcess/Enumeration/Order.lean` defines the ordered subset. `Enumeration/FromMeasure.lean` now constructs a canonical measurable member of this subset directly from every abstract counting measure, including the zero measure, and proves exact Dirac-sum reconstruction. Thus `firstDisplacement` and `keepSecond` refer to $\Xi_1$ and $\Xi_2$ for the canonical representation without adding a moment assumption.
`PointProcess/LocalFiniteness.lean` now proves the deterministic first step: a finite total exponential atom weight gives finitely many labelled atoms below each real threshold and, when at least one atom exists, a leftmost atom. It reuses mathlib's cofinite convergence of a finite `ENNReal` sum and the finite-set minimal-element theorem. The subsequent measurable sorting and law correspondence remain missing.
`PointProcess/Enumeration/FirstAtom.lean` and the recursive raw-slot enumeration remain useful for reordering an already indexed family. `Enumeration/FromMeasure.lean` is the stronger representation result for the thesis input: it enumerates an abstract measure directly and needs only the foundational counting and left-local-finiteness fields. `PointProcess/Measure.lean` reuses mathlib's `Measure.sum`, `Measure.dirac`, and measure-valued measurable space; multiplicities are preserved. Mathlib supplies no dedicated point-process type in the pinned revision, but the representation bridge is now complete locally.

An external Lean 4 project, [LeanLevy](https://github.com/slink/LeanLevy),
constructs a Poisson random measure by summing Dirac measures at realized
points; see its [`PoissonRandomMeasure.lean`](https://github.com/slink/LeanLevy/blob/main/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean).
This confirms the reusable mathlib construction pattern but its Poisson
point-family assumptions are not the thesis's arbitrary reproduction law.
Mathlib's [`HasPDF`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Density.html)
means absolute continuity of a random variable's law relative to a reference
measure. It is not the definition of a point process and is not assumed for
the present atomic offspring measure. The Brownian-motion development uses
process and Gaussian-law APIs, not a general point-process representation.
`PointProcess/Law/OrderedSupport.lean` proves that if the one-node mark law gives this ordered subset probability one, then every address in the entire pre-sampled tree has an ordered mark simultaneously almost surely. This uses mathlib's countable almost-everywhere intersection and the proved one-node marginals; it does not itself establish the antecedent from the abstract offspring point process.

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
- `ThesisSpeed/Probability/Genealogy/Tree.lean` defines the generation filtration on the pre-sampled Ulam--Harris tree (including the trivial generation-zero σ-algebra) and proves fixed-node, dynamically selected-node, and causal-lineage measurability. `Genealogy/FirstSplit.lean` contains the model-specific first observable split theorem.
- `ThesisSpeed/Probability/PointProcess/Encoding.lean` gives countably many uniformly optional child slots. The all-absent mark represents zero offspring. `PointProcess/Law/IID.lean` supplies the i.i.d. tree law, but no binomial lower-tail estimate has yet been proved for the retained population.
- `ThesisSpeed/Probability/Population/Processes/Retained.lean` instantiates the causal backbone recursion as a finite set of labelled particles. It proves adaptation, $Z_n\le2^n$, and conditional nonextinction under a first-child hypothesis. `Processes/Truncated.lean` separately implements the possibly empty fully truncated law $\Xi^{(M)}$ and proves its adaptation and binary upper bound without claiming nonextinction.
- `ThesisSpeed/Probability/PointProcess/Law/IID.lean` reuses mathlib's `Measure.infinitePi`, `infinitePi_map_eval`, and `iIndepFun_infinitePi` for a pre-sampled i.i.d. family at every genealogical address. The random law is parametrized; no moment or ordering hypothesis is silently imposed.
- `ThesisSpeed/Probability/Branching/BranchingProperty.lean` reuses mathlib's `indep_iSup_of_disjoint` and `Measure.map_infinitePi_infinitePi_of_inj`. It proves the actual generation domain is independent of all future raw marks, each fixed descendant subtree has the original i.i.d. law, and two distinct same-depth descendant domains are independent. It does not yet cover the joint random surviving set or positions.
- `ThesisSpeed/Probability/Branching/RandomSubtree.lean` proves the selected subtree is measurable for a generation-domain-measurable root; if that root has the current depth, a countable measurable partition gives the exact past/subtree event factorization, the original subtree law, and independence from the generation domain. The proof uses no look-ahead choice.
- `ThesisSpeed/Probability/Branching/JointSubtrees.lean` uses a prefix-address injection and mathlib's curry theorem for infinite product measures to prove the joint product law for any finite vector of distinct same-generation roots. It also proves the vector of subtrees reads only future marks and gives its past/future event factorization.
- `ThesisSpeed/Probability/Branching/RandomSubtreeVector.lean` partitions by the countable finite vector of selected addresses. It proves measurability, the event factorization, the joint i.i.d. product law, and independence from the generation domain for a measurable vector of $k$ distinct generation-$n$ roots. It does not yet identify such a vector with the actual selected or killed BRW population.
- `ThesisSpeed/Probability/Branching/MultiRootStoppingPopulation.lean` accepts an arbitrary stopped-domain-measurable finite set of labelled roots, including roots under different initial ancestors. On every prescribed set cell it proves the exact product descendant law by a further countable partition over the finite stopping generation. The theorem includes the empty population and applies directly with $m=\lfloor N^\alpha\rfloor$; it does not assume a child exists.
- `ThesisSpeed/Probability/Genealogy/Positions.lean` defines displacement of every child slot, the finite-path position sum, and realization of an address by all its ancestor presence flags. The latter two are measurable at the address's generation; the position of a measurably selected current-generation address is adapted. The position function is deliberately total on non-realized addresses, so later particle-system theorems must explicitly require `realizedNode`.
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
