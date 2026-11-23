# Doob and spine interface audit (2026-11-23)

The comparison uses pinned Mathlib
`26573066084e6e2aa8526ea358bc43b66d96f970`, its local source, and the official
[with-density composition API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/WithDensity.html),
[finite-history API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/IonescuTulcea/PartialTraj.html),
and [trajectory API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/IonescuTulcea/Traj.html).
The source-facing mathematical statements remain those of Zhan Shi,
*Branching Random Walks*, LNM 2151 (2015), §4.2, (4.3)–(4.4), and §4.4,
(4.8), Theorem 4.4(ii), DOI 10.1007/978-3-319-25372-5.

## Removed wrappers

| Removed declaration or module | Existing interface used by clients |
| --- | --- |
| `Kernel.doobTransform_apply` | Unfold the Doob weight, then use `Kernel.withDensity_apply`. |
| `Kernel.doobTransform_one` | `Kernel.withDensity_one` / `withDensity_one'`, through the existing simplifier. The constant-one regression remains. |
| `Kernel.doobTransform_isSFiniteKernel` | `IsSFiniteKernel.withDensity` and `ENNReal.div_ne_top`. The finite-positive weight hypotheses stay unchanged. |
| `Kernel.lintegral_pow_doobTransform` | This unused convenience statement combined the retained `doobTransform_pow` with `lintegral_doobTransform`; no independent implementation is needed. |
| `Kernel/IonescuTulcea/PartialTraj.lean`, containing `lintegral_partialTraj_succ` | Native `partialTraj_succ_of_le`, `Kernel.lintegral_comp`, `Kernel.lintegral_id_prod`, and `Kernel.lintegral_map`, directly at the finite-history proof steps. |
| `Process/Markov/DoobTransform.lean`, containing `doobTransformOnPositive_isMarkovChain` | The existing homogeneous `isMarkovChain_traj_historyKernel`, after eligible-region normalization. |
| `Spine.eligibleStateKernel_isMarkovChain` | The same homogeneous Markov realization, with the already proved spine-kernel normalization. |

All source imports, calls and axiom-test expectations were migrated. No
forwarding names, compatibility modules or replacement wrapper layers remain.

## Retained mathematics and abstraction boundaries

| Module or construction | Comparison and retention reason |
| --- | --- |
| `Kernel/DoobTransform/Basic.lean` | The definition uses native `Kernel.withDensity` with ratio `h(y)/h(x)`. The integral formula, harmonic normalization and zero/infinite-weight support express Doob-specific facts. The pinned kernel library has generic density operations but no corresponding Doob transform API. |
| `Kernel/DoobTransform/Composition.lean` | Native composition, powers and density transport do not themselves cancel the intermediate ratio. The substantive identities `Lʰ ∘ Kʰ = (L ∘ K)ʰ` and `(Kʰ)^n = (K^n)ʰ` retain that algebraic step. |
| `Kernel/DoobTransform/Restriction.lean` | Native `comap` and `comapRight` construct the restriction. Its normalization now uses native `IsMarkovKernel.comapRight`; the additional mathematics proves total mass one on `E = {0 < h < ∞}` from harmonicity only there. `map_comap` supplies the ambient-measure recovery identity. |
| `Kernel/DoobTransform/Trajectory.lean` | Native finite histories and with-density integrals are used throughout. The new content is the telescoping endpoint density `h(X_b)/h(x_a)`, proved for s-finite kernels without harmonicity. Generic density composition alone does not supply this path identity. |
| `Kernel/Composition/Pow.lean` | The pinned source provides native kernel multiplication/powers and s-finite composition closure, but no s-finite power instance. The induction supplies that missing closure for arbitrary s-finite kernels. A Markov-power instance would exclude unnormalized mean offspring kernels and is therefore insufficient. |
| `Kernel/IonescuTulcea/Markov.lean` | The homogeneous history adapter is a native input comap. The endpoint identification with `K^(b-a)` adds an induction over finite histories. Mathlib's `traj_map_frestrictLe` gives history marginals; it does not identify them with homogeneous kernel powers. |
| `Process/Markov/Trajectory.lean` | `condExp_traj` gives conditional expectations of complete continuations. Combining it with the homogeneous endpoint law proves the repository's `IsMarkovChain` property. No matching general process predicate or homogeneous realization was found in the pinned Mathlib probability sources. |
| `Spine/Family/` and `Spine/StateChain.lean` | The family/child bias, its marginal and the actual distinguished-child observation concern indexed optional offspring. They already use native kernel sums, densities and maps; Mathlib has no corresponding offspring/spine construction. The state transition remains the one generic Doob kernel applied to the mean child kernel. |
| `Spine/Observation.lean`, `Spine/Tree/Observation.lean` | The marked-population readout is model-specific; its measurability uses native countable-codomain and product interfaces. List/tuple conversion now uses native `List.ofFn_congr`, `List.ofFn_get` and `List.equivSigmaTuple`, replacing direct coordinate-conversion proofs. |
| `State.treeKernel_generations` | The tree-to-generation law concerns the existing canonical branching process. Its coordinate inverse now uses `List.equivSigmaTuple.apply_symm_apply` directly. |
| `Spine/Tree/PathLaw.lean` and `Tree/Lemmas/PathLaw.lean` | The public theorem identifies the actual tree observation with the Doob-chain law using `Kernel.map_eq_trajMeasure`. Its generation-assembly lemmas depend on the tagged reproduction rules and remain internal under `Lemmas/`, with `import all` at the caller. No second tree or chain law is constructed. |
| `Spine/Tree/BranchingProperty.lean` and `State/Descendants/Disintegration.lean` | The former is a weighted offspring-specific recursive split; the latter specializes the existing canonical descendant disintegration. Both use existing product/map and conditional-law interfaces. Mathlib's trajectory and density laws do not encode these branching families, so those mathematical results remain at their model owners. |

The conditional family/child formula was also compared with native
`ProbabilityTheory.posterior` in
[`Kernel/Posterior.lean`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Posterior.html).
That construction takes a finite prior and finite kernel and assumes a
nonempty standard-Borel parameter space. The existing algebraic conditional
selection identity allows a merely s-finite offspring kernel, a zero-weight
parent and an empty index type, with no standard-Borel assumption on its
spaces. Its explicit normalized weights are therefore retained; replacing
them by a posterior construction would require additional data or stronger
hypotheses.

## Assumptions preserved

The finite-history density and composition results still accept arbitrary
s-finite kernels and measurable finite positive weights; harmonicity is
required only for probability normalization. The eligible-state construction
requires harmonicity only on the finite positive-weight region. Ordinary
branches may have zero or infinite weight and can later return to that
region. State spaces remain arbitrary measurable spaces; no standard-Borel,
state-countability, moment or global positive-weight assumptions are added to
the realized-spine theorem.

Validation includes focused builds of the retained Doob and spine theorem
entries, the zero-weight-side-branch path-law regression, the constant-one
transform regression, axiom audits, import boundaries, Python script tests
and Mathlib style checks on changed production modules.
