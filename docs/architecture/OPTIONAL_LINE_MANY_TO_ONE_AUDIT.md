# Simple-line many-to-one and generation-truncated mass

Audit date: 2026-11-23. Mathlib revision:
`26573066084e6e2aa8526ea358bc43b66d96f970`.

## References and exact scope

J. D. Biggins and A. E. Kyprianou, *Measure change in multitype branching*,
*Advances in Applied Probability* 36 (2004), 544–581,
[DOI:10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585),
[published author PDF](https://warwick.ac.uk/fac/sci/statistics/staff/academic-research/kyprianou/BK2004.pdf),
was checked in its published form, particularly §6 and §14, pp. 577–579.
The existing local source copy supplied the full proofs when the author site
was temporarily unavailable. Zhan Shi, *Branching Random Walks* (2015),
§4.3, Lemma 4.1, [DOI:10.1007/978-3-319-25372-5](https://doi.org/10.1007/978-3-319-25372-5),
supplies the ordinary generation-martingale specialization.

A simple optional line satisfies `{u ∈ L} ∈ F_|u|`. This allows decisions to
use other branches in the current generation. It is stronger than optionality
alone and weaker than deciding membership from the node's own ancestral
states. `Tree.IsOptionalLine.IsSimple` records this condition relative to an
explicit native generation filtration, on the existing optional-line object.

| Source | Completed formalization |
| --- | --- |
| Biggins–Kyprianou, Lemma 14.1 | General-state simple-line many-to-one, including nonnegative generation-history payoffs; `E[W_L]=P_spine(spine meets L)≤1`, with equality to one exactly when entrance has probability one. |
| Biggins–Kyprianou, Lemma 14.3, mass recursion and martingale assertion | The frozen boundary mass `S_n = ∑_(k<n) A_k + U_n` is a native nonnegative generation martingale, has expectation one and converges almost surely to the native filtration limit process. |
| The combinatorial cut used in Lemma 14.3 | `mass_truncate` identifies `W_(L_n)=∑_(k<n) A_k+U_n` with the already implemented `RootIndexed.Line.truncate`. No second cut definition is introduced. |
| Shi, Lemma 4.1 | The ordinary ancestral generation-density martingale is derived from the empty-line case of the stopped-mass theorem. Its independent density-consistency proof was removed. |

The mean-harmonic weight is measurable and may vanish or be infinite outside
its eligible region. The root has finite positive weight. The existing
ancestral product `addressWeight` retains the eligibility check at every
parent; returning from a zero-weight state never restores ancestral mass.
State spaces are arbitrary measurable spaces and child slots are countable
with measurable singletons. No moment beyond the mean-harmonic normalization,
bounded depth, coverage or uniform integrability is used for the completed
statements. Initial state is a specified eligible root, as in these source
statements; arbitrary joint root laws remain available in the separate strong
branching theorem.

## Proof and reuse

The fixed-address identity is applied before summing over addresses and
generations, exactly as in the calculation proving Lemma 14.1. For a simple
line the membership event factors through the finite generation history.
The countable sum on the distinguished tree has at most one surviving term,
since a line is an antichain and the distinguished vertices lie on one ray.
This proves the entrance-probability identity without a finite entrance-time
assumption. The right side is the same complete distinguished-tree law;
for a simple rule depending on other branches it cannot be replaced just by
the marginal Doob state-chain law.

For the mass recursion, `A_n` is boundary mass at depth `n` and `U_n` is mass
with no strict ancestor on the line. At every generation event `B`,

`∫_B A_n + ∫_B U_(n+1) = ∫_B U_n`.

The existing generation densities give this conditional mean-conservation
identity by splitting the distinguished ray into entrance at `n` and
continued non-entrance. Freezing the earlier `A_k` yields the same one-step
recursion as Lemma 14.3. Every selected generation sum is dominated by
`totalWeight`; its mean-one identity gives the required integrability.
Mathlib's native set-integral martingale criterion and L¹-bounded
submartingale convergence theorem then supply the martingale and its limit.
No conditional expectation, martingale, tree law or spine process is redefined.

The pinned sources and official Mathlib documentation were compared:

| Operation | Native API used |
| --- | --- |
| Doob–Dynkin factorization | [`Measurable.exists_eq_measurable_comp`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/FactorsThrough.html); the Standard Borel target here is only `ENNReal`, not the state or history space. |
| Nonnegative sums and regrouping | `lintegral_tsum`, `Equiv.tsum_eq`, `List.equivSigmaTuple`, `tsum_sigma'`, `tsum_eq_sum`. |
| Finite real integration | `integrable_toReal_of_lintegral_ne_top`, `integral_toReal`, `integrable_finsetSum`, `integral_add`. |
| Martingale identification | [`martingale_of_setIntegral_eq_succ`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Basic.html), `Martingale.setIntegral_eq`. |
| Convergence | [`Submartingale.ae_tendsto_limitProcess`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Martingale/Convergence.html), with `eLpNorm_one_eq_lintegral_eNorm` and `ofReal_integral_norm_eq_lintegral_eNorm`. |

Mathlib's `densityProcess` concerns a particular countably generated kernel
disintegration construction. It does not supply a state-tree line or its mass.
Here the existing complete distinguished tree and its fixed-address densities
are reused directly. The already proved arbitrary-optional-line strong branching
law remains the basis for the pending conditional formula below; an ancestral
stopping-time interface is not substituted for it.

## Ownership and visibility

* `State/Observation/History.lean`: ordinary finite-tree observation and its
  native filtration, independent of probability and spine bias.
* `Process/Tree/Line/Optional.lean`: simple observability relative to an
  explicitly supplied filtration, without a branching model.
* `Spine/StoppingLine/Mass.lean`: reusable line-mass observations and their
  deterministic regrouping and truncation identities.
* `Spine/StoppingLine/ManyToOne.lean` and `Martingale.lean`: public theorem entries.
* `Spine/StoppingLine/Lemmas/Truncation.lean`: only the specific generation-test
  assembly, conditional recursion and domination steps. Cross-file helpers are
  ordinary internal `lemma`s, imported with `import all`; tactical steps remain
  private. They are not re-exported.
* `Spine/Tree/Density/Martingale.lean`: ordinary generation specialization,
  derived from the stopped-line theorem.

`StoppingLine/` has three direct files and one `Lemmas/` directory containing
one proof file; `Tree/Density/` has four direct files and `State/Observation/`
four. There are no path or declaration aliases.

## Remaining obligations

The source's statements have different hypotheses and are tracked separately:

1. Lemma 14.2's conditional identity at an arbitrary optional line is still
   open. Neither simple-line many-to-one nor the generation-martingale
   assertion is claimed to prove it.
2. Full optionality of the generation truncations for simple lines, the
   identification of the almost-sure limit with `W_L`, and L¹ convergence
   under `E[W_L]=1` remain to be connected. An empty line has `W_L=0` while
   `E[S_n]=1`, so omitting expectation preservation would be incorrect.
3. Lemma 14.4 and the martingale indexed by increasing mean-preserving lines
   in Theorem 6.1 remain open. The proved martingale is indexed by generations
   truncating one line, not by arbitrary successive optional lines.
4. The existing BRW first-entry field formula still needs its law-transport
   adapter to this state-tree entry and identification of its tilted path.
   No replacement BRW process or second generic spine law was added.

`ae_truncatedMass_eq` additionally identifies the real martingale with the
real value of the actual combinatorial truncated-line mass almost surely.
Finiteness follows from domination by the normalized generation densities.

The regression checks the ordinary martingale with zero-weight return branches,
its line-weight guard, simple-line entrance at a non-covering depth-two cut,
and the distinction between zero full empty-line mass and unit expected
truncated mass. Public conclusions have explicit axiom reports.

## Validation

The complete 11,969-job library build, all 150 Lean tests, 32 Python tests,
Mathlib style lint over 1,794 modules and the strengthened import-boundary
audit passed. Explicit public theorem reports use only `propext`,
`Classical.choice` and `Quot.sound`.


## Nonnegative conditional integration

`State.condLExp_descendantTrees_optionalLine` integrates a measurable
nonnegative payoff `g(x, trees)` against the already identified
`State.descendantTreesKernel`. Its first input is measured in the stopped
sigma-algebra. The index set of the tested family is arbitrary; each chosen
address has countable range, lies on the line, and the choices are injective.
No integrability is required. The empty tested family is allowed even when
the optional line is empty. This does not assert the existence of a selector
on an empty line, or replace the localized identities for random cardinality.

The only measure-theoretic addition is
`ProbabilityTheory.HasCondDistrib.condLExp_eq` in
`Probability/Kernel/ConditionalExpectation.lean`. It integrates the native
conditional distribution of an a.e. measurable pair. Assumptions: an s-finite
ambient measure, a measurable observation `X`, sigma-finite `P.trim` on the
sigma-algebra generated by `X`, an s-finite supplied kernel, and a measurable
nonnegative payoff. Finite measures automatically meet the trimmed
sigma-finiteness requirement. There is no standard-Borel assumption on either
value space and no regular conditional-distribution existence claim.

The pinned Mathlib revision `26573066084e6e2aa8526ea358bc43b66d96f970`
was searched for `HasCondDistrib`, conditional Lebesgue integration, and
kernel comp-products. Its `HasCondDistrib` supplies the joint law but no
nonnegative conditional-integration method. The proof reuses native
`MeasureTheory.ae_eq_condLExp`, `Measure.setLIntegral_compProd`, and
`lintegral_map'`; conditional expectation, kernels, and process laws are
not redefined. Official online API checked:
[ConditionalLExpectation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConditionalLExpectation.html).
This is the nonnegative integration of the same strong-branching kernel in
Jagers–Lagerås (2008), §2.3; the full Biggins–Kyprianou Lemma 14.2 identity
listed above remains a separate open assembly obligation.

Regression coverage includes an infinite payoff on an empty tested family,
with no global selector from the optional line. Both new declarations have
explicit axiom reports checked by the test runner.


### Localization to one boundary-membership event

`State.condLExp_on_optionalLine` proves, for a deterministic address `u`,

```
E[1_(u ∈ L) g(x,T_u) | F_L]
  = 1_(u ∈ L) ∫ g(x,t) P_(stateAt u)(dt).
```

The payoff may depend measurably on the stopped information, may be infinite,
and requires no moment assumption. No selector or countable enumeration of the
line is used. The proof restricts the existing generation-path measure to
`E={u∈L}`, identifies the supplied native subtree conditional law there from
the already proved localized bounded-test identities, applies
`HasCondDistrib.condLExp_eq`, and uses native conditional Lebesgue expectation
uniqueness to return to the ambient measure. The censored boundary state is
only a measurable kernel argument outside `E`; it defines no new process.

This completes the nonnegative subtree conditional-integration ingredient in
Biggins–Kyprianou Lemma 14.2. The required generation-weight decomposition and
its identification with `StoppingLine.mass` on the canonical state-tree law
remain open. Regression coverage localizes an infinite payoff to a random
line that is empty on one initial-state cell and has two different depths on
the complementary cell. An explicit axiom report is registered for this result.
