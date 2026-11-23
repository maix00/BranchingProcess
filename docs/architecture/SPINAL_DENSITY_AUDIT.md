# Fixed-address spinal densities and optional-line pasting

## Source proof and mathematical scope

The spinal density argument follows Zhan Shi, *Branching Random Walks*,
Lecture Notes in Mathematics 2151 (Springer, 2015), Chapter 4, §4.5,
proof of Theorem 4.3, (4.12)–(4.13), followed by (4.11) and Theorem 4.4(i),
(4.9). [DOI 10.1007/978-3-319-25372-5](https://doi.org/10.1007/978-3-319-25372-5);
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).

The canonical state-kernel tree and its original normal/distinguished
reproduction rules are retained. At each induction step, the terminal address
is fixed. Independent ordinary-parent families are integrated with their
original laws; the distinguished parent contributes the fixed child's ratio
`h(child)/h(parent)`. Appending the last generation is the induction in
Shi (4.13). Retaining an arbitrary measurable finite-history payoff expresses
the same ordinary-branch integration without introducing separate symbols for
the functions obtained by integrating each sibling subtree. Source finite
cylinder products, including the factored payoffs in (4.13), are covered by
this statement. The proof sums over terminal addresses only afterward.

For untyped history `Hₙ` and fixed address `z`, the results are

$$E_{\rm spine}[1_{\{w_n=z\}}g(H_n)]
 =E[W_z(H_n)g(H_n)],\qquad
 \mathcal L_{\rm spine}(H_n)=\mathcal L(H_n)\,\sum_z W_z.$$

`addressWeight_eq_endpointRatio` identifies the successive ratios with

$$W_z=1_{\{\text{all strict ancestors have finite positive weight}\}}
       \frac{h(x_z)}{h(x_\varnothing)}.$$

The root is finite and positive. An endpoint of weight zero contributes zero;
infinite weights can occur only on null sets relevant to the density. The
mean-harmonic condition is required only at finite positive-weight states.
Ordinary zero-weight branches are retained and can return to positive-weight
states, but this does not restore their ancestral spinal weight. A regression
checks a positive-weight endpoint below a zero-weight ancestor in the
constant-family binary tree.

The normalized total mass has expectation one. The finite marginals identify
the **complete untyped tree law** by projective-limit uniqueness. No assertion
of a global density at infinity is made. The conditional location is

$$P_{\rm spine}(w_n=z\mid H_n)=\frac{W_z(H_n)}{\sum_u W_u(H_n)},$$

and the denominator is positive and finite almost surely under the changed
law. The information here is the entire untyped finite tree, not just the
spine states. `untypedHistory` makes its comap sigma algebra explicit.

`spinePrefix` and `spineRay` read addresses using the existing
`distinguishedState` observer after mapping distinguished values to their
addresses. There is no second choice or tree construction. Their measurability
and almost-sure identification with the realized unique ray justify the
measurable joint representation `t ↦ (erase(t), spineRay(t))`.
`condLExp_treeKernel_spinePrefix` uses these actual observed addresses.
The already proved `Tree/PathLaw.lean` supplies the complete Doob state-path
law and Markov property of this same spine.

The stopped-information result follows the definitions in J. D. Biggins and
A. E. Kyprianou, *Measure change in multitype branching* (2004), §6,
pp. 556–557, [DOI 10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).
For `L ≼ M`, `A ∈ F_L`, and the existing pasted line `N`, it proves

$$B\in F_N\quad\Longleftrightarrow\quad
 B\cap A\in F_L\ \text{ and }\ B\cap A^c\in F_M.$$

This is a consequence of the definitions, not attributed as a numbered
result of that reference. Neither a branching law nor exhaustion of rays is
assumed. The regression uses a later-line event supported on the later
pasting cell. The general strong branching property at arbitrary optional
lines remains open.

## Pinned Mathlib review and direct reuse

Checked revision: `26573066084e6e2aa8526ea358bc43b66d96f970`.
The current official documentation was also inspected; the pinned source
and compiled declarations determine the APIs used here.

| Mathematical operation | Native interface used |
| --- | --- |
| Split coordinate products and keep the selected parent independent of the rest | `iIndepFun_infinitePi`, `iIndepFun.indepFun_set`, `IndepFun.map_prod_eq_prod_map_map`, `Measure.infinitePi_map_pi` |
| Reassemble the selected coordinate and its complement | `Equiv.piEquivPiSubtypeProd`, `MeasurableEquiv.piEquivPiSubtypeProd`; the proof-local notation uses their inverse, not a new coordinate constructor |
| Append one generation of the existing finite-history law | `Kernel.partialTraj_succ_of_le`, `Kernel.lintegral_map`, `Kernel.lintegral_comp`, `Kernel.lintegral_id_prod`, native `IicProdIoc` and `piSingleton` |
| Uniqueness of the complete tree law | `isProjectiveLimit_nat_iff`, `IsProjectiveLimit.unique`, with the existing list/tuple equivalence |
| Conditional spine distribution | `rnDeriv_map`, `Measure.rnDeriv_restrict_self`, `Measure.rnDeriv_withDensity`, `condLExp_congr_ae`, `withDensity_mul` |
| Read a measurable actual spine | Existing `distinguishedState` and its native countable-coordinate measurability proof; `List.ofFn_succ'`, `List.getLastD_concat` |

Official documentation:
[conditional expectations and Radon–Nikodym derivatives](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Function/ConditionalExpectation/RadonNikodym.html),
[measurable equivalences](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Embedding.html),
[projective-limit uniqueness](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Projective.html).

The removed public `Probability/Kernel/IonescuTulcea/PartialTraj.lean`
wrapper is not restored. A private proof step specializes the native
composition identities to the existing branching generation kernel.
The removed generic countable-evaluation/unique-value interfaces are not
restored either. No dependency revision is changed.

## Ownership and visibility

- `Tree/Density/Weight.lean`: public mathematical ancestral and total weights,
  their measurability, and the endpoint/root telescoping identity.
- `Tree/Density/FiniteGeneration.lean`: principal arbitrary-depth and
  complete-tree marginal results, including normalization.
- `Tree/Density/Conditional.lean`: principal conditional spine-location
  identities, for both tagged events and their actual address observation.
- `Tree/Observation.lean`: reusable state, address, and ray observations;
  these complete constructions remain outside `Lemmas/`.
- `Tree/Density/Lemmas/`: only the tagged-generation assembly and raw
  finite-history induction supporting those theorem entries. The latter is
  an implementation representation of the public whole-tree result, not a
  second public process or independent theorem family.
- `Tree/Lemmas/Generation.lean`: shared construction-specific tagged-generation
  support for the state-path and tree-density proofs; renamed from
  `Tree/Lemmas/PathLaw.lean` to reflect its actual scope, with no compatibility
  alias.
- `Process/Tree/Line/Information/Pasting.lean`: a reusable stopped-information
  theorem independent of branching models.

The tree subject has seven direct Lean files; its density subdirectory has
three public files and one `Lemmas/` directory containing two implementation
files. The general probabilistic line subject still has eight direct files;
its new information theorem is grouped under `Information/`.

## Remaining boundaries

The ancestral mass is now a native `Martingale`, derived as the empty-line
special case in `Tree/Density/Martingale.lean`; see
`OPTIONAL_LINE_MANY_TO_ONE_AUDIT.md`. The changed-measure uniform-integrability
criterion and renewal/barrier BRW instantiations remain separate obligations in `FORMALIZATION_CHECKLIST.md`. These are not
assumptions in the proved fixed-address, tree-law, or conditional-location
results. No global absolute continuity of infinite-horizon tree laws or
strong branching at arbitrary optional lines is inferred from them.
