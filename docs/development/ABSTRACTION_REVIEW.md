# Review proportional to mathematical risk

These levels change the investigation needed, not the standard of correctness.
The destination remains a reusable mathematical interface with natural hypotheses.

| Risk | Examples | Required review |
| --- | --- | --- |
| Local | Proof-body change; simple private algebraic estimate; helper with unchanged objects and assumptions | Search the repository and pinned Mathlib locally; check the actual API and affected callers. A concise review in the change description suffices. |
| Interface | Public lemma or corollary; outward module move; changed assumptions, domains, symmetry or quantifiers | Compare existing local/dependency statements, weakest natural hypotheses, target semantics and affected clients. Consult official current interfaces or relevant literature where local material leaves the mathematical boundary unclear. Record the chosen owner and exact APIs examined. |
| Foundational | New mathematical object/law; competing constructions; generalization across models; changed source proof strategy; a claimed necessity or source error | Review pinned implementations, official upstream interfaces and relevant primary mathematical literature. Compare candidate abstractions, hypotheses and law identities; document the decision and discrepancies. Obtain agreement for source-strategy replacement as required by CONTRIBUTING. |

Cross-module use is a review trigger, not evidence of independent mathematical
meaning. A definition should describe the object needed by other mathematics,
not just today's proof layout. Keep source-specific constants and assembly in
`Lemmas/` or private declarations. Move complete reusable constructions and
research tools to their mathematical owner. Derive special cases from the general
interface, and preserve displaced reference arguments as advisory tests.

If a supposedly local change reveals new mathematical content, escalate its
review. A small diff can alter an essential hypothesis; a large proof refactor
can preserve the interface. Investigate uncertainty rather than satisfying a
fixed quota of searches. Basic local estimates do not require a separate web
search or a new audit document solely because they will be imported elsewhere.

Use an existing subject audit for durable, consequential decisions. A new audit
file is justified by a substantive mathematical boundary, not by every lemma.
Record the pinned revision for APIs relied on and distinguish a proof limitation
from a proved necessity. No level permits duplicate public implementations,
compatibility aliases, hidden stronger hypotheses or unproved external results.
