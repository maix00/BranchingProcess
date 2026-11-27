/-!
# Zero-axiom report regression

`True.intro` is a proof of `True` with an empty transitive axiom set. Its
native `#print axioms` output must be checked against the central registry.
-/

#print axioms True.intro
