# Lean formalization: Sections 2–3

Regret-Optimal Wasserstein-Robust Linear Regression

Manuscript authors: Sloan Nietert and Daniel Kuhn.

Scope: Sections 2 and 3 of the manuscript, together with their required preliminary and appendix results. Later computational and finite-sample statistical results are outside this verification snapshot. Formalization of the full paper is in progress.

The 37 scoped manuscript results have complete Lean proofs. Four supporting cited-result wrappers
are also proved. Estimator guarantees quantify over every admissible minimizer selection;
uniqueness and a fixed tie-breaking rule are not assumed.

## Reproduce

Install elan (the Lean toolchain manager), extract this project, and run these commands here:

```sh
lake exe cache get
lake build
lake env lean Check.lean
lake env lean ScopeChecks.lean
```

The first command fetches pinned dependencies and their available compilation cache. It needs
internet access and sufficient local storage. This source archive does not contain compiled caches.
The project pins Lean 4.33.0, Mathlib db584cd6d46c92f209a44c0f1c829460d327499d, and
Causalean a7085d88d2e4b30003db7097ca374f4718da0f01. See lakefile.toml and built-against.json.

Check.lean prints transitive axioms for the 37 manuscript results. ScopeChecks.lean additionally
checks the four cited-support wrappers and the proved Euclidean-norm and singular-value conventions.
Only propext, Classical.choice and Quot.sound are permitted in those axiom lists.

## Evidence and scope

The original Lean source files, toolchain and lakefile are byte-identical to the completed
1 November 2026 verification snapshot. ScopeChecks.lean is an additional audit entry point;
this README describes the public scope. The website's evidence/ directory records the original
source hashes and per-result evidence. This export has not launched a new proof run.

Two convention predicates occurring in statements are proved in Helpers/LawDefs.lean and
Helpers/MatrixDefs.lean: assPin1_valid and assSingularValueConvention_valid. Their presence does
not assume unproved mathematical facts. The report's 25 bookkeeping classifications record the
explicit Euclidean-norm convention; no theorem was reported false, conditional or unresolved.

The four included Toolkit modules are required foundations from the verified snapshot.
Optional Round B generalizations and unfinished staging files are not included.

## Files

Papers/WassersteinRegretS2S3/ contains the paper's proofs. Toolkit/ contains the four required
foundation modules. Check.lean and ScopeChecks.lean are audit entry points. Public dependencies
are fetched from the exact revisions listed in lakefile.toml. License notices accompany this export.
