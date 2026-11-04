WEBSITE COMPANION — SECTIONS 2–3

Regret-Optimal Wasserstein-Robust Linear Regression
Sloan Nietert and Daniel Kuhn

WHAT TO UPLOAD
Upload this entire folder to any static directory on your own website.
Open its index.html. Every internal link is relative, so it also works in a subdirectory.
You can test it locally by opening index.html in a browser. No server, account, API key,
PaperFormalizer installation or third-party website submission is required for visitors.

PUBLIC SCOPE
Scope: Sections 2 and 3 of the manuscript, together with their required preliminary and appendix results. Later computational and finite-sample statistical results are outside this verification snapshot. Formalization of the full paper is in progress.
The 37 scoped manuscript results and four supporting cited-result wrappers are proved.
Estimator guarantees hold for any admissible minimizer selection, without uniqueness.
No claim is made that the full paper has been formalized.

CONTENTS
index.html                 Main page and searchable result index
results/                   Original statements, Lean signatures and statement crosswalks
source/                    Complete line-anchored HTML source browser
lean/                      Downloadable standalone Lean source project
downloads/lean-project.zip  Source-only archive for visitors
verification.html          Scope, conventions and recorded checks
evidence/                  Selected result evidence and original source hashes
assets/                    Local styles, fonts and search/copy script
SHA256SUMS.txt              SHA-256 hashes of all other files in this export
NOTICE.txt and licenses/    Attribution and dependency notices

PRIVACY AND PUBLICATION
The export omits the full draft manuscript, LaTeX comments, original paper PDFs, local
paths, credentials, chat records, run logs, raw review transcripts, compiled caches,
Git metadata, optional Round B generalizations and unfinished staging files.
The result pages contain the manuscript statements needed to explain the scoped proofs.
The website uses only local assets and does not contact analytics, APIs or third-party
services. Building Lean for the first time downloads the pinned public dependencies.

REPRODUCIBILITY
Formal proof snapshot: 1 November 2026. Public export: 3 November 2026.
All original Lean source files match the completed snapshot. See evidence/source-hashes.json.
The original project is retained privately; this public folder is a separate selected copy.
No new proof run was launched to prepare the export.

Extract downloads/lean-project.zip, install elan, and run inside the project:
lake exe cache get
lake build
lake env lean Check.lean
lake env lean ScopeChecks.lean

To check this folder's files on macOS or Linux, run here:
shasum -a 256 -c SHA256SUMS.txt
