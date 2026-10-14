# Retired 2026-10-14

Retired by the owner's decision (2026-10-14). Kept for history; not part of the active hostile suite
(`adversarial/hostile-submissions`).

Why: its replacement `Canon.lean` dates from the first reexec-v3-d3 reference (`935167ee`) and no
longer builds against the read-set reference (`ReadCanonDefs.lean:34: unknown identifier encP`), so a
judge would reject it at BUILD rather than at ADVERSARIAL_PROOFS as `expect.json` claims. The attack
also no longer applies: the deployed verifier uses `Read.check`, which requires an exact read-set
encoding, not `canonW`. Details: `docs/logs/v3-d3-recheck-2026-10.md`. A replacement lenient-codes
attack against the read-set reference can be derived later if wanted.
