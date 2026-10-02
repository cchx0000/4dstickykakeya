# Reproduce verification

This repository keeps the project's exact Lean and dependency pins. Follow the
[official Prove2Me Lean setup](https://github.com/prove2me/prove2me_workspace/blob/main/references/lean-setup.md)
and install Lean through the [official elan project](https://github.com/leanprover/elan).
An API account is not needed for the local checks below.

```sh
lake update
lake exe cache get
./scripts/check-environment.sh
./scripts/build-sequential.py
lake build
./scripts/check-axioms.sh
```

`build-sequential.py` bounds project-level concurrency by visiting local imports
in dependency order. It records passed, failed, and dependency-blocked modules in
`verification/build-logs/status.json` and continues independent modules after an
error. Logs and binary caches are not committed. You can request selected project
modules instead of the full graph:

```sh
./scripts/build-sequential.py \
  Theorems.Thm_StickyKakeya4_common_shading_obstruction
lake env lean verification/CommonShadingReadback.lean
```

`check-axioms.sh` deliberately fails when the final proof uses a nonstandard
project axiom. A successful `lake build` alone does not certify the final theorem
as unconditional. Likewise, a conditional implication with an unproved input is
not a proof of that input.

For an isolated elan installation, set `ELAN_HOME` and add `$ELAN_HOME/bin` to
`PATH` before these commands. `XDG_CACHE_HOME` can place the Mathlib download
cache outside the checkout. Do not commit toolchains, caches, or credentials.
