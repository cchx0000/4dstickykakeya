# Strict verification scheduling

From 2026-10-05 20:40 UTC, future staging jobs can use global compiler slots 2 and 3, with at most two single-threaded staging compilers. Immutable independent import checks use slot 1. The total compiler cap remains three. Existing queued commands keep their original slot-3 outer lock and are not rewritten.

The future pool obtains both its staging lock and matching global lock atomically before admission. It requires at least 3 GiB available memory, and every source attempt also holds a lock keyed by its exact olean output path. Different outputs may run concurrently; the same output is serialized. The original one-slot helper remains for historical commands. Every compiler uses Lean 4.33.1 with -j1, autoImplicit=false and warningAsError=true. Source snapshots, source/artifact hashes and independent declaration axiom gates remain unchanged.

The pool canary acquired slot 2 at 20:40:56 UTC with 7,945,216 KiB available memory and exited 0. This verifies admission, not an end-to-end throughput claim. Large definitional-equality elaboration remains a separate performance issue.

Two specific local coherence attempts were deliberately interrupted to replace an expensive implicit matrix-coordinate conversion with explicit lemmas. Attempt 03/session33737 ended with exit 130 at 20:38:54; attempt 04/session72294 ended with exit 130 at 20:57:17. Their snapshots and logs remain in the recovery archive. Neither is reported as passing. Their lock release was confirmed by subsequent admissions. The next repair has a finite diagnostic heartbeat budget. No full build was interrupted by this scheduling change.
