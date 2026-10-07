# Execution recovery after the15:10 transport failure

The source workspace remained intact. New commands initially failed with
`exec-server transport disconnected`, then recovered. At15:11 file reads
showed intact sources and later receipts; this was initially described as
continued original execution. A more precise15:17 check found all shared
slot locks free and several stale running records without terminal logs.
The terminal state of those original attempts is therefore UNKNOWN.
The earlier running interpretation is withdrawn; the historical logs remain.

Some attempts have distinct, actual terminal evidence and are not discarded:
- batch1459 ended15:05:42, six declarations, foundational axioms only
- batch1513 ended15:14:23, seven declarations, foundational axioms only

Recovery copies only individually hash-verified source-success artifacts to
an independent output directory. The baseline contains651 artifacts and has
a complete project import closure. This is hash validation and reuse, not651
new compilations or a new whole-cache import. The resumed prerequisite DAG
starts from526 certified entries and compiles only its36 remaining modules.
Original output paths and unknown logs are retained without overwrite.
The new process records must establish their own terminal results.

The new prerequisite pool uses two single-thread processes in slots1/2.
One isolated staging check may use slot3. Existing sources retain their
original compiler and dependency pins. No full build was restarted.

The last independent source/history backup before this recovery is
`libfile_4ef5d4b5bf488191bd26aef29ab843eb`, commit
`f1386923faab629ffee53490c1c247012ff3c677`.
The final original dimension-four theorem remains unfinished.
