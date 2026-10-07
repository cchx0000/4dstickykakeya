Project cache transport parts, October6 2026

The separate source/history archive is independently restorable and authoritative. These parts are only an optional acceleration cache. No credentials, dependency caches, or unfinished artifacts are included.

1. Download all files ending .part01, .part02, etc, and CACHE_PARTS_SHA256.json into one directory.
2. Verify each part byte count and SHA256 against the manifest.
3. Concatenate parts in numeric order into the exact archive filename shown in the manifest. On Linux/macOS: cat *.tar.gz.part* > restored-project-cache.tar.gz
4. Verify the reassembled archive SHA256 and byte count against the manifest BEFORE extraction.
5. Extract into a new directory. Verify every exact compiler version/binary hash, pinned dependency, source hash, olean hash and full project import closure in verified-project-cache/CACHE_MANIFEST.json before reusing anything. Do not copy artifacts over incompatible sources.
6. The independent import validation record used only the archived project outputs plus pinned official external dependency outputs; it passed with the normal project fallback removed. Cache reuse is not a new source compilation.

The whole cache archive and parts are byte-identical regardless of the temporary reassembly filename. The source archive contains full committed project history and proof receipts; pending source snapshots remain explicitly unverified.
