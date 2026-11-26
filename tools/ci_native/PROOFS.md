`native-proof` lends a registered runner to a ready batch rather than a whole PR.
The initial policy pins #91's public `9e273ce` snapshot, source `69b331c`, and its
49,094 affected-module list. Public head `c07c1fd` adds released-main metadata;
its proof source and raw build configuration match.

The coordinator supplies `seed.json` (`snapshot`, `missing`, `input_manifest`,
`input_archive_sha256`), the sorted worklist, and a dependency ZIP. An operator
uploads them under `ci/proof-leases/<SHA>/{seed.json,worklist.txt,inputs.zip}` in
the existing public cache, then dispatches `build-pr.yml` on main with
`mode=native-proof`, `pr_number=91`, and `proof_seed_sha256=<seed SHA>`.
Donors need no cloud token or SSH access. The runner group remains restricted
to this exact main workflow and only the dedicated approved label is eligible.

The runner restores 100,302 unchanged modules from the pinned public #66 cache,
then current dependency deltas. Stock Lake checks imports with `noBuild=true`
before compiling explicit targets. Batches have at most 256 targets; small
machines are refused. Package metadata uses private overlays or private copies.

Returns retain the existing Actions provenance, lease and per-file SHA checks.
`rpc.py accept` verifies transport; the coordinator owns promotion and merging.
Lost leases are retained for operator recovery. The proxy retains prior outputs
and includes their needed closure when a later job starts in a fresh workspace.

Run unit tests with `python3 -m unittest discover -s tools/ci_native -p 'test_*.py'`.
`pilot_proofs.py` exercises real stock proof compilation and the missing-import
guard. `pilot_mathlib_sandbox.py` checks the namespace and writable package
metadata with a real Mathlib import.

The unchanged baseline expands once into a sealed, snapshot-specific state directory.
A cold expansion runs in its own network-free namespace and publishes its seal only
on success. Later leases mount that tree read-only beneath a private build overlay;
older Bubblewrap versions use private copy/reflink inodes. Failed partial expansions
remain available for inspection and are never mistaken for a completed base.
