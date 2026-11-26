# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)

A [Comparator](https://github.com/leanprover/comparator) setup and community build cache for the Lean formalization that
claims a proof of the Riemann Hypothesis, and of GRH for Dirichlet L-functions, announced on
2026-11-20 at <https://alpo.ge/remark.pdf>.

The port did not touch the statements: `src/Challenge.lean` is byte for byte the file from
before it, and `src/Statements.lean` differs only in its module header.

`git diff --stat 40e56bab HEAD -- src` shows every change so far, and the
[notes](verification/NOTES.md#source) have more detail on the cleanup. For the original, check
out `40e56bab` or use
[riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original),
which keeps the published source frozen.

This repository also adds Comparator files, cache infrastructure and CI:

| File | What it is |
|---|---|
| [`src/Challenge.lean`](src/Challenge.lean) | the five theorems, stated in a file that imports only Mathlib |
| [`comparator.json`](comparator.json) | the Comparator config |
| [`export-targets.txt`](export-targets.txt) | the declarations to export |
| [`verification/`](verification/NOTES.md) | our notes, and the results once there are some |
| [`scripts/`](scripts/) | the cache client, the tools that bootstrap and publish caches, and the CI build scripts |
| [`tools/ci_native/`](tools/ci_native/README.md) | tools that lend a registered runner to a bounded batch of a build, in place of a whole pull request |
| [`.github/workflows/`](.github/workflows/) | CI, described [below](#ci) |

## Using the build cache

Fetch and restore Mathlib and this project's compiled modules:

```bash
lake exe cache get
lake build --no-build
```

The cache settings are in `lakefile.toml`; no user configuration is needed. The first command
needs Python 3.11 or newer as `python3`. It fetches both caches anonymously and extracts the
oleans to `.lake/build`. It prefers a successful CI build matching the current clean source,
configuration, dependency manifest and toolchain; documentation-only commits can reuse the same
cache. Otherwise it tries the complete build of the Lean 4.36 port pinned in
[`scripts/cache-baselines.json`](scripts/cache-baselines.json), which fits a tree whose `src/`,
`lakefile.toml`, `lake-manifest.json` and `lean-toolchain` are the ones #66 merged. If neither
fits, the command stops after fetching Mathlib and says that no cache matches; `lake build`
then compiles the project. The second command checks the default build targets without
compiling them. Subsequent ordinary builds compile changed modules and their dependents.

The community cache includes outputs from **untrusted pull requests and volunteer machines**.
Download integrity checks do not verify proofs. Use an independent fresh build when you need
to trust the result.

The [cache notes](verification/CACHE.md) describe the archive published for the original Lean
4.33.1 source, the cheaper bootstrap that reuses its proofs, and how to produce and publish
future caches. [PORTABLE-CACHE.md](verification/PORTABLE-CACHE.md) describes how a finished
Lean 4.36 build is turned into a cache. For independent verification, follow the clean-build
instructions below.

## What is claimed

| Theorem in `Main.lean` | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | the same, written out |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | the same, for primitive characters |

## Checking it

```bash
export LEAN_ABORT_ON_PANIC=1   # as Comparator sets it: stop on an internal error, don't continue
export LAKE_ARTIFACT_CACHE=false   # rebuild the submission even if cache-env.sh was sourced earlier
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4   # Mathlib's current cache server

# 1. Export the challenge. Clean clone at $CLEAN, Lean v4.36.0.
cd "$CLEAN"
lake exe mathlib/cache get
lake build Challenge
lake env leanexport Challenge -- $(cat export-targets.txt) > challenge.export

# 2. Build the solution. Second clone, inside a sandbox with no network. Takes hours.
lake exe mathlib/cache get      # before entering the sandbox
lake build Main         # inside the sandbox

# 3. Export the solution. Still inside the sandbox; only solution.export comes out.
lake env leanexport Main -- $(cat "$CLEAN/export-targets.txt") > solution.export

# 4. Judge. Lean v4.36.0, from an empty directory, with the config from the clean clone.
lake comparator --config "$CLEAN/comparator.json" \
  --challenge-from-export "$CLEAN/challenge.export" --solution-from-export solution.export
```

What to know before running it:

- **One Lean version.** Since
  [#66](https://github.com/leanprover-community/riemann-hypothesis/pull/66) the project is
  pinned to Lean `v4.36.0`, the release that judges it, so one toolchain builds, exports and
  judges. The exporter is `leanexport`, the copy of
  [lean4export](https://github.com/leanprover/lean4export) that Lean `v4.36.0` ships; nothing
  has to be built separately.
- **The published source needs two.** Before #66 the project was pinned to Lean `v4.33.1`,
  which has neither `lake comparator` nor `leanexport`. To check commit `40e56bab`, or anything
  else from before the port, build and export with `v4.33.1` and judge with `v4.36.0`, as
  [the README at `7cce738b`](https://github.com/leanprover-community/riemann-hypothesis/blob/7cce738ba719a32964ca3822d0994f4c6952c7ae/README.md#checking-it)
  describes.
- **Challenge first.** Compiling the submission runs its code, so the challenge is exported
  where none of that code has been compiled. CI builds `Challenge` against Mathlib alone on
  every push, but does not export it. The sha256 that earlier versions of this README gave for
  `challenge.export`, `bd484ac9…`, belongs to Lean `v4.33.1` and its Mathlib; no checksum for
  the port is recorded here yet.
- **Not `lake exe cache get`.** In this repository that command also downloads prebuilt files
  for the submission itself, and `lake build Main` then compiles nothing. Steps 1 and 2 use
  `lake exe mathlib/cache get`, which fetches Mathlib only.
- **Cost.** Not measured for the port yet. The published source took hours on a large machine,
  about 100 GB of disk, and a lot of memory for step 4.

The [notes](verification/NOTES.md) have the details: where the source came from, the Lean
version and its known kernel fixes, the tools, the sandboxes, the test of these steps, and the
limits of what a passing run shows. They describe the published source on Lean `v4.33.1` and
have not been updated for the port: the dependency pins, tool versions, smoke test and checker
results in them are that setup's. No run of the steps above on the port is recorded here yet.

## CI

| Workflow | What it does |
|---|---|
| [`checks`](.github/workflows/checks.yml) | builds `Challenge` against Mathlib alone on GitHub's runners, on every push and pull request |
| [`Build PR`](.github/workflows/build-pr.yml) | builds a pull request's merge result in full on a pool of volunteer machines, automatically or on a maintainer's dispatch |
| [`Publish CI cache`](.github/workflows/publish-ci-cache.yml) | publishes the compiled modules of a finished `Build PR` run; `lake exe cache get` restores only complete, successful builds |

Full builds run on machines that volunteers lend. To lend one, see
[CI-RUNNERS.md](verification/CI-RUNNERS.md).

## License

The submission belongs to its author and was published without a license. It is mirrored here
for verification only: unmodified at commit `40e56bab`, and changed since then as the top of
this page and the [notes](verification/NOTES.md#source) describe.
