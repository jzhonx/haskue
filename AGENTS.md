# Haskue Agent Guide

## Project overview

Haskue is a work-in-progress Haskell implementation of a useful subset of the
[CUE configuration language](https://cuelang.org/). It scans and parses CUE,
translates the AST into a value graph, evaluates that graph, and exports CUE,
JSON, or YAML.

Do not assume full CUE compatibility. In particular, package loading and
resolution, most built-ins, defaults in ellipses, first-class definitions and
hidden fields, and structural cycles are incomplete or unsupported. Preserve
these boundaries unless a task explicitly extends them.

## Architecture

The main evaluation pipeline is:

1. `src/Syntax/Scanner.hs` tokenizes source text.
2. `src/Syntax/Parser.hs` and `src/Syntax/AST.hs` produce the syntax tree.
3. `src/Semant/Semant.hs` translates syntax into the `VNode` value graph.
4. `src/Reduce/` creates constraints and performs top-down reduction.
5. `src/Reduce/Recalc.hs` resumes suspended nodes and propagates changes
   through the dependency graph.
6. Finalization and modules under `src/Value/Export/` produce user-facing
   CUE, JSON, or YAML.
7. `src/Eval.hs` orchestrates the pipeline, and `app/Main.hs` implements the
   CLI.

Important supporting areas:

- `src/Value/` contains the core value, constraint, operation, reference,
  struct, list, and disjunction representations.
- `src/DepGraph.hs` manages evaluation dependencies and reference cycles.
- `src/Reduce/TraceSpan.hs` and `src/Util/Trace.hs` support evaluator tracing.
- `tests/ScannerTest.hs` contains direct scanner unit tests.
- `tests/e2e/eval/*.txtar` contains end-to-end language behavior tests.
- `tests/e2e/explain/*.txtar` contains end-to-end explain-command tests; its
  case headers use the form `case-name __query__`.

## Evaluator invariants

CUE evaluation is order-independent. Avoid fixes that depend on source order
or on a particular traversal happening first.

- References turn the syntax tree into a directed value graph.
- Dependencies are discovered and updated dynamically during evaluation.
- A node may suspend until a dependency has been evaluated.
- Re-evaluation must propagate through affected dependents and the relevant
  ancestors, not only the node that changed.
- Node/dependency versions prevent unnecessary re-evaluation. Keep version
  bookkeeping consistent whenever a result or dependency changes.
- Reference cycles may form components in the dependency DAG, but structural
  cycles remain unsupported.

When changing reduction behavior, check both the initial top-down pass and the
recalculation path. A result that works only because a test happens to visit
nodes in one order is not correct.

## Build and run

Run commands from the repository root.

```sh
cabal build --project-file=cabal.project.debug
cabal test haskue-unit-test --project-file=cabal.project.debug
cabal run haskue --project-file=cabal.project.debug -- eval path/to/input.cue
cabal run haskue --project-file=cabal.project.debug -- export path/to/input.cue --out cue
cabal run haskue --project-file=cabal.project.debug -- export path/to/input.cue --out json
cabal run haskue --project-file=cabal.project.debug -- export path/to/input.cue --out yaml
```

For an evaluator trace:

```sh
cabal run haskue --project-file=cabal.project.debug -- export path/to/input.cue --trace --trace-output=trace.json
cabal run --project-dir=tools/show-trace haskue-show-trace -- trace.json
```

`cabal.project.debug` enables unoptimized debug/profiling settings;
`cabal.project.release` enables optimized, split-section builds. The
`build.sh` helper wraps several common debug, comparison, profiling, and
release workflows.

For development, use `cabal.project.debug` to build, run and test.

Format changed Haskell files using the repository's `fourmolu.yaml` settings:

```sh
fourmolu -i path/to/Changed.hs
```

The Cabal targets compile with `-Wall -Wpartial-fields`; leave changed code
warning-free.

## Testing changes

- Add scanner-only behavior to `tests/ScannerTest.hs`.
- Add language and evaluator regressions to the appropriate
  `tests/e2e/eval/*.txtar` file, or create a focused new one.
- A txtar case consists of an input header and body followed by an expected
  output header and body. Multiple cases may be placed in one file:

  ```text
  -- case-name.cue --
  a: 1 + 2
  -- expected.cue --
  a: 3
  ```

- `tests/E2ETest.hs` discovers every `.txtar` file under `tests/e2e/eval`
  automatically.
- Keep expected output deterministic. The harness ignores trailing whitespace
  at the end of expected output but otherwise compares output line by line.
- Run the full unit-test suite after changes to graph, reduction, value, or
  export code; these areas have broad semantic effects.

## Change guidelines

- Prefer a focused regression test that demonstrates the behavior being
  changed.
- Follow an affected feature through the whole pipeline: syntax, semantic
  translation, value representation, reduction/recalculation, finalization,
  and export.
- Preserve source locations and useful error context when adding syntax or
  semantic errors.
- Keep tracing side-effect-only: enabling trace output must not change the
  evaluated value.
- Add new library modules to `haskue.cabal` under `exposed-modules` or
  `other-modules`, as appropriate.
- Use the extensions and two-space formatting already configured by the Cabal
  file and `fourmolu.yaml` instead of introducing local style conventions.
- Update `README.md` when CLI behavior, supported features, limitations, or
  the high-level evaluation model changes.
