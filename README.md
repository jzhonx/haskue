# Haskue ![WIP](https://img.shields.io/badge/status-WIP-yellow)

A Haskell implementation of the [CUE](https://cuelang.org/) configuration language. Work in progress—it parses,
evaluates, and exports a useful subset of CUE, with broader language support still under development.

## Purpose of the Project

CUE is a configuration language built on top of ideas such as graph unification, constraint solving, and value lattice.
Writing configuration in CUE is more elegant and less error-prone than writing configuration in YAML or
JSON. However, in some cases, it is hard to understand why CUE evaluates a value to a certain result, or why it fails to
evaluate.

Haskell, on the other hand, is also a declarative language, and has a strong type system that shares a lot of
similarities with CUE's value lattice. In addition, they also share a lot of concepts, such as fixed-point evaluation
and lazy evaluation.

This project is an attempt to implement CUE in Haskell, to explore the similarities between the two
languages, and to make CUE's evaluation process easier to understand.

## AI tool use

Haskue’s architecture and core evaluator were designed and implemented by the project author.

Coding agents have been used for scoped tasks, including renaming functions and variables, drafting comments and tests, and implementing some standard-library code. All AI-assisted changes are reviewed, tested, and maintained by the project author.

## Limitations

- Package/module system (basic import parsing exists, but loading and resolution are not)
- Standard libraries are not fully implemented.
- Built-in functions (only `close` and `slice` variants are implemented)
- Default values in ellipsis (`...<value>`)
- Definitions (`#foo`) and hidden fields (`_foo`) as first-class features
- Structural cycles are not allowed

## CLI Usage

Currently, haskue supports `eval` and `export`. The older `explain` subcommand remains as a deprecated compatibility
alias.

```
haskue --version
haskue eval   <file> [-e <expression>] [--explain]
haskue export <file> [--out cue|json|yaml] [--trace]
```

Use `-` as the input file to read CUE from standard input:

```sh
printf 'a: 1 + 2\n' | haskue eval -
printf 'a: 1 + 2\n' | haskue export - --out json
printf 'a: 1 + 2\n' | haskue eval - -e a --explain
```

Use `-e` or `--expression` to evaluate a selected reference expression instead of the entire file:

```sh
haskue eval example.cue -e x.a
```

The current expression selector supports references that start with a file-level identifier, such as `x`, `x.a`, or
`x[i]`. Support for arbitrary CUE expressions is not yet implemented.

### Explaining values

Add `--explain` to show the constraints that contribute to a selected value and where each constraint originated.
For example, given `example.cue`:

```cue
database: {
  host: string
  port: >=1 & <=65535
}
database: {
  host: "db.example.com"
  port: 5432
}
```

Run:

```sh
haskue eval example.cue -e database.port --explain
```

The output includes both the evaluated value and its contributing constraints:

```text
database.port = 5432

Conjuncts:
├─ >=1        example.cue:3:9
├─ <=65535    example.cue:3:15
└─ 5432       example.cue:7:9
```

The older equivalents, `haskue explain example.cue database.port` and
`haskue explain -e '<source-expression>' database.port`, remain available as deprecated compatibility aliases.

## How evaluation is implemented

Evaluation of CUE values is order-independent. This is different from common imperative programming languages such as Go, Java, and C++, where execution order can affect a program’s behavior. As the [CUE specification](https://cuelang.org/docs/reference/spec/#unification) puts it:

> As a consequence, order of evaluation is irrelevant, a property that is key to many of the constructs in the CUE language as well as the tooling layered on top of it.

Here is a brief overview of how evaluation is implemented in haskue.

After scanning and parsing, the CUE source is represented as an AST. The AST is then converted into a graph of nodes.
Each node of the graph represents a value, which can be a primitive value, a struct, a list, an operation, or a
reference to another node. The presence of references turns the original tree structure of the AST into a directed graph.

The evaluation of the graph is divided into two phases: the initial reduction pass and re-evaluation.

### Initial reduction pass

The initial reduction pass starts at the root and recursively descends through the value graph. At each node, Haskue
reduces its constraints and unifies their results. Nested fields, list elements, and operation operands are generally
reduced before their enclosing value is completed. As references are encountered, Haskue records their dependency
relationships. If a referenced value is not ready yet, the current node remains incomplete and is revisited during
re-evaluation.

### Re-evaluation

Re-evaluation revisits incomplete nodes and nodes whose dependencies have changed. Haskue follows the recorded
dependency relationships breadth-first, re-evaluating only nodes that observed a different version of a dependency.

When a node’s value changes, its version is incremented and the change is propagated through its enclosing values up to
the root. Reference dependents of the changed node or its changed ancestors may then be re-evaluated. If re-evaluation
produces the same value as before, the node’s version does not change, so the update does not propagate any further.

Reference cycles are grouped and re-evaluated together. This process continues until no affected dependents remain.

Consider the following CUE value:

```cue
a: {
  b: c: f: z
  d: b.c.f
  e: b.c
  z: 1
}
```

During the initial reduction pass, `f` may be encountered before `z` is ready. In that case, `f` remains incomplete
and records its dependency on `z`. Once `z` evaluates to `1`, `f` is re-evaluated. Its updated value is propagated
through `c`, `b`, and `a`, while `d` and `e` are reconsidered because they reference `f` and `c`, respectively.

The final result is the same regardless of which field is encountered first:

```cue
a: {
    b: {
        c: {
            f: 1
        }
    }
    d: 1
    e: {
        f: 1
    }
    z: 1
}
```
