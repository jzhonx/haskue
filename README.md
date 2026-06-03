# Haskue ![WIP](https://img.shields.io/badge/status-WIP-yellow)

A Haskell implementation of the [CUE](https://cuelang.org/) configuration language. Work in progress — parses, evaluates, and exports a useful subset of CUE, but is not yet spec-compliant.

## CLI Usage

```
haskue export <file> [--out cue|json|yaml] [--debug] [--trace]
haskue eval   <file>
haskue show-trace <trace-file>
```

```sh
haskue eval config.cue
haskue export config.cue --out json
```

## Not Yet Implemented

- Package/module system (basic import parsing exists, but loading and resolution are not)
- Standard library (only `strings.Join` is available)
- Built-in functions (only `close` and `slice` variants are implemented)
- Default values in ellipsis (`...<value>`)
- Definitions (`#foo`) and hidden fields (`_foo`) as first-class features
