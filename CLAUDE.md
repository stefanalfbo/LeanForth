# Project

A Forth interpreter/compiler implemented in Lean 4, using Lake as the build system.

# Commands

```bash
lake build          # build the project
lake exe leanforth  # start the REPL
lake exe leanforth file.fth  # execute a Forth source file
lake exe test       # run the tests (compile-time #guard checks)
lake clean          # clean build artifacts
```

## Architecture

- `lakefile.toml` — Lake build config; defines the `LeanForth` library and `leanforth` executable
- `lean-toolchain` — pins Lean version (currently `v4.28.0`)
- `src/Main.lean` — executable entry point: REPL loop and file execution mode
- `src/LeanForth.lean` — library root; import new modules here
- `src/LeanForth/` — library source directory; add new `.lean` files here (e.g., `src/LeanForth/Interpreter.lean`)
- `src/Test.lean` — test suite; all tests are Lean `#guard` expressions

New modules go in `src/LeanForth/` and must be re-exported via `src/LeanForth.lean` to be included in the library build.

## Key Abstractions

- `RuntimeState` — the machine state: data stack, output buffer, memory cells, `here`/`latest` pointers, numeric `base`, and compile-mode flag
- `RuntimeSession` — persistent session used by the REPL: a `RuntimeDictionary` plus a `RuntimeState`; pass between calls to `runRuntimeFrom` to preserve definitions across inputs
- `WordDef` — either `.prim` (a Lean function `Nat → RuntimeState → Except RuntimeError RuntimeState`) or `.compiled` (a `List Op`)
- `Op` — the bytecode IR: `push`, `call`, `compileCall`, `emitText`, `pushString`, `evaluate`, `jump`, `jumpIfZero`
- `RuntimeDictionary` — a `List (String × DictEntry)`; looked up head-first so later definitions shadow earlier ones

## Testing

Tests live in `src/Test.lean` as `#guard` expressions evaluated at compile time. A failing assertion is a build error. Run them with `lake exe test`, which forces compilation of that file.

## Adding Built-in Words

New primitives follow the `WordDef.prim` pattern in `src/LeanForth/Runtime.lean` and must be registered in `initialDictionary`. The primitive function receives the current line number and `RuntimeState` and returns `Except RuntimeError RuntimeState`.
