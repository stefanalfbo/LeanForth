# LeanForth

LeanForth is a small experiment in building a Forth interpreter with the help of the [Lean programming language](https://lean-lang.org/).

## Running the program

Make sure Lean and Lake are available via `elan`, then run:

```powershell
lake build
lake exe leanforth
```

`lake build` compiles the library and executables defined in `lakefile.toml`. `lake exe leanforth sample.forth` runs the main program from `Main.lean` and evaluates the file as a small Forth-like program.

## Running the tests

This repository defines a separate test executable in `Test.lean`. Run it with:

```powershell
lake exe test
```

```powershell
lake exe leanforth test/tester.fr test/core.fr
```

The test file uses `#guard` assertions to validate the evaluator. If all checks pass, the executable prints `All tests passed!`.

## Resources

* [Implementing a Forth](https://ratfactor.com/forth/implementing)
* [forth-documents](https://github.com/larsbrinkhoff/forth-documents)
* [forth2012-test-suite](https://github.com/gerryjackson/forth2012-test-suite)