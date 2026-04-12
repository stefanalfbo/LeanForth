import LeanForth

def printSessionResult (session : LeanForth.RuntimeSession) : IO LeanForth.RuntimeSession := do
  if !session.state.output.isEmpty then
    IO.print session.state.output
  if !session.state.stack.isEmpty then
    IO.println s!"stack: {repr session.state.stack}"
  pure { session with state := { session.state with output := "" } }

partial def replLoop (session : LeanForth.RuntimeSession) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr "REPL> "
  stdout.flush
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  let input := line.trimAsciiEnd.toString
  if input == "#quit" then
    pure ()
  else if input.isEmpty then
    replLoop session
  else
    match LeanForth.runRuntimeFrom session input with
    | .ok nextSession =>
        let nextSession ← printSessionResult nextSession
        replLoop nextSession
    | .error err =>
        IO.eprintln s!"error: {LeanForth.formatRuntimeError err}"
        replLoop session

def runRepl : IO Unit := do
  IO.println "LeanForth REPL. Type #quit to exit."
  replLoop LeanForth.initialRuntimeSession

partial def runFiles (session : LeanForth.RuntimeSession) : List String → IO Unit
  | [] => pure ()
  | filePath :: rest => do
      let contents ← IO.FS.readFile filePath
      match LeanForth.runRuntimeFrom session contents with
      | .ok nextSession =>
          let nextSession ← printSessionResult nextSession
          runFiles nextSession rest
      | .error err => IO.eprintln s!"error in {filePath}: {LeanForth.formatRuntimeError err}"

def main (args : List String) : IO Unit := do
  match args with
  | [] => runRepl
  | _ => runFiles LeanForth.initialRuntimeSession args
