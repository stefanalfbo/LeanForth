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

def fileLines (contents : String) : List String :=
  contents.splitOn "\n" |>.map fun line => line.trimAsciiEnd.toString

def shiftErrorLine (lineOffset : Nat) : LeanForth.RuntimeError → LeanForth.RuntimeError
  | .stackUnderflow word line => .stackUnderflow word (line + lineOffset)
  | .divisionByZero word line => .divisionByZero word (line + lineOffset)
  | .unknownWord word line => .unknownWord word (line + lineOffset)
  | .invalidPrimitiveUse word line => .invalidPrimitiveUse word (line + lineOffset)
  | .invalidDefinition line => .invalidDefinition (line + lineOffset)
  | .missingSemicolon word line => .missingSemicolon word (line + lineOffset)
  | .unterminatedString line => .unterminatedString (line + lineOffset)
  | .unterminatedComment line => .unterminatedComment (line + lineOffset)
  | .missingCharArgument line => .missingCharArgument (line + lineOffset)
  | .invalidAddress addr line => .invalidAddress addr (line + lineOffset)

def isIncompleteChunkError : LeanForth.RuntimeError → Bool
  | .missingSemicolon _ _ => true
  | .unterminatedString _ => true
  | .unterminatedComment _ => true
  | _ => false

def normalizeTopLevelLine (pending : String) (line : String) : String :=
  if pending.isEmpty then
    let trimmed := line.trimAscii.toString
    if trimmed == "TESTING" || trimmed.startsWith "TESTING " then
      "TESTING"
    else
      line
  else
    line

partial def runFileLines
    (filePath : String)
    (session : LeanForth.RuntimeSession)
    (pending : String)
    (pendingStartLine : Nat)
    (currentLine : Nat)
    : List String → IO LeanForth.RuntimeSession
  | [] =>
      if pending.isEmpty then
        pure session
      else
        match LeanForth.runRuntimeFrom session pending with
        | .ok nextSession => printSessionResult nextSession
        | .error err => do
            let shifted := shiftErrorLine pendingStartLine err
            IO.eprintln s!"error in {filePath}: {LeanForth.formatRuntimeError shifted}"
            pure session
  | line :: rest => do
      let line := normalizeTopLevelLine pending line
      let chunk :=
        if pending.isEmpty then
          line
        else
          pending ++ "\n" ++ line
      let chunkStart :=
        if pending.isEmpty then currentLine else pendingStartLine
      match LeanForth.runRuntimeFrom session chunk with
      | .ok nextSession =>
          let nextSession ← printSessionResult nextSession
          runFileLines filePath nextSession "" 0 (currentLine + 1) rest
      | .error err =>
          if isIncompleteChunkError err then
            runFileLines filePath session chunk chunkStart (currentLine + 1) rest
          else do
            let shifted := shiftErrorLine chunkStart err
            IO.eprintln s!"error in {filePath}: {LeanForth.formatRuntimeError shifted}"
            pure session

partial def runFiles (session : LeanForth.RuntimeSession) : List String → IO Unit
  | [] => pure ()
  | filePath :: rest => do
      let contents ← IO.FS.readFile filePath
      let nextSession ← runFileLines filePath session "" 0 1 (fileLines contents)
      runFiles nextSession rest

def main (args : List String) : IO Unit := do
  match args with
  | [] => runRepl
  | _ => runFiles LeanForth.initialRuntimeSession args
