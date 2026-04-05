import LeanForth

def printResult (path : System.FilePath) : IO Unit := do
  let contents ← IO.FS.readFile path
  match LeanForth.runRuntime contents with
  | .ok state =>
      if !state.output.isEmpty then
        IO.print state.output
      if !state.stack.isEmpty then
        IO.println s!"stack: {repr state.stack}"
  | .error err => IO.eprintln s!"error: {repr err}"

def main (args : List String) : IO Unit := do
  match args with
  | filePath :: _ => printResult filePath
  | [] => IO.println "Usage: leanforth.exe <file>"
