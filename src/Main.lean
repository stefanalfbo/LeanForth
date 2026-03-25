import LeanForth

def printFileLines (path : System.FilePath) : IO Unit := do
  let contents ← IO.FS.readFile path
  for line in LeanForth.fileLines contents do
    IO.println line

def main (args : List String) : IO Unit := do
  match args with
  | filePath :: _ => printFileLines filePath
  | [] => IO.println "Usage: leanforth.exe <file>"
