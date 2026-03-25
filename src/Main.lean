import LeanForth

def printFileLines (path : System.FilePath) : IO Unit := do
  let contents ← IO.FS.readFile path
  for line in contents.splitOn "\n" do
    IO.println line.trimAsciiEnd.toString

def main (args : List String) : IO Unit := do
  match args with
  | filePath :: _ => printFileLines filePath
  | [] => IO.println "Usage: leanforth.exe <file>"
