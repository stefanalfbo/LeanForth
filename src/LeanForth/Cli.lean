namespace LeanForth

/--
Split raw file contents into the logical lines printed by the current CLI.

The CLI splits on line-feed characters and trims trailing ASCII whitespace
from each resulting line, which also removes carriage returns from Windows
`CRLF` line endings before printing.
-/
def fileLines (contents : String) : List String :=
  contents.splitOn "\n" |>.map fun line => line.trimAsciiEnd.toString

end LeanForth
