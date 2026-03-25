namespace LeanForth

def fileLines (contents : String) : List String :=
  contents.splitOn "\n" |>.map fun line => line.trimAsciiEnd.toString

end LeanForth
