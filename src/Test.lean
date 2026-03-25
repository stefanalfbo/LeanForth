import LeanForth.Eval
import LeanForth.Cli

open LeanForth

-- 3 4 + → [7]
#guard eval [.Push 3, .Push 4, .Add] == [7]

-- 10 3 - → [7]
#guard eval [.Push 10, .Push 3, .Sub] == [7]

-- 3 4 * → [12]
#guard eval [.Push 3, .Push 4, .Mul] == [12]

-- stack underflow leaves stack unchanged
#guard eval [.Add] == []

-- line splitting keeps each file line as a separate entry
#guard fileLines "1 2 +\n.\" hello\"\ndup *" == ["1 2 +", ".\" hello\"", "dup *"]

-- CRLF input is normalized for console printing
#guard fileLines "1 2 +\r\n3 4 +\r\n" == ["1 2 +", "3 4 +", ""]

def main : IO Unit :=
  IO.println "All tests passed!"
