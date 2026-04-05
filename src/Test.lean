import LeanForth.Eval
import LeanForth.Cli
import LeanForth.Runtime

open LeanForth

-- 3 4 + → [7]
#guard LeanForth.eval [.Push 3, .Push 4, .Add] == [7]

-- 10 3 - → [7]
#guard LeanForth.eval [.Push 10, .Push 3, .Sub] == [7]

-- 3 4 * → [12]
#guard LeanForth.eval [.Push 3, .Push 4, .Mul] == [12]

-- stack underflow leaves stack unchanged
#guard LeanForth.eval [.Add] == []

-- line splitting keeps each file line as a separate entry
#guard fileLines "1 2 +\n.\" hello\"\ndup *" == ["1 2 +", ".\" hello\"", "dup *"]

-- CRLF input is normalized for console printing
#guard fileLines "1 2 +\r\n3 4 +\r\n" == ["1 2 +", "3 4 +", ""]

-- tokenizer ignores repeated whitespace and newlines
#guard tokenizeRuntime "1  2\t+\n dup" == ["1", "2", "+", "dup"]

-- source programs are parsed and evaluated left-to-right
#guard runRuntime "3 4 +" == .ok { stack := [7] }

-- stack words operate on source text, not hand-built constructors
#guard runRuntime "2 dup *" == .ok { stack := [4] }
#guard runRuntime "1 2 swap" == .ok { stack := [1, 2] }
#guard runRuntime "1 2 over" == .ok { stack := [1, 2, 1] }

-- unknown words and underflow now surface explicit interpreter errors
#guard runRuntime "nope" == .error (.unknownWord "nope")
#guard runRuntime "+" == .error (.stackUnderflow "+")

def main : IO Unit :=
  IO.println "All tests passed!"
