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
#guard tokenizeRuntime "1  2\t+\n dup" == .ok
  [{ text := "1", line := 1 }, { text := "2", line := 1 }, { text := "+", line := 1 }, { text := "dup", line := 2 }]
#guard tokenizeRuntime ".\" hello world\"" == .ok
  [{ text := ".\"", line := 1 }, { text := "hello world", line := 1 }]
#guard tokenizeRuntime "1 2 + \\ ignore this\n dup" == .ok
  [{ text := "1", line := 1 }, { text := "2", line := 1 }, { text := "+", line := 1 }, { text := "dup", line := 2 }]

-- built-in words are available through the initial dictionary
#guard lookupWord initialDictionary "+" |>.isSome
#guard lookupWord initialDictionary "dup" |>.isSome
#guard lookupWord initialDictionary "." |>.isSome
#guard lookupWord initialDictionary "cr" |>.isSome
#guard lookupWord initialDictionary "nope" |>.isNone
#guard lookupWord (defineWord initialDictionary "sq" (.compiled [.call "dup" 1, .call "*" 1])) "sq" |>.isSome

-- source programs are parsed and evaluated left-to-right
#guard runRuntime "3 4 +" == .ok { stack := [7], output := "" }
#guard runRuntime "3 4 + \\ trailing comment" == .ok { stack := [7], output := "" }

-- stack words operate on source text, not hand-built constructors
#guard runRuntime "2 dup *" == .ok { stack := [4], output := "" }
#guard runRuntime "1 2 swap" == .ok { stack := [1, 2], output := "" }
#guard runRuntime "1 2 over" == .ok { stack := [1, 2, 1], output := "" }
#guard runRuntime "1 2 \\ comment here\n over" == .ok { stack := [1, 2, 1], output := "" }

-- output words append to the output buffer and `.` pops the printed value
#guard runRuntime "7 ." == .ok { stack := [], output := "7" }
#guard runRuntime "3 4 + . cr" == .ok { stack := [], output := "7\n" }
#guard runRuntime "1 2 . ." == .ok { stack := [], output := "21" }
#guard runRuntime ".\" hello\"" == .ok { stack := [], output := "hello" }
#guard runRuntime ".\" hello world\" cr" == .ok { stack := [], output := "hello world\n" }

-- user-defined words can be introduced with `: name ... ;`
#guard runRuntime ": sq dup * ; 5 sq" == .ok { stack := [25], output := "" }
#guard runRuntime ": sq dup * ; 3 sq 4 sq +" == .ok { stack := [25], output := "" }
#guard runRuntime ": twice dup + ; 7 twice" == .ok { stack := [14], output := "" }
#guard runRuntime ": show-square dup * . ; 5 show-square" == .ok { stack := [], output := "25" }
#guard runRuntime ": greet .\" hello\" ; greet" == .ok { stack := [], output := "hello" }
#guard runRuntime ": sq dup * \\ square it\n ; 6 sq" == .ok { stack := [36], output := "" }
#guard runRuntime ": x [ 3 4 + ] LITERAL ; x" == .ok { stack := [7], output := "" }
#guard runRuntime ": semicolon [ CHAR ; ] LITERAL ; semicolon" == .ok { stack := [59], output := "" }
#guard runRuntime ": ':' [ CHAR : ] LITERAL ; ':'" == .ok { stack := [58], output := "" }

-- unknown words and underflow now surface explicit interpreter errors
#guard runRuntime "nope" == .error (.unknownWord "nope" 1)
#guard runRuntime "+" == .error (.stackUnderflow "+" 1)
#guard runRuntime "." == .error (.stackUnderflow "." 1)
#guard runRuntime ":" == .error (.invalidDefinition 1)
#guard runRuntime ": sq dup *" == .error (.missingSemicolon "sq" 1)
#guard runRuntime ".\" hello" == .error (.unterminatedString 1)
#guard runRuntime ": x [ CHAR" == .error (.missingCharArgument 1)
#guard runRuntime "1\n]" == .error (.unknownWord "]" 2)

def main : IO Unit :=
  IO.println "All tests passed!"
