import LeanForth.Runtime

open LeanForth

def fileLines (contents : String) : List String :=
  contents.splitOn "\n" |>.map fun line => line.trimAsciiEnd.toString

def withoutLatest (state : RuntimeState) : RuntimeState :=
  { state with latest := 0 }

def expectState (result : Except RuntimeError RuntimeState) (expected : RuntimeState) : Bool :=
  match result with
  | .ok state => withoutLatest state == expected
  | .error _ => false

-- core arithmetic works through the real runtime entrypoints
#guard runRuntime "3 4 +" == .ok { stack := [7], output := "" }
#guard runRuntime "10 3 -" == .ok { stack := [7], output := "" }
#guard runRuntime "3 4 *" == .ok { stack := [12], output := "" }
#guard runRuntime "+" == .error (.stackUnderflow "+" 1)

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
#guard tokenizeRuntime ": '\\n' 10 ;" == .ok
  [{ text := ":", line := 1 }, { text := "'\\n'", line := 1 }, { text := "10", line := 1 }, { text := ";", line := 1 }]

-- built-in words are available through the initial dictionary
#guard lookupWord initialDictionary "+" |>.isSome
#guard lookupWord initialDictionary "/" |>.isSome
#guard lookupWord initialDictionary "/MOD" |>.isSome
#guard lookupWord initialDictionary "MOD" |>.isSome
#guard lookupWord initialDictionary "dup" |>.isSome
#guard lookupWord initialDictionary "." |>.isSome
#guard lookupWord initialDictionary "cr" |>.isSome
#guard lookupWord initialDictionary "SWAP" |>.isSome
#guard lookupWord initialDictionary "DROP" |>.isSome
#guard lookupWord initialDictionary "CR" |>.isSome
#guard lookupWord initialDictionary "=" |>.isSome
#guard lookupWord initialDictionary "INVERT" |>.isSome
#guard lookupWord initialDictionary "1+" |>.isSome
#guard lookupWord initialDictionary "1-" |>.isSome
#guard lookupWord initialDictionary "KEY" |>.isSome
#guard lookupWord initialDictionary "EMIT" |>.isSome
#guard lookupWord initialDictionary "TELL" |>.isSome
#guard lookupWord initialDictionary "HERE" |>.isSome
#guard lookupWord initialDictionary "LATEST" |>.isSome
#guard lookupWord initialDictionary "[']" |>.isSome
#guard lookupWord initialDictionary "LIT" |>.isSome
#guard lookupWord initialDictionary "LITSTRING" |>.isSome
#guard lookupWord initialDictionary "BRANCH" |>.isSome
#guard lookupWord initialDictionary "0BRANCH" |>.isSome
#guard lookupWord initialDictionary "EXIT" |>.isSome
#guard lookupWord initialDictionary ">CFA" |>.isSome
#guard lookupWord initialDictionary "@" |>.isSome
#guard lookupWord initialDictionary "!" |>.isSome
#guard lookupWord initialDictionary "+!" |>.isSome
#guard lookupWord initialDictionary "," |>.isSome
#guard lookupWord initialDictionary "nope" |>.isNone
#guard lookupWord (defineWord initialDictionary "sq" (.compiled [.call "dup" 1, .call "*" 1])) "sq" |>.isSome

-- source programs are parsed and evaluated left-to-right
#guard runRuntime "20 3 /" == .ok { stack := [6], output := "" }
#guard runRuntime "20 3 MOD" == .ok { stack := [2], output := "" }
#guard runRuntime "20 3 /MOD" == .ok { stack := [2, 6], output := "" }
#guard runRuntime "1 2 SWAP" == .ok { stack := [1, 2], output := "" }
#guard runRuntime "7 DUP *" == .ok { stack := [49], output := "" }
#guard runRuntime "3 3 =" == .ok { stack := [1], output := "" }
#guard runRuntime "3 4 =" == .ok { stack := [0], output := "" }
#guard runRuntime "0 INVERT" == .ok { stack := [-1], output := "" }
#guard runRuntime "41 1+" == .ok { stack := [42], output := "" }
#guard runRuntime "41 1-" == .ok { stack := [40], output := "" }
#guard runRuntime "KEY" == .ok { stack := [0], output := "", here := 0 }
#guard runRuntime "65 EMIT" == .ok { stack := [], output := "A", here := 0 }
#guard runRuntime "65 , 66 , 0 2 TELL" == .ok { stack := [], output := "AB", cells := [(0, 65), (1, 66)], here := 2 }
#guard runRuntime "3 4 + \\ trailing comment" == .ok { stack := [7], output := "" }
#guard runRuntime "3 ( add later ) 4 +" == .ok { stack := [7], output := "" }
#guard runRuntime "3 ( add\n later ) 4 +" == .ok { stack := [7], output := "" }
#guard runRuntime "HERE @" == .ok { stack := [0], output := "", here := 0 }
#guard runRuntime "LATEST @" == .ok { stack := [0], output := "", latest := 0 }
#guard runRuntime "' DUP >CFA ' dup =" == .ok { stack := [1], output := "" }
#guard runRuntime "0 @" == .error (.invalidAddress 0 1)
#guard runRuntime "-1 @" == .error (.invalidAddress (-1) 1)
#guard runRuntime "12 HERE ! HERE @" == .ok { stack := [12], output := "", here := 12 }
#guard runRuntime "12 HERE ! 12 @" == .error (.invalidAddress 12 1)
#guard runRuntime "3 HERE +! HERE @" == .ok { stack := [3], output := "", here := 3 }
#guard runRuntime "99 ," == .ok { stack := [], output := "", cells := [(0, 99)], here := 1 }
#guard runRuntime "99 , 0 @" == .ok { stack := [99], output := "", cells := [(0, 99)], here := 1 }
#guard runRuntime "' dup ' DUP =" == .ok { stack := [1], output := "" }
#guard runRuntime "' dup ' swap =" == .ok { stack := [0], output := "" }
#guard runRuntime "[CHAR] A" == .ok { stack := [65], output := "" }
#guard match runRuntimeFrom initialRuntimeSession ": sq dup * ;" with
  | .ok session => (lookupWord session.dict "sq").isSome && withoutLatest session.state == initialRuntimeState
  | .error _ => false
#guard match runRuntimeFrom initialRuntimeSession "2" with
  | .ok session =>
      match runRuntimeFrom session "3 +" with
      | .ok nextSession => nextSession.state == { stack := [5], output := "" }
      | .error _ => false
  | .error _ => false

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
#guard expectState (runRuntime ": sq dup * ; 5 sq") { stack := [25], output := "" }
#guard expectState (runRuntime ": sq dup * ; 3 sq 4 sq +") { stack := [25], output := "" }
#guard expectState (runRuntime ": twice dup + ; 7 twice") { stack := [14], output := "" }
#guard expectState (runRuntime ": show-square dup * . ; 5 show-square") { stack := [], output := "25" }
#guard expectState (runRuntime ": greet .\" hello\" ; greet") { stack := [], output := "hello" }
#guard expectState (runRuntime ": sq dup * \\ square it\n ; 6 sq") { stack := [36], output := "" }
#guard expectState (runRuntime ": sq ( n -- n^2 ) dup * ; 6 sq") { stack := [36], output := "" }
#guard expectState (runRuntime ": x [ 3 4 + ] LITERAL ; x") { stack := [7], output := "" }
#guard expectState (runRuntime ": x [CHAR] A ; x") { stack := [65], output := "" }
#guard expectState (runRuntime ": semicolon [ CHAR ; ] LITERAL ; semicolon") { stack := [59], output := "" }
#guard expectState (runRuntime ": ':' [ CHAR : ] LITERAL ; ':'") { stack := [58], output := "" }
#guard expectState (runRuntime ": push-five IMMEDIATE 5 ; : x push-five LITERAL ; x") { stack := [5], output := "" }
#guard expectState (runRuntime ": push-six 6 ; IMMEDIATE : x push-six LITERAL ; x") { stack := [6], output := "" }
#guard expectState (runRuntime ": push-five IMMEDIATE 5 ; : y [COMPILE] push-five ; y") { stack := [5], output := "" }
#guard expectState (runRuntime ": xt-word ' dup ; xt-word ' DUP =") { stack := [1], output := "" }
#guard expectState (runRuntime ": xt-word ['] dup ; xt-word ' DUP =") { stack := [1], output := "" }
#guard expectState (runRuntime ": stop-here 1 EXIT 2 ; stop-here") { stack := [1], output := "" }
#guard expectState (runRuntime ": inner 2 EXIT 3 ; : outer 1 inner 4 ; outer") { stack := [4, 2, 1], output := "" }
#guard expectState (runRuntime ": pick IF 111 ELSE 222 THEN ; 0 pick") { stack := [222], output := "" }
#guard expectState (runRuntime ": pick IF 111 ELSE 222 THEN ; 7 pick") { stack := [111], output := "" }
#guard expectState (runRuntime ": countdown BEGIN dup WHILE 1- REPEAT ; 3 countdown") { stack := [0], output := "" }

-- unknown words and underflow now surface explicit interpreter errors
#guard runRuntime "nope" == .error (.unknownWord "nope" 1)
#guard runRuntime "LIT" == .error (.invalidPrimitiveUse "LIT" 1)
#guard runRuntime "[']" == .error (.invalidPrimitiveUse "[']" 1)
#guard runRuntime "LITSTRING" == .error (.invalidPrimitiveUse "LITSTRING" 1)
#guard runRuntime "BRANCH" == .error (.invalidPrimitiveUse "BRANCH" 1)
#guard runRuntime "0BRANCH" == .error (.invalidPrimitiveUse "0BRANCH" 1)
#guard runRuntime "EXIT" == .error (.invalidPrimitiveUse "EXIT" 1)
#guard runRuntime "+" == .error (.stackUnderflow "+" 1)
#guard runRuntime "/" == .error (.stackUnderflow "/" 1)
#guard runRuntime "=" == .error (.stackUnderflow "=" 1)
#guard runRuntime "INVERT" == .error (.stackUnderflow "INVERT" 1)
#guard runRuntime "1+" == .error (.stackUnderflow "1+" 1)
#guard runRuntime "1-" == .error (.stackUnderflow "1-" 1)
#guard runRuntime "1 0 /" == .error (.divisionByZero "/" 1)
#guard runRuntime "1 0 MOD" == .error (.divisionByZero "MOD" 1)
#guard runRuntime "1 0 /MOD" == .error (.divisionByZero "/MOD" 1)
#guard runRuntime "TELL" == .error (.stackUnderflow "TELL" 1)
#guard runRuntime "." == .error (.stackUnderflow "." 1)
#guard runRuntime ":" == .error (.invalidDefinition 1)
#guard runRuntime ": sq dup *" == .error (.missingSemicolon "sq" 1)
#guard runRuntime ".\" hello" == .error (.unterminatedString 1)
#guard runRuntime "( never closes" == .error (.unterminatedComment 1)
#guard runRuntime "5 @" == .error (.invalidAddress 5 1)
#guard runRuntime "5 12 !" == .error (.invalidAddress 12 1)
#guard runRuntime "5 12 +!" == .error (.invalidAddress 12 1)
#guard runRuntime "[CHAR]" == .error (.missingCharArgument 1)
#guard runRuntime ": x [ CHAR" == .error (.missingCharArgument 1)
#guard runRuntime "'" == .error (.stackUnderflow "'" 1)
#guard runRuntime "1\n]" == .error (.unknownWord "]" 2)

def main : IO Unit :=
  IO.println "All tests passed!"
