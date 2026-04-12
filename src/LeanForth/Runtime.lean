namespace LeanForth

/--
The data stack for this Forth-like interpreter.

The head of the list is the top of the stack.
-/
abbrev RuntimeStack := List Int

/-- The current machine state. -/
structure RuntimeState where
  stack : RuntimeStack
  output : String
  cells : List (Int × Int) := []
  here : Int := 0
  deriving Repr, DecidableEq, BEq

/-- A token paired with its source line number. -/
structure SourceToken where
  text : String
  line : Nat
  deriving Repr, DecidableEq, BEq

/-- Errors reported by the interpreter. -/
inductive RuntimeError where
  | stackUnderflow (word : String) (line : Nat)
  | unknownWord (word : String) (line : Nat)
  | invalidPrimitiveUse (word : String) (line : Nat)
  | invalidDefinition (line : Nat)
  | missingSemicolon (word : String) (line : Nat)
  | unterminatedString (line : Nat)
  | unterminatedComment (line : Nat)
  | missingCharArgument (line : Nat)
  | invalidAddress (addr : Int) (line : Nat)
  deriving Repr, DecidableEq, BEq

/-- Compiled operations for user-defined words and top-level code. -/
inductive Op where
  | push (n : Int)
  | call (name : String) (line : Nat)
  | emitText (text : String)
  deriving Repr, DecidableEq, BEq

/-- Dictionary entries supported by the runtime. -/
inductive WordDef where
  | prim (run : Nat → RuntimeState → Except RuntimeError RuntimeState)
  | compiled (ops : List Op)

/-- A dictionary entry pairs a word definition with its immediate flag. -/
structure DictEntry where
  word : WordDef
  immediate : Bool
  xt : Int

/-- The active dictionary maps names to primitive or compiled words. -/
abbrev RuntimeDictionary := List (String × DictEntry)

/-- A persistent interpreter session used for incremental evaluation such as a REPL. -/
structure RuntimeSession where
  dict : RuntimeDictionary
  state : RuntimeState

instance : BEq (Except RuntimeError RuntimeState) where
  beq left right :=
    match left, right with
    | Except.ok leftState, Except.ok rightState => leftState == rightState
    | Except.error leftErr, Except.error rightErr => leftErr == rightErr
    | _, _ => false

instance : BEq (Except RuntimeError (List SourceToken)) where
  beq left right :=
    match left, right with
    | Except.ok leftTokens, Except.ok rightTokens => leftTokens == rightTokens
    | Except.error leftErr, Except.error rightErr => leftErr == rightErr
    | _, _ => false

/-- Render a runtime error for CLI output. -/
def formatRuntimeError : RuntimeError → String
  | .stackUnderflow word line => s!"line {line}: stack underflow in `{word}`"
  | .unknownWord word line => s!"line {line}: unknown word `{word}`"
  | .invalidPrimitiveUse word line => s!"line {line}: `{word}` is not valid in interpretation state"
  | .invalidDefinition line => s!"line {line}: invalid definition"
  | .missingSemicolon word line => s!"line {line}: missing `;` for `{word}`"
  | .unterminatedString line => s!"line {line}: unterminated string"
  | .unterminatedComment line => s!"line {line}: unterminated comment"
  | .missingCharArgument line => s!"line {line}: `CHAR` requires a following token"
  | .invalidAddress addr line => s!"line {line}: invalid address {addr}"

/-- Find a dictionary entry by word name. -/
def lookupEntry (dict : RuntimeDictionary) (name : String) : Option DictEntry :=
  match dict with
  | [] => none
  | (entryName, entry) :: rest =>
      if entryName == name then some entry else lookupEntry rest name

/-- Find a word definition in the dictionary by name. -/
def lookupWord (dict : RuntimeDictionary) (name : String) : Option WordDef :=
  (lookupEntry dict name).map DictEntry.word

/-- Add or shadow a dictionary entry. -/
def nextExecutionToken (dict : RuntimeDictionary) : Int :=
  dict.foldl (fun acc (_, entry) => max acc (entry.xt + 1)) 1

/-- Add or shadow a dictionary entry. -/
def defineWord (dict : RuntimeDictionary) (name : String) (word : WordDef) (immediate := false) : RuntimeDictionary :=
  let xt := nextExecutionToken dict
  (name, { word := word, immediate := immediate, xt := xt }) :: dict

/-- Push a value onto the stack. -/
def pushValue (state : RuntimeState) (n : Int) : RuntimeState :=
  { state with stack := n :: state.stack }

/-- Append text to the output buffer. -/
def appendOutput (state : RuntimeState) (text : String) : RuntimeState :=
  { state with output := state.output ++ text }

/-- Lookup a stored cell value by address. -/
def readCell (cells : List (Int × Int)) (addr : Int) : Option Int :=
  match cells with
  | [] => none
  | (cellAddr, value) :: rest =>
      if cellAddr == addr then some value else readCell rest addr

/-- Insert or overwrite a stored cell value by address. -/
def writeCell (cells : List (Int × Int)) (addr : Int) (value : Int) : List (Int × Int) :=
  match cells with
  | [] => [(addr, value)]
  | (cellAddr, current) :: rest =>
      if cellAddr == addr then
        (addr, value) :: rest
      else
        (cellAddr, current) :: writeCell rest addr value

/--
A dedicated address designator for the synthetic HERE cell.
This is fixed for identity comparisons and does not vary with the current `here` value.
-/
def hereAddress : Int := -314159265

/-- Function type for built-in primitive words. -/
abbrev BuiltinHandler := Nat → RuntimeState → Except RuntimeError RuntimeState

/-- Built-in arithmetic, stack, and output words. -/
def builtinDefs : List (String × BuiltinHandler) :=
  [ ("+", fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := (b + a) :: rest }
      | _ => Except.error (.stackUnderflow "+" line))
  , ("-", fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := (b - a) :: rest }
      | _ => Except.error (.stackUnderflow "-" line))
  , ("*", fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := (b * a) :: rest }
      | _ => Except.error (.stackUnderflow "*" line))
  , ("=", fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := (if b == a then 1 else 0) :: rest }
      | _ => Except.error (.stackUnderflow "=" line))
  , ("1+", fun line state =>
      match state.stack with
      | a :: rest => Except.ok { state with stack := (a + 1) :: rest }
      | _ => Except.error (.stackUnderflow "1+" line))
  , ("1-", fun line state =>
      match state.stack with
      | a :: rest => Except.ok { state with stack := (a - 1) :: rest }
      | _ => Except.error (.stackUnderflow "1-" line))
  , ("dup", fun line state =>
      match state.stack with
      | a :: rest => Except.ok { state with stack := a :: a :: rest }
      | _ => Except.error (.stackUnderflow "dup" line))
  , ("drop", fun line state =>
      match state.stack with
      | _ :: rest => Except.ok { state with stack := rest }
      | _ => Except.error (.stackUnderflow "drop" line))
  , ("swap", fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := b :: a :: rest }
      | _ => Except.error (.stackUnderflow "swap" line))
  , ("over", fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := b :: a :: b :: rest }
      | _ => Except.error (.stackUnderflow "over" line))
  , (".", fun line state =>
      match state.stack with
      | a :: rest => Except.ok <| appendOutput { state with stack := rest } (toString a)
      | _ => Except.error (.stackUnderflow "." line))
  , ("cr", fun _ state => Except.ok <| appendOutput state "\n")
  , ("KEY", fun _ state => Except.ok { state with stack := 0 :: state.stack })
  , ("EMIT", fun line state =>
      match state.stack with
      | ch :: rest =>
          Except.ok <| appendOutput { state with stack := rest } (String.singleton (Char.ofNat ch.toNat))
      | _ => Except.error (.stackUnderflow "EMIT" line))
  , ("HERE", fun _ state => Except.ok { state with stack := hereAddress :: state.stack })
  , ("LIT", fun line _ => Except.error (.invalidPrimitiveUse "LIT" line))
  , ("BRANCH", fun line _ => Except.error (.invalidPrimitiveUse "BRANCH" line))
  , ("0BRANCH", fun line _ => Except.error (.invalidPrimitiveUse "0BRANCH" line))
  , ("@", fun line state =>
      match state.stack with
      | addr :: rest =>
          if addr == hereAddress then
            Except.ok { state with stack := state.here :: rest }
          else if let some value := readCell state.cells addr then
            Except.ok { state with stack := value :: rest }
          else
            Except.error (.invalidAddress addr line)
      | _ => Except.error (.stackUnderflow "@" line))
  , ("!", fun line state =>
      match state.stack with
      | addr :: value :: rest =>
          if addr == hereAddress then
            Except.ok { state with here := value, stack := rest }
          else if (readCell state.cells addr).isSome then
            Except.ok { state with cells := writeCell state.cells addr value, stack := rest }
          else
            Except.error (.invalidAddress addr line)
      | _ => Except.error (.stackUnderflow "!" line))
  , ("+!", fun line state =>
      match state.stack with
      | addr :: delta :: rest =>
          if addr == hereAddress then
            Except.ok { state with here := state.here + delta, stack := rest }
          else if let some value := readCell state.cells addr then
            Except.ok { state with cells := writeCell state.cells addr (value + delta), stack := rest }
          else
            Except.error (.invalidAddress addr line)
      | _ => Except.error (.stackUnderflow "+!" line))
  , (",", fun line state =>
      match state.stack with
      | value :: rest =>
          Except.ok { state with stack := rest, cells := writeCell state.cells state.here value, here := state.here + 1 }
      | _ => Except.error (.stackUnderflow "," line))
  ]

/-- The initial dictionary of built-in words. -/
def initialDictionary : RuntimeDictionary :=
  let aliases :=
    builtinDefs.foldr (fun (name, handler) acc =>
      let xt := acc.foldl (fun n (_, entry) => max n (entry.xt + 1)) 1
      let upper := name.map Char.toUpper
      if upper == name then
        (name, { word := WordDef.prim handler, immediate := false, xt := xt }) :: acc
      else
        (name, { word := WordDef.prim handler, immediate := false, xt := xt }) ::
        (upper, { word := WordDef.prim handler, immediate := false, xt := xt }) ::
        acc
    ) []
  aliases

/-- The empty initial machine state. -/
def initialRuntimeState : RuntimeState :=
  { stack := [], output := "" }

/-- The initial interpreter session. -/
def initialRuntimeSession : RuntimeSession :=
  { dict := initialDictionary, state := initialRuntimeState }

/-- Compile-time state used while building a colon definition. -/
structure DefinitionCompileState where
  opsRev : List Op
  compileStack : RuntimeStack
  compileCells : List (Int × Int)
  compileHere : Int
  immediateMode : Bool
  definingWordImmediate : Bool
  deriving Repr, DecidableEq, BEq

/-- The initial compile-time state for a colon definition. -/
def initialDefinitionCompileState : DefinitionCompileState :=
  { opsRev := [], compileStack := [], compileCells := [], compileHere := 0, immediateMode := false, definingWordImmediate := false }

/-- Read a quoted string up to the next `"`, tracking line numbers. -/
partial def takeQuotedChars (line : Nat) : List Char → Except RuntimeError (List Char × List Char × Nat)
  | [] => Except.error (.unterminatedString line)
  | '"' :: rest => Except.ok ([], rest, line)
  | '\n' :: rest => do
      let (quoted, remaining, nextLine) ← takeQuotedChars (line + 1) rest
      Except.ok ('\n' :: quoted, remaining, nextLine)
  | '\r' :: '\n' :: rest => do
      let (quoted, remaining, nextLine) ← takeQuotedChars (line + 1) rest
      Except.ok ('\r' :: '\n' :: quoted, remaining, nextLine)
  | '\r' :: rest => do
      let (quoted, remaining, nextLine) ← takeQuotedChars (line + 1) rest
      Except.ok ('\r' :: quoted, remaining, nextLine)
  | ch :: rest => do
      let (quoted, remaining, nextLine) ← takeQuotedChars line rest
      Except.ok (ch :: quoted, remaining, nextLine)

/-- Skip whitespace directly after `."`, updating the line number. -/
def dropLeadingWhitespace (line : Nat) : List Char → Nat × List Char
  | '\n' :: rest => dropLeadingWhitespace (line + 1) rest
  | '\r' :: '\n' :: rest => dropLeadingWhitespace (line + 1) rest
  | '\r' :: rest => dropLeadingWhitespace (line + 1) rest
  | ch :: rest =>
      if ch.isWhitespace then
        dropLeadingWhitespace line rest
      else
        (line, ch :: rest)
  | [] => (line, [])

/-- Skip characters until the next line break for `\` comments. -/
def dropLineComment (line : Nat) : List Char → Nat × List Char
  | [] => (line, [])
  | '\n' :: rest => (line + 1, rest)
  | '\r' :: '\n' :: rest => (line + 1, rest)
  | '\r' :: rest => (line + 1, rest)
  | _ :: rest => dropLineComment line rest

/-- Turn source text into runtime tokens, preserving `." ..."` as two tokens. -/
partial def tokenizeChars
    (chars : List Char)
    (line : Nat)
    (current : List Char)
    (currentLine : Nat)
    (acc : List SourceToken)
    : Except RuntimeError (List SourceToken) := do
  let flushCurrent :=
    if current.isEmpty then
      acc
    else
      { text := String.ofList current.reverse, line := currentLine } :: acc
  match chars with
  | [] =>
      Except.ok flushCurrent.reverse
  | '.' :: '"' :: rest =>
      if current.isEmpty then
        let (quoteLine, afterWhitespace) := dropLeadingWhitespace line rest
        let (quoted, remaining, nextLine) ← takeQuotedChars quoteLine afterWhitespace
        tokenizeChars remaining nextLine [] nextLine
          ({ text := String.ofList quoted, line := quoteLine } :: { text := ".\"", line := line } :: acc)
      else
        let currentLine := if current.isEmpty then line else currentLine
        tokenizeChars ('"' :: rest) line ('.' :: current) currentLine acc
  | '\\' :: rest =>
      if current.isEmpty then
        let (nextLine, remaining) := dropLineComment line rest
        tokenizeChars remaining nextLine [] nextLine acc
      else
        let currentLine := if current.isEmpty then line else currentLine
        tokenizeChars rest line ('\\' :: current) currentLine acc
  | '\n' :: rest =>
      tokenizeChars rest (line + 1) [] (line + 1) flushCurrent
  | '\r' :: '\n' :: rest =>
      tokenizeChars rest (line + 1) [] (line + 1) flushCurrent
  | '\r' :: rest =>
      tokenizeChars rest (line + 1) [] (line + 1) flushCurrent
  | ch :: rest =>
      if ch.isWhitespace then
        tokenizeChars rest line [] line flushCurrent
      else
        let currentLine := if current.isEmpty then line else currentLine
        tokenizeChars rest line (ch :: current) currentLine acc

/-- Split source text into runtime tokens. -/
def tokenizeRuntime (source : String) : Except RuntimeError (List SourceToken) :=
  tokenizeChars source.toList 1 [] 1 []

/-- Compile one source token into a runtime operation. -/
def compileToken (token : SourceToken) : Op :=
  let trimmed := token.text.trimAscii.toString
  match trimmed.toInt? with
  | some n => .push n
  | none => .call trimmed token.line

/-- Lookup the execution token for a word already present in the dictionary. -/
def executionTokenOf (dict : RuntimeDictionary) (token : SourceToken) : Except RuntimeError Int :=
  match lookupEntry dict token.text with
  | some entry => Except.ok entry.xt
  | none => Except.error (.unknownWord token.text token.line)

/-- Skip tokenized `( ... )` comments up to and including the closing `)`. -/
def dropCommentTokens (startLine : Nat) : List SourceToken → Except RuntimeError (List SourceToken)
  | [] => Except.error (.unterminatedComment startLine)
  | token :: rest =>
      if token.text == ")" then
        Except.ok rest
      else
        dropCommentTokens startLine rest

mutual
  /-- Execute one compiled operation. -/
  partial def executeOp (dict : RuntimeDictionary) (state : RuntimeState) : Op → Except RuntimeError RuntimeState
    | .push n => Except.ok (pushValue state n)
    | .emitText text => Except.ok (appendOutput state text)
    | .call name line =>
        match lookupWord dict name with
        | some (.prim run) => run line state
        | some (.compiled ops) => executeOps dict state ops
        | none => Except.error (.unknownWord name line)

  /-- Execute compiled operations from left to right. -/
  partial def executeOps (dict : RuntimeDictionary) (state : RuntimeState) : List Op → Except RuntimeError RuntimeState
    | [] => Except.ok state
    | op :: rest => do
        let nextState ← executeOp dict state op
        executeOps dict nextState rest
end

/-- Execute a token immediately while compiling a definition. -/
partial def executeImmediateToken
    (dict : RuntimeDictionary)
    (state : DefinitionCompileState)
    (token : SourceToken)
    : Except RuntimeError DefinitionCompileState := do
  let runtimeState ← executeOp dict { stack := state.compileStack, output := "", cells := state.compileCells, here := state.compileHere } (compileToken token)
  Except.ok { state with compileStack := runtimeState.stack, compileCells := runtimeState.cells, compileHere := runtimeState.here }

/-- Compile a token as a call, even if the word is immediate. -/
def compileLiteralToken (token : SourceToken) (state : DefinitionCompileState) : DefinitionCompileState :=
  { state with opsRev := compileToken token :: state.opsRev, compileHere := state.compileHere + 1 }

/-- Compile a literal execution token for the next parsed word. -/
def compileExecutionToken (dict : RuntimeDictionary) (token : SourceToken) (state : DefinitionCompileState)
    : Except RuntimeError DefinitionCompileState := do
  let xt ← executionTokenOf dict token
  Except.ok { state with opsRev := .push xt :: state.opsRev, compileHere := state.compileHere + 1 }

/--
Compile one token inside a colon definition. The definition ends only on a
bare `;` while in compile mode, so `CHAR ;` remains legal inside `[ ... ]`.
-/
partial def compileDefinitionTokens
    (dict : RuntimeDictionary)
    (word : String)
    (startLine : Nat)
    (state : DefinitionCompileState)
    : List SourceToken → Except RuntimeError (DefinitionCompileState × List SourceToken)
  | [] => Except.error (.missingSemicolon word startLine)
  | token :: rest =>
      match state.immediateMode, token.text, rest with
      | true, "(", _ => do
          let remaining ← dropCommentTokens token.line rest
          compileDefinitionTokens dict word startLine state remaining
      | true, "]", _ =>
          compileDefinitionTokens dict word startLine { state with immediateMode := false } rest
      | true, "CHAR", [] =>
          Except.error (.missingCharArgument token.line)
      | true, "CHAR", charTok :: remaining =>
          let charCode := Int.ofNat <| (charTok.text.toList.head?.getD default).toNat
          compileDefinitionTokens dict word startLine
            { state with compileStack := charCode :: state.compileStack } remaining
      | true, ".\"", [] =>
          Except.error (.unterminatedString token.line)
      | true, ".\"", _ :: _ =>
          Except.error (.unknownWord ".\"" token.line)
      | true, _, _ => do
          let nextState ← executeImmediateToken dict state token
          compileDefinitionTokens dict word startLine nextState rest
      | false, ";", _ =>
          Except.ok (state, rest)
      | false, "(", _ => do
          let remaining ← dropCommentTokens token.line rest
          compileDefinitionTokens dict word startLine state remaining
      | false, "IMMEDIATE", _ =>
          compileDefinitionTokens dict word startLine { state with definingWordImmediate := true } rest
      | false, "[COMPILE]", [] =>
          Except.error (.unknownWord "[COMPILE]" token.line)
      | false, "[COMPILE]", nextTok :: remaining =>
          compileDefinitionTokens dict word startLine (compileLiteralToken nextTok state) remaining
      | false, "'", [] =>
          Except.error (.stackUnderflow "'" token.line)
      | false, "'", nextTok :: remaining => do
          let nextState ← compileExecutionToken dict nextTok state
          compileDefinitionTokens dict word startLine nextState remaining
      | false, "[", _ =>
          compileDefinitionTokens dict word startLine { state with immediateMode := true } rest
      | false, "LITERAL", _ =>
          match state.compileStack with
          | value :: remainingStack =>
              let nextState :=
                { state with
                    opsRev := .push value :: state.opsRev
                    compileStack := remainingStack
                    compileHere := state.compileHere + 1 }
              compileDefinitionTokens dict word startLine nextState rest
          | [] => Except.error (.stackUnderflow "LITERAL" token.line)
      | false, ".\"", [] =>
          Except.error (.unterminatedString token.line)
      | false, ".\"", textTok :: remaining =>
          compileDefinitionTokens dict word startLine
            { state with opsRev := .emitText textTok.text :: state.opsRev, compileHere := state.compileHere + 1 } remaining
      | false, _, _ =>
          match lookupEntry dict token.text with
          | some entry =>
              if entry.immediate then do
                let nextState ← executeImmediateToken dict state token
                compileDefinitionTokens dict word startLine nextState rest
              else
                compileDefinitionTokens dict word startLine (compileLiteralToken token state) rest
          | none =>
              compileDefinitionTokens dict word startLine (compileLiteralToken token state) rest

/-- Interpret source tokens, updating the dictionary and compiling top-level code. -/
partial def interpretTokens
    (dict : RuntimeDictionary)
    (opsRev : List Op)
    : List SourceToken → Except RuntimeError (RuntimeDictionary × List Op)
  | [] => Except.ok (dict, opsRev.reverse)
  | token :: rest =>
      if token.text == "(" then
        do
        let remaining ← dropCommentTokens token.line rest
        interpretTokens dict opsRev remaining
      else if token.text == "'" then
        match rest with
        | [] => Except.error (.stackUnderflow "'" token.line)
        | nextTok :: remaining => do
            let xt ← executionTokenOf dict nextTok
            interpretTokens dict (.push xt :: opsRev) remaining
      else if token.text == ":" then
        match rest with
        | [] => Except.error (.invalidDefinition token.line)
        | nameTok :: remaining => do
            let (compileState, afterDef) ←
              compileDefinitionTokens dict nameTok.text nameTok.line initialDefinitionCompileState remaining
            let nextDict := defineWord dict nameTok.text (.compiled compileState.opsRev.reverse) compileState.definingWordImmediate
            interpretTokens nextDict opsRev afterDef
      else if token.text == ".\"" then
        match rest with
        | [] => Except.error (.unterminatedString token.line)
        | textTok :: remaining =>
            interpretTokens dict (.emitText textTok.text :: opsRev) remaining
      else
        interpretTokens dict (compileToken token :: opsRev) rest

/-- Evaluate a source program token by token from left to right. -/
def evalRuntimeTokens (dict : RuntimeDictionary) (tokens : List SourceToken) : Except RuntimeError RuntimeState := do
  let (compiledDict, ops) ← interpretTokens dict [] tokens
  executeOps compiledDict initialRuntimeState ops

/-- Evaluate source tokens against an existing dictionary and runtime state. -/
def evalRuntimeTokensFrom (session : RuntimeSession) (tokens : List SourceToken) : Except RuntimeError RuntimeSession := do
  let (compiledDict, ops) ← interpretTokens session.dict [] tokens
  let nextState ← executeOps compiledDict session.state ops
  Except.ok { dict := compiledDict, state := nextState }

/-- Parse and evaluate source text in one step. -/
def runRuntime (source : String) : Except RuntimeError RuntimeState := do
  let tokens ← tokenizeRuntime source
  evalRuntimeTokens initialDictionary tokens

/-- Parse and evaluate source text against an existing interpreter session. -/
def runRuntimeFrom (session : RuntimeSession) (source : String) : Except RuntimeError RuntimeSession := do
  let tokens ← tokenizeRuntime source
  evalRuntimeTokensFrom session tokens

end LeanForth
