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
  latest : Int := 0
  base : Nat := 10
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A token paired with its source line number. -/
structure SourceToken where
  text : String
  line : Nat
  deriving Repr, DecidableEq, BEq

/-- Errors reported by the interpreter. -/
inductive RuntimeError where
  | stackUnderflow (word : String) (line : Nat)
  | divisionByZero (word : String) (line : Nat)
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
  | jump (target : Nat)
  | jumpIfZero (target : Nat) (line : Nat)
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

/-- Result of executing a compiled operation, including early return from a word body. -/
structure ExecResult where
  state : RuntimeState
  exited : Bool := false
  deriving Inhabited, Nonempty

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
  | .divisionByZero word line => s!"line {line}: division by zero in `{word}`"
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

/-- The most recent execution token present in the dictionary. -/
def latestExecutionToken (dict : RuntimeDictionary) : Int :=
  dict.foldl (fun acc (_, entry) => max acc entry.xt) 0

/-- Add or shadow a dictionary entry. -/
def defineWord (dict : RuntimeDictionary) (name : String) (word : WordDef) (immediate := false) : RuntimeDictionary :=
  let xt := nextExecutionToken dict
  (name, { word := word, immediate := immediate, xt := xt }) :: dict

/-- Add or shadow a dictionary entry with an explicitly chosen execution token. -/
def defineWordWithXt (dict : RuntimeDictionary) (name : String) (word : WordDef) (xt : Int) (immediate := false) : RuntimeDictionary :=
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

/-- Ensure every code address below `here` is writable during compile-time backpatching. -/
def populateCellsThrough (cells : List (Int × Int)) (here : Int) : List (Int × Int) :=
  if here <= 0 then
    cells
  else
    (List.range here.toNat).foldl
      (fun acc addr =>
        let addr := Int.ofNat addr
        if (readCell acc addr).isSome then acc else writeCell acc addr 0)
      cells

/-- Read a string of character cells from consecutive addresses. -/
def readCellString (cells : List (Int × Int)) (addr : Int) (len : Nat) : String :=
  String.ofList <| (List.range len).map fun i =>
    Char.ofNat <| Int.toNat <| (readCell cells (addr + Int.ofNat i)).getD 0

/--
A dedicated address designator for the synthetic HERE cell.
This is fixed for identity comparisons and does not vary with the current `here` value.
-/
def hereAddress : Int := -314159265

/-- A dedicated address designator for the synthetic LATEST cell. -/
def latestAddress : Int := -314159266

/-- Function type for built-in primitive words. -/
abbrev BuiltinHandler := Nat → RuntimeState → Except RuntimeError RuntimeState

/-- Wrap a normal primitive result so execution continues. -/
def continueExec (state : RuntimeState) : ExecResult :=
  { state := state, exited := false }

/-- Return early from the current compiled word. -/
def exitExec (state : RuntimeState) : ExecResult :=
  { state := state, exited := true }

/-- Helper to keep built-in table entries monomorphic for Lean's elaborator. -/
def builtin (name : String) (handler : BuiltinHandler) : String × BuiltinHandler :=
  (name, handler)

/-- Replace the operation at `idx` if it exists. -/
def replaceOpAt (ops : List Op) (idx : Nat) (op : Op) : List Op :=
  match ops, idx with
  | [], _ => []
  | _ :: rest, 0 => op :: rest
  | current :: rest, idx + 1 => current :: replaceOpAt rest idx op

/-- Read the operation at `idx` if it exists. -/
def getOpAt? (ops : List Op) (idx : Nat) : Option Op :=
  match ops, idx with
  | [], _ => none
  | op :: _, 0 => some op
  | _ :: rest, idx + 1 => getOpAt? rest idx

/-- Built-in arithmetic, stack, and output words. -/
def builtinDefs : List (String × BuiltinHandler) :=
  [ builtin "+" (fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := (b + a) :: rest }
      | _ => Except.error (.stackUnderflow "+" line))
  , builtin "-" (fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := (b - a) :: rest }
      | _ => Except.error (.stackUnderflow "-" line))
  , builtin "*" (fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := (b * a) :: rest }
      | _ => Except.error (.stackUnderflow "*" line))
  , builtin "/MOD" (fun line state =>
      match state.stack with
      | 0 :: _ :: _ => Except.error (.divisionByZero "/MOD" line)
      | a :: b :: rest => Except.ok { state with stack := (b % a) :: (b / a) :: rest }
      | _ => Except.error (.stackUnderflow "/MOD" line))
  , builtin "/" (fun line state =>
      match state.stack with
      | 0 :: _ :: _ => Except.error (.divisionByZero "/" line)
      | a :: b :: rest => Except.ok { state with stack := (b / a) :: rest }
      | _ => Except.error (.stackUnderflow "/" line))
  , builtin "MOD" (fun line state =>
      match state.stack with
      | 0 :: _ :: _ => Except.error (.divisionByZero "MOD" line)
      | a :: b :: rest => Except.ok { state with stack := (b % a) :: rest }
      | _ => Except.error (.stackUnderflow "MOD" line))
  , builtin "=" (fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := (if b == a then 1 else 0) :: rest }
      | _ => Except.error (.stackUnderflow "=" line))
  , builtin "INVERT" (fun line state =>
      match state.stack with
      | a :: rest => Except.ok { state with stack := (~~~a) :: rest }
      | _ => Except.error (.stackUnderflow "INVERT" line))
  , builtin "1+" (fun line state =>
      match state.stack with
      | a :: rest => Except.ok { state with stack := (a + 1) :: rest }
      | _ => Except.error (.stackUnderflow "1+" line))
  , builtin "1-" (fun line state =>
      match state.stack with
      | a :: rest => Except.ok { state with stack := (a - 1) :: rest }
      | _ => Except.error (.stackUnderflow "1-" line))
  , builtin "dup" (fun line state =>
      match state.stack with
      | a :: rest => Except.ok { state with stack := a :: a :: rest }
      | _ => Except.error (.stackUnderflow "dup" line))
  , builtin "drop" (fun line state =>
      match state.stack with
      | _ :: rest => Except.ok { state with stack := rest }
      | _ => Except.error (.stackUnderflow "drop" line))
  , builtin "swap" (fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := b :: a :: rest }
      | _ => Except.error (.stackUnderflow "swap" line))
  , builtin "over" (fun line state =>
      match state.stack with
      | a :: b :: rest => Except.ok { state with stack := b :: a :: b :: rest }
      | _ => Except.error (.stackUnderflow "over" line))
  , builtin "." (fun line state =>
      match state.stack with
      | a :: rest => Except.ok <| appendOutput { state with stack := rest } (toString a)
      | _ => Except.error (.stackUnderflow "." line))
  , builtin "cr" (fun _ state => Except.ok <| appendOutput state "\n")
  , builtin "KEY" (fun _ state => Except.ok { state with stack := 0 :: state.stack })
  , builtin "EMIT" (fun line state =>
      match state.stack with
      | ch :: rest =>
          Except.ok <| appendOutput { state with stack := rest } (String.singleton (Char.ofNat ch.toNat))
      | _ => Except.error (.stackUnderflow "EMIT" line))
  , builtin "TELL" (fun line state =>
      match state.stack with
      | len :: addr :: rest =>
          if len < 0 then
            Except.error (.invalidAddress len line)
          else
            let text := readCellString state.cells addr len.toNat
            Except.ok <| appendOutput { state with stack := rest } text
      | _ => Except.error (.stackUnderflow "TELL" line))
  , builtin "HERE" (fun _ state => Except.ok { state with stack := hereAddress :: state.stack })
  , builtin "LATEST" (fun _ state => Except.ok { state with stack := latestAddress :: state.stack })
  , builtin "[']" (fun line _ => Except.error (.invalidPrimitiveUse "[']" line))
  , builtin "LIT" (fun line _ => Except.error (.invalidPrimitiveUse "LIT" line))
  , builtin "LITSTRING" (fun line _ => Except.error (.invalidPrimitiveUse "LITSTRING" line))
  , builtin "BRANCH" (fun line _ => Except.error (.invalidPrimitiveUse "BRANCH" line))
  , builtin "0BRANCH" (fun line _ => Except.error (.invalidPrimitiveUse "0BRANCH" line))
  , builtin "EXIT" (fun line _ => Except.error (.invalidPrimitiveUse "EXIT" line))
  , builtin ">CFA" (fun line state =>
      match state.stack with
      | xt :: rest => Except.ok { state with stack := xt :: rest }
      | _ => Except.error (.stackUnderflow ">CFA" line))
  , builtin "@" (fun line state =>
      match state.stack with
      | addr :: rest =>
          if addr == hereAddress then
            Except.ok { state with stack := state.here :: rest }
          else if addr == latestAddress then
            Except.ok { state with stack := state.latest :: rest }
          else if let some value := readCell state.cells addr then
            Except.ok { state with stack := value :: rest }
          else
            Except.error (.invalidAddress addr line)
      | _ => Except.error (.stackUnderflow "@" line))
  , builtin "!" (fun line state =>
      match state.stack with
      | addr :: value :: rest =>
          if addr == hereAddress then
            Except.ok { state with here := value, stack := rest }
          else if addr == latestAddress then
            Except.ok { state with latest := value, stack := rest }
          else if (readCell state.cells addr).isSome then
            Except.ok { state with cells := writeCell state.cells addr value, stack := rest }
          else
            Except.error (.invalidAddress addr line)
      | _ => Except.error (.stackUnderflow "!" line))
  , builtin "+!" (fun line state =>
      match state.stack with
      | addr :: delta :: rest =>
          if addr == hereAddress then
            Except.ok { state with here := state.here + delta, stack := rest }
          else if let some value := readCell state.cells addr then
            Except.ok { state with cells := writeCell state.cells addr (value + delta), stack := rest }
          else
            Except.error (.invalidAddress addr line)
      | _ => Except.error (.stackUnderflow "+!" line))
  , builtin "," (fun line state =>
      match state.stack with
      | value :: rest =>
          Except.ok { state with stack := rest, cells := writeCell state.cells state.here value, here := state.here + 1 }
      | _ => Except.error (.stackUnderflow "," line))
  , builtin "HEX" (fun _ state => Except.ok { state with base := 16 })
  , builtin "DECIMAL" (fun _ state => Except.ok { state with base := 10 })
  , builtin "TRUE" (fun _ state => Except.ok { state with stack := (-1) :: state.stack })
  , builtin "FALSE" (fun _ state => Except.ok { state with stack := 0 :: state.stack })
  , builtin "CELLS" (fun _ state => Except.ok state)  -- 1 cell = 1 unit in this implementation
  , builtin "CELL+" (fun line state =>
      match state.stack with
      | n :: rest => Except.ok { state with stack := (n + 1) :: rest }
      | _ => Except.error (.stackUnderflow "CELL+" line))
  , builtin "ALLOT" (fun line state =>
      match state.stack with
      | n :: rest => Except.ok { state with stack := rest, here := state.here + n }
      | _ => Except.error (.stackUnderflow "ALLOT" line))
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
  compileLatest : Int
  base : Nat
  immediateMode : Bool
  definingWordImmediate : Bool
  deriving Repr, DecidableEq, BEq

/-- The initial compile-time state for a colon definition. -/
def initialDefinitionCompileState (base : Nat := 10) : DefinitionCompileState :=
  { opsRev := [], compileStack := [], compileCells := [], compileHere := 0, compileLatest := 0,
    base := base, immediateMode := false, definingWordImmediate := false }

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

/-- Parse an integer in the given base (digits 0–9, a–f/A–F for base 16). -/
def parseIntInBase (base : Nat) (s : String) : Option Int :=
  let chars := s.toList
  match chars with
  | [] => none
  | _ =>
    let (neg, digits) := match chars with
      | '-' :: rest => (true, rest)
      | _ => (false, chars)
    if digits.isEmpty then none
    else
      let rec go (acc : Nat) : List Char → Option Nat
        | [] => some acc
        | ch :: rest =>
            let d : Option Nat :=
              if ch >= '0' && ch <= '9' then some (ch.toNat - '0'.toNat)
              else if base > 10 && ch >= 'a' && ch <= 'f' then some (ch.toNat - 'a'.toNat + 10)
              else if base > 10 && ch >= 'A' && ch <= 'F' then some (ch.toNat - 'A'.toNat + 10)
              else none
            match d with
            | none => none
            | some d => if d < base then go (acc * base + d) rest else none
      (go 0 digits).map fun n => if neg then -(Int.ofNat n) else Int.ofNat n

/-- Compile one source token into a runtime operation. -/
def compileToken (base : Nat) (token : SourceToken) : Op :=
  let trimmed := token.text.trimAscii.toString
  match parseIntInBase base trimmed with
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
  /-- Execute one non-branch compiled operation. -/
  partial def executeOp (dict : RuntimeDictionary) (allowExit : Bool) (state : RuntimeState) : Op → Except RuntimeError ExecResult
    | .push n => Except.ok <| continueExec (pushValue state n)
    | .emitText text => Except.ok <| continueExec (appendOutput state text)
    | .jump _ => Except.ok <| continueExec state
    | .jumpIfZero _ _ => Except.ok <| continueExec state
    | .call name line =>
        if name == "EXIT" then
          if allowExit then
            Except.ok <| exitExec state
          else
            Except.error (.invalidPrimitiveUse "EXIT" line)
        else
          match lookupWord dict name with
          | some (.prim run) => do
              let nextState ← run line state
              Except.ok <| continueExec nextState
          | some (.compiled ops) => do
              let result ← executeOps dict true state ops
              Except.ok <| continueExec result.state
          | none => Except.error (.unknownWord name line)

  /-- Execute compiled operations from left to right, honoring branch targets. -/
  partial def executeOpsAt
      (dict : RuntimeDictionary)
      (allowExit : Bool)
      (ops : List Op)
      (pc : Nat)
      (state : RuntimeState)
      : Except RuntimeError ExecResult := do
    match getOpAt? ops pc with
    | none => Except.ok <| continueExec state
    | some (.jump target) =>
        executeOpsAt dict allowExit ops target state
    | some (.jumpIfZero target line) =>
        match state.stack with
        | value :: rest =>
            if value == 0 then
              executeOpsAt dict allowExit ops target { state with stack := rest }
            else
              executeOpsAt dict allowExit ops (pc + 1) { state with stack := rest }
        | _ => Except.error (.stackUnderflow "0BRANCH" line)
    | some op => do
        let result ← executeOp dict allowExit state op
        if result.exited then
          Except.ok result
        else
          executeOpsAt dict allowExit ops (pc + 1) result.state

  /-- Execute a compiled operation list. -/
  partial def executeOps (dict : RuntimeDictionary) (allowExit : Bool) (state : RuntimeState) (ops : List Op)
      : Except RuntimeError ExecResult :=
    executeOpsAt dict allowExit ops 0 state
end

/-- Execute a token immediately while compiling a definition. -/
partial def executeImmediateToken
    (dict : RuntimeDictionary)
    (state : DefinitionCompileState)
    (token : SourceToken)
    : Except RuntimeError DefinitionCompileState := do
  let compileCells := populateCellsThrough state.compileCells state.compileHere
  let runtimeState ← executeOp dict false
    { stack := state.compileStack, output := "", cells := compileCells
      , here := state.compileHere, latest := state.compileLatest, base := state.base }
    (compileToken state.base token)
  Except.ok
    { state with
        compileStack := runtimeState.state.stack
        compileCells := runtimeState.state.cells
        compileHere := runtimeState.state.here
        compileLatest := runtimeState.state.latest
        base := runtimeState.state.base }

/-- Compile a token as a call, even if the word is immediate. -/
def compileLiteralToken (token : SourceToken) (state : DefinitionCompileState) : DefinitionCompileState :=
  { state with opsRev := compileToken state.base token :: state.opsRev, compileHere := state.compileHere + 1 }

/-- Emit one compiled operation into the current definition. -/
def emitCompiledOp (op : Op) (state : DefinitionCompileState) : DefinitionCompileState :=
  { state with opsRev := op :: state.opsRev, compileHere := state.compileHere + 1 }

/-- Patch a previously emitted control-flow operation. -/
def patchCompiledOp (idx : Int) (op : Op) (state : DefinitionCompileState) : DefinitionCompileState :=
  { state with opsRev := replaceOpAt state.opsRev.reverse idx.toNat op |>.reverse }

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
      | false, "IF", _ =>
          let nextState := emitCompiledOp (.jumpIfZero 0 token.line) state
          compileDefinitionTokens dict word startLine
            { nextState with compileStack := state.compileHere :: nextState.compileStack } rest
      | false, "THEN", _ =>
          match state.compileStack with
          | branchIdx :: remainingStack =>
              let patchedOp :=
                match getOpAt? state.opsRev.reverse branchIdx.toNat with
                | some (Op.jump _) => Op.jump state.compileHere.toNat
                | _ => Op.jumpIfZero state.compileHere.toNat token.line
              let nextState := patchCompiledOp branchIdx patchedOp { state with compileStack := remainingStack }
              compileDefinitionTokens dict word startLine nextState rest
          | [] => Except.error (.stackUnderflow "THEN" token.line)
      | false, "ELSE", _ =>
          match state.compileStack with
          | branchIdx :: remainingStack =>
              let branchTarget := state.compileHere
              let emittedState := emitCompiledOp (.jump 0) { state with compileStack := remainingStack }
              let patchedState := patchCompiledOp branchIdx (Op.jumpIfZero emittedState.compileHere.toNat token.line) emittedState
              compileDefinitionTokens dict word startLine
                { patchedState with compileStack := branchTarget :: patchedState.compileStack } rest
          | [] => Except.error (.stackUnderflow "ELSE" token.line)
      | false, "BEGIN", _ =>
          compileDefinitionTokens dict word startLine
            { state with compileStack := state.compileHere :: state.compileStack } rest
      | false, "UNTIL", _ =>
          match state.compileStack with
          | beginIdx :: remainingStack =>
              let nextState := emitCompiledOp (.jumpIfZero beginIdx.toNat token.line)
                { state with compileStack := remainingStack }
              compileDefinitionTokens dict word startLine nextState rest
          | [] => Except.error (.stackUnderflow "UNTIL" token.line)
      | false, "AGAIN", _ =>
          match state.compileStack with
          | beginIdx :: remainingStack =>
              let nextState := emitCompiledOp (.jump beginIdx.toNat) { state with compileStack := remainingStack }
              compileDefinitionTokens dict word startLine nextState rest
          | [] => Except.error (.stackUnderflow "AGAIN" token.line)
      | false, "WHILE", _ =>
          match state.compileStack with
          | beginIdx :: remainingStack =>
              let nextState := emitCompiledOp (.jumpIfZero 0 token.line)
                { state with compileStack := remainingStack }
              compileDefinitionTokens dict word startLine
                { nextState with compileStack := state.compileHere :: beginIdx :: nextState.compileStack } rest
          | [] => Except.error (.stackUnderflow "WHILE" token.line)
      | false, "REPEAT", _ =>
          match state.compileStack with
          | branchIdx :: beginIdx :: remainingStack =>
              let emittedState := emitCompiledOp (.jump beginIdx.toNat)
                { state with compileStack := remainingStack }
              let patchedState := patchCompiledOp branchIdx (Op.jumpIfZero emittedState.compileHere.toNat token.line) emittedState
              compileDefinitionTokens dict word startLine patchedState rest
          | _ => Except.error (.stackUnderflow "REPEAT" token.line)
      | false, "(", _ => do
          let remaining ← dropCommentTokens token.line rest
          compileDefinitionTokens dict word startLine state remaining
      | false, "IMMEDIATE", _ =>
          compileDefinitionTokens dict word startLine { state with definingWordImmediate := true } rest
      | false, "[COMPILE]", [] =>
          Except.error (.unknownWord "[COMPILE]" token.line)
      | false, "[COMPILE]", nextTok :: remaining =>
          compileDefinitionTokens dict word startLine (compileLiteralToken nextTok state) remaining
      | false, "[CHAR]", [] =>
          Except.error (.missingCharArgument token.line)
      | false, "[CHAR]", charTok :: remaining =>
          let charCode := Int.ofNat <| (charTok.text.toList.head?.getD default).toNat
          let nextState :=
            { state with opsRev := .push charCode :: state.opsRev, compileHere := state.compileHere + 1 }
          compileDefinitionTokens dict word startLine nextState remaining
      | false, "'", [] =>
          Except.error (.stackUnderflow "'" token.line)
      | false, "[']", [] =>
          Except.error (.stackUnderflow "[']" token.line)
      | false, "'", nextTok :: remaining => do
          let nextState ← compileExecutionToken dict nextTok state
          compileDefinitionTokens dict word startLine nextState remaining
      | false, "[']", nextTok :: remaining => do
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
      | false, "HEX", _ =>
          compileDefinitionTokens dict word startLine { state with base := 16 } rest
      | false, "DECIMAL", _ =>
          compileDefinitionTokens dict word startLine { state with base := 10 } rest
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

/-- Interpretation-phase state threaded through interpretTokens. -/
structure InterpState where
  dict : RuntimeDictionary
  base : Nat
  here : Int
  cells : List (Int × Int)
  latest : Int

/-- Interpret source tokens, updating the dictionary and compiling top-level code. -/
partial def interpretTokens
    (istate : InterpState)
    (opsRev : List Op)
    : List SourceToken → Except RuntimeError (InterpState × List Op)
  | [] => Except.ok (istate, opsRev.reverse)
  | token :: rest =>
      if token.text == "(" then do
        let remaining ← dropCommentTokens token.line rest
        interpretTokens istate opsRev remaining
      else if token.text == "HEX" then
        interpretTokens { istate with base := 16 } (.call "HEX" token.line :: opsRev) rest
      else if token.text == "DECIMAL" then
        interpretTokens { istate with base := 10 } (.call "DECIMAL" token.line :: opsRev) rest
      else if token.text == "VARIABLE" then
        match rest with
        | [] => Except.error (.invalidDefinition token.line)
        | nameTok :: remaining =>
            let addr := istate.here
            let varWord := WordDef.compiled [.push addr]
            let nextDict := defineWord istate.dict nameTok.text varWord
            let nextCells := writeCell istate.cells addr 0
            let nextIstate :=
              { istate with
                  dict := nextDict
                  here := addr + 1
                  cells := nextCells
                  latest := latestExecutionToken nextDict }
            interpretTokens nextIstate opsRev remaining
      else if token.text == "CREATE" then
        match rest with
        | [] => Except.error (.invalidDefinition token.line)
        | nameTok :: remaining =>
            let addr := istate.here
            let createWord := WordDef.compiled [.push addr]
            let nextDict := defineWord istate.dict nameTok.text createWord
            let nextIstate := { istate with dict := nextDict, latest := latestExecutionToken nextDict }
            interpretTokens nextIstate opsRev remaining
      else if token.text == "'" then
        match rest with
        | [] => Except.error (.stackUnderflow "'" token.line)
        | nextTok :: remaining => do
            let xt ← executionTokenOf istate.dict nextTok
            interpretTokens istate (.push xt :: opsRev) remaining
      else if token.text == "[CHAR]" then
        match rest with
        | [] => Except.error (.missingCharArgument token.line)
        | charTok :: remaining =>
            let charCode := Int.ofNat <| (charTok.text.toList.head?.getD default).toNat
            interpretTokens istate (.push charCode :: opsRev) remaining
      else if token.text == ":" then
        match rest with
        | [] => Except.error (.invalidDefinition token.line)
        | nameTok :: remaining => do
            let xt := nextExecutionToken istate.dict
            let (compileState, afterDef) ←
              compileDefinitionTokens istate.dict nameTok.text nameTok.line
                { (initialDefinitionCompileState istate.base) with compileLatest := xt } remaining
            let nextDict := defineWordWithXt istate.dict nameTok.text (.compiled compileState.opsRev.reverse) xt compileState.definingWordImmediate
            interpretTokens { istate with dict := nextDict, base := compileState.base, latest := xt } opsRev afterDef
      else if token.text == ".\"" then
        match rest with
        | [] => Except.error (.unterminatedString token.line)
        | textTok :: remaining =>
            interpretTokens istate (.emitText textTok.text :: opsRev) remaining
      else
        interpretTokens istate (compileToken istate.base token :: opsRev) rest

/-- Evaluate a source program token by token from left to right. -/
def evalRuntimeTokens (dict : RuntimeDictionary) (base : Nat) (tokens : List SourceToken) : Except RuntimeError RuntimeState := do
  let istate : InterpState := { dict, base, here := 0, cells := [], latest := 0 }
  let (nextIstate, ops) ← interpretTokens istate [] tokens
  let initState : RuntimeState := { stack := [], output := "", here := nextIstate.here, cells := nextIstate.cells, latest := nextIstate.latest }
  let result ← executeOps nextIstate.dict false initState ops
  return result.state

/-- Evaluate source tokens against an existing dictionary and runtime state. -/
def evalRuntimeTokensFrom (session : RuntimeSession) (tokens : List SourceToken) : Except RuntimeError RuntimeSession := do
  let istate : InterpState :=
    { dict := session.dict, base := session.state.base, here := session.state.here
      , cells := session.state.cells, latest := session.state.latest }
  let (nextIstate, ops) ← interpretTokens istate [] tokens
  let initState : RuntimeState := { session.state with here := nextIstate.here, cells := nextIstate.cells, latest := nextIstate.latest }
  let nextState ← executeOps nextIstate.dict false initState ops
  Except.ok { dict := nextIstate.dict, state := { nextState.state with base := nextIstate.base } }

/-- Parse and evaluate source text in one step. -/
def runRuntime (source : String) : Except RuntimeError RuntimeState := do
  let tokens ← tokenizeRuntime source
  evalRuntimeTokens initialDictionary 10 tokens

/-- Parse and evaluate source text against an existing interpreter session. -/
def runRuntimeFrom (session : RuntimeSession) (source : String) : Except RuntimeError RuntimeSession := do
  let tokens ← tokenizeRuntime source
  evalRuntimeTokensFrom session tokens

end LeanForth
