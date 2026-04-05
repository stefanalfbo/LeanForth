namespace LeanForth

/--
The data stack for this Forth-like interpreter.

The head of the list is the top of the stack.
-/
abbrev RuntimeStack := List Int

/-- Backward-compatible alias for the old evaluator API. -/
abbrev Stack := RuntimeStack

/-- A small instruction language for low-level tests and direct execution. -/
inductive Instruction where
  | Push (n : Int)
  | Add
  | Sub
  | Mul
  deriving Repr, DecidableEq

/-- The current machine state. -/
structure RuntimeState where
  stack : RuntimeStack
  output : String
  deriving Repr, DecidableEq, BEq

/-- Errors reported by the interpreter. -/
inductive RuntimeError where
  | stackUnderflow (word : String)
  | unknownWord (word : String)
  | invalidDefinition
  | missingSemicolon (word : String)
  | unterminatedString
  deriving Repr, DecidableEq, BEq

/-- Compiled operations for user-defined words and top-level code. -/
inductive Op where
  | push (n : Int)
  | call (name : String)
  | emitText (text : String)
  deriving Repr, DecidableEq, BEq

/-- Dictionary entries supported by the runtime. -/
inductive WordDef where
  | prim (run : RuntimeState → Except RuntimeError RuntimeState)
  | compiled (ops : List Op)

/-- The active dictionary maps names to primitive or compiled words. -/
abbrev RuntimeDictionary := List (String × WordDef)

instance : BEq (Except RuntimeError RuntimeState) where
  beq left right :=
    match left, right with
    | Except.ok leftState, Except.ok rightState => leftState == rightState
    | Except.error leftErr, Except.error rightErr => leftErr == rightErr
    | _, _ => false

instance : BEq (Except RuntimeError (List String)) where
  beq left right :=
    match left, right with
    | Except.ok leftTokens, Except.ok rightTokens => leftTokens == rightTokens
    | Except.error leftErr, Except.error rightErr => leftErr == rightErr
    | _, _ => false

/-- Find a word in the dictionary by name. -/
def lookupWord (dict : RuntimeDictionary) (name : String) : Option WordDef :=
  match dict with
  | [] => none
  | (entryName, word) :: rest =>
      if entryName == name then some word else lookupWord rest name

/-- Add or shadow a dictionary entry. -/
def defineWord (dict : RuntimeDictionary) (name : String) (word : WordDef) : RuntimeDictionary :=
  (name, word) :: dict

/-- Push a value onto the stack. -/
def pushValue (state : RuntimeState) (n : Int) : RuntimeState :=
  { state with stack := n :: state.stack }

/-- Append text to the output buffer. -/
def appendOutput (state : RuntimeState) (text : String) : RuntimeState :=
  { state with output := state.output ++ text }

/-- Execute one low-level instruction against a stack. -/
def executeInstruction (stack : Stack) : Instruction → Stack
  | .Push n => n :: stack
  | .Add =>
      match stack with
      | a :: b :: rest => (b + a) :: rest
      | _ => stack
  | .Sub =>
      match stack with
      | a :: b :: rest => (b - a) :: rest
      | _ => stack
  | .Mul =>
      match stack with
      | a :: b :: rest => (b * a) :: rest
      | _ => stack

/-- Evaluate a low-level instruction sequence from an empty stack. -/
def eval (instructions : List Instruction) : Stack :=
  instructions.foldl executeInstruction []

/-- Built-in arithmetic, stack, and output words. -/
def builtinWord (name : String) : RuntimeState → Except RuntimeError RuntimeState :=
  fun state =>
    match name, state.stack with
    | "+", a :: b :: rest => Except.ok { state with stack := (b + a) :: rest }
    | "-", a :: b :: rest => Except.ok { state with stack := (b - a) :: rest }
    | "*", a :: b :: rest => Except.ok { state with stack := (b * a) :: rest }
    | "dup", a :: rest => Except.ok { state with stack := a :: a :: rest }
    | "drop", _ :: rest => Except.ok { state with stack := rest }
    | "swap", a :: b :: rest => Except.ok { state with stack := b :: a :: rest }
    | "over", a :: b :: rest => Except.ok { state with stack := b :: a :: b :: rest }
    | ".", a :: rest => Except.ok <| appendOutput { state with stack := rest } (toString a)
    | "cr", _ => Except.ok <| appendOutput state "\n"
    | "+", _ => Except.error (.stackUnderflow "+")
    | "-", _ => Except.error (.stackUnderflow "-")
    | "*", _ => Except.error (.stackUnderflow "*")
    | "dup", _ => Except.error (.stackUnderflow "dup")
    | "drop", _ => Except.error (.stackUnderflow "drop")
    | "swap", _ => Except.error (.stackUnderflow "swap")
    | "over", _ => Except.error (.stackUnderflow "over")
    | ".", _ => Except.error (.stackUnderflow ".")
    | _, _ => Except.error (.unknownWord name)

/-- The initial dictionary of built-in words. -/
def initialDictionary : RuntimeDictionary :=
  ["+", "-", "*", "dup", "drop", "swap", "over", ".", "cr"].map fun name =>
    (name, WordDef.prim (builtinWord name))

/-- The empty initial machine state. -/
def initialRuntimeState : RuntimeState :=
  { stack := [], output := "" }

/-- Read a quoted string up to the next `"`. -/
partial def takeQuotedChars : List Char → Except RuntimeError (List Char × List Char)
  | [] => Except.error .unterminatedString
  | '"' :: rest => Except.ok ([], rest)
  | ch :: rest => do
      let (quoted, remaining) ← takeQuotedChars rest
      Except.ok (ch :: quoted, remaining)

/-- Skip whitespace directly after `."`. -/
def dropLeadingWhitespace : List Char → List Char
  | ch :: rest =>
      if ch.isWhitespace then
        dropLeadingWhitespace rest
      else
        ch :: rest
  | [] => []

/-- Skip characters until the next line break for `\` comments. -/
def dropLineComment : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | '\r' :: '\n' :: rest => rest
  | '\r' :: rest => rest
  | _ :: rest => dropLineComment rest

/-- Turn source text into runtime tokens, preserving `." ..."` as two tokens. -/
partial def tokenizeChars (chars : List Char) (current : List Char) (acc : List String) :
    Except RuntimeError (List String) := do
  match chars with
  | [] =>
      let acc := if current.isEmpty then acc else String.ofList current :: acc
      Except.ok acc.reverse
  | '.' :: '"' :: rest =>
      let acc := if current.isEmpty then acc else String.ofList current :: acc
      let (quoted, remaining) ← takeQuotedChars (dropLeadingWhitespace rest)
      tokenizeChars remaining [] (String.ofList quoted :: ".\"" :: acc)
  | '\\' :: rest =>
      let acc := if current.isEmpty then acc else String.ofList current :: acc
      tokenizeChars (dropLineComment rest) [] acc
  | ch :: rest =>
      if ch.isWhitespace then
        let acc := if current.isEmpty then acc else String.ofList current :: acc
        tokenizeChars rest [] acc
      else
        tokenizeChars rest (current ++ [ch]) acc

/-- Split source text into runtime tokens. -/
def tokenizeRuntime (source : String) : Except RuntimeError (List String) :=
  tokenizeChars source.toList [] []

/-- Read tokens up to the next `;`, returning the body and remaining input. -/
def takeDefinitionBody (word : String) : List String → Except RuntimeError (List String × List String)
  | [] => Except.error (.missingSemicolon word)
  | ";" :: rest => Except.ok ([], rest)
  | token :: rest => do
      let (body, remaining) ← takeDefinitionBody word rest
      Except.ok (token :: body, remaining)

/-- Compile one source token into a runtime operation. -/
def compileToken (token : String) : Op :=
  let trimmed := token.trimAscii.toString
  match trimmed.toInt? with
  | some n => .push n
  | none => .call trimmed

/-- Compile a token list into runtime operations. -/
def compileTokens : List String → List Op
  | [] => []
  | ".\"" :: text :: rest => .emitText text :: compileTokens rest
  | ".\"" :: [] => [.call ".\""]
  | token :: rest => compileToken token :: compileTokens rest

mutual
  /-- Execute one compiled operation. -/
  partial def executeOp (dict : RuntimeDictionary) (state : RuntimeState) : Op → Except RuntimeError RuntimeState
    | .push n => Except.ok (pushValue state n)
    | .emitText text => Except.ok (appendOutput state text)
    | .call name =>
        match lookupWord dict name with
        | some (.prim run) => run state
        | some (.compiled ops) => executeOps dict state ops
        | none => Except.error (.unknownWord name)

  /-- Execute compiled operations from left to right. -/
  partial def executeOps (dict : RuntimeDictionary) (state : RuntimeState) : List Op → Except RuntimeError RuntimeState
    | [] => Except.ok state
    | op :: rest => do
        let nextState ← executeOp dict state op
        executeOps dict nextState rest

  /-- Interpret source tokens, updating the dictionary and compiling top-level code. -/
  partial def interpretTokens
      (dict : RuntimeDictionary)
      (opsRev : List Op)
      : List String → Except RuntimeError (RuntimeDictionary × List Op)
    | [] => Except.ok (dict, opsRev.reverse)
    | ":" :: name :: rest => do
        let (body, remaining) ← takeDefinitionBody name rest
        let nextDict := defineWord dict name (.compiled (compileTokens body))
        interpretTokens nextDict opsRev remaining
    | ":" :: [] => Except.error .invalidDefinition
    | ".\"" :: text :: rest =>
        interpretTokens dict (.emitText text :: opsRev) rest
    | ".\"" :: [] => Except.error .unterminatedString
    | token :: rest =>
        interpretTokens dict (compileToken token :: opsRev) rest
end

/-- Evaluate a source program token by token from left to right. -/
def evalRuntimeTokens (dict : RuntimeDictionary) (tokens : List String) : Except RuntimeError RuntimeState := do
  let (compiledDict, ops) ← interpretTokens dict [] tokens
  executeOps compiledDict initialRuntimeState ops

/-- Parse and evaluate source text in one step. -/
def runRuntime (source : String) : Except RuntimeError RuntimeState := do
  let tokens ← tokenizeRuntime source
  evalRuntimeTokens initialDictionary tokens

end LeanForth
