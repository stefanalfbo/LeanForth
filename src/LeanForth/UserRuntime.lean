namespace LeanForth

/--
The data stack for this Forth-like interpreter.

The head of the list is the top of the stack.
-/
abbrev RuntimeStack := List Int

/-- The current machine state. -/
structure RuntimeState where
  stack : RuntimeStack
  deriving Repr, DecidableEq, BEq

/-- Errors reported by the interpreter. -/
inductive RuntimeError where
  | stackUnderflow (word : String)
  | unknownWord (word : String)
  | invalidDefinition
  | missingSemicolon (word : String)
  deriving Repr, DecidableEq, BEq

/-- Dictionary entries supported by the runtime. -/
inductive WordDef where
  | prim (run : RuntimeState → Except RuntimeError RuntimeState)
  | user (body : List String)

/-- The active dictionary maps names to primitive or user-defined words. -/
abbrev RuntimeDictionary := List (String × WordDef)

instance : BEq (Except RuntimeError RuntimeState) where
  beq left right :=
    match left, right with
    | Except.ok leftState, Except.ok rightState => leftState == rightState
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

/-- Built-in arithmetic and stack words. -/
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
    | "+", _ => Except.error (.stackUnderflow "+")
    | "-", _ => Except.error (.stackUnderflow "-")
    | "*", _ => Except.error (.stackUnderflow "*")
    | "dup", _ => Except.error (.stackUnderflow "dup")
    | "drop", _ => Except.error (.stackUnderflow "drop")
    | "swap", _ => Except.error (.stackUnderflow "swap")
    | "over", _ => Except.error (.stackUnderflow "over")
    | _, _ => Except.error (.unknownWord name)

/-- The initial dictionary of built-in words. -/
def initialDictionary : RuntimeDictionary :=
  ["+", "-", "*", "dup", "drop", "swap", "over"].map fun name =>
    (name, WordDef.prim (builtinWord name))

/-- The empty initial machine state. -/
def initialRuntimeState : RuntimeState :=
  { stack := [] }

/-- Split source text into whitespace-separated tokens. -/
def tokenizeRuntime (source : String) : List String :=
  source.split (·.isWhitespace) |>.toList |>.map (·.toString) |>.filter fun token => !token.isEmpty

/-- Read tokens up to the next `;`, returning the body and remaining input. -/
def takeDefinitionBody (word : String) : List String → Except RuntimeError (List String × List String)
  | [] => Except.error (.missingSemicolon word)
  | ";" :: rest => Except.ok ([], rest)
  | token :: rest => do
      let (body, remaining) ← takeDefinitionBody word rest
      Except.ok (token :: body, remaining)

mutual
  /-- Execute a single token by either pushing a literal or looking up a word. -/
  partial def executeToken (dict : RuntimeDictionary) (state : RuntimeState) (token : String) : Except RuntimeError RuntimeState := do
    let trimmed := token.trimAscii.toString
    match trimmed.toInt? with
    | some n => Except.ok (pushValue state n)
    | none =>
        match lookupWord dict trimmed with
        | some (.prim run) => run state
        | some (.user body) =>
            let (_, nextState) ← interpretTokens dict state body
            Except.ok nextState
        | none => Except.error (.unknownWord trimmed)

  /-- Interpret source tokens, updating the dictionary when definitions appear. -/
  partial def interpretTokens
      (dict : RuntimeDictionary)
      (state : RuntimeState)
      : List String → Except RuntimeError (RuntimeDictionary × RuntimeState)
    | [] => Except.ok (dict, state)
    | ":" :: name :: rest => do
        let (body, remaining) ← takeDefinitionBody name rest
        let nextDict := defineWord dict name (.user body)
        interpretTokens nextDict state remaining
    | ":" :: [] => Except.error .invalidDefinition
    | token :: rest => do
        let nextState ← executeToken dict state token
        interpretTokens dict nextState rest
end

/-- Evaluate a source program token by token from left to right. -/
def evalRuntimeTokens
    (dict : RuntimeDictionary)
    (tokens : List String)
    : Except RuntimeError RuntimeState := do
  let (_, state) ← interpretTokens dict initialRuntimeState tokens
  Except.ok state

/-- Parse and evaluate source text in one step. -/
def runRuntime (source : String) : Except RuntimeError RuntimeState :=
  evalRuntimeTokens initialDictionary (tokenizeRuntime source)

end LeanForth
