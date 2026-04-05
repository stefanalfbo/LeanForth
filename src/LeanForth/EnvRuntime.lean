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
  deriving Repr, DecidableEq, BEq

/-- Primitive dictionary words operate as state transformers. -/
abbrev PrimitiveWord := RuntimeState → Except RuntimeError RuntimeState

/-- Dictionary entries supported by the runtime. -/
inductive WordDef where
  | prim (run : PrimitiveWord)

instance : BEq (Except RuntimeError RuntimeState) where
  beq left right :=
    match left, right with
    | Except.ok leftState, Except.ok rightState => leftState == rightState
    | Except.error leftErr, Except.error rightErr => leftErr == rightErr
    | _, _ => false

/-- Find a word in the dictionary by name. -/
def lookupWord (dict : List (String × WordDef)) (name : String) : Option WordDef :=
  match dict with
  | [] => none
  | (entryName, word) :: rest =>
      if entryName == name then some word else lookupWord rest name

/-- Push a value onto the stack. -/
def pushValue (state : RuntimeState) (n : Int) : RuntimeState :=
  { state with stack := n :: state.stack }

/-- Built-in arithmetic and stack words. -/
def builtinWord (name : String) : PrimitiveWord :=
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
def initialDictionary : List (String × WordDef) :=
  ["+", "-", "*", "dup", "drop", "swap", "over"].map fun name =>
    (name, WordDef.prim (builtinWord name))

/-- The empty initial machine state. -/
def initialRuntimeState : RuntimeState :=
  { stack := [] }

/-- Split source text into whitespace-separated tokens. -/
def tokenizeRuntime (source : String) : List String :=
  source.split (·.isWhitespace) |>.toList |>.map (·.toString) |>.filter fun token => !token.isEmpty

/-- Execute a single token by either pushing a literal or looking up a word. -/
def executeToken
    (dict : List (String × WordDef))
    (state : RuntimeState)
    (token : String)
    : Except RuntimeError RuntimeState :=
  let trimmed := token.trimAscii.toString
  match trimmed.toInt? with
  | some n => Except.ok (pushValue state n)
  | none =>
      match lookupWord dict trimmed with
      | some (WordDef.prim run) => run state
      | none => Except.error (.unknownWord trimmed)

/-- Evaluate a source program token by token from left to right. -/
def evalRuntimeTokens
    (dict : List (String × WordDef))
    (tokens : List String)
    : Except RuntimeError RuntimeState :=
  tokens.foldlM (executeToken dict) initialRuntimeState

/-- Parse and evaluate source text in one step. -/
def runRuntime (source : String) : Except RuntimeError RuntimeState :=
  evalRuntimeTokens initialDictionary (tokenizeRuntime source)

end LeanForth
