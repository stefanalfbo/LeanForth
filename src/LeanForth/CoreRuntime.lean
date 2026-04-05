namespace LeanForth

/--
The data stack for this Forth-like interpreter.

The head of the list is the top of the stack.
-/
abbrev RuntimeStack := List Int

/-- Errors reported by the interpreter. -/
inductive RuntimeError where
  | stackUnderflow (word : String)
  | unknownWord (word : String)
  deriving Repr, DecidableEq, BEq

/-- The runtime state and dictionary entries refer to each other. -/
mutual
  /-- The current machine state. -/
  structure RuntimeState where
    stack : RuntimeStack
    dict : List (String × WordDef)
    deriving Repr

  /-- Dictionary entries supported by the runtime. -/
  inductive WordDef where
    | prim (run : RuntimeState → Except RuntimeError RuntimeState)
end

instance : BEq RuntimeState where
  beq left right := left.stack == right.stack

instance : BEq (Except RuntimeError RuntimeState) where
  beq left right :=
    match left, right with
    | .ok leftState, .ok rightState => leftState == rightState
    | .error leftErr, .error rightErr => leftErr == rightErr
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
def builtinWord (name : String) : RuntimeState → Except RuntimeError RuntimeState :=
  fun state =>
    match name, state.stack with
    | "+", a :: b :: rest => .ok { state with stack := (b + a) :: rest }
    | "-", a :: b :: rest => .ok { state with stack := (b - a) :: rest }
    | "*", a :: b :: rest => .ok { state with stack := (b * a) :: rest }
    | "dup", a :: rest => .ok { state with stack := a :: a :: rest }
    | "drop", _ :: rest => .ok { state with stack := rest }
    | "swap", a :: b :: rest => .ok { state with stack := b :: a :: rest }
    | "over", a :: b :: rest => .ok { state with stack := b :: a :: b :: rest }
    | "+", _ => .error (.stackUnderflow "+")
    | "-", _ => .error (.stackUnderflow "-")
    | "*", _ => .error (.stackUnderflow "*")
    | "dup", _ => .error (.stackUnderflow "dup")
    | "drop", _ => .error (.stackUnderflow "drop")
    | "swap", _ => .error (.stackUnderflow "swap")
    | "over", _ => .error (.stackUnderflow "over")
    | _, _ => .error (.unknownWord name)

/-- The initial dictionary of built-in words. -/
def initialDictionary : List (String × WordDef) :=
  ["+", "-", "*", "dup", "drop", "swap", "over"].map fun name =>
    (name, .prim (builtinWord name))

/-- The empty initial machine state. -/
def initialRuntimeState : RuntimeState :=
  { stack := [], dict := initialDictionary }

/-- Split source text into whitespace-separated tokens. -/
def tokenizeRuntime (source : String) : List String :=
  source.split (·.isWhitespace) |>.toList |>.map (·.toString) |>.filter fun token => !token.isEmpty

/-- Execute a single token by either pushing a literal or looking up a word. -/
def executeToken (state : RuntimeState) (token : String) : Except RuntimeError RuntimeState :=
  let trimmed := token.trimAscii.toString
  match trimmed.toInt? with
  | some n => .ok (pushValue state n)
  | none =>
      match lookupWord state.dict trimmed with
      | some (.prim run) => run state
      | none => .error (.unknownWord trimmed)

/-- Evaluate a source program token by token from left to right. -/
def evalRuntimeTokens (tokens : List String) : Except RuntimeError RuntimeState :=
  tokens.foldlM executeToken initialRuntimeState

/-- Parse and evaluate source text in one step. -/
def runRuntime (source : String) : Except RuntimeError RuntimeState :=
  evalRuntimeTokens (tokenizeRuntime source)

end LeanForth
