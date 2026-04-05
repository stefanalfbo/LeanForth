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

instance : BEq (Except RuntimeError RuntimeState) where
  beq left right :=
    match left, right with
    | .ok leftState, .ok rightState => leftState == rightState
    | .error leftErr, .error rightErr => leftErr == rightErr
    | _, _ => false

/-- The instruction set supported by the interpreter. -/
inductive RuntimeInstruction where
  | push (n : Int)
  | add
  | sub
  | mul
  | dup
  | drop
  | swap
  | over
  deriving Repr, DecidableEq

/-- The empty initial machine state. -/
def initialRuntimeState : RuntimeState :=
  { stack := [] }

/--
Execute a single instruction against the current state.
-/
def executeRuntimeInstruction
    (state : RuntimeState)
    : RuntimeInstruction → Except RuntimeError RuntimeState
  | .push n =>
      .ok { state with stack := n :: state.stack }
  | .add =>
      match state.stack with
      | a :: b :: rest => .ok { state with stack := (b + a) :: rest }
      | _ => .error (.stackUnderflow "+")
  | .sub =>
      match state.stack with
      | a :: b :: rest => .ok { state with stack := (b - a) :: rest }
      | _ => .error (.stackUnderflow "-")
  | .mul =>
      match state.stack with
      | a :: b :: rest => .ok { state with stack := (b * a) :: rest }
      | _ => .error (.stackUnderflow "*")
  | .dup =>
      match state.stack with
      | a :: rest => .ok { state with stack := a :: a :: rest }
      | _ => .error (.stackUnderflow "dup")
  | .drop =>
      match state.stack with
      | _ :: rest => .ok { state with stack := rest }
      | _ => .error (.stackUnderflow "drop")
  | .swap =>
      match state.stack with
      | a :: b :: rest => .ok { state with stack := b :: a :: rest }
      | _ => .error (.stackUnderflow "swap")
  | .over =>
      match state.stack with
      | a :: b :: rest => .ok { state with stack := b :: a :: b :: rest }
      | _ => .error (.stackUnderflow "over")

/-- Parse a single token into an instruction. -/
def parseRuntimeToken (token : String) : Except RuntimeError RuntimeInstruction :=
  match token.trimAscii.toString with
  | "+" => .ok .add
  | "-" => .ok .sub
  | "*" => .ok .mul
  | "dup" => .ok .dup
  | "drop" => .ok .drop
  | "swap" => .ok .swap
  | "over" => .ok .over
  | trimmed =>
      match trimmed.toInt? with
      | some n => .ok (.push n)
      | none => .error (.unknownWord trimmed)

/-- Split source text into whitespace-separated tokens. -/
def tokenizeRuntime (source : String) : List String :=
  source.split (·.isWhitespace) |>.toList |>.map (·.toString) |>.filter fun token => !token.isEmpty

/-- Parse source text into executable instructions. -/
def parseRuntimeProgram (source : String) : Except RuntimeError (List RuntimeInstruction) :=
  tokenizeRuntime source |>.mapM parseRuntimeToken

/--
Evaluate a full program by starting from an empty stack and applying each
instruction from left to right.
-/
def evalRuntime (instructions : List RuntimeInstruction) : Except RuntimeError RuntimeState :=
  instructions.foldlM executeRuntimeInstruction initialRuntimeState

/-- Parse and evaluate source text in one step. -/
def runRuntime (source : String) : Except RuntimeError RuntimeState := do
  let instructions ← parseRuntimeProgram source
  evalRuntime instructions

end LeanForth
