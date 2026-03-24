namespace LeanForth

-- The data stack for this Forth-like interpreter.
-- The head of the list is the top of the stack.
abbrev Stack := List Int

-- The instruction set supported by the evaluator.
inductive Instruction where
  | Push (n : Int)
  | Add
  | Sub
  | Mul
  deriving Repr, DecidableEq

-- Execute a single instruction against the current stack.
-- Invalid arithmetic operations, such as trying to add with fewer
-- than two values on the stack, leave the stack unchanged.
def executeInstruction (s : Stack) : Instruction → Stack
  -- Pushing places the new value on top of the stack.
  | .Push n => n :: s
  -- Arithmetic pops the top value `a`, then the next value `b`,
  -- and pushes the result of `b op a`, matching stack-machine order.
  | .Add    => match s with | a :: b :: rest => (b + a) :: rest | _ => s
  | .Sub    => match s with | a :: b :: rest => (b - a) :: rest | _ => s
  | .Mul    => match s with | a :: b :: rest => (b * a) :: rest | _ => s

-- Evaluate a full program by starting from an empty stack and
-- applying each instruction from left to right.
def eval (instructions : List Instruction) : Stack :=
  instructions.foldl executeInstruction []

end LeanForth
