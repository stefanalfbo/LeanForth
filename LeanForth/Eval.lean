namespace LeanForth

abbrev Stack := List Int

inductive Instruction where
  | Push (n : Int)
  | Add
  | Sub
  | Mul
  deriving Repr, DecidableEq

def executeInstruction (s : Stack) : Instruction → Stack
  | .Push n => n :: s
  | .Add    => match s with | a :: b :: rest => (b + a) :: rest | _ => s
  | .Sub    => match s with | a :: b :: rest => (b - a) :: rest | _ => s
  | .Mul    => match s with | a :: b :: rest => (b * a) :: rest | _ => s

def eval (instrs : List Instruction) : Stack :=
  instrs.foldl executeInstruction []

end LeanForth
