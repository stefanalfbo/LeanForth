import LeanForth.Eval

open LeanForth

-- 3 4 + → [7]
#guard eval [.Push 3, .Push 4, .Add] == [7]

-- 10 3 - → [7]
#guard eval [.Push 10, .Push 3, .Sub] == [7]

-- 3 4 * → [12]
#guard eval [.Push 3, .Push 4, .Mul] == [12]

-- stack underflow leaves stack unchanged
#guard eval [.Add] == []

def main : IO Unit :=
  IO.println "All tests passed!"
