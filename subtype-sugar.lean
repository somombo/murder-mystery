import Lean

syntax "{" " // " term " }" : term

macro_rules
  | `({ // $e}) => do
    let e' := (← Lean.Elab.Term.expandCDot? e).getD e
    ``(Subtype $e')

----------
#check { // 1 ≤ · } -- is Subtype (1 ≤ ·)

def Nat.even (n : Nat) : Prop := n % 2 == 0
#check { // Nat.even } -- is Subtype Nat.even

example : { // 3 + · ≤ 11 }=Subtype (3 + · ≤ 11) := rfl

---------------
