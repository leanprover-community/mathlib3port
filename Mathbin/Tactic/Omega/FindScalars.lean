import Mathbin.Tactic.Omega.Term 
import Mathbin.Data.List.MinMax

open List.Func

namespace Omega

/-- Divide linear combinations into three groups by the coefficient of the
    `m`th variable in their resultant terms: negative, zero, or positive. -/
unsafe def trisect (m : Nat) :
  List (List Nat × term) → List (List Nat × term) × List (List Nat × term) × List (List Nat × term)
| [] => ([], [], [])
| (p, t) :: pts =>
  let (neg, zero, Pos) := trisect pts 
  if get m t.snd < 0 then ((p, t) :: neg, zero, Pos) else
    if get m t.snd = 0 then (neg, (p, t) :: zero, Pos) else (neg, zero, (p, t) :: Pos)

/-- Use two linear combinations to obtain a third linear combination
    whose resultant term does not include the `m`th variable. -/
unsafe def elim_var_aux (m : Nat) : (List Nat × term) × List Nat × term → tactic (List Nat × term)
| ((p1, t1), (p2, t2)) =>
  let n := Int.natAbs (get m t1.snd)
  let o := Int.natAbs (get m t2.snd)
  let lcm := Nat.lcmₓ n o 
  let n' := lcm / n 
  let o' := lcm / o 
  return (add (p1.map ((·*·) n')) (p2.map ((·*·) o')), term.add (t1.mul n') (t2.mul o'))

/-- Use two lists of linear combinations (one in which the resultant terms
    include occurrences of the `m`th variable with positive coefficients,
    and one with negative coefficients) and linearly combine them in every
    possible way that eliminates the `m`th variable. -/
unsafe def elim_var (m : Nat) (neg pos : List (List Nat × term)) : tactic (List (List Nat × term)) :=
  let pairs := List.product neg Pos 
  Monadₓ.mapm (elim_var_aux m) pairs

/-- Search through a list of (linear combination × resultant term) pairs,
    find the first pair whose resultant term has a negative constant term,
    and return its linear combination -/
unsafe def find_neg_const : List (List Nat × term) → tactic (List Nat)
| [] => tactic.failed
| (π, ⟨c, _⟩) :: l => if c < 0 then return π else find_neg_const l

/-- First, eliminate all variables by Fourier–Motzkin elimination.
    When all variables have been eliminated, find and return the
    linear combination which produces a constraint of the form
    `0 < k + t` such that `k` is the constant term of the RHS and `k < 0`. -/
unsafe def find_scalars_core : Nat → List (List Nat × term) → tactic (List Nat)
| 0, pts => find_neg_const pts
| m+1, pts =>
  let (neg, zero, Pos) := trisect m pts 
  do 
    let new ← elim_var m neg Pos 
    find_scalars_core m (new ++ zero)

-- error in Tactic.Omega.FindScalars: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Perform Fourier–Motzkin elimination to find a contradictory
    linear combination of input constraints. -/ meta def find_scalars (ts : list term) : tactic (list nat) :=
find_scalars_core (ts.map (λ
  t : term, t.snd.length)).maximum.iget (ts.map_with_index (λ m t, (list.func.set 1 «expr[ , ]»([]) m, t)))

end Omega

