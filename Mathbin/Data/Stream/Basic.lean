import Mathbin.Tactic.Ext 
import Mathbin.Data.Stream.Init 
import Mathbin.Data.List.Basic 
import Mathbin.Data.List.Range

/-!
# Additional instances and attributes for streams
-/


attribute [ext] Streamₓ.ext

instance  {α} [Inhabited α] : Inhabited (Streamₓ α) :=
  ⟨Streamₓ.const (default _)⟩

namespace Streamₓ

open Nat

/-- `take s n` returns a list of the `n` first elements of stream `s` -/
def take {α} (s : Streamₓ α) (n : ℕ) : List α :=
  (List.range n).map s

theorem length_take {α} (s : Streamₓ α) (n : ℕ) : (take s n).length = n :=
  by 
    simp [take]

/-- Use a state monad to generate a stream through corecursion -/
def corec_state {σ α} (cmd : State σ α) (s : σ) : Streamₓ α :=
  Streamₓ.corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

end Streamₓ

