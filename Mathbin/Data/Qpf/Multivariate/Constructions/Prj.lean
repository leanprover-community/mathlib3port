import Mathbin.Control.Functor.Multivariate
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/


universe u v

namespace Mvqpf

open_locale Mvfunctor

variable {n : ℕ} (i : Fin2 n)

/-- The projection `i` functor -/
def prj (v : Typevec.{u} n) : Type u :=
  v i

instance prj.inhabited {v : Typevec.{u} n} [Inhabited (v i)] : Inhabited (Prj i v) :=
  ⟨(default : v i)⟩

/-- `map` on functor `prj i` -/
def prj.map ⦃α β : Typevec n⦄ (f : α ⟹ β) : Prj i α → Prj i β :=
  f _

instance prj.mvfunctor : Mvfunctor (Prj i) where
  map := Prj.map i

/-- Polynomial representation of the projection functor -/
def prj.P : Mvpfunctor.{u} n where
  A := PUnit
  B := fun _ j => Ulift <| Plift <| i = j

/-- Abstraction function of the `qpf` instance -/
def prj.abs ⦃α : Typevec n⦄ : (Prj.p i).Obj α → Prj i α
  | ⟨x, f⟩ => f _ ⟨⟨rfl⟩⟩

/-- Representation function of the `qpf` instance -/
def prj.repr ⦃α : Typevec n⦄ : Prj i α → (Prj.p i).Obj α := fun x : α i => ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩

instance prj.mvqpf : Mvqpf (Prj i) where
  p := Prj.p i
  abs := Prj.abs i
  repr := Prj.repr i
  abs_repr := by
    intros <;> rfl
  abs_map := by
    intros <;> cases p <;> rfl

end Mvqpf

