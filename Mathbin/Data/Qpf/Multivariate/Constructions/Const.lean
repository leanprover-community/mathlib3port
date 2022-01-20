import Mathbin.Control.Functor.Multivariate
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
# Constant functors are QPFs

Constant functors map every type vectors to the same target type. This
is a useful device for constructing data types from more basic types
that are not actually functorial. For instance `const n nat` makes
`nat` into a functor that can be used in a functor-based data type
specification.
-/


universe u

namespace Mvqpf

open_locale Mvfunctor

variable (n : ℕ)

/-- Constant multivariate functor -/
@[nolint unused_arguments]
def const (A : Type _) (v : Typevec.{u} n) : Type _ :=
  A

instance const.inhabited {A α} [Inhabited A] : Inhabited (const n A α) :=
  ⟨(default : A)⟩

namespace Const

open Mvfunctor Mvpfunctor

variable {n} {A : Type u} {α β : Typevec.{u} n} (f : α ⟹ β)

/-- Constructor for constant functor -/
protected def mk (x : A) : (const n A) α :=
  x

/-- Destructor for constant functor -/
protected def get (x : (const n A) α) : A :=
  x

@[simp]
protected theorem mk_get (x : (const n A) α) : const.mk (const.get x) = x :=
  rfl

@[simp]
protected theorem get_mk (x : A) : const.get (const.mk x : const n A α) = x :=
  rfl

/-- `map` for constant functor -/
protected def map : (const n A) α → (const n A) β := fun x => x

instance : Mvfunctor (const n A) where
  map := fun α β f => const.map

theorem map_mk (x : A) : f <$$> const.mk x = const.mk x :=
  rfl

theorem get_map (x : (const n A) α) : const.get (f <$$> x) = const.get x :=
  rfl

instance Mvqpf : @Mvqpf _ (const n A) Mvqpf.Const.mvfunctor where
  p := Mvpfunctor.const n A
  abs := fun α x => Mvpfunctor.const.get x
  repr := fun α x => Mvpfunctor.const.mk n x
  abs_repr := by
    intros <;> simp
  abs_map := by
    intros <;> simp <;> rfl

end Const

end Mvqpf

