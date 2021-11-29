import Mathbin.Data.Pfunctor.Multivariate.Basic 
import Mathbin.Data.Qpf.Multivariate.Basic

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/


universe u

namespace Mvqpf

open_locale Mvfunctor

variable {n m : ℕ} (F : Typevec.{u} n → Type _) [fF : Mvfunctor F] [q : Mvqpf F] (G : Fin2 n → Typevec.{u} m → Type u)
  [fG : ∀ i, Mvfunctor$ G i] [q' : ∀ i, Mvqpf$ G i]

/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/
def comp (v : Typevec.{u} m) : Type _ :=
  F$ fun i : Fin2 n => G i v

namespace Comp

open Mvfunctor Mvpfunctor

variable {F G} {α β : Typevec.{u} m} (f : α ⟹ β)

instance [I : Inhabited (F$ fun i : Fin2 n => G i α)] : Inhabited (comp F G α) :=
  I

/-- Constructor for functor composition -/
protected def mk (x : F$ fun i => G i α) : (comp F G) α :=
  x

/-- Destructor for functor composition -/
protected def get (x : (comp F G) α) : F$ fun i => G i α :=
  x

@[simp]
protected theorem mk_get (x : (comp F G) α) : comp.mk (comp.get x) = x :=
  rfl

@[simp]
protected theorem get_mk (x : F$ fun i => G i α) : comp.get (comp.mk x) = x :=
  rfl

include fG

/-- map operation defined on a vector of functors -/
protected def map' : (fun i : Fin2 n => G i α) ⟹ fun i : Fin2 n => G i β :=
  fun i => map f

include fF

/-- The composition of functors is itself functorial -/
protected def map : (comp F G) α → (comp F G) β :=
  (map fun i => map f : (F fun i => G i α) → F fun i => G i β)

instance : Mvfunctor (comp F G) :=
  { map := fun α β => comp.map }

theorem map_mk (x : F$ fun i => G i α) : f <$$> comp.mk x = comp.mk ((fun i x : G i α => f <$$> x) <$$> x) :=
  rfl

theorem get_map (x : comp F G α) : comp.get (f <$$> x) = (fun i x : G i α => f <$$> x) <$$> comp.get x :=
  rfl

include q q'

instance : Mvqpf (comp F G) :=
  { p := Mvpfunctor.comp (P F) fun i => P$ G i,
    abs := fun α => comp.mk ∘ (map fun i => abs) ∘ abs ∘ Mvpfunctor.comp.get,
    repr :=
      fun α =>
        Mvpfunctor.comp.mk ∘ reprₓ ∘ (map fun i => (reprₓ : G i α → (fun i : Fin2 n => obj (P (G i)) α) i)) ∘ comp.get,
    abs_repr :=
      by 
        intros 
        simp [· ∘ ·, Mvfunctor.map_map, · ⊚ ·, abs_repr],
    abs_map :=
      by 
        intros 
        simp [· ∘ ·]
        rw [←abs_map]
        simp [Mvfunctor.id_map, · ⊚ ·, map_mk, Mvpfunctor.comp.get_map, abs_map, Mvfunctor.map_map, abs_repr] }

end Comp

end Mvqpf

