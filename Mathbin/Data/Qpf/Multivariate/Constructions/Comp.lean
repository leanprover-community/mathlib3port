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

variable{n m :
    ℕ}(F :
    Typevec.{u} n →
      Type
        _)[fF :
    Mvfunctor F][q : Mvqpf F](G : Fin2 n → Typevec.{u} m → Type u)[fG : ∀ i, Mvfunctor$ G i][q' : ∀ i, Mvqpf$ G i]

-- error in Data.Qpf.Multivariate.Constructions.Comp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/ def comp (v : typevec.{u} m) : Type* :=
«expr $ »(F, λ i : fin2 n, G i v)

namespace Comp

open Mvfunctor Mvpfunctor

variable{F G}{α β : Typevec.{u} m}(f : α ⟹ β)

-- error in Data.Qpf.Multivariate.Constructions.Comp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance [I : inhabited «expr $ »(F, λ i : fin2 n, G i α)] : inhabited (comp F G α) := I

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

-- error in Data.Qpf.Multivariate.Constructions.Comp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- map operation defined on a vector of functors -/
protected
def map' : «expr ⟹ »(λ i : fin2 n, G i α, λ i : fin2 n, G i β) :=
λ i, map f

include fF

/-- The composition of functors is itself functorial -/
protected def map : (comp F G) α → (comp F G) β :=
  (map fun i => map f : (F fun i => G i α) → F fun i => G i β)

instance  : Mvfunctor (comp F G) :=
  { map := fun α β => comp.map }

-- error in Data.Qpf.Multivariate.Constructions.Comp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem map_mk
(x : «expr $ »(F, λ
  i, G i α)) : «expr = »(«expr <$$> »(f, comp.mk x), comp.mk «expr <$$> »(λ (i) (x : G i α), «expr <$$> »(f, x), x)) :=
rfl

-- error in Data.Qpf.Multivariate.Constructions.Comp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem get_map
(x : comp F G α) : «expr = »(comp.get «expr <$$> »(f, x), «expr <$$> »(λ
  (i)
  (x : G i α), «expr <$$> »(f, x), comp.get x)) :=
rfl

include q q'

-- error in Data.Qpf.Multivariate.Constructions.Comp: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
instance : mvqpf (comp F G) :=
{ P := mvpfunctor.comp (P F) (λ i, «expr $ »(P, G i)),
  abs := λ α, «expr ∘ »(comp.mk, «expr ∘ »(map (λ i, abs), «expr ∘ »(abs, mvpfunctor.comp.get))),
  repr := λ
  α, «expr ∘ »(mvpfunctor.comp.mk, «expr ∘ »(repr, «expr ∘ »(map (λ
      i, (repr : G i α → λ i : fin2 n, obj (P (G i)) α i)), comp.get))),
  abs_repr := by { intros [],
    simp [] [] [] ["[", expr («expr ∘ »), ",", expr mvfunctor.map_map, ",", expr («expr ⊚ »), ",", expr abs_repr, "]"] [] [] },
  abs_map := by { intros [],
    simp [] [] [] ["[", expr («expr ∘ »), "]"] [] [],
    rw ["[", "<-", expr abs_map, "]"] [],
    simp [] [] [] ["[", expr mvfunctor.id_map, ",", expr («expr ⊚ »), ",", expr map_mk, ",", expr mvpfunctor.comp.get_map, ",", expr abs_map, ",", expr mvfunctor.map_map, ",", expr abs_repr, "]"] [] [] } }

end Comp

end Mvqpf

