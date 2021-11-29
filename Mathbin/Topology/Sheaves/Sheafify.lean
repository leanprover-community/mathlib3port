import Mathbin.Topology.Sheaves.LocalPredicate 
import Mathbin.Topology.Sheaves.Stalks

/-!
# Sheafification of `Type` valued presheaves

We construct the sheafification of a `Type` valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.

We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalk_to_fiber` which evaluates a germ of a dependent function at a point.

We construct a morphism `to_sheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.

## Future work
Show that the map induced on stalks by `to_sheafify` is the inverse of `stalk_to_fiber`.

Show sheafification is a functor from presheaves to sheaves,
and that it is the left adjoint of the forgetful functor,
following https://stacks.math.columbia.edu/tag/007X.
-/


universe v

noncomputable theory

open Top

open Opposite

open TopologicalSpace

variable{X : Top.{v}}(F : presheaf (Type v) X)

namespace Top.Presheaf

namespace Sheafify

/--
The prelocal predicate on functions into the stalks, asserting that the function is equal to a germ.
-/
def is_germ : prelocal_predicate fun x => F.stalk x :=
  { pred := fun U f => ∃ g : F.obj (op U), ∀ (x : U), f x = F.germ x g,
    res := fun V U i f ⟨g, p⟩ => ⟨F.map i.op g, fun x => (p (i x)).trans (F.germ_res_apply _ _ _).symm⟩ }

/--
The local predicate on functions into the stalks,
asserting that the function is locally equal to a germ.
-/
def is_locally_germ : local_predicate fun x => F.stalk x :=
  (is_germ F).sheafify

end Sheafify

/--
The sheafification of a `Type` valued presheaf, defined as the functions into the stalks which
are locally equal to germs.
-/
def sheafify : sheaf (Type v) X :=
  subsheaf_to_Types (sheafify.is_locally_germ F)

/--
The morphism from a presheaf to its sheafification,
sending each section to its germs.
(This forms the unit of the adjunction.)
-/
def to_sheafify : F ⟶ F.sheafify.1 :=
  { app := fun U f => ⟨fun x => F.germ x f, prelocal_predicate.sheafify_of ⟨f, fun x => rfl⟩⟩,
    naturality' :=
      fun U U' f =>
        by 
          ext x ⟨u, m⟩
          exact germ_res_apply F f.unop ⟨u, m⟩ x }

/--
The natural morphism from the stalk of the sheafification to the original stalk.
In `sheafify_stalk_iso` we show this is an isomorphism.
-/
def stalk_to_fiber (x : X) : F.sheafify.1.stalk x ⟶ F.stalk x :=
  stalk_to_fiber (sheafify.is_locally_germ F) x

theorem stalk_to_fiber_surjective (x : X) : Function.Surjective (F.stalk_to_fiber x) :=
  by 
    apply stalk_to_fiber_surjective 
    intro t 
    obtain ⟨U, m, s, rfl⟩ := F.germ_exist _ t
    ·
      use ⟨U, m⟩
      fsplit
      ·
        exact fun y => F.germ y s
      ·
        exact ⟨prelocal_predicate.sheafify_of ⟨s, fun _ => rfl⟩, rfl⟩

-- error in Topology.Sheaves.Sheafify: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem stalk_to_fiber_injective (x : X) : function.injective (F.stalk_to_fiber x) :=
begin
  apply [expr stalk_to_fiber_injective],
  intros [],
  rcases [expr hU ⟨x, U.2⟩, "with", "⟨", ident U', ",", ident mU, ",", ident iU, ",", ident gU, ",", ident wU, "⟩"],
  rcases [expr hV ⟨x, V.2⟩, "with", "⟨", ident V', ",", ident mV, ",", ident iV, ",", ident gV, ",", ident wV, "⟩"],
  have [ident wUx] [] [":=", expr wU ⟨x, mU⟩],
  dsimp [] [] [] ["at", ident wUx],
  erw [expr wUx] ["at", ident e],
  clear [ident wUx],
  have [ident wVx] [] [":=", expr wV ⟨x, mV⟩],
  dsimp [] [] [] ["at", ident wVx],
  erw [expr wVx] ["at", ident e],
  clear [ident wVx],
  rcases [expr F.germ_eq x mU mV gU gV e, "with", "⟨", ident W, ",", ident mW, ",", ident iU', ",", ident iV', ",", ident e', "⟩"],
  dsimp [] [] [] ["at", ident e'],
  use [expr ⟨«expr ⊓ »(W, «expr ⊓ »(U', V')), ⟨mW, mU, mV⟩⟩],
  refine [expr ⟨_, _, _⟩],
  { change [expr «expr ⟶ »(«expr ⊓ »(W, «expr ⊓ »(U', V')), U.val)] [] [],
    exact [expr «expr ≫ »(opens.inf_le_right _ _, «expr ≫ »(opens.inf_le_left _ _, iU))] },
  { change [expr «expr ⟶ »(«expr ⊓ »(W, «expr ⊓ »(U', V')), V.val)] [] [],
    exact [expr «expr ≫ »(opens.inf_le_right _ _, «expr ≫ »(opens.inf_le_right _ _, iV))] },
  { intro [ident w],
    dsimp [] [] [] [],
    specialize [expr wU ⟨w.1, w.2.2.1⟩],
    dsimp [] [] [] ["at", ident wU],
    specialize [expr wV ⟨w.1, w.2.2.2⟩],
    dsimp [] [] [] ["at", ident wV],
    erw ["[", expr wU, ",", "<-", expr F.germ_res iU' ⟨w, w.2.1⟩, ",", expr wV, ",", "<-", expr F.germ_res iV' ⟨w, w.2.1⟩, ",", expr category_theory.types_comp_apply, ",", expr category_theory.types_comp_apply, ",", expr e', "]"] [] }
end

/--
The isomorphism betweeen a stalk of the sheafification and the original stalk.
-/
def sheafify_stalk_iso (x : X) : F.sheafify.1.stalk x ≅ F.stalk x :=
  (Equiv.ofBijective _ ⟨stalk_to_fiber_injective _ _, stalk_to_fiber_surjective _ _⟩).toIso

end Top.Presheaf

