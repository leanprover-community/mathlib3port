import Mathbin.CategoryTheory.Limits.Shapes.Reflexive 
import Mathbin.CategoryTheory.Limits.Shapes.SplitCoequalizer 
import Mathbin.CategoryTheory.Monad.Algebra

/-!
# Special coequalizers associated to a monad

Associated to a monad `T : C ⥤ C` we have important coequalizer constructions:
Any algebra is a coequalizer (in the category of algebras) of free algebras. Furthermore, this
coequalizer is reflexive.
In `C`, this cofork diagram is a split coequalizer (in particular, it is still a coequalizer).
This split coequalizer is known as the Beck coequalizer (as it features heavily in Beck's
monadicity theorem).
-/


universe v₁ u₁

namespace CategoryTheory

namespace Monadₓ

open Limits

variable {C : Type u₁}

variable [category.{v₁} C]

variable {T : Monadₓ C} (X : algebra T)

/-!
Show that any algebra is a coequalizer of free algebras.
-/


/-- The top map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.top_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
  (monad.free T).map X.a

/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.bottom_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
  { f := T.μ.app X.A, h' := T.assoc X.A }

/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.π : (monad.free T).obj X.A ⟶ X :=
  { f := X.a, h' := X.assoc.symm }

theorem free_coequalizer.condition :
  free_coequalizer.top_map X ≫ free_coequalizer.π X = free_coequalizer.bottom_map X ≫ free_coequalizer.π X :=
  algebra.hom.ext _ _ X.assoc.symm

instance : is_reflexive_pair (free_coequalizer.top_map X) (free_coequalizer.bottom_map X) :=
  by 
    apply is_reflexive_pair.mk' _ _ _ 
    apply (free T).map (T.η.app X.A)
    ·
      ext 
      dsimp 
      rw [←functor.map_comp, X.unit, Functor.map_id]
    ·
      ext 
      apply monad.right_unit

/--
Construct the Beck cofork in the category of algebras. This cofork is reflexive as well as a
coequalizer.
-/
@[simps]
def beck_algebra_cofork : cofork (free_coequalizer.top_map X) (free_coequalizer.bottom_map X) :=
  cofork.of_π _ (free_coequalizer.condition X)

-- error in CategoryTheory.Monad.Coequalizer: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The cofork constructed is a colimit. This shows that any algebra is a (reflexive) coequalizer of
free algebras.
-/ def beck_algebra_coequalizer : is_colimit (beck_algebra_cofork X) :=
«expr $ »(cofork.is_colimit.mk' _, λ s, begin
   have [ident h₁] [":", expr «expr = »(«expr ≫ »((T : «expr ⥤ »(C, C)).map X.a, s.π.f), «expr ≫ »(T.μ.app X.A, s.π.f))] [":=", expr congr_arg monad.algebra.hom.f s.condition],
   have [ident h₂] [":", expr «expr = »(«expr ≫ »((T : «expr ⥤ »(C, C)).map s.π.f, s.X.a), «expr ≫ »(T.μ.app X.A, s.π.f))] [":=", expr s.π.h],
   refine [expr ⟨⟨«expr ≫ »(T.η.app _, s.π.f), _⟩, _, _⟩],
   { dsimp [] [] [] [],
     rw ["[", expr functor.map_comp, ",", expr category.assoc, ",", expr h₂, ",", expr monad.right_unit_assoc, ",", expr show «expr = »(«expr ≫ »(X.a, «expr ≫ »(_, _)), _), from T.η.naturality_assoc _ _, ",", expr h₁, ",", expr monad.left_unit_assoc, "]"] [] },
   { ext [] [] [],
     simpa [] [] [] ["[", "<-", expr T.η.naturality_assoc, ",", expr T.left_unit_assoc, "]"] [] ["using", expr «expr ≫= »(T.η.app ((T : «expr ⥤ »(C, C)).obj X.A), h₁)] },
   { intros [ident m, ident hm],
     ext [] [] [],
     dsimp ["only"] [] [] [],
     rw ["<-", expr hm] [],
     apply [expr (X.unit_assoc _).symm] }
 end)

/-- The Beck cofork is a split coequalizer. -/
def beck_split_coequalizer : is_split_coequalizer (T.map X.a) (T.μ.app _) X.a :=
  ⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simps]
def beck_cofork : cofork (T.map X.a) (T.μ.app _) :=
  (beck_split_coequalizer X).asCofork

/-- The Beck cofork is a coequalizer. -/
def beck_coequalizer : is_colimit (beck_cofork X) :=
  (beck_split_coequalizer X).isCoequalizer

end Monadₓ

end CategoryTheory

