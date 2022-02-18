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

variable [Category.{v₁} C]

variable {T : Monad C} (X : Algebra T)

/-!
Show that any algebra is a coequalizer of free algebras.
-/


/-- The top map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.top_map : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A :=
  (Monad.free T).map X.a

/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.bottom_map : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A where
  f := T.μ.app X.A
  h' := T.assoc X.A

/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
def free_coequalizer.π : (Monad.free T).obj X.A ⟶ X where
  f := X.a
  h' := X.assoc.symm

theorem free_coequalizer.condition :
    FreeCoequalizer.topMap X ≫ FreeCoequalizer.π X = FreeCoequalizer.bottomMap X ≫ FreeCoequalizer.π X :=
  Algebra.Hom.ext _ _ X.assoc.symm

instance : IsReflexivePair (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) := by
  apply is_reflexive_pair.mk' _ _ _
  apply (free T).map (T.η.app X.A)
  · ext
    dsimp
    rw [← functor.map_comp, X.unit, Functor.map_id]
    
  · ext
    apply monad.right_unit
    

/-- Construct the Beck cofork in the category of algebras. This cofork is reflexive as well as a
coequalizer.
-/
@[simps]
def beck_algebra_cofork : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) :=
  Cofork.ofπ _ (FreeCoequalizer.condition X)

/-- The cofork constructed is a colimit. This shows that any algebra is a (reflexive) coequalizer of
free algebras.
-/
def beck_algebra_coequalizer : IsColimit (beckAlgebraCofork X) :=
  (Cofork.IsColimit.mk' _) fun s => by
    have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f := congr_argₓ monad.algebra.hom.f s.condition
    have h₂ : (T : C ⥤ C).map s.π.f ≫ s.X.a = T.μ.app X.A ≫ s.π.f := s.π.h
    refine' ⟨⟨T.η.app _ ≫ s.π.f, _⟩, _, _⟩
    · dsimp
      rw [functor.map_comp, category.assoc, h₂, monad.right_unit_assoc,
        show X.a ≫ _ ≫ _ = _ from T.η.naturality_assoc _ _, h₁, monad.left_unit_assoc]
      
    · ext
      simpa [← T.η.naturality_assoc, T.left_unit_assoc] using T.η.app ((T : C ⥤ C).obj X.A) ≫= h₁
      
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      apply (X.unit_assoc _).symm
      

/-- The Beck cofork is a split coequalizer. -/
def beck_split_coequalizer : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a :=
  ⟨T.η.app _, T.η.app _, X.assoc.symm, X.Unit, T.left_unit _, (T.η.naturality _).symm⟩

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simps]
def beck_cofork : Cofork (T.map X.a) (T.μ.app _) :=
  (beckSplitCoequalizer X).asCofork

/-- The Beck cofork is a coequalizer. -/
def beck_coequalizer : IsColimit (beckCofork X) :=
  (beckSplitCoequalizer X).isCoequalizer

end Monadₓ

end CategoryTheory

