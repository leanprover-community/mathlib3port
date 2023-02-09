/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau

! This file was ported from Lean 3 source module data.multiset.functor
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Bind
import Mathbin.Control.Traversable.Lemmas
import Mathbin.Control.Traversable.Instances

/-!
# Functoriality of `multiset`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u

namespace Multiset

open List

instance : Functor Multiset where map := @map

#print Multiset.fmap_def /-
@[simp]
theorem fmap_def {α' β'} {s : Multiset α'} (f : α' → β') : f <$> s = s.map f :=
  rfl
#align multiset.fmap_def Multiset.fmap_def
-/

instance : LawfulFunctor Multiset := by refine' { .. } <;> intros <;> simp

open IsLawfulTraversable CommApplicative

variable {F : Type u → Type u} [Applicative F] [CommApplicative F]

variable {α' β' : Type u} (f : α' → F β')

#print Multiset.traverse /-
def traverse : Multiset α' → F (Multiset β') :=
  Quotient.lift (Functor.map coe ∘ Traversable.traverse f)
    (by
      introv p; unfold Function.comp
      induction p
      case nil => rfl
      case
        cons =>
        have :
          Multiset.cons <$> f p_x <*> coe <$> traverse f p_l₁ =
            Multiset.cons <$> f p_x <*> coe <$> traverse f p_l₂ :=
          by rw [p_ih]
        simpa [functor_norm]
      case
        swap =>
        have :
          (fun a b (l : List β') => (↑(a :: b :: l) : Multiset β')) <$> f p_y <*> f p_x =
            (fun a b l => ↑(a :: b :: l)) <$> f p_x <*> f p_y :=
          by
          rw [CommApplicative.commutative_map]
          congr
          funext a b l
          simpa [flip] using Perm.swap b a l
        simp [(· ∘ ·), this, functor_norm]
      case trans => simp [*])
#align multiset.traverse Multiset.traverse
-/

instance : Monad Multiset :=
  { Multiset.functor with
    pure := fun α x => {x}
    bind := @bind }

/- warning: multiset.pure_def -> Multiset.pure_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (α -> (Multiset.{u1} α)) (Pure.pure.{u1, u1} (fun {α : Type.{u1}} => Multiset.{u1} α) (Applicative.toHasPure.{u1, u1} (fun {α : Type.{u1}} => Multiset.{u1} α) (Monad.toApplicative.{u1, u1} (fun {α : Type.{u1}} => Multiset.{u1} α) Multiset.monad.{u1})) α) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.hasSingleton.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (α -> (Multiset.{u1} α)) (Pure.pure.{u1, u1} Multiset.{u1} (Applicative.toPure.{u1, u1} Multiset.{u1} (Monad.toApplicative.{u1, u1} Multiset.{u1} Multiset.instMonadMultiset.{u1})) α) (Singleton.singleton.{u1, u1} α (Multiset.{u1} α) (Multiset.instSingletonMultiset.{u1} α))
Case conversion may be inaccurate. Consider using '#align multiset.pure_def Multiset.pure_defₓ'. -/
@[simp]
theorem pure_def {α} : (pure : α → Multiset α) = singleton :=
  rfl
#align multiset.pure_def Multiset.pure_def

/- warning: multiset.bind_def -> Multiset.bind_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}}, Eq.{succ u1} ((Multiset.{u1} α) -> (α -> (Multiset.{u1} β)) -> (Multiset.{u1} β)) (Bind.bind.{u1, u1} Multiset.{u1} (Monad.toHasBind.{u1, u1} Multiset.{u1} Multiset.monad.{u1}) α β) (Multiset.bind.{u1, u1} α β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}}, Eq.{succ u1} ((Multiset.{u1} α) -> (α -> (Multiset.{u1} β)) -> (Multiset.{u1} β)) (fun (x._@.Mathlib.Data.Multiset.Functor._hyg.718 : Multiset.{u1} α) (x._@.Mathlib.Data.Multiset.Functor._hyg.720 : α -> (Multiset.{u1} β)) => Bind.bind.{u1, u1} Multiset.{u1} (Monad.toBind.{u1, u1} Multiset.{u1} Multiset.instMonadMultiset.{u1}) α β x._@.Mathlib.Data.Multiset.Functor._hyg.718 x._@.Mathlib.Data.Multiset.Functor._hyg.720) (Multiset.bind.{u1, u1} α β)
Case conversion may be inaccurate. Consider using '#align multiset.bind_def Multiset.bind_defₓ'. -/
@[simp]
theorem bind_def {α β} : (· >>= ·) = @bind α β :=
  rfl
#align multiset.bind_def Multiset.bind_def

instance : LawfulMonad Multiset
    where
  bind_pure_comp_eq_map α β f s := Multiset.induction_on s rfl fun a s ih => by simp
  pure_bind α β x f := by simp [pure]
  bind_assoc := @bind_assoc

open Functor

open Traversable IsLawfulTraversable

/- warning: multiset.lift_coe -> Multiset.lift_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (x : List.{u1} α) (f : (List.{u1} α) -> β) (h : forall (a : List.{u1} α) (b : List.{u1} α), (HasEquivₓ.Equiv.{succ u1} (List.{u1} α) (setoidHasEquiv.{succ u1} (List.{u1} α) (List.isSetoid.{u1} α)) a b) -> (Eq.{succ u2} β (f a) (f b))), Eq.{succ u2} β (Quotient.lift.{succ u1, succ u2} (List.{u1} α) β (List.isSetoid.{u1} α) f h ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))) x)) (f x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (x : List.{u2} α) (f : (List.{u2} α) -> β) (h : forall (a : List.{u2} α) (b : List.{u2} α), (HasEquiv.Equiv.{succ u2, 0} (List.{u2} α) (instHasEquiv.{succ u2} (List.{u2} α) (List.isSetoid.{u2} α)) a b) -> (Eq.{succ u1} β (f a) (f b))), Eq.{succ u1} β (Quotient.lift.{succ u2, succ u1} (List.{u2} α) β (List.isSetoid.{u2} α) f h (Multiset.ofList.{u2} α x)) (f x)
Case conversion may be inaccurate. Consider using '#align multiset.lift_coe Multiset.lift_coeₓ'. -/
@[simp]
theorem lift_coe {α β : Type _} (x : List α) (f : List α → β)
    (h : ∀ a b : List α, a ≈ b → f a = f b) : Quotient.lift f h (x : Multiset α) = f x :=
  Quotient.lift_mk _ _ _
#align multiset.lift_coe Multiset.lift_coe

/- warning: multiset.map_comp_coe -> Multiset.map_comp_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} (h : α -> β), Eq.{succ u1} ((List.{u1} α) -> (Multiset.{u1} β)) (Function.comp.{succ u1, succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.{u1} β) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => Multiset.{u1} β) Multiset.functor.{u1} α β h) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} α) (Multiset.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (coeBase.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.hasCoe.{u1} α)))))) (Function.comp.{succ u1, succ u1, succ u1} (List.{u1} α) (List.{u1} β) (Multiset.{u1} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (List.{u1} β) (Multiset.{u1} β) (HasLiftT.mk.{succ u1, succ u1} (List.{u1} β) (Multiset.{u1} β) (CoeTCₓ.coe.{succ u1, succ u1} (List.{u1} β) (Multiset.{u1} β) (coeBase.{succ u1, succ u1} (List.{u1} β) (Multiset.{u1} β) (Multiset.hasCoe.{u1} β))))) (Functor.map.{u1, u1} List.{u1} (Traversable.toFunctor.{u1} List.{u1} List.traversable.{u1}) α β h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} (h : α -> β), Eq.{succ u1} ((List.{u1} α) -> (Multiset.{u1} β)) (Function.comp.{succ u1, succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.{u1} β) (Functor.map.{u1, u1} Multiset.{u1} Multiset.functor.{u1} α β h) (Coe.coe.{succ u1, succ u1} (List.{u1} α) (Multiset.{u1} α) (Multiset.instCoeListMultiset.{u1} α))) (Function.comp.{succ u1, succ u1, succ u1} (List.{u1} α) (List.{u1} β) (Multiset.{u1} β) (Coe.coe.{succ u1, succ u1} (List.{u1} β) (Multiset.{u1} β) (Multiset.instCoeListMultiset.{u1} β)) (Functor.map.{u1, u1} List.{u1} List.instFunctorList.{u1} α β h))
Case conversion may be inaccurate. Consider using '#align multiset.map_comp_coe Multiset.map_comp_coeₓ'. -/
@[simp]
theorem map_comp_coe {α β} (h : α → β) :
    Functor.map h ∘ coe = (coe ∘ Functor.map h : List α → Multiset β) := by
  funext <;> simp [functor.map]
#align multiset.map_comp_coe Multiset.map_comp_coe

/- warning: multiset.id_traverse -> Multiset.id_traverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : Multiset.{u1} α), Eq.{succ u1} (id.{succ (succ u1)} Type.{u1} (Multiset.{u1} α)) (Multiset.traverse.{u1} (id.{succ (succ u1)} Type.{u1}) (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1}) id.commApplicative.{u1} α α (id.mk.{succ u1} α) x) x
but is expected to have type
  forall {α : Type.{u1}} (x : Multiset.{u1} α), Eq.{succ u1} (Id.{u1} (Multiset.{u1} α)) (Multiset.traverse.{u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) instCommApplicativeIdToApplicativeInstMonadId.{u1} α α (Pure.pure.{u1, u1} Id.{u1} (Applicative.toPure.{u1, u1} Id.{u1} (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1})) α) x) x
Case conversion may be inaccurate. Consider using '#align multiset.id_traverse Multiset.id_traverseₓ'. -/
theorem id_traverse {α : Type _} (x : Multiset α) : traverse id.mk x = x :=
  Quotient.inductionOn x (by intro ; simp [traverse]; rfl)
#align multiset.id_traverse Multiset.id_traverse

/- warning: multiset.comp_traverse -> Multiset.comp_traverse is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1} -> Type.{u1}} {H : Type.{u1} -> Type.{u1}} [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : Applicative.{u1, u1} H] [_inst_5 : CommApplicative.{u1, u1} G _inst_3] [_inst_6 : CommApplicative.{u1, u1} H _inst_4] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (g : α -> (G β)) (h : β -> (H γ)) (x : Multiset.{u1} α), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) H (Multiset.{u1} γ)) (Multiset.traverse.{u1} (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) H) (Functor.Comp.applicative.{u1, u1, u1} (fun {β : Type.{u1}} => G β) H _inst_3 _inst_4) (Functor.Comp.commApplicative.{u1, u1, u1} (fun {β : Type.{u1}} => G β) H _inst_3 _inst_4 _inst_5 _inst_6) α γ (Function.comp.{succ u1, succ u1, succ u1} α (G (H γ)) (Functor.Comp.{u1, u1, u1} (fun {β : Type.{u1}} => G β) H γ) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) H γ) (Function.comp.{succ u1, succ u1, succ u1} α (G β) (G (H γ)) (Functor.map.{u1, u1} (fun {β : Type.{u1}} => G β) (Applicative.toFunctor.{u1, u1} (fun {β : Type.{u1}} => G β) _inst_3) β (H γ) h) g)) x) (Functor.Comp.mk.{u1, u1, u1} (fun {β : Type.{u1}} => G β) H (Multiset.{u1} γ) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_3) (Multiset.{u1} β) (H (Multiset.{u1} γ)) (Multiset.traverse.{u1} H _inst_4 _inst_6 β γ h) (Multiset.traverse.{u1} G _inst_3 _inst_5 α β g x)))
but is expected to have type
  forall {G : Type.{u1} -> Type.{u1}} {H : Type.{u1} -> Type.{u1}} [_inst_3 : Applicative.{u1, u1} G] [_inst_4 : Applicative.{u1, u1} H] [_inst_5 : CommApplicative.{u1, u1} G _inst_3] [_inst_6 : CommApplicative.{u1, u1} H _inst_4] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} (g : α -> (G β)) (h : β -> (H γ)) (x : Multiset.{u1} α), Eq.{succ u1} (Functor.Comp.{u1, u1, u1} G H (Multiset.{u1} γ)) (Multiset.traverse.{u1} (Functor.Comp.{u1, u1, u1} G H) (Functor.Comp.instApplicativeComp.{u1, u1, u1} G H _inst_3 _inst_4) (Functor.Comp.instCommApplicativeCompInstApplicativeComp.{u1, u1, u1} G H _inst_3 _inst_4 _inst_5 _inst_6) α γ (Function.comp.{succ u1, succ u1, succ u1} α (G (H γ)) (Functor.Comp.{u1, u1, u1} G H γ) (Functor.Comp.mk.{u1, u1, u1} G H γ) (Function.comp.{succ u1, succ u1, succ u1} α (G β) (G (H γ)) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_3) β (H γ) h) g)) x) (Functor.Comp.mk.{u1, u1, u1} G H (Multiset.{u1} γ) (Functor.map.{u1, u1} G (Applicative.toFunctor.{u1, u1} G _inst_3) (Multiset.{u1} β) (H (Multiset.{u1} γ)) (Multiset.traverse.{u1} H _inst_4 _inst_6 β γ h) (Multiset.traverse.{u1} G _inst_3 _inst_5 α β g x)))
Case conversion may be inaccurate. Consider using '#align multiset.comp_traverse Multiset.comp_traverseₓ'. -/
theorem comp_traverse {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] {α β γ : Type _} (g : α → G β) (h : β → H γ) (x : Multiset α) :
    traverse (Comp.mk ∘ Functor.map h ∘ g) x = Comp.mk (Functor.map (traverse h) (traverse g x)) :=
  Quotient.inductionOn x
    (by
      intro <;> simp [traverse, comp_traverse, functor_norm] <;>
        simp [(· <$> ·), (· ∘ ·), functor_norm])
#align multiset.comp_traverse Multiset.comp_traverse

#print Multiset.map_traverse /-
theorem map_traverse {G : Type _ → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → G β) (h : β → γ) (x : Multiset α) :
    Functor.map (Functor.map h) (traverse g x) = traverse (Functor.map h ∘ g) x :=
  Quotient.inductionOn x
    (by intro <;> simp [traverse, functor_norm] <;> rw [LawfulFunctor.comp_map, map_traverse])
#align multiset.map_traverse Multiset.map_traverse
-/

#print Multiset.traverse_map /-
theorem traverse_map {G : Type _ → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → β) (h : β → G γ) (x : Multiset α) : traverse h (map g x) = traverse (h ∘ g) x :=
  Quotient.inductionOn x
    (by intro <;> simp [traverse] <;> rw [← Traversable.traverse_map h g] <;> [rfl, infer_instance])
#align multiset.traverse_map Multiset.traverse_map
-/

#print Multiset.naturality /-
theorem naturality {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] (eta : ApplicativeTransformation G H) {α β : Type _} (f : α → G β)
    (x : Multiset α) : eta (traverse f x) = traverse (@eta _ ∘ f) x :=
  Quotient.inductionOn x
    (by intro <;> simp [traverse, IsLawfulTraversable.naturality, functor_norm])
#align multiset.naturality Multiset.naturality
-/

end Multiset

