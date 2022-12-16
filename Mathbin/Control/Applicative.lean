/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module control.applicative
! leanprover-community/mathlib commit b3f25363ae62cb169e72cd6b8b1ac97bacf21ca7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Control.Functor

/-!
# `applicative` instances

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/798
> Any changes to this file require a corresponding PR to mathlib4.

This file provides `applicative` instances for concrete functors:
* `id`
* `functor.comp`
* `functor.const`
* `functor.add_const`
-/


universe u v w

section Lemmas

open Function

variable {F : Type u → Type v}

variable [Applicative F] [LawfulApplicative F]

variable {α β γ σ : Type u}

/- warning: applicative.map_seq_map -> Applicative.map_seq_map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} {σ : Type.{u1}} (f : α -> β -> γ) (g : σ -> β) (x : F α) (y : F σ), Eq.{succ u2} (F γ) (Seq.seq.{u1, u2} (fun {α : Type.{u1}} => F α) (Applicative.toHasSeq.{u1, u2} (fun {α : Type.{u1}} => F α) _inst_1) β γ (Functor.map.{u1, u2} (fun {α : Type.{u1}} => F α) (Applicative.toFunctor.{u1, u2} (fun {α : Type.{u1}} => F α) _inst_1) α (β -> γ) f x) (Functor.map.{u1, u2} F (Applicative.toFunctor.{u1, u2} F _inst_1) σ β g y)) (Seq.seq.{u1, u2} F (Applicative.toHasSeq.{u1, u2} F _inst_1) σ γ (Functor.map.{u1, u2} F (Applicative.toFunctor.{u1, u2} F _inst_1) α (σ -> γ) (Function.comp.{succ u1, succ u1, succ u1} α (β -> γ) (σ -> γ) (flip.{succ u1, succ u1, succ u1} (β -> γ) (σ -> β) (σ -> γ) (Function.comp.{succ u1, succ u1, succ u1} σ β γ) g) f) x) y)
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {α : Type.{u1}} {β : Type.{u1}} {γ : Type.{u1}} {σ : Type.{u1}} (f : α -> β -> γ) (g : σ -> β) (x : F α) (y : F σ), Eq.{succ u2} (F γ) (Seq.seq.{u1, u2} F (Applicative.toSeq.{u1, u2} F _inst_1) β γ (Functor.map.{u1, u2} F (Applicative.toFunctor.{u1, u2} F _inst_1) α (β -> γ) f x) (fun (x._@.Mathlib.Control.Applicative._hyg.86 : Unit) => Functor.map.{u1, u2} F (Applicative.toFunctor.{u1, u2} F _inst_1) σ β g y)) (Seq.seq.{u1, u2} F (Applicative.toSeq.{u1, u2} F _inst_1) σ γ (Functor.map.{u1, u2} F (Applicative.toFunctor.{u1, u2} F _inst_1) α (σ -> γ) (Function.comp.{succ u1, succ u1, succ u1} α (β -> γ) (σ -> γ) (flip.{succ u1, succ u1, succ u1} (β -> γ) (σ -> β) (σ -> γ) (fun (x._@.Mathlib.Control.Applicative._hyg.109 : β -> γ) (x._@.Mathlib.Control.Applicative._hyg.111 : σ -> β) => Function.comp.{succ u1, succ u1, succ u1} σ β γ x._@.Mathlib.Control.Applicative._hyg.109 x._@.Mathlib.Control.Applicative._hyg.111) g) f) x) (fun (x._@.Mathlib.Control.Applicative._hyg.128 : Unit) => y))
Case conversion may be inaccurate. Consider using '#align applicative.map_seq_map Applicative.map_seq_mapₓ'. -/
theorem Applicative.map_seq_map (f : α → β → γ) (g : σ → β) (x : F α) (y : F σ) :
    f <$> x <*> g <$> y = (flip (· ∘ ·) g ∘ f) <$> x <*> y := by simp [flip, functor_norm]
#align applicative.map_seq_map Applicative.map_seq_map

/- warning: applicative.pure_seq_eq_map' -> Applicative.pure_seq_eq_map' is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {α : Type.{u1}} {β : Type.{u1}} (f : α -> β), Eq.{succ u2} ((F α) -> (F β)) (Seq.seq.{u1, u2} F (Applicative.toHasSeq.{u1, u2} F _inst_1) α β (Pure.pure.{u1, u2} F (Applicative.toHasPure.{u1, u2} F _inst_1) (α -> β) f)) (Functor.map.{u1, u2} F (Applicative.toFunctor.{u1, u2} F _inst_1) α β f)
but is expected to have type
  forall {F : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} F] [_inst_2 : LawfulApplicative.{u1, u2} F _inst_1] {α : Type.{u1}} {β : Type.{u1}} (f : α -> β), Eq.{succ u2} ((F α) -> (F β)) ((fun (x._@.Mathlib.Control.Applicative._hyg.164 : F (α -> β)) (x._@.Mathlib.Control.Applicative._hyg.166 : F α) => Seq.seq.{u1, u2} F (Applicative.toSeq.{u1, u2} F _inst_1) α β x._@.Mathlib.Control.Applicative._hyg.164 (fun (x._@.Mathlib.Control.Applicative._hyg.179 : Unit) => x._@.Mathlib.Control.Applicative._hyg.166)) (Pure.pure.{u1, u2} F (Applicative.toPure.{u1, u2} F _inst_1) (α -> β) f)) ((fun (x._@.Mathlib.Control.Applicative._hyg.196 : α -> β) (x._@.Mathlib.Control.Applicative._hyg.198 : F α) => Functor.map.{u1, u2} F (Applicative.toFunctor.{u1, u2} F _inst_1) α β x._@.Mathlib.Control.Applicative._hyg.196 x._@.Mathlib.Control.Applicative._hyg.198) f)
Case conversion may be inaccurate. Consider using '#align applicative.pure_seq_eq_map' Applicative.pure_seq_eq_map'ₓ'. -/
theorem Applicative.pure_seq_eq_map' (f : α → β) : (· <*> ·) (pure f : F (α → β)) = (· <$> ·) f :=
  by ext <;> simp [functor_norm]
#align applicative.pure_seq_eq_map' Applicative.pure_seq_eq_map'

/- warning: applicative.ext -> Applicative.ext is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} {A1 : Applicative.{u1, u2} F} {A2 : Applicative.{u1, u2} F} [_inst_3 : LawfulApplicative.{u1, u2} F A1] [_inst_4 : LawfulApplicative.{u1, u2} F A2], (forall {α : Type.{u1}} (x : α), Eq.{succ u2} (F α) (Pure.pure.{u1, u2} F (Applicative.toHasPure.{u1, u2} F A1) α x) (Pure.pure.{u1, u2} F (Applicative.toHasPure.{u1, u2} F A2) α x)) -> (forall {α : Type.{u1}} {β : Type.{u1}} (f : F (α -> β)) (x : F α), Eq.{succ u2} (F β) (Seq.seq.{u1, u2} F (Applicative.toHasSeq.{u1, u2} F A1) α β f x) (Seq.seq.{u1, u2} F (Applicative.toHasSeq.{u1, u2} F A2) α β f x)) -> (Eq.{max (succ (succ u1)) (succ u2)} (Applicative.{u1, u2} F) A1 A2)
but is expected to have type
  forall {F : Type.{u2} -> Type.{u1}} {A1 : Applicative.{u2, u1} F} {A2 : Applicative.{u2, u1} F} [_inst_3 : LawfulApplicative.{u2, u1} F A1] [_inst_4 : LawfulApplicative.{u2, u1} F A2], (forall {α : Type.{u2}} (x : α), Eq.{succ u1} (F α) (Pure.pure.{u2, u1} F (Applicative.toPure.{u2, u1} F A1) α x) (Pure.pure.{u2, u1} F (Applicative.toPure.{u2, u1} F A2) α x)) -> (forall {α : Type.{u2}} {β : Type.{u2}} (f : F (α -> β)) (x : F α), Eq.{succ u1} (F β) (Seq.seq.{u2, u1} F (Applicative.toSeq.{u2, u1} F A1) α β f (fun (x._@.Mathlib.Control.Applicative._hyg.297 : Unit) => x)) (Seq.seq.{u2, u1} F (Applicative.toSeq.{u2, u1} F A2) α β f (fun (x._@.Mathlib.Control.Applicative._hyg.310 : Unit) => x))) -> (Eq.{max (succ (succ u2)) (succ u1)} (Applicative.{u2, u1} F) A1 A2)
Case conversion may be inaccurate. Consider using '#align applicative.ext Applicative.extₓ'. -/
theorem Applicative.ext {F} :
    ∀ {A1 : Applicative F} {A2 : Applicative F} [@LawfulApplicative F A1] [@LawfulApplicative F A2]
      (H1 : ∀ {α : Type u} (x : α), @Pure.pure _ A1.toHasPure _ x = @Pure.pure _ A2.toHasPure _ x)
      (H2 :
        ∀ {α β : Type u} (f : F (α → β)) (x : F α),
          @Seq.seq _ A1.toHasSeq _ _ f x = @Seq.seq _ A2.toHasSeq _ _ f x),
      A1 = A2
  | { toFunctor := F1
      seq := s1
      pure := p1
      seqLeft := sl1
      seqRight := sr1 },
    { toFunctor := F2
      seq := s2
      pure := p2
      seqLeft := sl2
      seqRight := sr2 },
    L1, L2, H1, H2 => by
    obtain rfl : @p1 = @p2 := by 
      funext α x
      apply H1
    obtain rfl : @s1 = @s2 := by 
      funext α β f x
      apply H2
    cases L1
    cases L2
    obtain rfl : F1 = F2 := by 
      skip
      apply Functor.ext
      intros
      exact (L1_pure_seq_eq_map _ _).symm.trans (L2_pure_seq_eq_map _ _)
    congr <;> funext α β x y
    · exact (L1_seq_left_eq _ _).trans (L2_seq_left_eq _ _).symm
    · exact (L1_seq_right_eq _ _).trans (L2_seq_right_eq _ _).symm
#align applicative.ext Applicative.ext

end Lemmas

instance : CommApplicative id := by refine' { .. } <;> intros <;> rfl

namespace Functor

namespace Comp

open Function hiding comp

open Functor

variable {F : Type u → Type w} {G : Type v → Type u}

variable [Applicative F] [Applicative G]

variable [LawfulApplicative F] [LawfulApplicative G]

variable {α β γ : Type v}

#print Functor.Comp.map_pure /-
theorem map_pure (f : α → β) (x : α) : (f <$> pure x : Comp F G β) = pure (f x) :=
  comp.ext <| by simp
#align functor.comp.map_pure Functor.Comp.map_pure
-/

/- warning: functor.comp.seq_pure -> Functor.Comp.seq_pure is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u3}} {G : Type.{u2} -> Type.{u1}} [_inst_1 : Applicative.{u1, u3} F] [_inst_2 : Applicative.{u2, u1} G] [_inst_3 : LawfulApplicative.{u1, u3} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u2}} (f : Functor.Comp.{u1, u2, u3} F G (α -> β)) (x : α), Eq.{succ u3} (Functor.Comp.{u1, u2, u3} F G β) (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.hasSeq.{u1, u2, u3} F G _inst_1 _inst_2) α β f (Pure.pure.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.hasPure.{u1, u2, u3} F G _inst_1 _inst_2) α x)) (Functor.map.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.functor.{u1, u2, u3} F G (Applicative.toFunctor.{u1, u3} F _inst_1) (Applicative.toFunctor.{u2, u1} G _inst_2)) (α -> β) β (fun (g : α -> β) => g x) f)
but is expected to have type
  forall {F : Type.{u1} -> Type.{u3}} {G : Type.{u2} -> Type.{u1}} [_inst_1 : Applicative.{u1, u3} F] [_inst_2 : Applicative.{u2, u1} G] [_inst_3 : LawfulApplicative.{u1, u3} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u2}} (f : Functor.Comp.{u1, u2, u3} F G (α -> β)) (x : α), Eq.{succ u3} (Functor.Comp.{u1, u2, u3} F G β) (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.instSeqComp.{u1, u2, u3} F G _inst_1 _inst_2) α β f (fun (x._@.Mathlib.Control.Applicative._hyg.997 : Unit) => Pure.pure.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.instPureComp.{u1, u2, u3} F G _inst_1 _inst_2) α x)) (Functor.map.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.functor.{u1, u2, u3} F G (Applicative.toFunctor.{u1, u3} F _inst_1) (Applicative.toFunctor.{u2, u1} G _inst_2)) (α -> β) β (fun (g : α -> β) => g x) f)
Case conversion may be inaccurate. Consider using '#align functor.comp.seq_pure Functor.Comp.seq_pureₓ'. -/
theorem seq_pure (f : Comp F G (α → β)) (x : α) : f <*> pure x = (fun g : α → β => g x) <$> f :=
  comp.ext <| by simp [(· ∘ ·), functor_norm]
#align functor.comp.seq_pure Functor.Comp.seq_pure

/- warning: functor.comp.seq_assoc -> Functor.Comp.seq_assoc is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u3}} {G : Type.{u2} -> Type.{u1}} [_inst_1 : Applicative.{u1, u3} F] [_inst_2 : Applicative.{u2, u1} G] [_inst_3 : LawfulApplicative.{u1, u3} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u2}} {γ : Type.{u2}} (x : Functor.Comp.{u1, u2, u3} F G α) (f : Functor.Comp.{u1, u2, u3} F G (α -> β)) (g : Functor.Comp.{u1, u2, u3} F G (β -> γ)), Eq.{succ u3} (Functor.Comp.{u1, u2, u3} F G γ) (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.hasSeq.{u1, u2, u3} F G _inst_1 _inst_2) β γ g (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.hasSeq.{u1, u2, u3} F G _inst_1 _inst_2) α β f x)) (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.hasSeq.{u1, u2, u3} F G _inst_1 _inst_2) α γ (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.hasSeq.{u1, u2, u3} F G _inst_1 _inst_2) (α -> β) (α -> γ) (Functor.map.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.functor.{u1, u2, u3} F G (Applicative.toFunctor.{u1, u3} F _inst_1) (Applicative.toFunctor.{u2, u1} G _inst_2)) (β -> γ) ((α -> β) -> α -> γ) (Function.comp.{succ u2, succ u2, succ u2} α β γ) g) f) x)
but is expected to have type
  forall {F : Type.{u1} -> Type.{u3}} {G : Type.{u2} -> Type.{u1}} [_inst_1 : Applicative.{u1, u3} F] [_inst_2 : Applicative.{u2, u1} G] [_inst_3 : LawfulApplicative.{u1, u3} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u2}} {γ : Type.{u2}} (x : Functor.Comp.{u1, u2, u3} F G α) (f : Functor.Comp.{u1, u2, u3} F G (α -> β)) (g : Functor.Comp.{u1, u2, u3} F G (β -> γ)), Eq.{succ u3} (Functor.Comp.{u1, u2, u3} F G γ) (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.instSeqComp.{u1, u2, u3} F G _inst_1 _inst_2) β γ g (fun (x._@.Mathlib.Control.Applicative._hyg.1085 : Unit) => Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.instSeqComp.{u1, u2, u3} F G _inst_1 _inst_2) α β f (fun (x._@.Mathlib.Control.Applicative._hyg.1097 : Unit) => x))) (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.instSeqComp.{u1, u2, u3} F G _inst_1 _inst_2) α γ (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.instSeqComp.{u1, u2, u3} F G _inst_1 _inst_2) (α -> β) (α -> γ) (Functor.map.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.functor.{u1, u2, u3} F G (Applicative.toFunctor.{u1, u3} F _inst_1) (Applicative.toFunctor.{u2, u1} G _inst_2)) (β -> γ) ((α -> β) -> α -> γ) (Function.comp.{succ u2, succ u2, succ u2} α β γ) g) (fun (x._@.Mathlib.Control.Applicative._hyg.1119 : Unit) => f)) (fun (x._@.Mathlib.Control.Applicative._hyg.1126 : Unit) => x))
Case conversion may be inaccurate. Consider using '#align functor.comp.seq_assoc Functor.Comp.seq_assocₓ'. -/
theorem seq_assoc (x : Comp F G α) (f : Comp F G (α → β)) (g : Comp F G (β → γ)) :
    g <*> (f <*> x) = @Function.comp α β γ <$> g <*> f <*> x :=
  comp.ext <| by simp [(· ∘ ·), functor_norm]
#align functor.comp.seq_assoc Functor.Comp.seq_assoc

/- warning: functor.comp.pure_seq_eq_map -> Functor.Comp.pure_seq_eq_map is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u3}} {G : Type.{u2} -> Type.{u1}} [_inst_1 : Applicative.{u1, u3} F] [_inst_2 : Applicative.{u2, u1} G] [_inst_3 : LawfulApplicative.{u1, u3} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u2}} (f : α -> β) (x : Functor.Comp.{u1, u2, u3} F G α), Eq.{succ u3} (Functor.Comp.{u1, u2, u3} F G β) (Seq.seq.{u2, u3} (fun {α : Type.{u2}} => Functor.Comp.{u1, u2, u3} F G α) (Functor.Comp.hasSeq.{u1, u2, u3} F G _inst_1 _inst_2) α β (Pure.pure.{u2, u3} (fun {α : Type.{u2}} => Functor.Comp.{u1, u2, u3} F G α) (Functor.Comp.hasPure.{u1, u2, u3} F G _inst_1 _inst_2) (α -> β) f) x) (Functor.map.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.functor.{u1, u2, u3} F G (Applicative.toFunctor.{u1, u3} F _inst_1) (Applicative.toFunctor.{u2, u1} G _inst_2)) α β f x)
but is expected to have type
  forall {F : Type.{u1} -> Type.{u3}} {G : Type.{u2} -> Type.{u1}} [_inst_1 : Applicative.{u1, u3} F] [_inst_2 : Applicative.{u2, u1} G] [_inst_3 : LawfulApplicative.{u1, u3} F _inst_1] [_inst_4 : LawfulApplicative.{u2, u1} G _inst_2] {α : Type.{u2}} {β : Type.{u2}} (f : α -> β) (x : Functor.Comp.{u1, u2, u3} F G α), Eq.{succ u3} (Functor.Comp.{u1, u2, u3} F G β) (Seq.seq.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.instSeqComp.{u1, u2, u3} F G _inst_1 _inst_2) α β (Pure.pure.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.instPureComp.{u1, u2, u3} F G _inst_1 _inst_2) (α -> β) f) (fun (x._@.Mathlib.Control.Applicative._hyg.1185 : Unit) => x)) (Functor.map.{u2, u3} (Functor.Comp.{u1, u2, u3} F G) (Functor.Comp.functor.{u1, u2, u3} F G (Applicative.toFunctor.{u1, u3} F _inst_1) (Applicative.toFunctor.{u2, u1} G _inst_2)) α β f x)
Case conversion may be inaccurate. Consider using '#align functor.comp.pure_seq_eq_map Functor.Comp.pure_seq_eq_mapₓ'. -/
theorem pure_seq_eq_map (f : α → β) (x : Comp F G α) : pure f <*> x = f <$> x :=
  comp.ext <| by simp [Applicative.pure_seq_eq_map', functor_norm]
#align functor.comp.pure_seq_eq_map Functor.Comp.pure_seq_eq_map

instance :
    LawfulApplicative
      (Comp F G) where 
  pure_seq_eq_map := @Comp.pure_seq_eq_map F G _ _ _ _
  map_pure := @Comp.map_pure F G _ _ _ _
  seq_pure := @Comp.seq_pure F G _ _ _ _
  seq_assoc := @Comp.seq_assoc F G _ _ _ _

/- warning: functor.comp.applicative_id_comp -> Functor.Comp.applicative_id_comp is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [AF : Applicative.{u1, u2} F] [LF : LawfulApplicative.{u1, u2} F AF], Eq.{max (succ (succ u1)) (succ u2)} (Applicative.{u1, u2} (Functor.Comp.{u2, u1, u2} (id.{succ (succ u2)} Type.{u2}) F)) (Functor.Comp.applicative.{u2, u1, u2} (id.{succ (succ u2)} Type.{u2}) F (Monad.toApplicative.{u2, u2} (id.{succ (succ u2)} Type.{u2}) id.monad.{u2}) AF) AF
but is expected to have type
  forall {F : Type.{u2} -> Type.{u1}} [AF : Applicative.{u2, u1} F] [LF : LawfulApplicative.{u2, u1} F AF], Eq.{max (succ u1) (succ (succ u2))} (Applicative.{u2, u1} (Functor.Comp.{u1, u2, u1} Id.{u1} F)) (Functor.Comp.instApplicativeComp.{u1, u2, u1} Id.{u1} F (Monad.toApplicative.{u1, u1} Id.{u1} Id.instMonadId.{u1}) AF) AF
Case conversion may be inaccurate. Consider using '#align functor.comp.applicative_id_comp Functor.Comp.applicative_id_compₓ'. -/
theorem applicative_id_comp {F} [AF : Applicative F] [LF : LawfulApplicative F] :
    @Comp.applicative id F _ _ = AF :=
  @Applicative.ext F _ _ (@Comp.is_lawful_applicative id F _ _ _ _) _ (fun α x => rfl)
    fun α β f x => rfl
#align functor.comp.applicative_id_comp Functor.Comp.applicative_id_comp

/- warning: functor.comp.applicative_comp_id -> Functor.Comp.applicative_comp_id is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1} -> Type.{u2}} [AF : Applicative.{u1, u2} F] [LF : LawfulApplicative.{u1, u2} F AF], Eq.{max (succ (succ u1)) (succ u2)} (Applicative.{u1, u2} (Functor.Comp.{u1, u1, u2} F (id.{succ (succ u1)} Type.{u1}))) (Functor.Comp.applicative.{u1, u1, u2} F (id.{succ (succ u1)} Type.{u1}) AF (Monad.toApplicative.{u1, u1} (id.{succ (succ u1)} Type.{u1}) id.monad.{u1})) AF
but is expected to have type
  forall {F : Type.{u2} -> Type.{u1}} [AF : Applicative.{u2, u1} F] [LF : LawfulApplicative.{u2, u1} F AF], Eq.{max (succ u1) (succ (succ u2))} (Applicative.{u2, u1} (Functor.Comp.{u2, u2, u1} F Id.{u2})) (Functor.Comp.instApplicativeComp.{u2, u2, u1} F Id.{u2} AF (Monad.toApplicative.{u2, u2} Id.{u2} Id.instMonadId.{u2})) AF
Case conversion may be inaccurate. Consider using '#align functor.comp.applicative_comp_id Functor.Comp.applicative_comp_idₓ'. -/
theorem applicative_comp_id {F} [AF : Applicative F] [LF : LawfulApplicative F] :
    @Comp.applicative F id _ _ = AF :=
  @Applicative.ext F _ _ (@Comp.is_lawful_applicative F id _ _ _ _) _ (fun α x => rfl)
    fun α β f x => show id <$> f <*> x = f <*> x by rw [id_map]
#align functor.comp.applicative_comp_id Functor.Comp.applicative_comp_id

open CommApplicative

instance {f : Type u → Type w} {g : Type v → Type u} [Applicative f] [Applicative g]
    [CommApplicative f] [CommApplicative g] : CommApplicative (Comp f g) := by
  refine' { @comp.is_lawful_applicative f g _ _ _ _ with .. }
  intros
  casesm*comp _ _ _
  simp! [map, Seq.seq, functor_norm]
  rw [commutative_map]
  simp [comp.mk, flip, (· ∘ ·), functor_norm]
  congr
  funext
  rw [commutative_map]
  congr

end Comp

end Functor

open Functor

/- warning: comp.seq_mk -> Comp.seq_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u3}} {β : Type.{u3}} {f : Type.{u1} -> Type.{u2}} {g : Type.{u3} -> Type.{u1}} [_inst_1 : Applicative.{u1, u2} f] [_inst_2 : Applicative.{u3, u1} g] (h : f (g (α -> β))) (x : f (g α)), Eq.{succ u2} (Functor.Comp.{u1, u3, u2} f g β) (Seq.seq.{u3, u2} (Functor.Comp.{u1, u3, u2} f g) (Functor.Comp.hasSeq.{u1, u3, u2} f g _inst_1 _inst_2) α β (Functor.Comp.mk.{u1, u3, u2} f g (α -> β) h) (Functor.Comp.mk.{u1, u3, u2} f g α x)) (Functor.Comp.mk.{u1, u3, u2} f g β (Seq.seq.{u1, u2} f (Applicative.toHasSeq.{u1, u2} f _inst_1) (g α) (g β) (Functor.map.{u1, u2} f (Applicative.toFunctor.{u1, u2} f _inst_1) (g (α -> β)) ((g α) -> (g β)) (Seq.seq.{u3, u1} g (Applicative.toHasSeq.{u3, u1} g _inst_2) α β) h) x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u3}} {f : Type.{u1} -> Type.{u2}} {g : Type.{u3} -> Type.{u1}} [_inst_1 : Applicative.{u1, u2} f] [_inst_2 : Applicative.{u3, u1} g] (h : f (g (α -> β))) (x : f (g α)), Eq.{succ u2} (Functor.Comp.{u1, u3, u2} f g β) (Seq.seq.{u3, u2} (Functor.Comp.{u1, u3, u2} f g) (Functor.Comp.instSeqComp.{u1, u3, u2} f g _inst_1 _inst_2) α β (Functor.Comp.mk.{u1, u3, u2} f g (α -> β) h) (fun (x._@.Mathlib.Control.Applicative._hyg.1732 : Unit) => Functor.Comp.mk.{u1, u3, u2} f g α x)) (Functor.Comp.mk.{u1, u3, u2} f g β (Seq.seq.{u1, u2} f (Applicative.toSeq.{u1, u2} f _inst_1) (g α) (g β) (Functor.map.{u1, u2} f (Applicative.toFunctor.{u1, u2} f _inst_1) (g (α -> β)) ((g α) -> (g β)) (fun (x._@.Mathlib.Control.Applicative._hyg.1748 : g (α -> β)) (x._@.Mathlib.Control.Applicative._hyg.1750 : g α) => Seq.seq.{u3, u1} g (Applicative.toSeq.{u3, u1} g _inst_2) α β x._@.Mathlib.Control.Applicative._hyg.1748 (fun (x._@.Mathlib.Control.Applicative._hyg.1763 : Unit) => x._@.Mathlib.Control.Applicative._hyg.1750)) h) (fun (x._@.Mathlib.Control.Applicative._hyg.1771 : Unit) => x)))
Case conversion may be inaccurate. Consider using '#align comp.seq_mk Comp.seq_mkₓ'. -/
@[functor_norm]
theorem Comp.seq_mk {α β : Type w} {f : Type u → Type v} {g : Type w → Type u} [Applicative f]
    [Applicative g] (h : f (g (α → β))) (x : f (g α)) :
    Comp.mk h <*> Comp.mk x = Comp.mk (Seq.seq <$> h <*> x) :=
  rfl
#align comp.seq_mk Comp.seq_mk

instance {α} [One α] [Mul α] :
    Applicative (Const α) where 
  pure β x := (1 : α)
  seq β γ f x := (f * x : α)

instance {α} [Monoid α] : LawfulApplicative (Const α) := by
  refine' { .. } <;> intros <;> simp [mul_assoc, (· <$> ·), (· <*> ·), pure]

instance {α} [Zero α] [Add α] :
    Applicative (AddConst α) where 
  pure β x := (0 : α)
  seq β γ f x := (f + x : α)

instance {α} [AddMonoid α] : LawfulApplicative (AddConst α) := by
  refine' { .. } <;> intros <;> simp [add_assoc, (· <$> ·), (· <*> ·), pure]

