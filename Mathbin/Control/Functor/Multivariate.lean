/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon

! This file was ported from Lean 3 source module control.functor.multivariate
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fin.Fin2
import Mathbin.Data.Typevec

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


Functors between the category of tuples of types, and the category Type

Features:

`mvfunctor n` : the type class of multivariate functors
`f <$$> x`    : notation for map

-/


universe u v w

open MvFunctor

#print MvFunctor /-
/-- multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
class MvFunctor {n : ℕ} (F : TypeVec n → Type _) where
  map : ∀ {α β : TypeVec n}, α ⟹ β → F α → F β
#align mvfunctor MvFunctor
-/

-- mathport name: mvfunctor.map
scoped[MvFunctor] infixr:100 " <$$> " => MvFunctor.map

variable {n : ℕ}

namespace MvFunctor

variable {α β γ : TypeVec.{u} n} {F : TypeVec.{u} n → Type v} [MvFunctor F]

#print MvFunctor.LiftP /-
/-- predicate lifting over multivariate functors -/
def LiftP {α : TypeVec n} (p : ∀ i, α i → Prop) (x : F α) : Prop :=
  ∃ u : F fun i => Subtype (p i), (fun i => @Subtype.val _ (p i)) <$$> u = x
#align mvfunctor.liftp MvFunctor.LiftP
-/

#print MvFunctor.LiftR /-
/-- relational lifting over multivariate functors -/
def LiftR {α : TypeVec n} (r : ∀ {i}, α i → α i → Prop) (x y : F α) : Prop :=
  ∃ u : F fun i => { p : α i × α i // r p.fst p.snd },
    (fun i (t : { p : α i × α i // r p.fst p.snd }) => t.val.fst) <$$> u = x ∧
      (fun i (t : { p : α i × α i // r p.fst p.snd }) => t.val.snd) <$$> u = y
#align mvfunctor.liftr MvFunctor.LiftR
-/

#print MvFunctor.supp /-
/-- given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x` -/
def supp {α : TypeVec n} (x : F α) (i : Fin2 n) : Set (α i) :=
  { y : α i | ∀ ⦃p⦄, LiftP p x → p i y }
#align mvfunctor.supp MvFunctor.supp
-/

#print MvFunctor.of_mem_supp /-
theorem of_mem_supp {α : TypeVec n} {x : F α} {p : ∀ ⦃i⦄, α i → Prop} (h : LiftP p x) (i : Fin2 n) :
    ∀ y ∈ supp x i, p y := fun y hy => hy h
#align mvfunctor.of_mem_supp MvFunctor.of_mem_supp
-/

end MvFunctor

#print LawfulMvFunctor /-
/-- laws for `mvfunctor` -/
class LawfulMvFunctor {n : ℕ} (F : TypeVec n → Type _) [MvFunctor F] : Prop where
  id_map : ∀ {α : TypeVec n} (x : F α), TypeVec.id <$$> x = x
  comp_map :
    ∀ {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α), (h ⊚ g) <$$> x = h <$$> g <$$> x
#align is_lawful_mvfunctor LawfulMvFunctor
-/

open Nat TypeVec

namespace MvFunctor

export LawfulMvFunctor (comp_map)

open LawfulMvFunctor

variable {α β γ : TypeVec.{u} n}

variable {F : TypeVec.{u} n → Type v} [MvFunctor F]

variable (p : α ⟹ repeat n Prop) (r : α ⊗ α ⟹ repeat n Prop)

#print MvFunctor.LiftP' /-
/-- adapt `mvfunctor.liftp` to accept predicates as arrows -/
def LiftP' : F α → Prop :=
  MvFunctor.LiftP fun i x => of_repeat <| p i x
#align mvfunctor.liftp' MvFunctor.LiftP'
-/

#print MvFunctor.LiftR' /-
/-- adapt `mvfunctor.liftp` to accept relations as arrows -/
def LiftR' : F α → F α → Prop :=
  MvFunctor.LiftR fun i x y => of_repeat <| r i <| TypeVec.prod.mk _ x y
#align mvfunctor.liftr' MvFunctor.LiftR'
-/

variable [LawfulMvFunctor F]

#print MvFunctor.id_map /-
@[simp]
theorem id_map (x : F α) : TypeVec.id <$$> x = x :=
  id_map x
#align mvfunctor.id_map MvFunctor.id_map
-/

#print MvFunctor.id_map' /-
@[simp]
theorem id_map' (x : F α) : (fun i a => a) <$$> x = x :=
  id_map x
#align mvfunctor.id_map' MvFunctor.id_map'
-/

#print MvFunctor.map_map /-
theorem map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h <$$> g <$$> x = (h ⊚ g) <$$> x :=
  Eq.symm <| comp_map _ _ _
#align mvfunctor.map_map MvFunctor.map_map
-/

section Liftp'

variable (F)

#print MvFunctor.exists_iff_exists_of_mono /-
theorem exists_iff_exists_of_mono {p : F α → Prop} {q : F β → Prop} (f : α ⟹ β) (g : β ⟹ α)
    (h₀ : f ⊚ g = id) (h₁ : ∀ u : F α, p u ↔ q (f <$$> u)) : (∃ u : F α, p u) ↔ ∃ u : F β, q u :=
  by
  constructor <;> rintro ⟨u, h₂⟩ <;> [use f <$$> u, use g <$$> u]
  · apply (h₁ u).mp h₂
  · apply (h₁ _).mpr _
    simp only [MvFunctor.map_map, h₀, LawfulMvFunctor.id_map, h₂]
#align mvfunctor.exists_iff_exists_of_mono MvFunctor.exists_iff_exists_of_mono
-/

variable {F}

#print MvFunctor.LiftP_def /-
theorem LiftP_def (x : F α) : LiftP' p x ↔ ∃ u : F (Subtype_ p), subtypeVal p <$$> u = x :=
  exists_iff_exists_of_mono F _ _ (toSubtype_of_subtype p) (by simp [MvFunctor.map_map])
#align mvfunctor.liftp_def MvFunctor.LiftP_def
-/

#print MvFunctor.LiftR_def /-
theorem LiftR_def (x y : F α) :
    LiftR' r x y ↔
      ∃ u : F (Subtype_ r),
        (TypeVec.prod.fst ⊚ subtypeVal r) <$$> u = x ∧
          (TypeVec.prod.snd ⊚ subtypeVal r) <$$> u = y :=
  exists_iff_exists_of_mono _ _ _ (toSubtype'_of_subtype' r)
    (by simp only [map_map, comp_assoc, subtype_val_to_subtype'] <;> simp [comp])
#align mvfunctor.liftr_def MvFunctor.LiftR_def
-/

end Liftp'

end MvFunctor

open Nat

namespace MvFunctor

open TypeVec

section LiftpLastPredIff

variable {F : TypeVec.{u} (n + 1) → Type _} [MvFunctor F] [LawfulMvFunctor F] {α : TypeVec.{u} n}

variable (p : α ⟹ repeat n Prop) (r : α ⊗ α ⟹ repeat n Prop)

open MvFunctor

variable {β : Type u}

variable (pp : β → Prop)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private def f :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 // ofRepeat (PredLast' α pp i p_1) }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 : (α ::: β) i // PredLast α pp p_1 }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [pred_last] <;> erw [const_iff_true]) x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩
#align mvfunctor.f mvfunctor.f

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private def g :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i // PredLast α pp p_1 }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 // ofRepeat (PredLast' α pp i p_1) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [pred_last] <;> erw [const_iff_true]) x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩
#align mvfunctor.g mvfunctor.g

/- warning: mvfunctor.liftp_last_pred_iff -> MvFunctor.LiftP_PredLast_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) F] [_inst_2 : LawfulMvFunctor.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) F _inst_1] {α : TypeVec.{u1} n} {β : Type.{u1}} (p : β -> Prop) (x : F (TypeVec.append1.{u1} n α β)), Iff (MvFunctor.LiftP'.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α β) F _inst_1 (TypeVec.PredLast'.{u1} n α β p) x) (MvFunctor.LiftP.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) F _inst_1 (fun (i : Fin2 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => TypeVec.append1.{u1} n α β i) (TypeVec.PredLast.{u1} n α β p) x)
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) F] [_inst_2 : LawfulMvFunctor.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) F _inst_1] {α : TypeVec.{u2} n} {β : Type.{u2}} (p : β -> Prop) (x : F (TypeVec.append1.{u2} n α β)), Iff (MvFunctor.LiftP'.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u2} n α β) F _inst_1 (TypeVec.PredLast'.{u2} n α β p) x) (MvFunctor.LiftP.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) F _inst_1 (fun (i : Fin2 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => TypeVec.append1.{u2} n α β i) (TypeVec.PredLast.{u2} n α β p) x)
Case conversion may be inaccurate. Consider using '#align mvfunctor.liftp_last_pred_iff MvFunctor.LiftP_PredLast_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem LiftP_PredLast_iff {β} (p : β → Prop) (x : F (α ::: β)) :
    LiftP' (PredLast' _ p) x ↔ LiftP (PredLast _ p) x :=
  by
  dsimp only [liftp, liftp']
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α)
  · ext (i⟨x, _⟩)
    cases i <;> rfl
  · intros
    rw [MvFunctor.map_map, (· ⊚ ·)]
    congr <;> ext (i⟨x, _⟩) <;> cases i <;> rfl
#align mvfunctor.liftp_last_pred_iff MvFunctor.LiftP_PredLast_iff

open Function

variable (rr : β → β → Prop)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private def f :
    ∀ n α,
      (fun i : Fin2 (n + 1) =>
          { p_1 : _ × _ // ofRepeat (RelLast' α rr i (TypeVec.prod.mk _ p_1.fst p_1.snd)) }) ⟹
        fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [rel_last] <;> erw [repeat_eq_iff_eq]) x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩
#align mvfunctor.f mvfunctor.f

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
private def g :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }) ⟹
        fun i : Fin2 (n + 1) =>
        { p_1 : _ × _ // ofRepeat (RelLast' α rr i (TypeVec.prod.mk _ p_1.1 p_1.2)) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [rel_last] <;> erw [repeat_eq_iff_eq]) x.property⟩
  | _, α, Fin2.fz, x => ⟨x.val, x.property⟩
#align mvfunctor.g mvfunctor.g

/- warning: mvfunctor.liftr_last_rel_iff -> MvFunctor.LiftR_RelLast_iff is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {F : (TypeVec.{u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> Type.{u2}} [_inst_1 : MvFunctor.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) F] [_inst_2 : LawfulMvFunctor.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) F _inst_1] {α : TypeVec.{u1} n} {β : Type.{u1}} (rr : β -> β -> Prop) (x : F (TypeVec.append1.{u1} n α β)) (y : F (TypeVec.append1.{u1} n α β)), Iff (MvFunctor.LiftR'.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (TypeVec.append1.{u1} n α β) F _inst_1 (TypeVec.RelLast'.{u1} n α β rr) x y) (MvFunctor.LiftR.{u1, u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) F _inst_1 (fun (i : Fin2 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => TypeVec.append1.{u1} n α β i) (TypeVec.RelLast.{u1} n α β β rr) x y)
but is expected to have type
  forall {n : Nat} {F : (TypeVec.{u2} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> Type.{u1}} [_inst_1 : MvFunctor.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) F] [_inst_2 : LawfulMvFunctor.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) F _inst_1] {α : TypeVec.{u2} n} {β : Type.{u2}} (rr : β -> β -> Prop) (x : F (TypeVec.append1.{u2} n α β)) (y : F (TypeVec.append1.{u2} n α β)), Iff (MvFunctor.LiftR'.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (TypeVec.append1.{u2} n α β) F _inst_1 (TypeVec.RelLast'.{u2} n α β rr) x y) (MvFunctor.LiftR.{u2, u1} (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) F _inst_1 (fun {i : Fin2 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} => TypeVec.append1.{u2} n α β i) (fun {i._@.Mathlib.Control.Functor.Multivariate._hyg.3392 : Fin2 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))} => TypeVec.RelLast.{u2} n α β β rr i._@.Mathlib.Control.Functor.Multivariate._hyg.3392) x y)
Case conversion may be inaccurate. Consider using '#align mvfunctor.liftr_last_rel_iff MvFunctor.LiftR_RelLast_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem LiftR_RelLast_iff (x y : F (α ::: β)) :
    LiftR' (RelLast' _ rr) x y ↔ LiftR (RelLast _ rr) x y :=
  by
  dsimp only [liftr, liftr']
  apply exists_iff_exists_of_mono F (f rr _ _) (g rr _ _)
  · ext (i⟨x, _⟩) : 2
    cases i <;> rfl
  · intros
    rw [MvFunctor.map_map, MvFunctor.map_map, (· ⊚ ·), (· ⊚ ·)]
    congr <;> ext (i⟨x, _⟩) <;> cases i <;> rfl
#align mvfunctor.liftr_last_rel_iff MvFunctor.LiftR_RelLast_iff

end LiftpLastPredIff

end MvFunctor

