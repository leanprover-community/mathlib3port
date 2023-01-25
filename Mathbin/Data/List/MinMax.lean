/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes, Mantas Bakšys

! This file was ported from Lean 3 source module data.list.min_max
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Basic

/-!
# Minimum and maximum of lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f []` = none`

`minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/


namespace List

variable {α β : Type _}

section ArgAux

variable (r : α → α → Prop) [DecidableRel r] {l : List α} {o : Option α} {a m : α}

#print List.argAux /-
/-- Auxiliary definition for `argmax` and `argmin`. -/
def argAux (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if r b c then some b else some c
#align list.arg_aux List.argAux
-/

#print List.foldl_argAux_eq_none /-
@[simp]
theorem foldl_argAux_eq_none : l.foldl (argAux r) o = none ↔ l = [] ∧ o = none :=
  List.reverseRecOn l (by simp) fun tl hd => by
    simp [arg_aux] <;> cases foldl (arg_aux r) o tl <;> simp <;> try split_ifs <;> simp
#align list.foldl_arg_aux_eq_none List.foldl_argAux_eq_none
-/

private theorem foldl_arg_aux_mem (l) : ∀ a m : α, m ∈ foldl (argAux r) (some a) l → m ∈ a :: l :=
  List.reverseRecOn l (by simp [eq_comm])
    (by
      intro tl hd ih a m
      simp only [foldl_append, foldl_cons, foldl_nil, arg_aux]
      cases hf : foldl (arg_aux r) (some a) tl
      · simp (config := { contextual := true })
      · dsimp only
        split_ifs
        · simp (config := { contextual := true })
        · -- `finish [ih _ _ hf]` closes this goal
          rcases ih _ _ hf with (rfl | H)
          · simp only [mem_cons_iff, mem_append, mem_singleton, Option.mem_def]
            tauto
          · apply fun hm => Or.inr (list.mem_append.mpr <| Or.inl _)
            exact option.mem_some_iff.mp hm ▸ H)
#align list.foldl_arg_aux_mem list.foldl_arg_aux_mem

#print List.arg_aux_self /-
@[simp]
theorem arg_aux_self (hr₀ : Irreflexive r) (a : α) : argAux r (some a) a = a :=
  if_neg <| hr₀ _
#align list.arg_aux_self List.arg_aux_self
-/

#print List.not_of_mem_foldl_argAux /-
theorem not_of_mem_foldl_argAux (hr₀ : Irreflexive r) (hr₁ : Transitive r) :
    ∀ {a m : α} {o : Option α}, a ∈ l → m ∈ foldl (argAux r) o l → ¬r a m :=
  by
  induction' l using List.reverseRecOn with tl a ih
  · exact fun _ _ _ h => absurd h <| not_mem_nil _
  intro b m o hb ho
  rw [foldl_append, foldl_cons, foldl_nil, arg_aux] at ho
  cases' hf : foldl (arg_aux r) o tl with c
  · rw [hf] at ho
    rw [foldl_arg_aux_eq_none] at hf
    simp_all [hf.1, hf.2, hr₀ _]
  rw [hf, Option.mem_def] at ho
  dsimp only at ho
  split_ifs  at ho with hac hac <;> cases' mem_append.1 hb with h h <;> subst ho
  · exact fun hba => ih h hf (hr₁ hba hac)
  · simp_all [hr₀ _]
  · exact ih h hf
  · simp_all
#align list.not_of_mem_foldl_arg_aux List.not_of_mem_foldl_argAux
-/

end ArgAux

section Preorder

variable [Preorder β] [@DecidableRel β (· < ·)] {f : α → β} {l : List α} {o : Option α} {a m : α}

#print List.argmax /-
/-- `argmax f l` returns `some a`, where `f a` is maximal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f a < f b`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmax f []` = none`. -/
def argmax (f : α → β) (l : List α) : Option α :=
  l.foldl (arg_aux fun b c => f c < f b) none
#align list.argmax List.argmax
-/

#print List.argmin /-
/-- `argmin f l` returns `some a`, where `f a` is minimal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f b < f a`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmin f []` = none`. -/
def argmin (f : α → β) (l : List α) :=
  l.foldl (arg_aux fun b c => f b < f c) none
#align list.argmin List.argmin
-/

/- warning: list.argmax_nil -> List.argmax_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] (f : α -> β), Eq.{succ u1} (Option.{u1} α) (List.argmax.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (List.nil.{u1} α)) (Option.none.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.929 : β) (x._@.Mathlib.Data.List.MinMax._hyg.931 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.929 x._@.Mathlib.Data.List.MinMax._hyg.931)] (f : α -> β), Eq.{succ u2} (Option.{u2} α) (List.argmax.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (List.nil.{u2} α)) (Option.none.{u2} α)
Case conversion may be inaccurate. Consider using '#align list.argmax_nil List.argmax_nilₓ'. -/
@[simp]
theorem argmax_nil (f : α → β) : argmax f [] = none :=
  rfl
#align list.argmax_nil List.argmax_nil

/- warning: list.argmin_nil -> List.argmin_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] (f : α -> β), Eq.{succ u1} (Option.{u1} α) (List.argmin.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (List.nil.{u1} α)) (Option.none.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.976 : β) (x._@.Mathlib.Data.List.MinMax._hyg.978 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.976 x._@.Mathlib.Data.List.MinMax._hyg.978)] (f : α -> β), Eq.{succ u2} (Option.{u2} α) (List.argmin.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (List.nil.{u2} α)) (Option.none.{u2} α)
Case conversion may be inaccurate. Consider using '#align list.argmin_nil List.argmin_nilₓ'. -/
@[simp]
theorem argmin_nil (f : α → β) : argmin f [] = none :=
  rfl
#align list.argmin_nil List.argmin_nil

/- warning: list.argmax_singleton -> List.argmax_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] {f : α -> β} {a : α}, Eq.{succ u1} (Option.{u1} α) (List.argmax.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (List.cons.{u1} α a (List.nil.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1023 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1025 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1023 x._@.Mathlib.Data.List.MinMax._hyg.1025)] {f : α -> β} {a : α}, Eq.{succ u2} (Option.{u2} α) (List.argmax.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (List.cons.{u2} α a (List.nil.{u2} α))) (Option.some.{u2} α a)
Case conversion may be inaccurate. Consider using '#align list.argmax_singleton List.argmax_singletonₓ'. -/
@[simp]
theorem argmax_singleton {f : α → β} {a : α} : argmax f [a] = a :=
  rfl
#align list.argmax_singleton List.argmax_singleton

/- warning: list.argmin_singleton -> List.argmin_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] {f : α -> β} {a : α}, Eq.{succ u1} (Option.{u1} α) (List.argmin.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (List.cons.{u1} α a (List.nil.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (Option.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (Option.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (Option.{u1} α) (coeOption.{u1} α))) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1073 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1075 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1073 x._@.Mathlib.Data.List.MinMax._hyg.1075)] {f : α -> β} {a : α}, Eq.{succ u2} (Option.{u2} α) (List.argmin.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (List.cons.{u2} α a (List.nil.{u2} α))) (Option.some.{u2} α a)
Case conversion may be inaccurate. Consider using '#align list.argmin_singleton List.argmin_singletonₓ'. -/
@[simp]
theorem argmin_singleton {f : α → β} {a : α} : argmin f [a] = a :=
  rfl
#align list.argmin_singleton List.argmin_singleton

/- warning: list.not_lt_of_mem_argmax -> List.not_lt_of_mem_argmax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] {f : α -> β} {l : List.{u1} α} {a : α} {m : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmax.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l)) -> (Not (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1) (f m) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1123 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1125 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1123 x._@.Mathlib.Data.List.MinMax._hyg.1125)] {f : α -> β} {l : List.{u2} α} {a : α} {m : α}, (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmax.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l)) -> (Not (LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) (f m) (f a)))
Case conversion may be inaccurate. Consider using '#align list.not_lt_of_mem_argmax List.not_lt_of_mem_argmaxₓ'. -/
theorem not_lt_of_mem_argmax : a ∈ l → m ∈ argmax f l → ¬f m < f a :=
  not_of_mem_foldl_argAux _ (fun _ => lt_irrefl _) fun _ _ _ => gt_trans
#align list.not_lt_of_mem_argmax List.not_lt_of_mem_argmax

/- warning: list.not_lt_of_mem_argmin -> List.not_lt_of_mem_argmin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] {f : α -> β} {l : List.{u1} α} {a : α} {m : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmin.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l)) -> (Not (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1) (f a) (f m)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1211 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1213 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1211 x._@.Mathlib.Data.List.MinMax._hyg.1213)] {f : α -> β} {l : List.{u2} α} {a : α} {m : α}, (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmin.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l)) -> (Not (LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) (f a) (f m)))
Case conversion may be inaccurate. Consider using '#align list.not_lt_of_mem_argmin List.not_lt_of_mem_argminₓ'. -/
theorem not_lt_of_mem_argmin : a ∈ l → m ∈ argmin f l → ¬f a < f m :=
  not_of_mem_foldl_argAux _ (fun _ => lt_irrefl _) fun _ _ _ => lt_trans
#align list.not_lt_of_mem_argmin List.not_lt_of_mem_argmin

/- warning: list.argmax_concat -> List.argmax_concat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] (f : α -> β) (a : α) (l : List.{u1} α), Eq.{succ u1} (Option.{u1} α) (List.argmax.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l (List.cons.{u1} α a (List.nil.{u1} α)))) (Option.casesOn.{succ u1, u1} α (fun (_x : Option.{u1} α) => Option.{u1} α) (List.argmax.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l) (Option.some.{u1} α a) (fun (c : α) => ite.{succ u1} (Option.{u1} α) (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1) (f c) (f a)) (_inst_2 (f c) (f a)) (Option.some.{u1} α a) (Option.some.{u1} α c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1299 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1301 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1299 x._@.Mathlib.Data.List.MinMax._hyg.1301)] (f : α -> β) (a : α) (l : List.{u2} α), Eq.{succ u2} (Option.{u2} α) (List.argmax.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l (List.cons.{u2} α a (List.nil.{u2} α)))) (Option.casesOn.{succ u2, u2} α (fun (_x : Option.{u2} α) => Option.{u2} α) (List.argmax.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l) (Option.some.{u2} α a) (fun (c : α) => ite.{succ u2} (Option.{u2} α) (LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) (f c) (f a)) (_inst_2 (f c) (f a)) (Option.some.{u2} α a) (Option.some.{u2} α c)))
Case conversion may be inaccurate. Consider using '#align list.argmax_concat List.argmax_concatₓ'. -/
theorem argmax_concat (f : α → β) (a : α) (l : List α) :
    argmax f (l ++ [a]) =
      Option.casesOn (argmax f l) (some a) fun c => if f c < f a then some a else some c :=
  by rw [argmax, argmax] <;> simp [arg_aux]
#align list.argmax_concat List.argmax_concat

/- warning: list.argmin_concat -> List.argmin_concat is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] (f : α -> β) (a : α) (l : List.{u1} α), Eq.{succ u1} (Option.{u1} α) (List.argmin.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l (List.cons.{u1} α a (List.nil.{u1} α)))) (Option.casesOn.{succ u1, u1} α (fun (_x : Option.{u1} α) => Option.{u1} α) (List.argmin.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l) (Option.some.{u1} α a) (fun (c : α) => ite.{succ u1} (Option.{u1} α) (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1) (f a) (f c)) (_inst_2 (f a) (f c)) (Option.some.{u1} α a) (Option.some.{u1} α c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1423 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1425 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1423 x._@.Mathlib.Data.List.MinMax._hyg.1425)] (f : α -> β) (a : α) (l : List.{u2} α), Eq.{succ u2} (Option.{u2} α) (List.argmin.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f (HAppend.hAppend.{u2, u2, u2} (List.{u2} α) (List.{u2} α) (List.{u2} α) (instHAppend.{u2} (List.{u2} α) (List.instAppendList.{u2} α)) l (List.cons.{u2} α a (List.nil.{u2} α)))) (Option.casesOn.{succ u2, u2} α (fun (_x : Option.{u2} α) => Option.{u2} α) (List.argmin.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l) (Option.some.{u2} α a) (fun (c : α) => ite.{succ u2} (Option.{u2} α) (LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) (f a) (f c)) (_inst_2 (f a) (f c)) (Option.some.{u2} α a) (Option.some.{u2} α c)))
Case conversion may be inaccurate. Consider using '#align list.argmin_concat List.argmin_concatₓ'. -/
theorem argmin_concat (f : α → β) (a : α) (l : List α) :
    argmin f (l ++ [a]) =
      Option.casesOn (argmin f l) (some a) fun c => if f a < f c then some a else some c :=
  @argmax_concat _ βᵒᵈ _ _ _ _ _
#align list.argmin_concat List.argmin_concat

/- warning: list.argmax_mem -> List.argmax_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] {f : α -> β} {l : List.{u1} α} {m : α}, (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmax.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l)) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) m l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1522 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1524 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1522 x._@.Mathlib.Data.List.MinMax._hyg.1524)] {f : α -> β} {l : List.{u2} α} {m : α}, (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmax.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l)) -> (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) m l)
Case conversion may be inaccurate. Consider using '#align list.argmax_mem List.argmax_memₓ'. -/
theorem argmax_mem : ∀ {l : List α} {m : α}, m ∈ argmax f l → m ∈ l
  | [], m => by simp
  | hd :: tl, m => by simpa [argmax, arg_aux] using foldl_arg_aux_mem _ tl hd m
#align list.argmax_mem List.argmax_mem

/- warning: list.argmin_mem -> List.argmin_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] {f : α -> β} {l : List.{u1} α} {m : α}, (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmin.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l)) -> (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) m l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1635 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1637 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1635 x._@.Mathlib.Data.List.MinMax._hyg.1637)] {f : α -> β} {l : List.{u2} α} {m : α}, (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmin.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l)) -> (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) m l)
Case conversion may be inaccurate. Consider using '#align list.argmin_mem List.argmin_memₓ'. -/
theorem argmin_mem : ∀ {l : List α} {m : α}, m ∈ argmin f l → m ∈ l :=
  @argmax_mem _ βᵒᵈ _ _ _
#align list.argmin_mem List.argmin_mem

/- warning: list.argmax_eq_none -> List.argmax_eq_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] {f : α -> β} {l : List.{u1} α}, Iff (Eq.{succ u1} (Option.{u1} α) (List.argmax.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l) (Option.none.{u1} α)) (Eq.{succ u1} (List.{u1} α) l (List.nil.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1694 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1696 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1694 x._@.Mathlib.Data.List.MinMax._hyg.1696)] {f : α -> β} {l : List.{u2} α}, Iff (Eq.{succ u2} (Option.{u2} α) (List.argmax.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l) (Option.none.{u2} α)) (Eq.{succ u2} (List.{u2} α) l (List.nil.{u2} α))
Case conversion may be inaccurate. Consider using '#align list.argmax_eq_none List.argmax_eq_noneₓ'. -/
@[simp]
theorem argmax_eq_none : l.argmax f = none ↔ l = [] := by simp [argmax]
#align list.argmax_eq_none List.argmax_eq_none

/- warning: list.argmin_eq_none -> List.argmin_eq_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] [_inst_2 : DecidableRel.{succ u2} β (LT.lt.{u2} β (Preorder.toLT.{u2} β _inst_1))] {f : α -> β} {l : List.{u1} α}, Iff (Eq.{succ u1} (Option.{u1} α) (List.argmin.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l) (Option.none.{u1} α)) (Eq.{succ u1} (List.{u1} α) l (List.nil.{u1} α))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u1} β] [_inst_2 : DecidableRel.{succ u1} β (fun (x._@.Mathlib.Data.List.MinMax._hyg.1749 : β) (x._@.Mathlib.Data.List.MinMax._hyg.1751 : β) => LT.lt.{u1} β (Preorder.toLT.{u1} β _inst_1) x._@.Mathlib.Data.List.MinMax._hyg.1749 x._@.Mathlib.Data.List.MinMax._hyg.1751)] {f : α -> β} {l : List.{u2} α}, Iff (Eq.{succ u2} (Option.{u2} α) (List.argmin.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f l) (Option.none.{u2} α)) (Eq.{succ u2} (List.{u2} α) l (List.nil.{u2} α))
Case conversion may be inaccurate. Consider using '#align list.argmin_eq_none List.argmin_eq_noneₓ'. -/
@[simp]
theorem argmin_eq_none : l.argmin f = none ↔ l = [] :=
  @argmax_eq_none _ βᵒᵈ _ _ _ _
#align list.argmin_eq_none List.argmin_eq_none

end Preorder

section LinearOrder

variable [LinearOrder β] {f : α → β} {l : List α} {o : Option α} {a m : α}

/- warning: list.le_of_mem_argmax -> List.le_of_mem_argmax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {f : α -> β} {l : List.{u1} α} {a : α} {m : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmax.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l)) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f m))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {f : α -> β} {l : List.{u2} α} {a : α} {m : α}, (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmax.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l)) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f a) (f m))
Case conversion may be inaccurate. Consider using '#align list.le_of_mem_argmax List.le_of_mem_argmaxₓ'. -/
theorem le_of_mem_argmax : a ∈ l → m ∈ argmax f l → f a ≤ f m := fun ha hm =>
  le_of_not_lt <| not_lt_of_mem_argmax ha hm
#align list.le_of_mem_argmax List.le_of_mem_argmax

/- warning: list.le_of_mem_argmin -> List.le_of_mem_argmin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {f : α -> β} {l : List.{u1} α} {a : α} {m : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmin.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l)) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f m) (f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {f : α -> β} {l : List.{u2} α} {a : α} {m : α}, (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmin.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l)) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f m) (f a))
Case conversion may be inaccurate. Consider using '#align list.le_of_mem_argmin List.le_of_mem_argminₓ'. -/
theorem le_of_mem_argmin : a ∈ l → m ∈ argmin f l → f m ≤ f a :=
  @le_of_mem_argmax _ βᵒᵈ _ _ _ _ _
#align list.le_of_mem_argmin List.le_of_mem_argmin

/- warning: list.argmax_cons -> List.argmax_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] (f : α -> β) (a : α) (l : List.{u1} α), Eq.{succ u1} (Option.{u1} α) (List.argmax.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f (List.cons.{u1} α a l)) (Option.casesOn.{succ u1, u1} α (fun (_x : Option.{u1} α) => Option.{u1} α) (List.argmax.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l) (Option.some.{u1} α a) (fun (c : α) => ite.{succ u1} (Option.{u1} α) (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f c)) (LT.lt.decidable.{u2} β _inst_1 (f a) (f c)) (Option.some.{u1} α c) (Option.some.{u1} α a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] (f : α -> β) (a : α) (l : List.{u2} α), Eq.{succ u2} (Option.{u2} α) (List.argmax.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f (List.cons.{u2} α a l)) (Option.casesOn.{succ u2, u2} α (fun (_x : Option.{u2} α) => Option.{u2} α) (List.argmax.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l) (Option.some.{u2} α a) (fun (c : α) => ite.{succ u2} (Option.{u2} α) (LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f a) (f c)) (instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 (f a) (f c)) (Option.some.{u2} α c) (Option.some.{u2} α a)))
Case conversion may be inaccurate. Consider using '#align list.argmax_cons List.argmax_consₓ'. -/
theorem argmax_cons (f : α → β) (a : α) (l : List α) :
    argmax f (a :: l) =
      Option.casesOn (argmax f l) (some a) fun c => if f a < f c then some c else some a :=
  List.reverseRecOn l rfl fun hd tl ih =>
    by
    rw [← cons_append, argmax_concat, ih, argmax_concat]
    cases' h : argmax f hd with m
    · simp [h]
    dsimp
    rw [← apply_ite, ← apply_ite]
    dsimp
    split_ifs <;> try rfl
    · exact absurd (lt_trans ‹f a < f m› ‹_›) ‹_›
    · cases (‹f a < f tl›.lt_or_lt _).elim ‹_› ‹_›
#align list.argmax_cons List.argmax_cons

/- warning: list.argmin_cons -> List.argmin_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] (f : α -> β) (a : α) (l : List.{u1} α), Eq.{succ u1} (Option.{u1} α) (List.argmin.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f (List.cons.{u1} α a l)) (Option.casesOn.{succ u1, u1} α (fun (_x : Option.{u1} α) => Option.{u1} α) (List.argmin.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l) (Option.some.{u1} α a) (fun (c : α) => ite.{succ u1} (Option.{u1} α) (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f c) (f a)) (LT.lt.decidable.{u2} β _inst_1 (f c) (f a)) (Option.some.{u1} α c) (Option.some.{u1} α a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] (f : α -> β) (a : α) (l : List.{u2} α), Eq.{succ u2} (Option.{u2} α) (List.argmin.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f (List.cons.{u2} α a l)) (Option.casesOn.{succ u2, u2} α (fun (_x : Option.{u2} α) => Option.{u2} α) (List.argmin.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l) (Option.some.{u2} α a) (fun (c : α) => ite.{succ u2} (Option.{u2} α) (LT.lt.{u1} β (Preorder.toLT.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f c) (f a)) (instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 (f c) (f a)) (Option.some.{u2} α c) (Option.some.{u2} α a)))
Case conversion may be inaccurate. Consider using '#align list.argmin_cons List.argmin_consₓ'. -/
theorem argmin_cons (f : α → β) (a : α) (l : List α) :
    argmin f (a :: l) =
      Option.casesOn (argmin f l) (some a) fun c => if f c < f a then some c else some a :=
  by convert @argmax_cons _ βᵒᵈ _ _ _ _
#align list.argmin_cons List.argmin_cons

variable [DecidableEq α]

/- warning: list.index_of_argmax -> List.index_of_argmax is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {f : α -> β} [_inst_2 : DecidableEq.{succ u1} α] {l : List.{u1} α} {m : α}, (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmax.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l)) -> (forall {a : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f m) (f a)) -> (LE.le.{0} Nat Nat.hasLe (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m l) (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a l)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {f : α -> β} [_inst_2 : DecidableEq.{succ u2} α] {l : List.{u2} α} {m : α}, (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmax.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l)) -> (forall {a : α}, (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f m) (f a)) -> (LE.le.{0} Nat instLENat (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) m l) (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a l)))
Case conversion may be inaccurate. Consider using '#align list.index_of_argmax List.index_of_argmaxₓ'. -/
theorem index_of_argmax :
    ∀ {l : List α} {m : α}, m ∈ argmax f l → ∀ {a}, a ∈ l → f m ≤ f a → l.indexOf m ≤ l.indexOf a
  | [], m, _, _, _, _ => by simp
  | hd :: tl, m, hm, a, ha, ham =>
    by
    simp only [index_of_cons, argmax_cons, Option.mem_def] at hm⊢
    cases h : argmax f tl
    · rw [h] at hm
      simp_all
    rw [h] at hm
    dsimp only at hm
    obtain rfl | ha := ha <;> split_ifs  at hm <;> subst hm
    · cases not_le_of_lt ‹_› ‹_›
    · rw [if_neg, if_neg]
      exact Nat.succ_le_succ (index_of_argmax h ha ham)
      · exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne'
      · exact ne_of_apply_ne _ ‹f hd < f val›.ne'
    · rw [if_pos rfl]
      exact bot_le
#align list.index_of_argmax List.index_of_argmax

/- warning: list.index_of_argmin -> List.index_of_argmin is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {f : α -> β} [_inst_2 : DecidableEq.{succ u1} α] {l : List.{u1} α} {m : α}, (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmin.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l)) -> (forall {a : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f m)) -> (LE.le.{0} Nat Nat.hasLe (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m l) (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a l)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {f : α -> β} [_inst_2 : DecidableEq.{succ u2} α] {l : List.{u2} α} {m : α}, (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmin.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l)) -> (forall {a : α}, (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f a) (f m)) -> (LE.le.{0} Nat instLENat (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) m l) (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a l)))
Case conversion may be inaccurate. Consider using '#align list.index_of_argmin List.index_of_argminₓ'. -/
theorem index_of_argmin :
    ∀ {l : List α} {m : α}, m ∈ argmin f l → ∀ {a}, a ∈ l → f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  @index_of_argmax _ βᵒᵈ _ _ _
#align list.index_of_argmin List.index_of_argmin

/- warning: list.mem_argmax_iff -> List.mem_argmax_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {f : α -> β} {l : List.{u1} α} {m : α} [_inst_2 : DecidableEq.{succ u1} α], Iff (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmax.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l)) (And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) m l) (And (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f m))) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f m) (f a)) -> (LE.le.{0} Nat Nat.hasLe (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m l) (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a l)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {f : α -> β} {l : List.{u2} α} {m : α} [_inst_2 : DecidableEq.{succ u2} α], Iff (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmax.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l)) (And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) m l) (And (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f a) (f m))) (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f m) (f a)) -> (LE.le.{0} Nat instLENat (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) m l) (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a l)))))
Case conversion may be inaccurate. Consider using '#align list.mem_argmax_iff List.mem_argmax_iffₓ'. -/
theorem mem_argmax_iff :
    m ∈ argmax f l ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.indexOf m ≤ l.indexOf a :=
  ⟨fun hm => ⟨argmax_mem hm, fun a ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩,
    by
    rintro ⟨hml, ham, hma⟩
    cases' harg : argmax f l with n
    · simp_all
    · have :=
        le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
          (index_of_argmax harg hml (ham _ (argmax_mem harg)))
      rw [(index_of_inj hml (argmax_mem harg)).1 this, Option.mem_def]⟩
#align list.mem_argmax_iff List.mem_argmax_iff

/- warning: list.argmax_eq_some_iff -> List.argmax_eq_some_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {f : α -> β} {l : List.{u1} α} {m : α} [_inst_2 : DecidableEq.{succ u1} α], Iff (Eq.{succ u1} (Option.{u1} α) (List.argmax.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l) (Option.some.{u1} α m)) (And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) m l) (And (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f m))) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f m) (f a)) -> (LE.le.{0} Nat Nat.hasLe (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m l) (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a l)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {f : α -> β} {l : List.{u2} α} {m : α} [_inst_2 : DecidableEq.{succ u2} α], Iff (Eq.{succ u2} (Option.{u2} α) (List.argmax.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l) (Option.some.{u2} α m)) (And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) m l) (And (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f a) (f m))) (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f m) (f a)) -> (LE.le.{0} Nat instLENat (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) m l) (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a l)))))
Case conversion may be inaccurate. Consider using '#align list.argmax_eq_some_iff List.argmax_eq_some_iffₓ'. -/
theorem argmax_eq_some_iff :
    argmax f l = some m ↔
      m ∈ l ∧ (∀ a ∈ l, f a ≤ f m) ∧ ∀ a ∈ l, f m ≤ f a → l.indexOf m ≤ l.indexOf a :=
  mem_argmax_iff
#align list.argmax_eq_some_iff List.argmax_eq_some_iff

/- warning: list.mem_argmin_iff -> List.mem_argmin_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {f : α -> β} {l : List.{u1} α} {m : α} [_inst_2 : DecidableEq.{succ u1} α], Iff (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) m (List.argmin.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l)) (And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) m l) (And (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f m) (f a))) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f m)) -> (LE.le.{0} Nat Nat.hasLe (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m l) (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a l)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {f : α -> β} {l : List.{u2} α} {m : α} [_inst_2 : DecidableEq.{succ u2} α], Iff (Membership.mem.{u2, u2} α (Option.{u2} α) (Option.instMembershipOption.{u2} α) m (List.argmin.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l)) (And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) m l) (And (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f m) (f a))) (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f a) (f m)) -> (LE.le.{0} Nat instLENat (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) m l) (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a l)))))
Case conversion may be inaccurate. Consider using '#align list.mem_argmin_iff List.mem_argmin_iffₓ'. -/
theorem mem_argmin_iff :
    m ∈ argmin f l ↔
      m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧ ∀ a ∈ l, f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  @mem_argmax_iff _ βᵒᵈ _ _ _ _ _
#align list.mem_argmin_iff List.mem_argmin_iff

/- warning: list.argmin_eq_some_iff -> List.argmin_eq_some_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LinearOrder.{u2} β] {f : α -> β} {l : List.{u1} α} {m : α} [_inst_2 : DecidableEq.{succ u1} α], Iff (Eq.{succ u1} (Option.{u1} α) (List.argmin.{u1, u2} α β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (fun (a : β) (b : β) => LT.lt.decidable.{u2} β _inst_1 a b) f l) (Option.some.{u1} α m)) (And (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) m l) (And (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f m) (f a))) (forall (a : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) a l) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f a) (f m)) -> (LE.le.{0} Nat Nat.hasLe (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) m l) (List.indexOfₓ.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a l)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LinearOrder.{u1} β] {f : α -> β} {l : List.{u2} α} {m : α} [_inst_2 : DecidableEq.{succ u2} α], Iff (Eq.{succ u2} (Option.{u2} α) (List.argmin.{u2, u1} α β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1))))) (fun (a : β) (b : β) => instDecidableLtToLTToPreorderToPartialOrder.{u1} β _inst_1 a b) f l) (Option.some.{u2} α m)) (And (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) m l) (And (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f m) (f a))) (forall (a : α), (Membership.mem.{u2, u2} α (List.{u2} α) (List.instMembershipList.{u2} α) a l) -> (LE.le.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β (SemilatticeInf.toPartialOrder.{u1} β (Lattice.toSemilatticeInf.{u1} β (DistribLattice.toLattice.{u1} β (instDistribLattice.{u1} β _inst_1)))))) (f a) (f m)) -> (LE.le.{0} Nat instLENat (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) m l) (List.indexOf.{u2} α (instBEq.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a l)))))
Case conversion may be inaccurate. Consider using '#align list.argmin_eq_some_iff List.argmin_eq_some_iffₓ'. -/
theorem argmin_eq_some_iff :
    argmin f l = some m ↔
      m ∈ l ∧ (∀ a ∈ l, f m ≤ f a) ∧ ∀ a ∈ l, f a ≤ f m → l.indexOf m ≤ l.indexOf a :=
  mem_argmin_iff
#align list.argmin_eq_some_iff List.argmin_eq_some_iff

end LinearOrder

section MaximumMinimum

section Preorder

variable [Preorder α] [@DecidableRel α (· < ·)] {l : List α} {a m : α}

#print List.maximum /-
/-- `maximum l` returns an `with_bot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]`  -/
def maximum (l : List α) : WithBot α :=
  argmax id l
#align list.maximum List.maximum
-/

#print List.minimum /-
/-- `minimum l` returns an `with_top α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`  -/
def minimum (l : List α) : WithTop α :=
  argmin id l
#align list.minimum List.minimum
-/

#print List.maximum_nil /-
@[simp]
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl
#align list.maximum_nil List.maximum_nil
-/

#print List.minimum_nil /-
@[simp]
theorem minimum_nil : minimum ([] : List α) = ⊤ :=
  rfl
#align list.minimum_nil List.minimum_nil
-/

#print List.maximum_singleton /-
@[simp]
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl
#align list.maximum_singleton List.maximum_singleton
-/

#print List.minimum_singleton /-
@[simp]
theorem minimum_singleton (a : α) : minimum [a] = a :=
  rfl
#align list.minimum_singleton List.minimum_singleton
-/

#print List.maximum_mem /-
theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m → m ∈ l :=
  argmax_mem
#align list.maximum_mem List.maximum_mem
-/

#print List.minimum_mem /-
theorem minimum_mem {l : List α} {m : α} : (minimum l : WithBot α) = m → m ∈ l :=
  argmin_mem
#align list.minimum_mem List.minimum_mem
-/

#print List.maximum_eq_none /-
@[simp]
theorem maximum_eq_none {l : List α} : l.maximum = none ↔ l = [] :=
  argmax_eq_none
#align list.maximum_eq_none List.maximum_eq_none
-/

#print List.minimum_eq_none /-
@[simp]
theorem minimum_eq_none {l : List α} : l.minimum = none ↔ l = [] :=
  argmin_eq_none
#align list.minimum_eq_none List.minimum_eq_none
-/

#print List.not_lt_maximum_of_mem /-
theorem not_lt_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → ¬m < a :=
  not_lt_of_mem_argmax
#align list.not_lt_maximum_of_mem List.not_lt_maximum_of_mem
-/

#print List.minimum_not_lt_of_mem /-
theorem minimum_not_lt_of_mem : a ∈ l → (minimum l : WithTop α) = m → ¬a < m :=
  not_lt_of_mem_argmin
#align list.minimum_not_lt_of_mem List.minimum_not_lt_of_mem
-/

#print List.not_lt_maximum_of_mem' /-
theorem not_lt_maximum_of_mem' (ha : a ∈ l) : ¬maximum l < (a : WithBot α) :=
  by
  cases h : l.maximum
  · simp_all
  · simp_rw [WithBot.some_eq_coe, WithBot.coe_lt_coe, not_lt_maximum_of_mem ha h, not_false_iff]
#align list.not_lt_maximum_of_mem' List.not_lt_maximum_of_mem'
-/

#print List.not_lt_minimum_of_mem' /-
theorem not_lt_minimum_of_mem' (ha : a ∈ l) : ¬(a : WithTop α) < minimum l :=
  @not_lt_maximum_of_mem' αᵒᵈ _ _ _ _ ha
#align list.not_lt_minimum_of_mem' List.not_lt_minimum_of_mem'
-/

end Preorder

section LinearOrder

variable [LinearOrder α] {l : List α} {a m : α}

#print List.maximum_concat /-
theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a :=
  by
  simp only [maximum, argmax_concat, id]
  cases h : argmax id l
  · exact (max_eq_right bot_le).symm
  · simp [Option.coe_def, max_def_lt]
#align list.maximum_concat List.maximum_concat
-/

#print List.le_maximum_of_mem /-
theorem le_maximum_of_mem : a ∈ l → (maximum l : WithBot α) = m → a ≤ m :=
  le_of_mem_argmax
#align list.le_maximum_of_mem List.le_maximum_of_mem
-/

#print List.minimum_le_of_mem /-
theorem minimum_le_of_mem : a ∈ l → (minimum l : WithTop α) = m → m ≤ a :=
  le_of_mem_argmin
#align list.minimum_le_of_mem List.minimum_le_of_mem
-/

#print List.le_maximum_of_mem' /-
theorem le_maximum_of_mem' (ha : a ∈ l) : (a : WithBot α) ≤ maximum l :=
  le_of_not_lt <| not_lt_maximum_of_mem' ha
#align list.le_maximum_of_mem' List.le_maximum_of_mem'
-/

#print List.le_minimum_of_mem' /-
theorem le_minimum_of_mem' (ha : a ∈ l) : minimum l ≤ (a : WithTop α) :=
  @le_maximum_of_mem' αᵒᵈ _ _ _ ha
#align list.le_minimum_of_mem' List.le_minimum_of_mem'
-/

#print List.minimum_concat /-
theorem minimum_concat (a : α) (l : List α) : minimum (l ++ [a]) = min (minimum l) a :=
  @maximum_concat αᵒᵈ _ _ _
#align list.minimum_concat List.minimum_concat
-/

#print List.maximum_cons /-
theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max a (maximum l) :=
  List.reverseRecOn l (by simp [@max_eq_left (WithBot α) _ _ _ bot_le]) fun tl hd ih => by
    rw [← cons_append, maximum_concat, ih, maximum_concat, max_assoc]
#align list.maximum_cons List.maximum_cons
-/

#print List.minimum_cons /-
theorem minimum_cons (a : α) (l : List α) : minimum (a :: l) = min a (minimum l) :=
  @maximum_cons αᵒᵈ _ _ _
#align list.minimum_cons List.minimum_cons
-/

#print List.maximum_eq_coe_iff /-
theorem maximum_eq_coe_iff : maximum l = m ↔ m ∈ l ∧ ∀ a ∈ l, a ≤ m :=
  by
  unfold_coes
  simp only [maximum, argmax_eq_some_iff, id]
  constructor
  · simp (config := { contextual := true }) only [true_and_iff, forall_true_iff]
  · simp (config := { contextual := true }) only [true_and_iff, forall_true_iff]
    intro h a hal hma
    rw [le_antisymm hma (h.2 a hal)]
#align list.maximum_eq_coe_iff List.maximum_eq_coe_iff
-/

#print List.minimum_eq_coe_iff /-
theorem minimum_eq_coe_iff : minimum l = m ↔ m ∈ l ∧ ∀ a ∈ l, m ≤ a :=
  @maximum_eq_coe_iff αᵒᵈ _ _ _
#align list.minimum_eq_coe_iff List.minimum_eq_coe_iff
-/

end LinearOrder

end MaximumMinimum

section Fold

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {l : List α}

/- warning: list.foldr_max_of_ne_nil -> List.foldr_max_of_ne_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {l : List.{u1} α}, (Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) -> (Eq.{succ u1} (WithBot.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithBot.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithBot.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithBot.{u1} α) (WithBot.hasCoeT.{u1} α))) (List.foldr.{u1, u1} α α (LinearOrder.max.{u1} α _inst_1) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2)) l)) (List.maximum.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] {l : List.{u1} α}, (Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) -> (Eq.{succ u1} (WithBot.{u1} α) (WithBot.some.{u1} α (List.foldr.{u1, u1} α α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) _inst_2)) l)) (List.maximum.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_1 a b) l))
Case conversion may be inaccurate. Consider using '#align list.foldr_max_of_ne_nil List.foldr_max_of_ne_nilₓ'. -/
@[simp]
theorem foldr_max_of_ne_nil (h : l ≠ []) : ↑(l.foldr max ⊥) = l.maximum :=
  by
  induction' l with hd tl IH
  · contradiction
  · rw [maximum_cons, foldr, WithBot.coe_max]
    by_cases h : tl = []
    · simp [h]
    · simp [IH h]
#align list.foldr_max_of_ne_nil List.foldr_max_of_ne_nil

/- warning: list.max_le_of_forall_le -> List.max_le_of_forall_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (l : List.{u1} α) (a : α), (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (List.foldr.{u1, u1} α α (LinearOrder.max.{u1} α _inst_1) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2)) l) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] (l : List.{u1} α) (a : α), (forall (x : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x a)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (List.foldr.{u1, u1} α α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) _inst_2)) l) a)
Case conversion may be inaccurate. Consider using '#align list.max_le_of_forall_le List.max_le_of_forall_leₓ'. -/
theorem max_le_of_forall_le (l : List α) (a : α) (h : ∀ x ∈ l, x ≤ a) : l.foldr max ⊥ ≤ a :=
  by
  induction' l with y l IH
  · simp
  · simpa [h y (mem_cons_self _ _)] using IH fun x hx => h x <| mem_cons_of_mem _ hx
#align list.max_le_of_forall_le List.max_le_of_forall_le

/- warning: list.le_max_of_le -> List.le_max_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {l : List.{u1} α} {a : α} {x : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a x) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (List.foldr.{u1, u1} α α (LinearOrder.max.{u1} α _inst_1) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2)) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] {l : List.{u1} α} {a : α} {x : α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a x) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (List.foldr.{u1, u1} α α (Max.max.{u1} α (LinearOrder.toMax.{u1} α _inst_1)) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) _inst_2)) l))
Case conversion may be inaccurate. Consider using '#align list.le_max_of_le List.le_max_of_leₓ'. -/
theorem le_max_of_le {l : List α} {a x : α} (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max ⊥ :=
  by
  induction' l with y l IH
  · exact absurd hx (not_mem_nil _)
  · obtain rfl | hl := hx
    simp only [foldr, foldr_cons]
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)
#align list.le_max_of_le List.le_max_of_le

end OrderBot

section OrderTop

variable [OrderTop α] {l : List α}

/- warning: list.foldr_min_of_ne_nil -> List.foldr_min_of_ne_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] {l : List.{u1} α}, (Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) -> (Eq.{succ u1} (WithTop.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithTop.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithTop.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithTop.{u1} α) (WithTop.hasCoeT.{u1} α))) (List.foldr.{u1, u1} α α (LinearOrder.min.{u1} α _inst_1) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2)) l)) (List.minimum.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))) (fun (a : α) (b : α) => LT.lt.decidable.{u1} α _inst_1 a b) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] {l : List.{u1} α}, (Ne.{succ u1} (List.{u1} α) l (List.nil.{u1} α)) -> (Eq.{succ u1} (WithTop.{u1} α) (WithTop.some.{u1} α (List.foldr.{u1, u1} α α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1)) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) _inst_2)) l)) (List.minimum.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))) (fun (a : α) (b : α) => instDecidableLtToLTToPreorderToPartialOrder.{u1} α _inst_1 a b) l))
Case conversion may be inaccurate. Consider using '#align list.foldr_min_of_ne_nil List.foldr_min_of_ne_nilₓ'. -/
@[simp]
theorem foldr_min_of_ne_nil (h : l ≠ []) : ↑(l.foldr min ⊤) = l.minimum :=
  @foldr_max_of_ne_nil αᵒᵈ _ _ _ h
#align list.foldr_min_of_ne_nil List.foldr_min_of_ne_nil

/- warning: list.le_min_of_forall_le -> List.le_min_of_forall_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (l : List.{u1} α) (a : α), (forall (x : α), (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) a (List.foldr.{u1, u1} α α (LinearOrder.min.{u1} α _inst_1) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2)) l))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] (l : List.{u1} α) (a : α), (forall (x : α), (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a x)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) a (List.foldr.{u1, u1} α α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1)) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) _inst_2)) l))
Case conversion may be inaccurate. Consider using '#align list.le_min_of_forall_le List.le_min_of_forall_leₓ'. -/
theorem le_min_of_forall_le (l : List α) (a : α) (h : ∀ x ∈ l, a ≤ x) : a ≤ l.foldr min ⊤ :=
  @max_le_of_forall_le αᵒᵈ _ _ _ _ h
#align list.le_min_of_forall_le List.le_min_of_forall_le

/- warning: list.min_le_of_le -> List.min_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1)))))] (l : List.{u1} α) (a : α) {x : α}, (Membership.Mem.{u1, u1} α (List.{u1} α) (List.hasMem.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) x a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) (List.foldr.{u1, u1} α α (LinearOrder.min.{u1} α _inst_1) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (LinearOrder.toLattice.{u1} α _inst_1))))) _inst_2)) l) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1))))))] (l : List.{u1} α) (a : α) {x : α}, (Membership.mem.{u1, u1} α (List.{u1} α) (List.instMembershipList.{u1} α) x l) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) x a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) (List.foldr.{u1, u1} α α (Min.min.{u1} α (LinearOrder.toMin.{u1} α _inst_1)) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (DistribLattice.toLattice.{u1} α (instDistribLattice.{u1} α _inst_1)))))) _inst_2)) l) a)
Case conversion may be inaccurate. Consider using '#align list.min_le_of_le List.min_le_of_leₓ'. -/
theorem min_le_of_le (l : List α) (a : α) {x : α} (hx : x ∈ l) (h : x ≤ a) : l.foldr min ⊤ ≤ a :=
  @le_max_of_le αᵒᵈ _ _ _ _ _ hx h
#align list.min_le_of_le List.min_le_of_le

end OrderTop

end Fold

end List

