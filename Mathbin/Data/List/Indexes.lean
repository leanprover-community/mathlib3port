/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg

! This file was ported from Lean 3 source module data.list.indexes
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.OfFn
import Mathbin.Data.List.Range

/-!
# Lemmas about list.*_with_index functions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Some specification lemmas for `list.map_with_index`, `list.mmap_with_index`, `list.foldl_with_index`
and `list.foldr_with_index`.
-/


universe u v

open Function

namespace List

variable {α : Type u} {β : Type v}

section MapWithIndex

/- warning: list.map_with_index_nil -> List.mapIdx_nil is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Nat -> α -> β), Eq.{succ u2} (List.{u2} β) (List.mapIdx.{u1, u2} α β f (List.nil.{u1} α)) (List.nil.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Nat -> α -> β), Eq.{succ u1} (List.{u1} β) (List.mapIdx.{u2, u1} α β f (List.nil.{u2} α)) (List.nil.{u1} β)
Case conversion may be inaccurate. Consider using '#align list.map_with_index_nil List.mapIdx_nilₓ'. -/
@[simp]
theorem mapIdx_nil {α β} (f : ℕ → α → β) : mapIdx f [] = [] :=
  rfl
#align list.map_with_index_nil List.mapIdx_nil

/- warning: list.map_with_index_core_eq clashes with [anonymous] -> [anonymous]
warning: list.map_with_index_core_eq -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : Nat -> α -> β) (n : Nat), Eq.{succ u2} (List.{u2} β) ([anonymous].{u1, u2} α β f n l) (List.mapIdx.{u1, u2} α β (fun (i : Nat) (a : α) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i n) a) l)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β) -> Nat -> (List.{u1} α) -> (List.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.map_with_index_core_eq [anonymous]ₓ'. -/
theorem [anonymous] (l : List α) (f : ℕ → α → β) (n : ℕ) :
    l.map_with_index_core f n = l.mapIdx fun i a => f (i + n) a :=
  by
  induction' l with hd tl hl generalizing f n
  · simpa
  · rw [map_with_index]
    simp [map_with_index_core, hl, add_left_comm, add_assoc, add_comm]
#align list.map_with_index_core_eq [anonymous]

#print List.mapIdx_eq_enum_map /-
theorem mapIdx_eq_enum_map (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = l.enum.map (Function.uncurry f) :=
  by
  induction' l with hd tl hl generalizing f
  · simp [List.enum_eq_zip_range]
  · rw [map_with_index, map_with_index_core, map_with_index_core_eq, hl]
    simp [enum_eq_zip_range, range_succ_eq_map, zip_with_map_left, map_uncurry_zip_eq_zip_with]
#align list.map_with_index_eq_enum_map List.mapIdx_eq_enum_map
-/

/- warning: list.map_with_index_cons -> List.mapIdx_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : Nat -> α -> β) (a : α), Eq.{succ u2} (List.{u2} β) (List.mapIdx.{u1, u2} α β f (List.cons.{u1} α a l)) (List.cons.{u2} β (f (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) a) (List.mapIdx.{u1, u2} α β (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) l))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (f : Nat -> α -> β) (a : α), Eq.{succ u1} (List.{u1} β) (List.mapIdx.{u2, u1} α β f (List.cons.{u2} α a l)) (List.cons.{u1} β (f (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) a) (List.mapIdx.{u2, u1} α β (fun (i : Nat) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) l))
Case conversion may be inaccurate. Consider using '#align list.map_with_index_cons List.mapIdx_consₓ'. -/
@[simp]
theorem mapIdx_cons {α β} (l : List α) (f : ℕ → α → β) (a : α) :
    mapIdx f (a :: l) = f 0 a :: mapIdx (fun i => f (i + 1)) l := by
  simp [map_with_index_eq_enum_map, enum_eq_zip_range, map_uncurry_zip_eq_zip_with,
    range_succ_eq_map, zip_with_map_left]
#align list.map_with_index_cons List.mapIdx_cons

/- warning: list.map_with_index_append -> List.mapIdx_append is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {α : Type.{u2}} (K : List.{u2} α) (L : List.{u2} α) (f : Nat -> α -> β), Eq.{succ u1} (List.{u1} β) (List.mapIdx.{u2, u1} α β f (Append.append.{u2} (List.{u2} α) (List.hasAppend.{u2} α) K L)) (Append.append.{u1} (List.{u1} β) (List.hasAppend.{u1} β) (List.mapIdx.{u2, u1} α β f K) (List.mapIdx.{u2, u1} α β (fun (i : Nat) (a : α) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (List.length.{u2} α K)) a) L))
but is expected to have type
  forall {β : Type.{u2}} {α : Type.{u1}} (K : List.{u1} α) (L : List.{u1} α) (f : Nat -> α -> β), Eq.{succ u2} (List.{u2} β) (List.mapIdx.{u1, u2} α β f (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) K L)) (HAppend.hAppend.{u2, u2, u2} (List.{u2} β) (List.{u2} β) (List.{u2} β) (instHAppend.{u2} (List.{u2} β) (List.instAppendList.{u2} β)) (List.mapIdx.{u1, u2} α β f K) (List.mapIdx.{u1, u2} α β (fun (i : Nat) (a : α) => f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (List.length.{u1} α K)) a) L))
Case conversion may be inaccurate. Consider using '#align list.map_with_index_append List.mapIdx_appendₓ'. -/
theorem mapIdx_append {α} (K L : List α) (f : ℕ → α → β) :
    (K ++ L).mapIdx f = K.mapIdx f ++ L.mapIdx fun i a => f (i + K.length) a :=
  by
  induction' K with a J IH generalizing f
  · simp
  · simp [IH fun i => f (i + 1), add_assoc]
#align list.map_with_index_append List.mapIdx_append

/- warning: list.length_map_with_index -> List.length_mapIdx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : Nat -> α -> β), Eq.{1} Nat (List.length.{u2} β (List.mapIdx.{u1, u2} α β f l)) (List.length.{u1} α l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (f : Nat -> α -> β), Eq.{1} Nat (List.length.{u1} β (List.mapIdx.{u2, u1} α β f l)) (List.length.{u2} α l)
Case conversion may be inaccurate. Consider using '#align list.length_map_with_index List.length_mapIdxₓ'. -/
@[simp]
theorem length_mapIdx {α β} (l : List α) (f : ℕ → α → β) : (l.mapIdx f).length = l.length :=
  by
  induction' l with hd tl IH generalizing f
  · simp
  · simp [IH]
#align list.length_map_with_index List.length_mapIdx

/- warning: list.nth_le_map_with_index -> List.nthLe_mapIdx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : Nat -> α -> β) (i : Nat) (h : LT.lt.{0} Nat Nat.hasLt i (List.length.{u1} α l)) (h' : optParam.{0} (LT.lt.{0} Nat (Preorder.toLT.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) i (List.length.{u2} β (List.mapIdx.{u1, u2} α β f l))) (LT.lt.trans_le.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) i (List.length.{u1} α l) (List.length.{u2} β (List.mapIdx.{u1, u2} α β f l)) h (Eq.ge.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))) (List.length.{u2} β (List.mapIdx.{u1, u2} α β f l)) (List.length.{u1} α l) (List.length_mapIdx.{u1, u2} α β l f)))), Eq.{succ u2} β (List.nthLe.{u2} β (List.mapIdx.{u1, u2} α β f l) i h') (f i (List.nthLe.{u1} α l i h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (f : Nat -> α -> β) (i : Nat) (h : LT.lt.{0} Nat instLTNat i (List.length.{u2} α l)) (h' : optParam.{0} (LT.lt.{0} Nat instLTNat i (List.length.{u1} β (List.mapIdx.{u2, u1} α β f l))) (LT.lt.trans_le.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) i (List.length.{u2} α l) (List.length.{u1} β (List.mapIdx.{u2, u1} α β f l)) h (Eq.ge.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)) (List.length.{u1} β (List.mapIdx.{u2, u1} α β f l)) (List.length.{u2} α l) (List.length_mapIdx.{u1, u2} α β l f)))), Eq.{succ u1} β (List.nthLe.{u1} β (List.mapIdx.{u2, u1} α β f l) i h') (f i (List.nthLe.{u2} α l i h))
Case conversion may be inaccurate. Consider using '#align list.nth_le_map_with_index List.nthLe_mapIdxₓ'. -/
@[simp]
theorem nthLe_mapIdx {α β} (l : List α) (f : ℕ → α → β) (i : ℕ) (h : i < l.length)
    (h' : i < (l.mapIdx f).length := h.trans_le (l.length_mapIdx f).ge) :
    (l.mapIdx f).nthLe i h' = f i (l.nthLe i h) := by
  simp [map_with_index_eq_enum_map, enum_eq_zip_range]
#align list.nth_le_map_with_index List.nthLe_mapIdx

/- warning: list.map_with_index_eq_of_fn -> List.mapIdx_eq_ofFn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : List.{u1} α) (f : Nat -> α -> β), Eq.{succ u2} (List.{u2} β) (List.mapIdx.{u1, u2} α β f l) (List.ofFn.{u2} β (List.length.{u1} α l) (fun (i : Fin (List.length.{u1} α l)) => f ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} α l)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} α l)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} α l)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} α l)) Nat (Fin.coeToNat (List.length.{u1} α l))))) i) (List.nthLe.{u1} α l ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Fin (List.length.{u1} α l)) Nat (HasLiftT.mk.{1, 1} (Fin (List.length.{u1} α l)) Nat (CoeTCₓ.coe.{1, 1} (Fin (List.length.{u1} α l)) Nat (coeBase.{1, 1} (Fin (List.length.{u1} α l)) Nat (Fin.coeToNat (List.length.{u1} α l))))) i) (Fin.is_lt (List.length.{u1} α l) i))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : List.{u2} α) (f : Nat -> α -> β), Eq.{succ u1} (List.{u1} β) (List.mapIdx.{u2, u1} α β f l) (List.ofFn.{u1} β (List.length.{u2} α l) (fun (i : Fin (List.length.{u2} α l)) => f (Fin.val (List.length.{u2} α l) i) (List.get.{u2} α l i)))
Case conversion may be inaccurate. Consider using '#align list.map_with_index_eq_of_fn List.mapIdx_eq_ofFnₓ'. -/
theorem mapIdx_eq_ofFn {α β} (l : List α) (f : ℕ → α → β) :
    l.mapIdx f = ofFn fun i : Fin l.length => f (i : ℕ) (l.nthLe i i.is_lt) :=
  by
  induction' l with hd tl IH generalizing f
  · simp
  · simpa [IH]
#align list.map_with_index_eq_of_fn List.mapIdx_eq_ofFn

end MapWithIndex

section FoldrWithIndex

/-- Specification of `foldr_with_index_aux`. -/
def foldrIdxSpec (f : ℕ → α → β → β) (start : ℕ) (b : β) (as : List α) : β :=
  foldr (uncurry f) b <| enumFrom start as
#align list.foldr_with_index_aux_spec List.foldrIdxSpecₓ

theorem foldrIdxSpec_cons (f : ℕ → α → β → β) (start b a as) :
    foldrIdxSpec f start b (a :: as) = f start a (foldrIdxSpec f (start + 1) b as) :=
  rfl
#align list.foldr_with_index_aux_spec_cons List.foldrIdxSpec_consₓ

theorem foldrIdx_eq_foldrIdxSpec (f : ℕ → α → β → β) (start b as) :
    foldrWithIndexAux f start b as = foldrIdxSpec f start b as :=
  by
  induction as generalizing start
  · rfl
  · simp only [foldr_with_index_aux, foldr_with_index_aux_spec_cons, *]
#align list.foldr_with_index_aux_eq_foldr_with_index_aux_spec List.foldrIdx_eq_foldrIdxSpecₓ

/- warning: list.foldr_with_index_eq_foldr_enum -> List.foldrIdx_eq_foldr_enum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Nat -> α -> β -> β) (b : β) (as : List.{u1} α), Eq.{succ u2} β (List.foldrIdx.{u1, u2} α β f b as) (List.foldr.{u1, u2} (Prod.{0, u1} Nat α) β (Function.uncurry.{0, u1, u2} Nat α (β -> β) f) b (List.enum.{u1} α as))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Nat -> α -> β -> β) (b : β) (as : List.{u1} α), Eq.{succ u2} β (List.foldrIdx.{u1, succ u2} α β f b as (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (List.foldr.{u1, u2} (Prod.{0, u1} Nat α) β (Function.uncurry.{0, u1, u2} Nat α (β -> β) f) b (List.enum.{u1} α as))
Case conversion may be inaccurate. Consider using '#align list.foldr_with_index_eq_foldr_enum List.foldrIdx_eq_foldr_enumₓ'. -/
theorem foldrIdx_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : List α) :
    foldrIdx f b as = foldr (uncurry f) b (enum as) := by
  simp only [foldr_with_index, foldr_with_index_aux_spec,
    foldr_with_index_aux_eq_foldr_with_index_aux_spec, enum]
#align list.foldr_with_index_eq_foldr_enum List.foldrIdx_eq_foldr_enum

end FoldrWithIndex

#print List.indexesValues_eq_filter_enum /-
theorem indexesValues_eq_filter_enum (p : α → Prop) [DecidablePred p] (as : List α) :
    indexesValues p as = filter (p ∘ Prod.snd) (enum as) := by
  simp [indexes_values, foldr_with_index_eq_foldr_enum, uncurry, filter_eq_foldr]
#align list.indexes_values_eq_filter_enum List.indexesValues_eq_filter_enum
-/

#print List.findIdxs_eq_map_indexesValues /-
theorem findIdxs_eq_map_indexesValues (p : α → Prop) [DecidablePred p] (as : List α) :
    findIdxs p as = map Prod.fst (indexesValues p as) := by
  simp only [indexes_values_eq_filter_enum, map_filter_eq_foldr, find_indexes,
    foldr_with_index_eq_foldr_enum, uncurry]
#align list.find_indexes_eq_map_indexes_values List.findIdxs_eq_map_indexesValues
-/

section FoldlWithIndex

/-- Specification of `foldl_with_index_aux`. -/
def foldlIdxSpec (f : ℕ → α → β → α) (start : ℕ) (a : α) (bs : List β) : α :=
  foldl (fun a (p : ℕ × β) => f p.fst a p.snd) a <| enumFrom start bs
#align list.foldl_with_index_aux_spec List.foldlIdxSpecₓ

theorem foldlIdxSpec_cons (f : ℕ → α → β → α) (start a b bs) :
    foldlIdxSpec f start a (b :: bs) = foldlIdxSpec f (start + 1) (f start a b) bs :=
  rfl
#align list.foldl_with_index_aux_spec_cons List.foldlIdxSpec_consₓ

theorem foldlIdx_eq_foldlIdxSpec (f : ℕ → α → β → α) (start a bs) :
    foldlWithIndexAux f start a bs = foldlIdxSpec f start a bs :=
  by
  induction bs generalizing start a
  · rfl
  · simp [foldl_with_index_aux, foldl_with_index_aux_spec_cons, *]
#align list.foldl_with_index_aux_eq_foldl_with_index_aux_spec List.foldlIdx_eq_foldlIdxSpecₓ

/- warning: list.foldl_with_index_eq_foldl_enum -> List.foldlIdx_eq_foldl_enum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Nat -> α -> β -> α) (a : α) (bs : List.{u2} β), Eq.{succ u1} α (List.foldlIdx.{u1, u2} α β f a bs) (List.foldl.{u1, u2} α (Prod.{0, u2} Nat β) (fun (a : α) (p : Prod.{0, u2} Nat β) => f (Prod.fst.{0, u2} Nat β p) a (Prod.snd.{0, u2} Nat β p)) a (List.enum.{u2} β bs))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Nat -> α -> β -> α) (a : α) (bs : List.{u2} β), Eq.{succ u1} α (List.foldlIdx.{succ u1, u2} α β f a bs (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (List.foldl.{u1, u2} α (Prod.{0, u2} Nat β) (fun (a : α) (p : Prod.{0, u2} Nat β) => f (Prod.fst.{0, u2} Nat β p) a (Prod.snd.{0, u2} Nat β p)) a (List.enum.{u2} β bs))
Case conversion may be inaccurate. Consider using '#align list.foldl_with_index_eq_foldl_enum List.foldlIdx_eq_foldl_enumₓ'. -/
theorem foldlIdx_eq_foldl_enum (f : ℕ → α → β → α) (a : α) (bs : List β) :
    foldlIdx f a bs = foldl (fun a (p : ℕ × β) => f p.fst a p.snd) a (enum bs) := by
  simp only [foldl_with_index, foldl_with_index_aux_spec,
    foldl_with_index_aux_eq_foldl_with_index_aux_spec, enum]
#align list.foldl_with_index_eq_foldl_enum List.foldlIdx_eq_foldl_enum

end FoldlWithIndex

section MfoldWithIndex

variable {m : Type u → Type v} [Monad m]

/- warning: list.mfoldr_with_index_eq_mfoldr_enum -> List.foldrIdxM_eq_foldrM_enum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}} (f : Nat -> α -> β -> (m β)) (b : β) (as : List.{u3} α), Eq.{succ u2} (m β) (List.foldrIdxM.{u1, u2, u3} (fun {β : Type.{u1}} => m β) _inst_1 α β f b as) (List.foldrM.{u1, u2, u3} m _inst_1 β (Prod.{0, u3} Nat α) (Function.uncurry.{0, u3, max u1 u2} Nat α (β -> (m β)) f) b (List.enum.{u3} α as))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] {α : Type.{u1}} {β : Type.{u2}} (f : Nat -> α -> β -> (m β)) (b : β) (as : List.{u1} α) [inst._@.Mathlib.Data.List.Indexes._hyg.2615 : LawfulMonad.{u2, u3} m _inst_1], Eq.{succ u3} (m β) (List.foldrIdxM.{u2, u3, u1} m _inst_1 α β f b as) (List.foldrM.{u2, u3, u1} m _inst_1 β (Prod.{0, u1} Nat α) (Function.uncurry.{0, u1, max u3 u2} Nat α (β -> (m β)) f) b (List.enum.{u1} α as))
Case conversion may be inaccurate. Consider using '#align list.mfoldr_with_index_eq_mfoldr_enum List.foldrIdxM_eq_foldrM_enumₓ'. -/
theorem foldrIdxM_eq_foldrM_enum {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) :
    foldrIdxM f b as = foldrM (uncurry f) b (enum as) := by
  simp only [mfoldr_with_index, mfoldr_eq_foldr, foldr_with_index_eq_foldr_enum, uncurry]
#align list.mfoldr_with_index_eq_mfoldr_enum List.foldrIdxM_eq_foldrM_enum

/- warning: list.mfoldl_with_index_eq_mfoldl_enum -> List.foldlIdxM_eq_foldlM_enum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] [_inst_2 : LawfulMonad.{u1, u2} m _inst_1] {α : Type.{u3}} {β : Type.{u1}} (f : Nat -> β -> α -> (m β)) (b : β) (as : List.{u3} α), Eq.{succ u2} (m β) (List.foldlIdxM.{u1, u2, u3} (fun {β : Type.{u1}} => m β) _inst_1 α β f b as) (List.foldlM.{u1, u2, u3} m _inst_1 β (Prod.{0, u3} Nat α) (fun (b : β) (p : Prod.{0, u3} Nat α) => f (Prod.fst.{0, u3} Nat α p) b (Prod.snd.{0, u3} Nat α p)) b (List.enum.{u3} α as))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] [_inst_2 : LawfulMonad.{u2, u3} m _inst_1] {α : Type.{u1}} {β : Type.{u2}} (f : Nat -> β -> α -> (m β)) (b : β) (as : List.{u1} α), Eq.{succ u3} (m β) (List.foldlIdxM.{u2, u3, u1} m _inst_1 α β f b as) (List.foldlM.{u2, u3, u1} m _inst_1 β (Prod.{0, u1} Nat α) (fun (b : β) (p : Prod.{0, u1} Nat α) => f (Prod.fst.{0, u1} Nat α p) b (Prod.snd.{0, u1} Nat α p)) b (List.enum.{u1} α as))
Case conversion may be inaccurate. Consider using '#align list.mfoldl_with_index_eq_mfoldl_enum List.foldlIdxM_eq_foldlM_enumₓ'. -/
theorem foldlIdxM_eq_foldlM_enum [LawfulMonad m] {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) :
    foldlIdxM f b as = foldlM (fun b (p : ℕ × α) => f p.fst b p.snd) b (enum as) := by
  rw [mfoldl_with_index, mfoldl_eq_foldl, foldl_with_index_eq_foldl_enum]
#align list.mfoldl_with_index_eq_mfoldl_enum List.foldlIdxM_eq_foldlM_enum

end MfoldWithIndex

section MmapWithIndex

variable {m : Type u → Type v} [Applicative m]

/- warning: list.mmap_with_index_aux_spec -> List.mapIdxMAuxSpec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}}, (Nat -> α -> (m β)) -> Nat -> (List.{u3} α) -> (m (List.{u1} β))
but is expected to have type
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}}, (Nat -> α -> (m β)) -> Nat -> (List.{u3} α) -> (m (List.{u1} β))
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index_aux_spec List.mapIdxMAuxSpecₓ'. -/
/-- Specification of `mmap_with_index_aux`. -/
def mapIdxMAuxSpec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) : m (List β) :=
  List.traverse (uncurry f) <| enumFrom start as
#align list.mmap_with_index_aux_spec List.mapIdxMAuxSpec

/- warning: list.mmap_with_index_aux_spec_cons -> List.mapIdxMAuxSpec_cons is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}} (f : Nat -> α -> (m β)) (start : Nat) (a : α) (as : List.{u3} α), Eq.{succ u2} (m (List.{u1} β)) (List.mapIdxMAuxSpec.{u1, u2, u3} m _inst_1 α β f start (List.cons.{u3} α a as)) (Seq.seq.{u1, u2} m (Applicative.toHasSeq.{u1, u2} m _inst_1) (List.{u1} β) (List.{u1} β) (Functor.map.{u1, u2} m (Applicative.toFunctor.{u1, u2} m _inst_1) β ((List.{u1} β) -> (List.{u1} β)) (List.cons.{u1} β) (f start a)) (List.mapIdxMAuxSpec.{u1, u2, u3} m _inst_1 α β f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) start (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) as))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] {α : Type.{u1}} {β : Type.{u2}} (f : Nat -> α -> (m β)) (start : Nat) (a : α) (as : List.{u1} α), Eq.{succ u3} (m (List.{u2} β)) (List.mapIdxMAuxSpec.{u2, u3, u1} m _inst_1 α β f start (List.cons.{u1} α a as)) (Seq.seq.{u2, u3} m (Applicative.toSeq.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) (List.{u2} β) (List.{u2} β) (Functor.map.{u2, u3} m (Applicative.toFunctor.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) β ((List.{u2} β) -> (List.{u2} β)) (List.cons.{u2} β) (f start a)) (fun (x._@.Mathlib.Data.List.Indexes._hyg.2838 : Unit) => List.mapIdxMAuxSpec.{u2, u3, u1} m _inst_1 α β f (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) start (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) as))
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index_aux_spec_cons List.mapIdxMAuxSpec_consₓ'. -/
-- Note: `traverse` the class method would require a less universe-polymorphic
-- `m : Type u → Type u`.
theorem mapIdxMAuxSpec_cons {α β} (f : ℕ → α → m β) (start : ℕ) (a : α) (as : List α) :
    mapIdxMAuxSpec f start (a :: as) =
      List.cons <$> f start a <*> mapIdxMAuxSpec f (start + 1) as :=
  rfl
#align list.mmap_with_index_aux_spec_cons List.mapIdxMAuxSpec_cons

/- warning: list.mmap_with_index_aux_eq_mmap_with_index_aux_spec -> List.mapIdxMGo_eq_mapIdxMAuxSpec is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}} (f : Nat -> α -> (m β)) (start : Nat) (as : List.{u3} α), Eq.{succ u2} (m (List.{u1} β)) (List.mmapWithIndexAux.{u1, u2, u3} m _inst_1 α β f start as) (List.mapIdxMAuxSpec.{u1, u2, u3} m _inst_1 α β f start as)
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] [α : LawfulMonad.{u2, u3} m _inst_1] {β : Type.{u1}} {f : Type.{u2}} (start : Nat -> β -> (m f)) (as : Array.{u2} f) (as_1 : List.{u1} β), Eq.{succ u3} (m (List.{u2} f)) (List.mapIdxM.go.{u2, u3, u1} β f m _inst_1 start as_1 as) (Functor.map.{u2, u3} m (Applicative.toFunctor.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) (List.{u2} f) (List.{u2} f) (fun (x._@.Mathlib.Data.List.Indexes._hyg.2890 : List.{u2} f) => HAppend.hAppend.{u2, u2, u2} (List.{u2} f) (List.{u2} f) (List.{u2} f) (instHAppend.{u2} (List.{u2} f) (List.instAppendList.{u2} f)) (Array.toList.{u2} f as) x._@.Mathlib.Data.List.Indexes._hyg.2890) (List.mapIdxMAuxSpec.{u2, u3, u1} m _inst_1 β f start (Array.size.{u2} f as) as_1))
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index_aux_eq_mmap_with_index_aux_spec List.mapIdxMGo_eq_mapIdxMAuxSpecₓ'. -/
theorem mapIdxMGo_eq_mapIdxMAuxSpec {α β} (f : ℕ → α → m β) (start : ℕ) (as : List α) :
    mmapWithIndexAux f start as = mapIdxMAuxSpec f start as :=
  by
  induction as generalizing start
  · rfl
  · simp [mmap_with_index_aux, mmap_with_index_aux_spec_cons, *]
#align list.mmap_with_index_aux_eq_mmap_with_index_aux_spec List.mapIdxMGo_eq_mapIdxMAuxSpec

/- warning: list.mmap_with_index_eq_mmap_enum -> List.mapIdxM_eq_mmap_enum is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}} (f : Nat -> α -> (m β)) (as : List.{u3} α), Eq.{succ u2} (m (List.{u1} β)) (List.mapIdxM.{u1, u2, u3} m _inst_1 α β f as) (List.traverse.{u1, u2, u3} m _inst_1 (Prod.{0, u3} Nat α) β (Function.uncurry.{0, u3, u2} Nat α (m β) f) (List.enum.{u3} α as))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] [α : LawfulMonad.{u2, u3} m _inst_1] {β : Type.{u1}} {f : Type.{u2}} (as : Nat -> β -> (m f)) (as_1 : List.{u1} β), Eq.{succ u3} (m (List.{u2} f)) (List.mapIdxM.{u2, u3, u1} β f m _inst_1 as_1 as) (List.traverse.{u2, u3, u1} m (Monad.toApplicative.{u2, u3} m _inst_1) (Prod.{0, u1} Nat β) f (Function.uncurry.{0, u1, u3} Nat β (m f) as) (List.enum.{u1} β as_1))
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index_eq_mmap_enum List.mapIdxM_eq_mmap_enumₓ'. -/
theorem mapIdxM_eq_mmap_enum {α β} (f : ℕ → α → m β) (as : List α) :
    mapIdxM f as = List.traverse (uncurry f) (enum as) := by
  simp only [mmap_with_index, mmap_with_index_aux_spec,
    mmap_with_index_aux_eq_mmap_with_index_aux_spec, enum]
#align list.mmap_with_index_eq_mmap_enum List.mapIdxM_eq_mmap_enum

end MmapWithIndex

section MmapWithIndex'

variable {m : Type u → Type v} [Applicative m] [LawfulApplicative m]

/- warning: list.mmap_with_index'_aux_eq_mmap_with_index_aux -> List.mapIdxMAux'_eq_mapIdxMGo is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] [_inst_2 : LawfulApplicative.{u1, u2} m _inst_1] {α : Type.{u3}} (f : Nat -> α -> (m PUnit.{succ u1})) (start : Nat) (as : List.{u3} α), Eq.{succ u2} (m PUnit.{succ u1}) (List.mapIdxMAux'.{u1, u2, u3} m _inst_1 α f start as) (SeqRight.seqRight.{u1, u2} m (Applicative.toHasSeqRight.{u1, u2} m _inst_1) (List.{u1} PUnit.{succ u1}) PUnit.{succ u1} (List.mmapWithIndexAux.{u1, u2, u3} m _inst_1 α PUnit.{succ u1} f start as) (Pure.pure.{u1, u2} m (Applicative.toHasPure.{u1, u2} m _inst_1) PUnit.{succ u1} PUnit.unit.{succ u1}))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] [_inst_2 : LawfulMonad.{u2, u3} m _inst_1] {α : Type.{u1}} (f : Nat -> α -> (m PUnit.{succ u2})) (start : List.{u1} α) (as : Array.{u2} PUnit.{succ u2}), Eq.{succ u3} (m PUnit.{succ u2}) (List.mapIdxMAux'.{u2, u3, u1} m _inst_1 α f (Array.size.{u2} PUnit.{succ u2} as) start) (SeqRight.seqRight.{u2, u3} m (Applicative.toSeqRight.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) (List.{u2} PUnit.{succ u2}) PUnit.{succ u2} (List.mapIdxM.go.{u2, u3, u1} α PUnit.{succ u2} m _inst_1 f start as) (fun (x._@.Mathlib.Data.List.Indexes._hyg.3196 : Unit) => Pure.pure.{u2, u3} m (Applicative.toPure.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) PUnit.{succ u2} PUnit.unit.{succ u2}))
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index'_aux_eq_mmap_with_index_aux List.mapIdxMAux'_eq_mapIdxMGoₓ'. -/
theorem mapIdxMAux'_eq_mapIdxMGo {α} (f : ℕ → α → m PUnit) (start : ℕ) (as : List α) :
    mapIdxMAux' f start as = mmapWithIndexAux f start as *> pure PUnit.unit := by
  induction as generalizing start <;>
    simp [mmap_with_index'_aux, mmap_with_index_aux, *, seq_right_eq, const, -comp_const,
      functor_norm]
#align list.mmap_with_index'_aux_eq_mmap_with_index_aux List.mapIdxMAux'_eq_mapIdxMGo

/- warning: list.mmap_with_index'_eq_mmap_with_index -> List.mapIdxM'_eq_mapIdxM is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] [_inst_2 : LawfulApplicative.{u1, u2} m _inst_1] {α : Type.{u3}} (f : Nat -> α -> (m PUnit.{succ u1})) (as : List.{u3} α), Eq.{succ u2} (m PUnit.{succ u1}) (List.mapIdxM'.{u1, u2, u3} m _inst_1 α f as) (SeqRight.seqRight.{u1, u2} m (Applicative.toHasSeqRight.{u1, u2} m _inst_1) (List.{u1} PUnit.{succ u1}) PUnit.{succ u1} (List.mapIdxM.{u1, u2, u3} m _inst_1 α PUnit.{succ u1} f as) (Pure.pure.{u1, u2} m (Applicative.toHasPure.{u1, u2} m _inst_1) PUnit.{succ u1} PUnit.unit.{succ u1}))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Monad.{u2, u3} m] [_inst_2 : LawfulMonad.{u2, u3} m _inst_1] {α : Type.{u1}} (f : Nat -> α -> (m PUnit.{succ u2})) (as : List.{u1} α), Eq.{succ u3} (m PUnit.{succ u2}) (List.mapIdxM'.{u2, u3, u1} m _inst_1 α f as) (SeqRight.seqRight.{u2, u3} m (Applicative.toSeqRight.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) (List.{u2} PUnit.{succ u2}) PUnit.{succ u2} (List.mapIdxM.{u2, u3, u1} α PUnit.{succ u2} m _inst_1 as f) (fun (x._@.Mathlib.Data.List.Indexes._hyg.3370 : Unit) => Pure.pure.{u2, u3} m (Applicative.toPure.{u2, u3} m (Monad.toApplicative.{u2, u3} m _inst_1)) PUnit.{succ u2} PUnit.unit.{succ u2}))
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index'_eq_mmap_with_index List.mapIdxM'_eq_mapIdxMₓ'. -/
theorem mapIdxM'_eq_mapIdxM {α} (f : ℕ → α → m PUnit) (as : List α) :
    mapIdxM' f as = mapIdxM f as *> pure PUnit.unit := by
  apply mmap_with_index'_aux_eq_mmap_with_index_aux
#align list.mmap_with_index'_eq_mmap_with_index List.mapIdxM'_eq_mapIdxM

end MmapWithIndex'

end List

