/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module topology.bornology.constructions
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Bornology.Basic

/-!
# Bornology structure on products and subtypes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `bornology` and `bounded_space` instances on `α × β`, `Π i, π i`, and
`{x // p x}`. We also prove basic lemmas about `bornology.cobounded` and `bornology.is_bounded`
on these types.
-/


open Set Filter Bornology Function

open Filter

variable {α β ι : Type _} {π : ι → Type _} [Fintype ι] [Bornology α] [Bornology β]
  [∀ i, Bornology (π i)]

instance : Bornology (α × β)
    where
  cobounded := (cobounded α).coprod (cobounded β)
  le_cofinite :=
    @coprod_cofinite α β ▸ coprod_mono ‹Bornology α›.le_cofinite ‹Bornology β›.le_cofinite

instance : Bornology (∀ i, π i)
    where
  cobounded := Filter.coprodᵢ fun i => cobounded (π i)
  le_cofinite := @coprodᵢ_cofinite ι π _ ▸ Filter.coprodᵢ_mono fun i => Bornology.le_cofinite _

#print Bornology.induced /-
/-- Inverse image of a bornology. -/
@[reducible]
def Bornology.induced {α β : Type _} [Bornology β] (f : α → β) : Bornology α
    where
  cobounded := comap f (cobounded β)
  le_cofinite := (comap_mono (Bornology.le_cofinite β)).trans (comap_cofinite_le _)
#align bornology.induced Bornology.induced
-/

instance {p : α → Prop} : Bornology (Subtype p) :=
  Bornology.induced (coe : Subtype p → α)

namespace Bornology

/-!
### Bounded sets in `α × β`
-/


/- warning: bornology.cobounded_prod -> Bornology.cobounded_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β], Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (Prod.{u1, u2} α β)) (Bornology.cobounded.{max u1 u2} (Prod.{u1, u2} α β) (Prod.bornology.{u1, u2} α β _inst_2 _inst_3)) (Filter.coprod.{u1, u2} α β (Bornology.cobounded.{u1} α _inst_2) (Bornology.cobounded.{u2} β _inst_3))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : Bornology.{u2} α] [_inst_3 : Bornology.{u1} β], Eq.{max (succ u2) (succ u1)} (Filter.{max u1 u2} (Prod.{u2, u1} α β)) (Bornology.cobounded.{max u1 u2} (Prod.{u2, u1} α β) (instBornologyProd.{u2, u1} α β _inst_2 _inst_3)) (Filter.coprod.{u2, u1} α β (Bornology.cobounded.{u2} α _inst_2) (Bornology.cobounded.{u1} β _inst_3))
Case conversion may be inaccurate. Consider using '#align bornology.cobounded_prod Bornology.cobounded_prodₓ'. -/
theorem cobounded_prod : cobounded (α × β) = (cobounded α).coprod (cobounded β) :=
  rfl
#align bornology.cobounded_prod Bornology.cobounded_prod

/- warning: bornology.is_bounded_image_fst_and_snd -> Bornology.isBounded_image_fst_and_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{max u1 u2} (Prod.{u1, u2} α β)}, Iff (And (Bornology.IsBounded.{u1} α _inst_2 (Set.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s)) (Bornology.IsBounded.{u2} β _inst_3 (Set.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) s))) (Bornology.IsBounded.{max u1 u2} (Prod.{u1, u2} α β) (Prod.bornology.{u1, u2} α β _inst_2 _inst_3) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{max u2 u1} (Prod.{u1, u2} α β)}, Iff (And (Bornology.IsBounded.{u1} α _inst_2 (Set.image.{max u2 u1, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s)) (Bornology.IsBounded.{u2} β _inst_3 (Set.image.{max u2 u1, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) s))) (Bornology.IsBounded.{max u1 u2} (Prod.{u1, u2} α β) (instBornologyProd.{u1, u2} α β _inst_2 _inst_3) s)
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_image_fst_and_snd Bornology.isBounded_image_fst_and_sndₓ'. -/
theorem isBounded_image_fst_and_snd {s : Set (α × β)} :
    IsBounded (Prod.fst '' s) ∧ IsBounded (Prod.snd '' s) ↔ IsBounded s :=
  compl_mem_coprod.symm
#align bornology.is_bounded_image_fst_and_snd Bornology.isBounded_image_fst_and_snd

variable {s : Set α} {t : Set β} {S : ∀ i, Set (π i)}

/- warning: bornology.is_bounded.fst_of_prod -> Bornology.IsBounded.fst_of_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Bornology.IsBounded.{max u1 u2} (Prod.{u1, u2} α β) (Prod.bornology.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t)) -> (Set.Nonempty.{u2} β t) -> (Bornology.IsBounded.{u1} α _inst_2 s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Bornology.IsBounded.{max u2 u1} (Prod.{u1, u2} α β) (instBornologyProd.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t)) -> (Set.Nonempty.{u2} β t) -> (Bornology.IsBounded.{u1} α _inst_2 s)
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded.fst_of_prod Bornology.IsBounded.fst_of_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsBounded.fst_of_prod (h : IsBounded (s ×ˢ t)) (ht : t.Nonempty) : IsBounded s :=
  fst_image_prod s ht ▸ (isBounded_image_fst_and_snd.2 h).1
#align bornology.is_bounded.fst_of_prod Bornology.IsBounded.fst_of_prod

/- warning: bornology.is_bounded.snd_of_prod -> Bornology.IsBounded.snd_of_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Bornology.IsBounded.{max u1 u2} (Prod.{u1, u2} α β) (Prod.bornology.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t)) -> (Set.Nonempty.{u1} α s) -> (Bornology.IsBounded.{u2} β _inst_3 t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Bornology.IsBounded.{max u2 u1} (Prod.{u1, u2} α β) (instBornologyProd.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t)) -> (Set.Nonempty.{u1} α s) -> (Bornology.IsBounded.{u2} β _inst_3 t)
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded.snd_of_prod Bornology.IsBounded.snd_of_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsBounded.snd_of_prod (h : IsBounded (s ×ˢ t)) (hs : s.Nonempty) : IsBounded t :=
  snd_image_prod hs t ▸ (isBounded_image_fst_and_snd.2 h).2
#align bornology.is_bounded.snd_of_prod Bornology.IsBounded.snd_of_prod

/- warning: bornology.is_bounded.prod -> Bornology.IsBounded.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Bornology.IsBounded.{u1} α _inst_2 s) -> (Bornology.IsBounded.{u2} β _inst_3 t) -> (Bornology.IsBounded.{max u1 u2} (Prod.{u1, u2} α β) (Prod.bornology.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_2 : Bornology.{u2} α] [_inst_3 : Bornology.{u1} β] {s : Set.{u2} α} {t : Set.{u1} β}, (Bornology.IsBounded.{u2} α _inst_2 s) -> (Bornology.IsBounded.{u1} β _inst_3 t) -> (Bornology.IsBounded.{max u1 u2} (Prod.{u2, u1} α β) (instBornologyProd.{u2, u1} α β _inst_2 _inst_3) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded.prod Bornology.IsBounded.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem IsBounded.prod (hs : IsBounded s) (ht : IsBounded t) : IsBounded (s ×ˢ t) :=
  isBounded_image_fst_and_snd.1
    ⟨hs.subset <| fst_image_prod_subset _ _, ht.subset <| snd_image_prod_subset _ _⟩
#align bornology.is_bounded.prod Bornology.IsBounded.prod

/- warning: bornology.is_bounded_prod_of_nonempty -> Bornology.isBounded_prod_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) -> (Iff (Bornology.IsBounded.{max u1 u2} (Prod.{u1, u2} α β) (Prod.bornology.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t)) (And (Bornology.IsBounded.{u1} α _inst_2 s) (Bornology.IsBounded.{u2} β _inst_3 t)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{max u2 u1} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) -> (Iff (Bornology.IsBounded.{max u2 u1} (Prod.{u1, u2} α β) (instBornologyProd.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t)) (And (Bornology.IsBounded.{u1} α _inst_2 s) (Bornology.IsBounded.{u2} β _inst_3 t)))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_prod_of_nonempty Bornology.isBounded_prod_of_nonemptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem isBounded_prod_of_nonempty (hne : Set.Nonempty (s ×ˢ t)) :
    IsBounded (s ×ˢ t) ↔ IsBounded s ∧ IsBounded t :=
  ⟨fun h => ⟨h.fst_of_prod hne.snd, h.snd_of_prod hne.fst⟩, fun h => h.1.prod h.2⟩
#align bornology.is_bounded_prod_of_nonempty Bornology.isBounded_prod_of_nonempty

/- warning: bornology.is_bounded_prod -> Bornology.isBounded_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, Iff (Bornology.IsBounded.{max u1 u2} (Prod.{u1, u2} α β) (Prod.bornology.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t)) (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Or (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (And (Bornology.IsBounded.{u1} α _inst_2 s) (Bornology.IsBounded.{u2} β _inst_3 t))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_2 : Bornology.{u1} α] [_inst_3 : Bornology.{u2} β] {s : Set.{u1} α} {t : Set.{u2} β}, Iff (Bornology.IsBounded.{max u2 u1} (Prod.{u1, u2} α β) (instBornologyProd.{u1, u2} α β _inst_2 _inst_3) (Set.prod.{u1, u2} α β s t)) (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Or (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.instEmptyCollectionSet.{u2} β))) (And (Bornology.IsBounded.{u1} α _inst_2 s) (Bornology.IsBounded.{u2} β _inst_3 t))))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_prod Bornology.isBounded_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem isBounded_prod : IsBounded (s ×ˢ t) ↔ s = ∅ ∨ t = ∅ ∨ IsBounded s ∧ IsBounded t :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht); · simp
  simp only [hs.ne_empty, ht.ne_empty, isBounded_prod_of_nonempty (hs.prod ht), false_or_iff]
#align bornology.is_bounded_prod Bornology.isBounded_prod

/- warning: bornology.is_bounded_prod_self -> Bornology.isBounded_prod_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : Bornology.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} (Prod.{u1, u1} α α) (Prod.bornology.{u1, u1} α α _inst_2 _inst_2) (Set.prod.{u1, u1} α α s s)) (Bornology.IsBounded.{u1} α _inst_2 s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : Bornology.{u1} α] {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} (Prod.{u1, u1} α α) (instBornologyProd.{u1, u1} α α _inst_2 _inst_2) (Set.prod.{u1, u1} α α s s)) (Bornology.IsBounded.{u1} α _inst_2 s)
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_prod_self Bornology.isBounded_prod_selfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem isBounded_prod_self : IsBounded (s ×ˢ s) ↔ IsBounded s :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hs); · simp
  exact (isBounded_prod_of_nonempty (hs.prod hs)).trans (and_self_iff _)
#align bornology.is_bounded_prod_self Bornology.isBounded_prod_self

/-!
### Bounded sets in `Π i, π i`
-/


/- warning: bornology.cobounded_pi -> Bornology.cobounded_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_4 : forall (i : ι), Bornology.{u2} (π i)], Eq.{succ (max u1 u2)} (Filter.{max u1 u2} (forall (i : ι), π i)) (Bornology.cobounded.{max u1 u2} (forall (i : ι), π i) (Pi.bornology.{u1, u2} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i))) (Filter.coprodᵢ.{u1, u2} ι (fun (i : ι) => π i) (fun (i : ι) => Bornology.cobounded.{u2} (π i) (_inst_4 i)))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_4 : forall (i : ι), Bornology.{u1} (π i)], Eq.{max (succ u2) (succ u1)} (Filter.{max u2 u1} (forall (i : ι), π i)) (Bornology.cobounded.{max u2 u1} (forall (i : ι), π i) (instBornologyForAll.{u2, u1} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i))) (Filter.coprodᵢ.{u2, u1} ι (fun (i : ι) => π i) (fun (i : ι) => Bornology.cobounded.{u1} (π i) (_inst_4 i)))
Case conversion may be inaccurate. Consider using '#align bornology.cobounded_pi Bornology.cobounded_piₓ'. -/
theorem cobounded_pi : cobounded (∀ i, π i) = Filter.coprodᵢ fun i => cobounded (π i) :=
  rfl
#align bornology.cobounded_pi Bornology.cobounded_pi

/- warning: bornology.forall_is_bounded_image_eval_iff -> Bornology.forall_isBounded_image_eval_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_4 : forall (i : ι), Bornology.{u2} (π i)] {s : Set.{max u1 u2} (forall (i : ι), π i)}, Iff (forall (i : ι), Bornology.IsBounded.{u2} (π i) (_inst_4 i) (Set.image.{max u1 u2, u2} (forall (x : ι), π x) (π i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => π i) i) s)) (Bornology.IsBounded.{max u1 u2} (forall (i : ι), π i) (Pi.bornology.{u1, u2} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i)) s)
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_4 : forall (i : ι), Bornology.{u1} (π i)] {s : Set.{max u2 u1} (forall (i : ι), π i)}, Iff (forall (i : ι), Bornology.IsBounded.{u1} (π i) (_inst_4 i) (Set.image.{max u2 u1, u1} (forall (x : ι), π x) (π i) (Function.eval.{succ u2, succ u1} ι (fun (i : ι) => π i) i) s)) (Bornology.IsBounded.{max u2 u1} (forall (i : ι), π i) (instBornologyForAll.{u2, u1} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i)) s)
Case conversion may be inaccurate. Consider using '#align bornology.forall_is_bounded_image_eval_iff Bornology.forall_isBounded_image_eval_iffₓ'. -/
theorem forall_isBounded_image_eval_iff {s : Set (∀ i, π i)} :
    (∀ i, IsBounded (eval i '' s)) ↔ IsBounded s :=
  compl_mem_coprodᵢ.symm
#align bornology.forall_is_bounded_image_eval_iff Bornology.forall_isBounded_image_eval_iff

/- warning: bornology.is_bounded.pi -> Bornology.IsBounded.pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_4 : forall (i : ι), Bornology.{u2} (π i)] {S : forall (i : ι), Set.{u2} (π i)}, (forall (i : ι), Bornology.IsBounded.{u2} (π i) (_inst_4 i) (S i)) -> (Bornology.IsBounded.{max u1 u2} (forall (i : ι), π i) (Pi.bornology.{u1, u2} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) (Set.univ.{u1} ι) S))
but is expected to have type
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_4 : forall (i : ι), Bornology.{u2} (π i)] {S : forall (i : ι), Set.{u2} (π i)}, (forall (i : ι), Bornology.IsBounded.{u2} (π i) (_inst_4 i) (S i)) -> (Bornology.IsBounded.{max u2 u1} (forall (i : ι), π i) (instBornologyForAll.{u1, u2} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) (Set.univ.{u1} ι) S))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded.pi Bornology.IsBounded.piₓ'. -/
theorem IsBounded.pi (h : ∀ i, IsBounded (S i)) : IsBounded (pi univ S) :=
  forall_isBounded_image_eval_iff.1 fun i => (h i).subset eval_image_univ_pi_subset
#align bornology.is_bounded.pi Bornology.IsBounded.pi

/- warning: bornology.is_bounded_pi_of_nonempty -> Bornology.isBounded_pi_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_4 : forall (i : ι), Bornology.{u2} (π i)] {S : forall (i : ι), Set.{u2} (π i)}, (Set.Nonempty.{max u1 u2} (forall (i : ι), π i) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) (Set.univ.{u1} ι) S)) -> (Iff (Bornology.IsBounded.{max u1 u2} (forall (i : ι), π i) (Pi.bornology.{u1, u2} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) (Set.univ.{u1} ι) S)) (forall (i : ι), Bornology.IsBounded.{u2} (π i) (_inst_4 i) (S i)))
but is expected to have type
  forall {ι : Type.{u2}} {π : ι -> Type.{u1}} [_inst_1 : Fintype.{u2} ι] [_inst_4 : forall (i : ι), Bornology.{u1} (π i)] {S : forall (i : ι), Set.{u1} (π i)}, (Set.Nonempty.{max u2 u1} (forall (i : ι), π i) (Set.pi.{u2, u1} ι (fun (i : ι) => π i) (Set.univ.{u2} ι) S)) -> (Iff (Bornology.IsBounded.{max u1 u2} (forall (i : ι), π i) (instBornologyForAll.{u2, u1} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i)) (Set.pi.{u2, u1} ι (fun (i : ι) => π i) (Set.univ.{u2} ι) S)) (forall (i : ι), Bornology.IsBounded.{u1} (π i) (_inst_4 i) (S i)))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_pi_of_nonempty Bornology.isBounded_pi_of_nonemptyₓ'. -/
theorem isBounded_pi_of_nonempty (hne : (pi univ S).Nonempty) :
    IsBounded (pi univ S) ↔ ∀ i, IsBounded (S i) :=
  ⟨fun H i => @eval_image_univ_pi _ _ _ i hne ▸ forall_isBounded_image_eval_iff.2 H i, IsBounded.pi⟩
#align bornology.is_bounded_pi_of_nonempty Bornology.isBounded_pi_of_nonempty

/- warning: bornology.is_bounded_pi -> Bornology.isBounded_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_4 : forall (i : ι), Bornology.{u2} (π i)] {S : forall (i : ι), Set.{u2} (π i)}, Iff (Bornology.IsBounded.{max u1 u2} (forall (i : ι), π i) (Pi.bornology.{u1, u2} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) (Set.univ.{u1} ι) S)) (Or (Exists.{succ u1} ι (fun (i : ι) => Eq.{succ u2} (Set.{u2} (π i)) (S i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (π i)) (Set.hasEmptyc.{u2} (π i))))) (forall (i : ι), Bornology.IsBounded.{u2} (π i) (_inst_4 i) (S i)))
but is expected to have type
  forall {ι : Type.{u1}} {π : ι -> Type.{u2}} [_inst_1 : Fintype.{u1} ι] [_inst_4 : forall (i : ι), Bornology.{u2} (π i)] {S : forall (i : ι), Set.{u2} (π i)}, Iff (Bornology.IsBounded.{max u2 u1} (forall (i : ι), π i) (instBornologyForAll.{u1, u2} ι (fun (i : ι) => π i) _inst_1 (fun (i : ι) => _inst_4 i)) (Set.pi.{u1, u2} ι (fun (i : ι) => π i) (Set.univ.{u1} ι) S)) (Or (Exists.{succ u1} ι (fun (i : ι) => Eq.{succ u2} (Set.{u2} (π i)) (S i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (π i)) (Set.instEmptyCollectionSet.{u2} (π i))))) (forall (i : ι), Bornology.IsBounded.{u2} (π i) (_inst_4 i) (S i)))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_pi Bornology.isBounded_piₓ'. -/
theorem isBounded_pi : IsBounded (pi univ S) ↔ (∃ i, S i = ∅) ∨ ∀ i, IsBounded (S i) :=
  by
  by_cases hne : ∃ i, S i = ∅
  · simp [hne, univ_pi_eq_empty_iff.2 hne]
  · simp only [hne, false_or_iff]
    simp only [not_exists, ← Ne.def, ← nonempty_iff_ne_empty, ← univ_pi_nonempty_iff] at hne
    exact isBounded_pi_of_nonempty hne
#align bornology.is_bounded_pi Bornology.isBounded_pi

/-!
### Bounded sets in `{x // p x}`
-/


/- warning: bornology.is_bounded_induced -> Bornology.isBounded_induced is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_5 : Bornology.{u2} β] {f : α -> β} {s : Set.{u1} α}, Iff (Bornology.IsBounded.{u1} α (Bornology.induced.{u1, u2} α β _inst_5 f) s) (Bornology.IsBounded.{u2} β _inst_5 (Set.image.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_5 : Bornology.{u1} β] {f : α -> β} {s : Set.{u2} α}, Iff (Bornology.IsBounded.{u2} α (Bornology.induced.{u2, u1} α β _inst_5 f) s) (Bornology.IsBounded.{u1} β _inst_5 (Set.image.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align bornology.is_bounded_induced Bornology.isBounded_inducedₓ'. -/
theorem isBounded_induced {α β : Type _} [Bornology β] {f : α → β} {s : Set α} :
    @IsBounded α (Bornology.induced f) s ↔ IsBounded (f '' s) :=
  compl_mem_comap
#align bornology.is_bounded_induced Bornology.isBounded_induced

#print Bornology.isBounded_image_subtype_val /-
theorem isBounded_image_subtype_val {p : α → Prop} {s : Set { x // p x }} :
    IsBounded (coe '' s : Set α) ↔ IsBounded s :=
  isBounded_induced.symm
#align bornology.is_bounded_image_subtype_coe Bornology.isBounded_image_subtype_val
-/

end Bornology

/-!
### Bounded spaces
-/


open Bornology

instance [BoundedSpace α] [BoundedSpace β] : BoundedSpace (α × β) := by
  simp [← cobounded_eq_bot_iff, cobounded_prod]

instance [∀ i, BoundedSpace (π i)] : BoundedSpace (∀ i, π i) := by
  simp [← cobounded_eq_bot_iff, cobounded_pi]

/- warning: bounded_space_induced_iff -> boundedSpace_induced_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_5 : Bornology.{u2} β] {f : α -> β}, Iff (BoundedSpace.{u1} α (Bornology.induced.{u1, u2} α β _inst_5 f)) (Bornology.IsBounded.{u2} β _inst_5 (Set.range.{u2, succ u1} β α f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_5 : Bornology.{u1} β] {f : α -> β}, Iff (BoundedSpace.{u2} α (Bornology.induced.{u2, u1} α β _inst_5 f)) (Bornology.IsBounded.{u1} β _inst_5 (Set.range.{u1, succ u2} β α f))
Case conversion may be inaccurate. Consider using '#align bounded_space_induced_iff boundedSpace_induced_iffₓ'. -/
theorem boundedSpace_induced_iff {α β : Type _} [Bornology β] {f : α → β} :
    @BoundedSpace α (Bornology.induced f) ↔ IsBounded (range f) := by
  rw [← isBounded_univ, isBounded_induced, image_univ]
#align bounded_space_induced_iff boundedSpace_induced_iff

#print boundedSpace_subtype_iff /-
theorem boundedSpace_subtype_iff {p : α → Prop} :
    BoundedSpace (Subtype p) ↔ IsBounded { x | p x } := by
  rw [boundedSpace_induced_iff, Subtype.range_coe_subtype]
#align bounded_space_subtype_iff boundedSpace_subtype_iff
-/

#print boundedSpace_val_set_iff /-
theorem boundedSpace_val_set_iff {s : Set α} : BoundedSpace s ↔ IsBounded s :=
  boundedSpace_subtype_iff
#align bounded_space_coe_set_iff boundedSpace_val_set_iff
-/

alias boundedSpace_subtype_iff ↔ _ Bornology.IsBounded.boundedSpace_subtype
#align bornology.is_bounded.bounded_space_subtype Bornology.IsBounded.boundedSpace_subtype

alias boundedSpace_val_set_iff ↔ _ Bornology.IsBounded.boundedSpace_val
#align bornology.is_bounded.bounded_space_coe Bornology.IsBounded.boundedSpace_val

instance [BoundedSpace α] {p : α → Prop} : BoundedSpace (Subtype p) :=
  (IsBounded.all { x | p x }).boundedSpace_subtype

/-!
### `additive`, `multiplicative`

The bornology on those type synonyms is inherited without change.
-/


instance : Bornology (Additive α) :=
  ‹Bornology α›

instance : Bornology (Multiplicative α) :=
  ‹Bornology α›

instance [BoundedSpace α] : BoundedSpace (Additive α) :=
  ‹BoundedSpace α›

instance [BoundedSpace α] : BoundedSpace (Multiplicative α) :=
  ‹BoundedSpace α›

/-!
### Order dual

The bornology on this type synonym is inherited without change.
-/


instance : Bornology αᵒᵈ :=
  ‹Bornology α›

instance [BoundedSpace α] : BoundedSpace αᵒᵈ :=
  ‹BoundedSpace α›

