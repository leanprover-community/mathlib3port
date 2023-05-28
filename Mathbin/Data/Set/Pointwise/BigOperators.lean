/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.set.pointwise.big_operators
! leanprover-community/mathlib commit fa2cb8a9e2b987db233e4e6eb47645feafba8861
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Set.Pointwise.Basic

/-!
# Results about pointwise operations on sets and big operators.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Set

open BigOperators Pointwise

open Function

variable {ι α β F : Type _}

section Monoid

variable [Monoid α] [Monoid β] [MonoidHomClass F α β]

/- warning: set.image_list_prod -> Set.image_list_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {F : Type.{u3}} [_inst_1 : Monoid.{u1} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MonoidHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)] (f : F) (l : List.{u1} (Set.{u1} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2) _inst_3))) f) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) l)) (List.prod.{u2} (Set.{u2} β) (Set.mul.{u2} β (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (Set.one.{u2} β (MulOneClass.toHasOne.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (List.map.{u1, u2} (Set.{u1} α) (Set.{u2} β) (fun (s : Set.{u1} α) => Set.image.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1)) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2) _inst_3))) f) s) l))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {F : Type.{u1}} [_inst_1 : Monoid.{u3} α] [_inst_2 : Monoid.{u2} β] [_inst_3 : MonoidHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2)] (f : F) (l : List.{u3} (Set.{u3} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α _inst_1)) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2) _inst_3)) f) (List.prod.{u3} (Set.{u3} α) (Set.mul.{u3} α (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α _inst_1))) (Set.one.{u3} α (Monoid.toOne.{u3} α _inst_1)) l)) (List.prod.{u2} (Set.{u2} β) (Set.mul.{u2} β (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2))) (Set.one.{u2} β (Monoid.toOne.{u2} β _inst_2)) (List.map.{u3, u2} (Set.{u3} α) (Set.{u2} β) (fun (s : Set.{u3} α) => Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α _inst_1)) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α _inst_1) (Monoid.toMulOneClass.{u2} β _inst_2) _inst_3)) f) s) l))
Case conversion may be inaccurate. Consider using '#align set.image_list_prod Set.image_list_prodₓ'. -/
@[to_additive]
theorem image_list_prod (f : F) :
    ∀ l : List (Set α), (f : α → β) '' l.Prod = (l.map fun s => f '' s).Prod
  | [] => image_one.trans <| congr_arg singleton (map_one f)
  | a :: as => by rw [List.map_cons, List.prod_cons, List.prod_cons, image_mul, image_list_prod]
#align set.image_list_prod Set.image_list_prod
#align set.image_list_sum Set.image_list_sum

end Monoid

section CommMonoid

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

/- warning: set.image_multiset_prod -> Set.image_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {F : Type.{u3}} [_inst_1 : CommMonoid.{u1} α] [_inst_2 : CommMonoid.{u2} β] [_inst_3 : MonoidHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))] (f : F) (m : Multiset.{u1} (Set.{u1} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3))) f) (Multiset.prod.{u1} (Set.{u1} α) (Set.commMonoid.{u1} α _inst_1) m)) (Multiset.prod.{u2} (Set.{u2} β) (Set.commMonoid.{u2} β _inst_2) (Multiset.map.{u1, u2} (Set.{u1} α) (Set.{u2} β) (fun (s : Set.{u1} α) => Set.image.{u1, u2} α β (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u3, u1, u2} F α β (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F α β (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3))) f) s) m))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {F : Type.{u1}} [_inst_1 : CommMonoid.{u3} α] [_inst_2 : CommMonoid.{u2} β] [_inst_3 : MonoidHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))] (f : F) (m : Multiset.{u3} (Set.{u3} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3)) f) (Multiset.prod.{u3} (Set.{u3} α) (Set.commMonoid.{u3} α _inst_1) m)) (Multiset.prod.{u2} (Set.{u2} β) (Set.commMonoid.{u2} β _inst_2) (Multiset.map.{u3, u2} (Set.{u3} α) (Set.{u2} β) (fun (s : Set.{u3} α) => Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3)) f) s) m))
Case conversion may be inaccurate. Consider using '#align set.image_multiset_prod Set.image_multiset_prodₓ'. -/
@[to_additive]
theorem image_multiset_prod (f : F) :
    ∀ m : Multiset (Set α), (f : α → β) '' m.Prod = (m.map fun s => f '' s).Prod :=
  Quotient.ind <| by
    simpa only [Multiset.quot_mk_to_coe, Multiset.coe_prod, Multiset.coe_map] using
      image_list_prod f
#align set.image_multiset_prod Set.image_multiset_prod
#align set.image_multiset_sum Set.image_multiset_sum

/- warning: set.image_finset_prod -> Set.image_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {F : Type.{u4}} [_inst_1 : CommMonoid.{u2} α] [_inst_2 : CommMonoid.{u3} β] [_inst_3 : MonoidHomClass.{u4, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))] (f : F) (m : Finset.{u1} ι) (s : ι -> (Set.{u2} α)), Eq.{succ u3} (Set.{u3} β) (Set.image.{u2, u3} α β (coeFn.{succ u4, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u4, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))) (MonoidHomClass.toMulHomClass.{u4, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)) _inst_3))) f) (Finset.prod.{u2, u1} (Set.{u2} α) ι (Set.commMonoid.{u2} α _inst_1) m (fun (i : ι) => s i))) (Finset.prod.{u3, u1} (Set.{u3} β) ι (Set.commMonoid.{u3} β _inst_2) m (fun (i : ι) => Set.image.{u2, u3} α β (coeFn.{succ u4, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u4, u2, u3} F α β (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toHasMul.{u3} β (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2))) (MonoidHomClass.toMulHomClass.{u4, u2, u3} F α β (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)) (Monoid.toMulOneClass.{u3} β (CommMonoid.toMonoid.{u3} β _inst_2)) _inst_3))) f) (s i)))
but is expected to have type
  forall {ι : Type.{u4}} {α : Type.{u3}} {β : Type.{u2}} {F : Type.{u1}} [_inst_1 : CommMonoid.{u3} α] [_inst_2 : CommMonoid.{u2} β] [_inst_3 : MonoidHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))] (f : F) (m : Finset.{u4} ι) (s : ι -> (Set.{u3} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3)) f) (Finset.prod.{u3, u4} (Set.{u3} α) ι (Set.commMonoid.{u3} α _inst_1) m (fun (i : ι) => s i))) (Finset.prod.{u2, u4} (Set.{u2} β) ι (Set.commMonoid.{u2} β _inst_2) m (fun (i : ι) => Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1))) (MulOneClass.toMul.{u2} β (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β (Monoid.toMulOneClass.{u3} α (CommMonoid.toMonoid.{u3} α _inst_1)) (Monoid.toMulOneClass.{u2} β (CommMonoid.toMonoid.{u2} β _inst_2)) _inst_3)) f) (s i)))
Case conversion may be inaccurate. Consider using '#align set.image_finset_prod Set.image_finset_prodₓ'. -/
@[to_additive]
theorem image_finset_prod (f : F) (m : Finset ι) (s : ι → Set α) :
    ((f : α → β) '' ∏ i in m, s i) = ∏ i in m, f '' s i :=
  (image_multiset_prod f _).trans <| congr_arg Multiset.prod <| Multiset.map_map _ _ _
#align set.image_finset_prod Set.image_finset_prod
#align set.image_finset_sum Set.image_finset_sum

/- warning: set.mem_finset_prod -> Set.mem_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (t : Finset.{u1} ι) (f : ι -> (Set.{u2} α)) (a : α), Iff (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) a (Finset.prod.{u2, u1} (Set.{u2} α) ι (Set.commMonoid.{u2} α _inst_1) t (fun (i : ι) => f i))) (Exists.{max (succ u1) (succ u2)} (ι -> α) (fun (g : ι -> α) => Exists.{0} (forall {i : ι}, (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i t) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (g i) (f i))) (fun (hg : forall {i : ι}, (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i t) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (g i) (f i))) => Eq.{succ u2} α (Finset.prod.{u2, u1} α ι _inst_1 t (fun (i : ι) => g i)) a)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (t : Finset.{u2} ι) (f : ι -> (Set.{u1} α)) (a : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Finset.prod.{u1, u2} (Set.{u1} α) ι (Set.commMonoid.{u1} α _inst_1) t (fun (i : ι) => f i))) (Exists.{max (succ u2) (succ u1)} (ι -> α) (fun (g : ι -> α) => Exists.{0} (forall {i : ι}, (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (g i) (f i))) (fun (hg : forall {i : ι}, (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (g i) (f i))) => Eq.{succ u1} α (Finset.prod.{u1, u2} α ι _inst_1 t (fun (i : ι) => g i)) a)))
Case conversion may be inaccurate. Consider using '#align set.mem_finset_prod Set.mem_finset_prodₓ'. -/
/-- The n-ary version of `set.mem_mul`. -/
@[to_additive " The n-ary version of `set.mem_add`. "]
theorem mem_finset_prod (t : Finset ι) (f : ι → Set α) (a : α) :
    (a ∈ ∏ i in t, f i) ↔ ∃ (g : ι → α)(hg : ∀ {i}, i ∈ t → g i ∈ f i), (∏ i in t, g i) = a := by
  classical
    induction' t using Finset.induction_on with i is hi ih generalizing a
    · simp_rw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h => ⟨fun i => a, fun i => False.elim, h.symm⟩, fun ⟨f, _, hf⟩ => hf.symm⟩
    rw [Finset.prod_insert hi, Set.mem_mul]
    simp_rw [Finset.prod_insert hi]
    simp_rw [ih]
    constructor
    · rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
      refine' ⟨Function.update g i x, fun j hj => _, _⟩
      obtain rfl | hj := finset.mem_insert.mp hj
      · rw [Function.update_same]; exact hx
      · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]; exact hg hj
      rw [Finset.prod_update_of_not_mem hi, Function.update_same]
    · rintro ⟨g, hg, rfl⟩
      exact
        ⟨g i, is.prod g, hg (is.mem_insert_self _),
          ⟨g, fun i hi => hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩
#align set.mem_finset_prod Set.mem_finset_prod
#align set.mem_finset_sum Set.mem_finset_sum

/- warning: set.mem_fintype_prod -> Set.mem_fintype_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] [_inst_4 : Fintype.{u1} ι] (f : ι -> (Set.{u2} α)) (a : α), Iff (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) a (Finset.prod.{u2, u1} (Set.{u2} α) ι (Set.commMonoid.{u2} α _inst_1) (Finset.univ.{u1} ι _inst_4) (fun (i : ι) => f i))) (Exists.{max (succ u1) (succ u2)} (ι -> α) (fun (g : ι -> α) => Exists.{0} (forall (i : ι), Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (g i) (f i)) (fun (hg : forall (i : ι), Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (g i) (f i)) => Eq.{succ u2} α (Finset.prod.{u2, u1} α ι _inst_1 (Finset.univ.{u1} ι _inst_4) (fun (i : ι) => g i)) a)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] [_inst_4 : Fintype.{u2} ι] (f : ι -> (Set.{u1} α)) (a : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Finset.prod.{u1, u2} (Set.{u1} α) ι (Set.commMonoid.{u1} α _inst_1) (Finset.univ.{u2} ι _inst_4) (fun (i : ι) => f i))) (Exists.{max (succ u2) (succ u1)} (ι -> α) (fun (g : ι -> α) => Exists.{0} (forall (i : ι), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (g i) (f i)) (fun (hg : forall (i : ι), Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (g i) (f i)) => Eq.{succ u1} α (Finset.prod.{u1, u2} α ι _inst_1 (Finset.univ.{u2} ι _inst_4) (fun (i : ι) => g i)) a)))
Case conversion may be inaccurate. Consider using '#align set.mem_fintype_prod Set.mem_fintype_prodₓ'. -/
/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[to_additive " A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "]
theorem mem_fintype_prod [Fintype ι] (f : ι → Set α) (a : α) :
    (a ∈ ∏ i, f i) ↔ ∃ (g : ι → α)(hg : ∀ i, g i ∈ f i), (∏ i, g i) = a := by rw [mem_finset_prod];
  simp
#align set.mem_fintype_prod Set.mem_fintype_prod
#align set.mem_fintype_sum Set.mem_fintype_sum

/- warning: set.list_prod_mem_list_prod -> Set.list_prod_mem_list_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (t : List.{u1} ι) (f : ι -> (Set.{u2} α)) (g : ι -> α), (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i t) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (g i) (f i))) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (List.prod.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1))) (List.map.{u1, u2} ι α g t)) (List.prod.{u2} (Set.{u2} α) (Set.mul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (Set.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (List.map.{u1, u2} ι (Set.{u2} α) f t)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (t : List.{u2} ι) (f : ι -> (Set.{u1} α)) (g : ι -> α), (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (g i) (f i))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (List.map.{u2, u1} ι α g t)) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.map.{u2, u1} ι (Set.{u1} α) f t)))
Case conversion may be inaccurate. Consider using '#align set.list_prod_mem_list_prod Set.list_prod_mem_list_prodₓ'. -/
/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `set.add_mem_add`. "]
theorem list_prod_mem_list_prod (t : List ι) (f : ι → Set α) (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
    (t.map g).Prod ∈ (t.map f).Prod :=
  by
  induction' t with h tl ih
  · simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
  · simp_rw [List.map_cons, List.prod_cons]
    exact
      mul_mem_mul (hg h <| List.mem_cons_self _ _)
        (ih fun i hi => hg i <| List.mem_cons_of_mem _ hi)
#align set.list_prod_mem_list_prod Set.list_prod_mem_list_prod
#align set.list_sum_mem_list_sum Set.list_sum_mem_list_sum

/- warning: set.list_prod_subset_list_prod -> Set.list_prod_subset_list_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (t : List.{u1} ι) (f₁ : ι -> (Set.{u2} α)) (f₂ : ι -> (Set.{u2} α)), (forall (i : ι), (Membership.Mem.{u1, u1} ι (List.{u1} ι) (List.hasMem.{u1} ι) i t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (f₁ i) (f₂ i))) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (List.prod.{u2} (Set.{u2} α) (Set.mul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (Set.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (List.map.{u1, u2} ι (Set.{u2} α) f₁ t)) (List.prod.{u2} (Set.{u2} α) (Set.mul.{u2} α (MulOneClass.toHasMul.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (Set.one.{u2} α (MulOneClass.toHasOne.{u2} α (Monoid.toMulOneClass.{u2} α (CommMonoid.toMonoid.{u2} α _inst_1)))) (List.map.{u1, u2} ι (Set.{u2} α) f₂ t)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (t : List.{u2} ι) (f₁ : ι -> (Set.{u1} α)) (f₂ : ι -> (Set.{u1} α)), (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (f₁ i) (f₂ i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.map.{u2, u1} ι (Set.{u1} α) f₁ t)) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.map.{u2, u1} ι (Set.{u1} α) f₂ t)))
Case conversion may be inaccurate. Consider using '#align set.list_prod_subset_list_prod Set.list_prod_subset_list_prodₓ'. -/
/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `set.add_subset_add`. "]
theorem list_prod_subset_list_prod (t : List ι) (f₁ f₂ : ι → Set α) (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) :
    (t.map f₁).Prod ⊆ (t.map f₂).Prod :=
  by
  induction' t with h tl ih
  · rfl
  · simp_rw [List.map_cons, List.prod_cons]
    exact
      mul_subset_mul (hf h <| List.mem_cons_self _ _)
        (ih fun i hi => hf i <| List.mem_cons_of_mem _ hi)
#align set.list_prod_subset_list_prod Set.list_prod_subset_list_prod
#align set.list_sum_subset_list_sum Set.list_sum_subset_list_sum

/- warning: set.list_prod_singleton -> Set.list_prod_singleton is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (s : List.{u1} M), Eq.{succ u1} (Set.{u1} M) (List.prod.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) (Set.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) (List.map.{u1, u1} M (Set.{u1} M) (fun (i : M) => Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) i) s)) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (s : List.{u1} M), Eq.{succ u1} (Set.{u1} M) (List.prod.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) (Set.one.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (List.map.{u1, u1} M (Set.{u1} M) (fun (i : M) => Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) i) s)) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)) s))
Case conversion may be inaccurate. Consider using '#align set.list_prod_singleton Set.list_prod_singletonₓ'. -/
@[to_additive]
theorem list_prod_singleton {M : Type _} [CommMonoid M] (s : List M) :
    (s.map fun i => ({i} : Set M)).Prod = {s.Prod} :=
  (map_list_prod (singletonMonoidHom : M →* Set M) _).symm
#align set.list_prod_singleton Set.list_prod_singleton
#align set.list_sum_singleton Set.list_sum_singleton

/- warning: set.multiset_prod_mem_multiset_prod -> Set.multiset_prod_mem_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (t : Multiset.{u1} ι) (f : ι -> (Set.{u2} α)) (g : ι -> α), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Multiset.{u1} ι) (Multiset.hasMem.{u1} ι) i t) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (g i) (f i))) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (Multiset.prod.{u2} α _inst_1 (Multiset.map.{u1, u2} ι α g t)) (Multiset.prod.{u2} (Set.{u2} α) (Set.commMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι (Set.{u2} α) f t)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (t : Multiset.{u2} ι) (f : ι -> (Set.{u1} α)) (g : ι -> α), (forall (i : ι), (Membership.mem.{u2, u2} ι (Multiset.{u2} ι) (Multiset.instMembershipMultiset.{u2} ι) i t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (g i) (f i))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Multiset.prod.{u1} α _inst_1 (Multiset.map.{u2, u1} ι α g t)) (Multiset.prod.{u1} (Set.{u1} α) (Set.commMonoid.{u1} α _inst_1) (Multiset.map.{u2, u1} ι (Set.{u1} α) f t)))
Case conversion may be inaccurate. Consider using '#align set.multiset_prod_mem_multiset_prod Set.multiset_prod_mem_multiset_prodₓ'. -/
/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `set.add_mem_add`. "]
theorem multiset_prod_mem_multiset_prod (t : Multiset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (t.map g).Prod ∈ (t.map f).Prod :=
  by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.coe_map, Multiset.coe_prod]
  exact list_prod_mem_list_prod _ _ _ hg
#align set.multiset_prod_mem_multiset_prod Set.multiset_prod_mem_multiset_prod
#align set.multiset_sum_mem_multiset_sum Set.multiset_sum_mem_multiset_sum

/- warning: set.multiset_prod_subset_multiset_prod -> Set.multiset_prod_subset_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (t : Multiset.{u1} ι) (f₁ : ι -> (Set.{u2} α)) (f₂ : ι -> (Set.{u2} α)), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Multiset.{u1} ι) (Multiset.hasMem.{u1} ι) i t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (f₁ i) (f₂ i))) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (Multiset.prod.{u2} (Set.{u2} α) (Set.commMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι (Set.{u2} α) f₁ t)) (Multiset.prod.{u2} (Set.{u2} α) (Set.commMonoid.{u2} α _inst_1) (Multiset.map.{u1, u2} ι (Set.{u2} α) f₂ t)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (t : Multiset.{u2} ι) (f₁ : ι -> (Set.{u1} α)) (f₂ : ι -> (Set.{u1} α)), (forall (i : ι), (Membership.mem.{u2, u2} ι (Multiset.{u2} ι) (Multiset.instMembershipMultiset.{u2} ι) i t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (f₁ i) (f₂ i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Multiset.prod.{u1} (Set.{u1} α) (Set.commMonoid.{u1} α _inst_1) (Multiset.map.{u2, u1} ι (Set.{u1} α) f₁ t)) (Multiset.prod.{u1} (Set.{u1} α) (Set.commMonoid.{u1} α _inst_1) (Multiset.map.{u2, u1} ι (Set.{u1} α) f₂ t)))
Case conversion may be inaccurate. Consider using '#align set.multiset_prod_subset_multiset_prod Set.multiset_prod_subset_multiset_prodₓ'. -/
/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `set.add_subset_add`. "]
theorem multiset_prod_subset_multiset_prod (t : Multiset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : (t.map f₁).Prod ⊆ (t.map f₂).Prod :=
  by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.coe_map, Multiset.coe_prod]
  exact list_prod_subset_list_prod _ _ _ hf
#align set.multiset_prod_subset_multiset_prod Set.multiset_prod_subset_multiset_prod
#align set.multiset_sum_subset_multiset_sum Set.multiset_sum_subset_multiset_sum

#print Set.multiset_prod_singleton /-
@[to_additive]
theorem multiset_prod_singleton {M : Type _} [CommMonoid M] (s : Multiset M) :
    (s.map fun i => ({i} : Set M)).Prod = {s.Prod} :=
  (map_multiset_prod (singletonMonoidHom : M →* Set M) _).symm
#align set.multiset_prod_singleton Set.multiset_prod_singleton
#align set.multiset_sum_singleton Set.multiset_sum_singleton
-/

/- warning: set.finset_prod_mem_finset_prod -> Set.finset_prod_mem_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (t : Finset.{u1} ι) (f : ι -> (Set.{u2} α)) (g : ι -> α), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i t) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (g i) (f i))) -> (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (Finset.prod.{u2, u1} α ι _inst_1 t (fun (i : ι) => g i)) (Finset.prod.{u2, u1} (Set.{u2} α) ι (Set.commMonoid.{u2} α _inst_1) t (fun (i : ι) => f i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (t : Finset.{u2} ι) (f : ι -> (Set.{u1} α)) (g : ι -> α), (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (g i) (f i))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Finset.prod.{u1, u2} α ι _inst_1 t (fun (i : ι) => g i)) (Finset.prod.{u1, u2} (Set.{u1} α) ι (Set.commMonoid.{u1} α _inst_1) t (fun (i : ι) => f i)))
Case conversion may be inaccurate. Consider using '#align set.finset_prod_mem_finset_prod Set.finset_prod_mem_finset_prodₓ'. -/
/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `set.add_mem_add`. "]
theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (∏ i in t, g i) ∈ ∏ i in t, f i :=
  multiset_prod_mem_multiset_prod _ _ _ hg
#align set.finset_prod_mem_finset_prod Set.finset_prod_mem_finset_prod
#align set.finset_sum_mem_finset_sum Set.finset_sum_mem_finset_sum

/- warning: set.finset_prod_subset_finset_prod -> Set.finset_prod_subset_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (t : Finset.{u1} ι) (f₁ : ι -> (Set.{u2} α)) (f₂ : ι -> (Set.{u2} α)), (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i t) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (f₁ i) (f₂ i))) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.hasSubset.{u2} α) (Finset.prod.{u2, u1} (Set.{u2} α) ι (Set.commMonoid.{u2} α _inst_1) t (fun (i : ι) => f₁ i)) (Finset.prod.{u2, u1} (Set.{u2} α) ι (Set.commMonoid.{u2} α _inst_1) t (fun (i : ι) => f₂ i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (t : Finset.{u2} ι) (f₁ : ι -> (Set.{u1} α)) (f₂ : ι -> (Set.{u1} α)), (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (f₁ i) (f₂ i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Finset.prod.{u1, u2} (Set.{u1} α) ι (Set.commMonoid.{u1} α _inst_1) t (fun (i : ι) => f₁ i)) (Finset.prod.{u1, u2} (Set.{u1} α) ι (Set.commMonoid.{u1} α _inst_1) t (fun (i : ι) => f₂ i)))
Case conversion may be inaccurate. Consider using '#align set.finset_prod_subset_finset_prod Set.finset_prod_subset_finset_prodₓ'. -/
/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `set.add_subset_add`. "]
theorem finset_prod_subset_finset_prod (t : Finset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : (∏ i in t, f₁ i) ⊆ ∏ i in t, f₂ i :=
  multiset_prod_subset_multiset_prod _ _ _ hf
#align set.finset_prod_subset_finset_prod Set.finset_prod_subset_finset_prod
#align set.finset_sum_subset_finset_sum Set.finset_sum_subset_finset_sum

/- warning: set.finset_prod_singleton -> Set.finset_prod_singleton is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {ι : Type.{u2}} [_inst_4 : CommMonoid.{u1} M] (s : Finset.{u2} ι) (I : ι -> M), Eq.{succ u1} (Set.{u1} M) (Finset.prod.{u1, u2} (Set.{u1} M) ι (Set.commMonoid.{u1} M _inst_4) s (fun (i : ι) => Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) (I i))) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) (Finset.prod.{u1, u2} M ι _inst_4 s (fun (i : ι) => I i)))
but is expected to have type
  forall {M : Type.{u2}} {ι : Type.{u1}} [_inst_4 : CommMonoid.{u2} M] (s : Finset.{u1} ι) (I : ι -> M), Eq.{succ u2} (Set.{u2} M) (Finset.prod.{u2, u1} (Set.{u2} M) ι (Set.commMonoid.{u2} M _inst_4) s (fun (i : ι) => Singleton.singleton.{u2, u2} M (Set.{u2} M) (Set.instSingletonSet.{u2} M) (I i))) (Singleton.singleton.{u2, u2} M (Set.{u2} M) (Set.instSingletonSet.{u2} M) (Finset.prod.{u2, u1} M ι _inst_4 s (fun (i : ι) => I i)))
Case conversion may be inaccurate. Consider using '#align set.finset_prod_singleton Set.finset_prod_singletonₓ'. -/
@[to_additive]
theorem finset_prod_singleton {M ι : Type _} [CommMonoid M] (s : Finset ι) (I : ι → M) :
    (∏ i : ι in s, ({I i} : Set M)) = {∏ i : ι in s, I i} :=
  (map_prod (singletonMonoidHom : M →* Set M) _ _).symm
#align set.finset_prod_singleton Set.finset_prod_singleton
#align set.finset_sum_singleton Set.finset_sum_singleton

/- warning: set.image_finset_prod_pi -> Set.image_finset_prod_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] (l : Finset.{u1} ι) (S : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.image.{max u1 u2, u2} (ι -> α) α (fun (f : ι -> α) => Finset.prod.{u2, u1} α ι _inst_1 l (fun (i : ι) => f i)) (Set.pi.{u1, u2} ι (fun (ᾰ : ι) => α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) l) S)) (Finset.prod.{u2, u1} (Set.{u2} α) ι (Set.commMonoid.{u2} α _inst_1) l (fun (i : ι) => S i))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (l : Finset.{u2} ι) (S : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.image.{max u2 u1, u1} (ι -> α) α (fun (f : ι -> α) => Finset.prod.{u1, u2} α ι _inst_1 l (fun (i : ι) => f i)) (Set.pi.{u2, u1} ι (fun (ᾰ : ι) => α) (Finset.toSet.{u2} ι l) S)) (Finset.prod.{u1, u2} (Set.{u1} α) ι (Set.commMonoid.{u1} α _inst_1) l (fun (i : ι) => S i))
Case conversion may be inaccurate. Consider using '#align set.image_finset_prod_pi Set.image_finset_prod_piₓ'. -/
/-- The n-ary version of `set.image_mul_prod`. -/
@[to_additive "The n-ary version of `set.add_image_prod`. "]
theorem image_finset_prod_pi (l : Finset ι) (S : ι → Set α) :
    (fun f : ι → α => ∏ i in l, f i) '' (l : Set ι).pi S = ∏ i in l, S i := by ext;
  simp_rw [mem_finset_prod, mem_image, mem_pi, exists_prop, Finset.mem_coe]
#align set.image_finset_prod_pi Set.image_finset_prod_pi
#align set.image_finset_sum_pi Set.image_finset_sum_pi

/- warning: set.image_fintype_prod_pi -> Set.image_fintype_prod_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : CommMonoid.{u2} α] [_inst_4 : Fintype.{u1} ι] (S : ι -> (Set.{u2} α)), Eq.{succ u2} (Set.{u2} α) (Set.image.{max u1 u2, u2} (ι -> α) α (fun (f : ι -> α) => Finset.prod.{u2, u1} α ι _inst_1 (Finset.univ.{u1} ι _inst_4) (fun (i : ι) => f i)) (Set.pi.{u1, u2} ι (fun (ᾰ : ι) => α) (Set.univ.{u1} ι) S)) (Finset.prod.{u2, u1} (Set.{u2} α) ι (Set.commMonoid.{u2} α _inst_1) (Finset.univ.{u1} ι _inst_4) (fun (i : ι) => S i))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] [_inst_4 : Fintype.{u2} ι] (S : ι -> (Set.{u1} α)), Eq.{succ u1} (Set.{u1} α) (Set.image.{max u2 u1, u1} (ι -> α) α (fun (f : ι -> α) => Finset.prod.{u1, u2} α ι _inst_1 (Finset.univ.{u2} ι _inst_4) (fun (i : ι) => f i)) (Set.pi.{u2, u1} ι (fun (ᾰ : ι) => α) (Set.univ.{u2} ι) S)) (Finset.prod.{u1, u2} (Set.{u1} α) ι (Set.commMonoid.{u1} α _inst_1) (Finset.univ.{u2} ι _inst_4) (fun (i : ι) => S i))
Case conversion may be inaccurate. Consider using '#align set.image_fintype_prod_pi Set.image_fintype_prod_piₓ'. -/
/-- A special case of `set.image_finset_prod_pi` for `finset.univ`. -/
@[to_additive "A special case of `set.image_finset_sum_pi` for `finset.univ`. "]
theorem image_fintype_prod_pi [Fintype ι] (S : ι → Set α) :
    (fun f : ι → α => ∏ i, f i) '' univ.pi S = ∏ i, S i := by
  simpa only [Finset.coe_univ] using image_finset_prod_pi Finset.univ S
#align set.image_fintype_prod_pi Set.image_fintype_prod_pi
#align set.image_fintype_sum_pi Set.image_fintype_sum_pi

end CommMonoid

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/


end Set

