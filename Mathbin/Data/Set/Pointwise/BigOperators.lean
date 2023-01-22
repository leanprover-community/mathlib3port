/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module data.set.pointwise.big_operators
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Set.Pointwise.Basic

/-!
# Results about pointwise operations on sets and big operators.
-/


namespace Set

section BigOperators

open BigOperators Pointwise

open Function

variable {α : Type _} {ι : Type _} [CommMonoid α]

#print Set.mem_finset_prod /-
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
      · rw [Function.update_same]
        exact hx
      · rw [update_noteq (ne_of_mem_of_not_mem hj hi)]
        exact hg hj
      rw [Finset.prod_update_of_not_mem hi, Function.update_same]
    · rintro ⟨g, hg, rfl⟩
      exact
        ⟨g i, is.prod g, hg (is.mem_insert_self _),
          ⟨g, fun i hi => hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩
#align set.mem_finset_prod Set.mem_finset_prod
#align set.mem_finset_sum Set.mem_finset_sum
-/

#print Set.mem_fintype_prod /-
/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[to_additive " A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "]
theorem mem_fintype_prod [Fintype ι] (f : ι → Set α) (a : α) :
    (a ∈ ∏ i, f i) ↔ ∃ (g : ι → α)(hg : ∀ i, g i ∈ f i), (∏ i, g i) = a :=
  by
  rw [mem_finset_prod]
  simp
#align set.mem_fintype_prod Set.mem_fintype_prod
#align set.mem_fintype_sum Set.mem_fintype_sum
-/

/- warning: set.list_prod_mem_list_prod -> Set.list_prod_mem_list_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] (t : List.{u2} ι) (f : ι -> (Set.{u1} α)) (g : ι -> α), (forall (i : ι), (Membership.Mem.{u2, u2} ι (List.{u2} ι) (List.hasMem.{u2} ι) i t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (g i) (f i))) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (List.prod.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.map.{u2, u1} ι α g t)) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.map.{u2, u1} ι (Set.{u1} α) f t)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] (t : List.{u2} ι) (f : ι -> (Set.{u1} α)) (g : ι -> α), (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i t) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (g i) (f i))) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (List.prod.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (List.map.{u2, u1} ι α g t)) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.map.{u2, u1} ι (Set.{u1} α) f t)))
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
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] (t : List.{u2} ι) (f₁ : ι -> (Set.{u1} α)) (f₂ : ι -> (Set.{u1} α)), (forall (i : ι), (Membership.Mem.{u2, u2} ι (List.{u2} ι) (List.hasMem.{u2} ι) i t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (f₁ i) (f₂ i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.map.{u2, u1} ι (Set.{u1} α) f₁ t)) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (List.map.{u2, u1} ι (Set.{u1} α) f₂ t)))
but is expected to have type
  forall {α : Type.{u1}} {ι : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] (t : List.{u2} ι) (f₁ : ι -> (Set.{u1} α)) (f₂ : ι -> (Set.{u1} α)), (forall (i : ι), (Membership.mem.{u2, u2} ι (List.{u2} ι) (List.instMembershipList.{u2} ι) i t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (f₁ i) (f₂ i))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.map.{u2, u1} ι (Set.{u1} α) f₁ t)) (List.prod.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Set.one.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (List.map.{u2, u1} ι (Set.{u1} α) f₂ t)))
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
  forall {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] (s : List.{u1} M), Eq.{succ u1} (Set.{u1} M) (List.prod.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) (Set.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) (List.map.{u1, u1} M (Set.{u1} M) (fun (i : M) => Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) i) s)) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] (s : List.{u1} M), Eq.{succ u1} (Set.{u1} M) (List.prod.{u1} (Set.{u1} M) (Set.mul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) (Set.one.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (List.map.{u1, u1} M (Set.{u1} M) (fun (i : M) => Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) i) s)) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) s))
Case conversion may be inaccurate. Consider using '#align set.list_prod_singleton Set.list_prod_singletonₓ'. -/
@[to_additive]
theorem list_prod_singleton {M : Type _} [CommMonoid M] (s : List M) :
    (s.map fun i => ({i} : Set M)).Prod = {s.Prod} :=
  (map_list_prod (singletonMonoidHom : M →* Set M) _).symm
#align set.list_prod_singleton Set.list_prod_singleton
#align set.list_sum_singleton Set.list_sum_singleton

#print Set.multiset_prod_mem_multiset_prod /-
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
-/

#print Set.multiset_prod_subset_multiset_prod /-
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
-/

#print Set.multiset_prod_singleton /-
@[to_additive]
theorem multiset_prod_singleton {M : Type _} [CommMonoid M] (s : Multiset M) :
    (s.map fun i => ({i} : Set M)).Prod = {s.Prod} :=
  (map_multiset_prod (singletonMonoidHom : M →* Set M) _).symm
#align set.multiset_prod_singleton Set.multiset_prod_singleton
#align set.multiset_sum_singleton Set.multiset_sum_singleton
-/

#print Set.finset_prod_mem_finset_prod /-
/-- An n-ary version of `set.mul_mem_mul`. -/
@[to_additive " An n-ary version of `set.add_mem_add`. "]
theorem finset_prod_mem_finset_prod (t : Finset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (∏ i in t, g i) ∈ ∏ i in t, f i :=
  multiset_prod_mem_multiset_prod _ _ _ hg
#align set.finset_prod_mem_finset_prod Set.finset_prod_mem_finset_prod
#align set.finset_sum_mem_finset_sum Set.finset_sum_mem_finset_sum
-/

#print Set.finset_prod_subset_finset_prod /-
/-- An n-ary version of `set.mul_subset_mul`. -/
@[to_additive " An n-ary version of `set.add_subset_add`. "]
theorem finset_prod_subset_finset_prod (t : Finset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : (∏ i in t, f₁ i) ⊆ ∏ i in t, f₂ i :=
  multiset_prod_subset_multiset_prod _ _ _ hf
#align set.finset_prod_subset_finset_prod Set.finset_prod_subset_finset_prod
#align set.finset_sum_subset_finset_sum Set.finset_sum_subset_finset_sum
-/

/- warning: set.finset_prod_singleton -> Set.finset_prod_singleton is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {ι : Type.{u2}} [_inst_2 : CommMonoid.{u1} M] (s : Finset.{u2} ι) (I : ι -> M), Eq.{succ u1} (Set.{u1} M) (Finset.prod.{u1, u2} (Set.{u1} M) ι (Set.commMonoid.{u1} M _inst_2) s (fun (i : ι) => Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) (I i))) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) (Finset.prod.{u1, u2} M ι _inst_2 s (fun (i : ι) => I i)))
but is expected to have type
  forall {M : Type.{u2}} {ι : Type.{u1}} [_inst_2 : CommMonoid.{u2} M] (s : Finset.{u1} ι) (I : ι -> M), Eq.{succ u2} (Set.{u2} M) (Finset.prod.{u2, u1} (Set.{u2} M) ι (Set.commMonoid.{u2} M _inst_2) s (fun (i : ι) => Singleton.singleton.{u2, u2} M (Set.{u2} M) (Set.instSingletonSet.{u2} M) (I i))) (Singleton.singleton.{u2, u2} M (Set.{u2} M) (Set.instSingletonSet.{u2} M) (Finset.prod.{u2, u1} M ι _inst_2 s (fun (i : ι) => I i)))
Case conversion may be inaccurate. Consider using '#align set.finset_prod_singleton Set.finset_prod_singletonₓ'. -/
@[to_additive]
theorem finset_prod_singleton {M ι : Type _} [CommMonoid M] (s : Finset ι) (I : ι → M) :
    (∏ i : ι in s, ({I i} : Set M)) = {∏ i : ι in s, I i} :=
  (map_prod (singletonMonoidHom : M →* Set M) _ _).symm
#align set.finset_prod_singleton Set.finset_prod_singleton
#align set.finset_sum_singleton Set.finset_sum_singleton

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/


end BigOperators

end Set

