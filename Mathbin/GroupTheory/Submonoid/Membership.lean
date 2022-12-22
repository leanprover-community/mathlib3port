/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov

! This file was ported from Lean 3 source module group_theory.submonoid.membership
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.FreeMonoid.Basic
import Mathbin.Data.Finset.NoncommProd

/-!
# Submonoids: membership criteria

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) submonoid and
  `n` is a natural number, then `x^n` (resp., `n • x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of submonoid is their union.
* `sup_eq_range`, `mem_sup`: supremum of two submonoids `S`, `T` of a commutative monoid is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`, `mem_closure_pair`: the multiplicative (resp.,
  additive) closure of `{x}` consists of powers (resp., natural multiples) of `x`, and a similar
  result holds for the closure of `{x, y}`.

## Tags
submonoid, submonoids
-/


open BigOperators

variable {M A B : Type _}

section Assoc

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {S : B}

namespace SubmonoidClass

@[simp, norm_cast, to_additive]
theorem coe_list_prod (l : List S) : (l.Prod : M) = (l.map coe).Prod :=
  (SubmonoidClass.subtype S : _ →* M).map_list_prod l
#align submonoid_class.coe_list_prod SubmonoidClass.coe_list_prod

@[simp, norm_cast, to_additive]
theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.Prod : M) = (m.map coe).Prod :=
  (SubmonoidClass.subtype S : _ →* M).map_multiset_prod m
#align submonoid_class.coe_multiset_prod SubmonoidClass.coe_multiset_prod

@[simp, norm_cast, to_additive]
theorem coe_finset_prod {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι → S)
    (s : Finset ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  (SubmonoidClass.subtype S : _ →* M).map_prod f s
#align submonoid_class.coe_finset_prod SubmonoidClass.coe_finset_prod

end SubmonoidClass

open SubmonoidClass

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ S) : l.Prod ∈ S := by
  lift l to List S using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop
#align list_prod_mem list_prod_mem

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive
      "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is\nin the `add_submonoid`."]
theorem multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.Prod ∈ S := by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop
#align multiset_prod_mem multiset_prod_mem

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`\nis in the `add_submonoid`."]
theorem prod_mem {M : Type _} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : Type _}
    {t : Finset ι} {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c in t, f c) ∈ S :=
  (multiset_prod_mem (t.1.map f)) fun x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi
#align prod_mem prod_mem

namespace Submonoid

variable (s : Submonoid M)

@[simp, norm_cast, to_additive]
theorem coe_list_prod (l : List s) : (l.Prod : M) = (l.map coe).Prod :=
  s.Subtype.map_list_prod l
#align submonoid.coe_list_prod Submonoid.coe_list_prod

@[simp, norm_cast, to_additive]
theorem coe_multiset_prod {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S) :
    (m.Prod : M) = (m.map coe).Prod :=
  S.Subtype.map_multiset_prod m
#align submonoid.coe_multiset_prod Submonoid.coe_multiset_prod

@[simp, norm_cast, to_additive]
theorem coe_finset_prod {ι M} [CommMonoid M] (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  S.Subtype.map_prod f s
#align submonoid.coe_finset_prod Submonoid.coe_finset_prod

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ s) : l.Prod ∈ s := by
  lift l to List s using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop
#align submonoid.list_prod_mem Submonoid.list_prod_mem

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive
      "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is\nin the `add_submonoid`."]
theorem multiset_prod_mem {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.Prod ∈ S := by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop
#align submonoid.multiset_prod_mem Submonoid.multiset_prod_mem

@[to_additive]
theorem multiset_noncomm_prod_mem (S : Submonoid M) (m : Multiset M) (comm) (h : ∀ x ∈ m, x ∈ S) :
    m.noncommProd comm ∈ S := by
  induction' m using Quotient.induction_on with l
  simp only [Multiset.quot_mk_to_coe, Multiset.noncomm_prod_coe]
  exact Submonoid.list_prod_mem _ h
#align submonoid.multiset_noncomm_prod_mem Submonoid.multiset_noncomm_prod_mem

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`\nis in the `add_submonoid`."]
theorem prod_mem {M : Type _} [CommMonoid M] (S : Submonoid M) {ι : Type _} {t : Finset ι}
    {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c in t, f c) ∈ S :=
  (S.multiset_prod_mem (t.1.map f)) fun x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi
#align submonoid.prod_mem Submonoid.prod_mem

@[to_additive]
theorem noncomm_prod_mem (S : Submonoid M) {ι : Type _} (t : Finset ι) (f : ι → M) (comm)
    (h : ∀ c ∈ t, f c ∈ S) : t.noncommProd f comm ∈ S := by
  apply multiset_noncomm_prod_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx
#align submonoid.noncomm_prod_mem Submonoid.noncomm_prod_mem

end Submonoid

end Assoc

section NonAssoc

variable [MulOneClass M]

open Set

namespace Submonoid

-- TODO: this section can be generalized to `[submonoid_class B M] [complete_lattice B]`
-- such that `complete_lattice.le` coincides with `set_like.le`
@[to_additive]
theorem mem_supr_of_directed {ι} [hι : Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S)
    {x : M} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i := by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_supᵢ S i) hi⟩
  suffices x ∈ closure (⋃ i, (S i : Set M)) → ∃ i, x ∈ S i by
    simpa only [closure_Union, closure_eq (S _)] using this
  refine' fun hx => closure_induction hx (fun _ => mem_Union.1) _ _
  · exact hι.elim fun i => ⟨i, (S i).one_mem⟩
  · rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    rcases hS i j with ⟨k, hki, hkj⟩
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩
#align submonoid.mem_supr_of_directed Submonoid.mem_supr_of_directed

@[to_additive]
theorem coe_supr_of_directed {ι} [Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Submonoid M) : Set M) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_supr_of_directed hS]
#align submonoid.coe_supr_of_directed Submonoid.coe_supr_of_directed

@[to_additive]
theorem mem_Sup_of_directed_on {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : M} : x ∈ supₛ S ↔ ∃ s ∈ S, x ∈ s := by
  haveI : Nonempty S := Sne.to_subtype
  simp only [supₛ_eq_supᵢ', mem_supr_of_directed hS.directed_coe, SetCoe.exists, Subtype.coe_mk]
#align submonoid.mem_Sup_of_directed_on Submonoid.mem_Sup_of_directed_on

@[to_additive]
theorem coe_Sup_of_directed_on {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(supₛ S) : Set M) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_Sup_of_directed_on Sne hS]
#align submonoid.coe_Sup_of_directed_on Submonoid.coe_Sup_of_directed_on

@[to_additive]
theorem mem_sup_left {S T : Submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
  show S ≤ S ⊔ T from le_sup_left
#align submonoid.mem_sup_left Submonoid.mem_sup_left

@[to_additive]
theorem mem_sup_right {S T : Submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
  show T ≤ S ⊔ T from le_sup_right
#align submonoid.mem_sup_right Submonoid.mem_sup_right

@[to_additive]
theorem mul_mem_sup {S T : Submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align submonoid.mul_mem_sup Submonoid.mul_mem_sup

@[to_additive]
theorem mem_supr_of_mem {ι : Sort _} {S : ι → Submonoid M} (i : ι) :
    ∀ {x : M}, x ∈ S i → x ∈ supᵢ S :=
  show S i ≤ supᵢ S from le_supᵢ _ _
#align submonoid.mem_supr_of_mem Submonoid.mem_supr_of_mem

@[to_additive]
theorem mem_Sup_of_mem {S : Set (Submonoid M)} {s : Submonoid M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ supₛ S :=
  show s ≤ supₛ S from le_supₛ hs
#align submonoid.mem_Sup_of_mem Submonoid.mem_Sup_of_mem

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[elab_as_elim,
  to_additive
      " An induction principle for elements of `⨆ i, S i`.\nIf `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,\nthen it holds for all elements of the supremum of `S`. "]
theorem supr_induction {ι : Sort _} (S : ι → Submonoid M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, S i)
    (hp : ∀ (i), ∀ x ∈ S i, C x) (h1 : C 1) (hmul : ∀ x y, C x → C y → C (x * y)) : C x := by
  rw [supr_eq_closure] at hx
  refine' closure_induction hx (fun x hx => _) h1 hmul
  obtain ⟨i, hi⟩ := set.mem_Union.mp hx
  exact hp _ _ hi
#align submonoid.supr_induction Submonoid.supr_induction

/-- A dependent version of `submonoid.supr_induction`. -/
@[elab_as_elim, to_additive "A dependent version of `add_submonoid.supr_induction`. "]
theorem supr_induction' {ι : Sort _} (S : ι → Submonoid M) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (hp : ∀ (i), ∀ x ∈ S i, C x (mem_supr_of_mem i ‹_›)) (h1 : C 1 (one_mem _))
    (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, S i) : C x hx := by
  refine' Exists.elim _ fun (hx : x ∈ ⨆ i, S i) (hc : C x hx) => hc
  refine' supr_induction S hx (fun i x hx => _) _ fun x y => _
  · exact ⟨_, hp _ _ hx⟩
  · exact ⟨_, h1⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    refine' ⟨_, hmul _ _ _ _ Cx Cy⟩
#align submonoid.supr_induction' Submonoid.supr_induction'

end Submonoid

end NonAssoc

namespace FreeMonoid

variable {α : Type _}

open Submonoid

@[to_additive]
theorem closure_range_of : closure (Set.range <| @of α) = ⊤ :=
  eq_top_iff.2 fun x hx =>
    (FreeMonoid.recOn x (one_mem _)) fun x xs hxs =>
      mul_mem (subset_closure <| Set.mem_range_self _) hxs
#align free_monoid.closure_range_of FreeMonoid.closure_range_of

end FreeMonoid

namespace Submonoid

variable [Monoid M]

open MonoidHom

theorem closure_singleton_eq (x : M) : closure ({x} : Set M) = (powersHom M x).mrange :=
  (closure_eq_of_le (Set.singleton_subset_iff.2 ⟨Multiplicative.ofAdd 1, pow_one x⟩))
    fun x ⟨n, hn⟩ => hn ▸ pow_mem (subset_closure <| Set.mem_singleton _) _
#align submonoid.closure_singleton_eq Submonoid.closure_singleton_eq

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
theorem mem_closure_singleton {x y : M} : y ∈ closure ({x} : Set M) ↔ ∃ n : ℕ, x ^ n = y := by
  rw [closure_singleton_eq, mem_mrange] <;> rfl
#align submonoid.mem_closure_singleton Submonoid.mem_closure_singleton

theorem mem_closure_singleton_self {y : M} : y ∈ closure ({y} : Set M) :=
  mem_closure_singleton.2 ⟨1, pow_one y⟩
#align submonoid.mem_closure_singleton_self Submonoid.mem_closure_singleton_self

theorem closure_singleton_one : closure ({1} : Set M) = ⊥ := by
  simp [eq_bot_iff_forall, mem_closure_singleton]
#align submonoid.closure_singleton_one Submonoid.closure_singleton_one

@[to_additive]
theorem FreeMonoid.mrange_lift {α} (f : α → M) :
    (FreeMonoid.lift f).mrange = closure (Set.range f) := by
  rw [mrange_eq_map, ← FreeMonoid.closure_range_of, map_mclosure, ← Set.range_comp,
    FreeMonoid.lift_comp_of]
#align free_monoid.mrange_lift FreeMonoid.mrange_lift

@[to_additive]
theorem closure_eq_mrange (s : Set M) : closure s = (FreeMonoid.lift (coe : s → M)).mrange := by
  rw [FreeMonoid.mrange_lift, Subtype.range_coe]
#align submonoid.closure_eq_mrange Submonoid.closure_eq_mrange

@[to_additive]
theorem closure_eq_image_prod (s : Set M) :
    (closure s : Set M) = List.prod '' { l : List M | ∀ x ∈ l, x ∈ s } := by
  rw [closure_eq_mrange, coe_mrange, ← List.range_map_coe, ← Set.range_comp]
  rfl
#align submonoid.closure_eq_image_prod Submonoid.closure_eq_image_prod

@[to_additive]
theorem exists_list_of_mem_closure {s : Set M} {x : M} (hx : x ∈ closure s) :
    ∃ (l : List M)(hl : ∀ y ∈ l, y ∈ s), l.Prod = x := by
  rwa [← SetLike.mem_coe, closure_eq_image_prod, Set.mem_image_iff_bex] at hx
#align submonoid.exists_list_of_mem_closure Submonoid.exists_list_of_mem_closure

@[to_additive]
theorem exists_multiset_of_mem_closure {M : Type _} [CommMonoid M] {s : Set M} {x : M}
    (hx : x ∈ closure s) : ∃ (l : Multiset M)(hl : ∀ y ∈ l, y ∈ s), l.Prod = x := by
  obtain ⟨l, h1, h2⟩ := exists_list_of_mem_closure hx
  exact ⟨l, h1, (Multiset.coe_prod l).trans h2⟩
#align submonoid.exists_multiset_of_mem_closure Submonoid.exists_multiset_of_mem_closure

@[to_additive]
theorem closure_induction_left {s : Set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
    (Hmul : ∀ x ∈ s, ∀ (y), p y → p (x * y)) : p x := by
  rw [closure_eq_mrange] at h
  obtain ⟨l, rfl⟩ := h
  induction' l using FreeMonoid.recOn with x y ih
  · exact H1
  · simpa only [map_mul, FreeMonoid.lift_eval_of] using Hmul _ x.prop _ ih
#align submonoid.closure_induction_left Submonoid.closure_induction_left

@[elab_as_elim, to_additive]
theorem induction_of_closure_eq_top_left {s : Set M} {p : M → Prop} (hs : closure s = ⊤) (x : M)
    (H1 : p 1) (Hmul : ∀ x ∈ s, ∀ (y), p y → p (x * y)) : p x :=
  closure_induction_left
    (by 
      rw [hs]
      exact mem_top _)
    H1 Hmul
#align submonoid.induction_of_closure_eq_top_left Submonoid.induction_of_closure_eq_top_left

@[to_additive]
theorem closure_induction_right {s : Set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
    (Hmul : ∀ (x), ∀ y ∈ s, p x → p (x * y)) : p x :=
  @closure_induction_left _ _ (MulOpposite.unop ⁻¹' s) (p ∘ MulOpposite.unop) (MulOpposite.op x)
    (closure_induction h (fun x hx => subset_closure hx) (one_mem _) fun x y hx hy => mul_mem hy hx)
    H1 fun x hx y => Hmul _ _ hx
#align submonoid.closure_induction_right Submonoid.closure_induction_right

@[elab_as_elim, to_additive]
theorem induction_of_closure_eq_top_right {s : Set M} {p : M → Prop} (hs : closure s = ⊤) (x : M)
    (H1 : p 1) (Hmul : ∀ (x), ∀ y ∈ s, p x → p (x * y)) : p x :=
  closure_induction_right
    (by 
      rw [hs]
      exact mem_top _)
    H1 Hmul
#align submonoid.induction_of_closure_eq_top_right Submonoid.induction_of_closure_eq_top_right

/-- The submonoid generated by an element. -/
def powers (n : M) : Submonoid M :=
  Submonoid.copy (powersHom M n).mrange (Set.range ((· ^ ·) n : ℕ → M)) <|
    Set.ext fun n => exists_congr fun i => by simp <;> rfl
#align submonoid.powers Submonoid.powers

@[simp]
theorem mem_powers (n : M) : n ∈ powers n :=
  ⟨1, pow_one _⟩
#align submonoid.mem_powers Submonoid.mem_powers

theorem mem_powers_iff (x z : M) : x ∈ powers z ↔ ∃ n : ℕ, z ^ n = x :=
  Iff.rfl
#align submonoid.mem_powers_iff Submonoid.mem_powers_iff

theorem powers_eq_closure (n : M) : powers n = closure {n} := by
  ext
  exact mem_closure_singleton.symm
#align submonoid.powers_eq_closure Submonoid.powers_eq_closure

theorem powers_subset {n : M} {P : Submonoid M} (h : n ∈ P) : powers n ≤ P := fun x hx =>
  match x, hx with
  | _, ⟨i, rfl⟩ => pow_mem h i
#align submonoid.powers_subset Submonoid.powers_subset

@[simp]
theorem powers_one : powers (1 : M) = ⊥ :=
  bot_unique <| powers_subset (one_mem _)
#align submonoid.powers_one Submonoid.powers_one

/-- Exponentiation map from natural numbers to powers. -/
@[simps]
def pow (n : M) (m : ℕ) : powers n :=
  (powersHom M n).mrangeRestrict (Multiplicative.ofAdd m)
#align submonoid.pow Submonoid.pow

theorem pow_apply (n : M) (m : ℕ) : Submonoid.pow n m = ⟨n ^ m, m, rfl⟩ :=
  rfl
#align submonoid.pow_apply Submonoid.pow_apply

/-- Logarithms from powers to natural numbers. -/
def log [DecidableEq M] {n : M} (p : powers n) : ℕ :=
  Nat.find <| (mem_powers_iff p.val n).mp p.Prop
#align submonoid.log Submonoid.log

@[simp]
theorem pow_log_eq_self [DecidableEq M] {n : M} (p : powers n) : pow n (log p) = p :=
  Subtype.ext <| Nat.find_spec p.Prop
#align submonoid.pow_log_eq_self Submonoid.pow_log_eq_self

theorem pow_right_injective_iff_pow_injective {n : M} :
    (Function.Injective fun m : ℕ => n ^ m) ↔ Function.Injective (pow n) :=
  Subtype.coe_injective.of_comp_iff (pow n)
#align
  submonoid.pow_right_injective_iff_pow_injective Submonoid.pow_right_injective_iff_pow_injective

@[simp]
theorem log_pow_eq_self [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (m : ℕ) : log (pow n m) = m :=
  pow_right_injective_iff_pow_injective.mp h <| pow_log_eq_self _
#align submonoid.log_pow_eq_self Submonoid.log_pow_eq_self

/-- The exponentiation map is an isomorphism from the additive monoid on natural numbers to powers
when it is injective. The inverse is given by the logarithms. -/
@[simps]
def powLogEquiv [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m) :
    Multiplicative ℕ ≃* powers n where 
  toFun m := pow n m.toAdd
  invFun m := Multiplicative.ofAdd (log m)
  left_inv := log_pow_eq_self h
  right_inv := pow_log_eq_self
  map_mul' _ _ := by simp only [pow, map_mul, ofAdd_add, toAdd_mul]
#align submonoid.pow_log_equiv Submonoid.powLogEquiv

theorem log_mul [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (x y : powers (n : M)) : log (x * y) = log x + log y :=
  (powLogEquiv h).symm.map_mul x y
#align submonoid.log_mul Submonoid.log_mul

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.natAbs) (m : ℕ) : log (pow x m) = m :=
  (powLogEquiv (Int.pow_right_injective h)).symm_apply_apply _
#align submonoid.log_pow_int_eq_self Submonoid.log_pow_int_eq_self

@[simp]
theorem map_powers {N : Type _} {F : Type _} [Monoid N] [MonoidHomClass F M N] (f : F) (m : M) :
    (powers m).map f = powers (f m) := by
  simp only [powers_eq_closure, map_mclosure f, Set.image_singleton]
#align submonoid.map_powers Submonoid.map_powers

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a b «expr ∈ » s) -/
/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
@[to_additive
      "If all the elements of a set `s` commute, then `closure s` forms an additive\ncommutative monoid."]
def closureCommMonoidOfComm {s : Set M} (hcomm : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a * b = b * a) :
    CommMonoid (closure s) :=
  { (closure s).toMonoid with
    mul_comm := fun x y => by 
      ext
      simp only [Submonoid.coe_mul]
      exact
        closure_induction₂ x.prop y.prop hcomm Commute.one_left Commute.one_right
          (fun x y z => Commute.mul_left) fun x y z => Commute.mul_right }
#align submonoid.closure_comm_monoid_of_comm Submonoid.closureCommMonoidOfComm

end Submonoid

@[to_additive]
theorem IsScalarTower.of_mclosure_eq_top {N α} [Monoid M] [MulAction M N] [HasSmul N α]
    [MulAction M α] {s : Set M} (htop : Submonoid.closure s = ⊤)
    (hs : ∀ x ∈ s, ∀ (y : N) (z : α), (x • y) • z = x • y • z) : IsScalarTower M N α := by
  refine' ⟨fun x => Submonoid.induction_of_closure_eq_top_left htop x _ _⟩
  · intro y z
    rw [one_smul, one_smul]
  · clear x
    intro x hx x' hx' y z
    rw [mul_smul, mul_smul, hs x hx, hx']
#align is_scalar_tower.of_mclosure_eq_top IsScalarTower.of_mclosure_eq_top

@[to_additive]
theorem SMulCommClass.of_mclosure_eq_top {N α} [Monoid M] [HasSmul N α] [MulAction M α] {s : Set M}
    (htop : Submonoid.closure s = ⊤) (hs : ∀ x ∈ s, ∀ (y : N) (z : α), x • y • z = y • x • z) :
    SMulCommClass M N α := by
  refine' ⟨fun x => Submonoid.induction_of_closure_eq_top_left htop x _ _⟩
  · intro y z
    rw [one_smul, one_smul]
  · clear x
    intro x hx x' hx' y z
    rw [mul_smul, mul_smul, hx', hs x hx]
#align smul_comm_class.of_mclosure_eq_top SMulCommClass.of_mclosure_eq_top

namespace Submonoid

variable {N : Type _} [CommMonoid N]

open MonoidHom

@[to_additive]
theorem sup_eq_range (s t : Submonoid N) : s ⊔ t = (s.Subtype.coprod t.Subtype).mrange := by
  rw [mrange_eq_map, ← mrange_inl_sup_mrange_inr, map_sup, map_mrange, coprod_comp_inl, map_mrange,
    coprod_comp_inr, range_subtype, range_subtype]
#align submonoid.sup_eq_range Submonoid.sup_eq_range

@[to_additive]
theorem mem_sup {s t : Submonoid N} {x : N} : x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  simp only [sup_eq_range, mem_mrange, coprod_apply, Prod.exists, SetLike.exists, coeSubtype,
    Subtype.coe_mk]
#align submonoid.mem_sup Submonoid.mem_sup

end Submonoid

namespace AddSubmonoid

variable [AddMonoid A]

open Set

theorem closure_singleton_eq (x : A) : closure ({x} : Set A) = (multiplesHom A x).mrange :=
  (closure_eq_of_le (Set.singleton_subset_iff.2 ⟨1, one_nsmul x⟩)) fun x ⟨n, hn⟩ =>
    hn ▸ nsmul_mem (subset_closure <| Set.mem_singleton _) _
#align add_submonoid.closure_singleton_eq AddSubmonoid.closure_singleton_eq

/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
theorem mem_closure_singleton {x y : A} : y ∈ closure ({x} : Set A) ↔ ∃ n : ℕ, n • x = y := by
  rw [closure_singleton_eq, AddMonoidHom.mem_mrange] <;> rfl
#align add_submonoid.mem_closure_singleton AddSubmonoid.mem_closure_singleton

theorem closure_singleton_zero : closure ({0} : Set A) = ⊥ := by
  simp [eq_bot_iff_forall, mem_closure_singleton, nsmul_zero]
#align add_submonoid.closure_singleton_zero AddSubmonoid.closure_singleton_zero

/-- The additive submonoid generated by an element. -/
def multiples (x : A) : AddSubmonoid A :=
  AddSubmonoid.copy (multiplesHom A x).mrange (Set.range (fun i => i • x : ℕ → A)) <|
    Set.ext fun n => exists_congr fun i => by simp <;> rfl
#align add_submonoid.multiples AddSubmonoid.multiples

attribute [to_additive multiples] Submonoid.powers

attribute [to_additive mem_multiples] Submonoid.mem_powers

attribute [to_additive mem_multiples_iff] Submonoid.mem_powers_iff

attribute [to_additive multiples_eq_closure] Submonoid.powers_eq_closure

attribute [to_additive multiples_subset] Submonoid.powers_subset

attribute [to_additive multiples_zero] Submonoid.powers_one

end AddSubmonoid

/-! Lemmas about additive closures of `subsemigroup`. -/


namespace MulMemClass

variable {R : Type _} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

/-- The product of an element of the additive closure of a multiplicative subsemigroup `M`
and an element of `M` is contained in the additive closure of `M`. -/
theorem mul_right_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R)) (hb : b ∈ S) :
    a * b ∈ AddSubmonoid.closure (S : Set R) := by
  revert b
  refine' AddSubmonoid.closure_induction ha _ _ _ <;> clear ha a
  · exact fun r hr b hb => add_submonoid.mem_closure.mpr fun y hy => hy (mul_mem hr hb)
  · exact fun b hb => by simp only [zero_mul, (AddSubmonoid.closure (S : Set R)).zero_mem]
  · simp_rw [add_mul]
    exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)
#align mul_mem_class.mul_right_mem_add_closure MulMemClass.mul_right_mem_add_closure

/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
theorem mul_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R))
    (hb : b ∈ AddSubmonoid.closure (S : Set R)) : a * b ∈ AddSubmonoid.closure (S : Set R) := by
  revert a
  refine' AddSubmonoid.closure_induction hb _ _ _ <;> clear hb b
  · exact fun r hr b hb => MulMemClass.mul_right_mem_add_closure hb hr
  · exact fun b hb => by simp only [mul_zero, (AddSubmonoid.closure (S : Set R)).zero_mem]
  · simp_rw [mul_add]
    exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)
#align mul_mem_class.mul_mem_add_closure MulMemClass.mul_mem_add_closure

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
theorem mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ AddSubmonoid.closure (S : Set R)) :
    a * b ∈ AddSubmonoid.closure (S : Set R) :=
  mul_mem_add_closure (AddSubmonoid.mem_closure.mpr fun sT hT => hT ha) hb
#align mul_mem_class.mul_left_mem_add_closure MulMemClass.mul_left_mem_add_closure

end MulMemClass

namespace Submonoid

/-- An element is in the closure of a two-element set if it is a linear combination of those two
elements. -/
@[to_additive
      "An element is in the closure of a two-element set if it is a linear combination of\nthose two elements."]
theorem mem_closure_pair {A : Type _} [CommMonoid A] (a b c : A) :
    c ∈ Submonoid.closure ({a, b} : Set A) ↔ ∃ m n : ℕ, a ^ m * b ^ n = c := by
  rw [← Set.singleton_union, Submonoid.closure_union, mem_sup]
  simp_rw [exists_prop, mem_closure_singleton, exists_exists_eq_and]
#align submonoid.mem_closure_pair Submonoid.mem_closure_pair

end Submonoid

section mul_add

theorem of_mul_image_powers_eq_multiples_of_mul [Monoid M] {x : M} :
    Additive.ofMul '' (Submonoid.powers x : Set M) = AddSubmonoid.multiples (Additive.ofMul x) := by
  ext
  constructor
  · rintro ⟨y, ⟨n, hy1⟩, hy2⟩
    use n
    simpa [← ofMul_pow, hy1]
  · rintro ⟨n, hn⟩
    refine' ⟨x ^ n, ⟨n, rfl⟩, _⟩
    rwa [ofMul_pow]
#align of_mul_image_powers_eq_multiples_of_mul of_mul_image_powers_eq_multiples_of_mul

theorem of_add_image_multiples_eq_powers_of_add [AddMonoid A] {x : A} :
    Multiplicative.ofAdd '' (AddSubmonoid.multiples x : Set A) =
      Submonoid.powers (Multiplicative.ofAdd x) :=
  by 
  symm
  rw [Equiv.eq_image_iff_symm_image_eq]
  exact of_mul_image_powers_eq_multiples_of_mul
#align of_add_image_multiples_eq_powers_of_add of_add_image_multiples_eq_powers_of_add

end mul_add

