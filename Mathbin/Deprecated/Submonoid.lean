/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard

! This file was ported from Lean 3 source module deprecated.submonoid
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Submonoid.Basic
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Deprecated.Group

/-!
# Unbundled submonoids (deprecated)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines unbundled multiplicative and additive submonoids. Instead of using this file,
please use `submonoid G` and `add_submonoid A`, defined in `group_theory.submonoid.basic`.

## Main definitions

`is_add_submonoid (S : set M)` : the predicate that `S` is the underlying subset of an additive
submonoid of `M`. The bundled variant `add_submonoid M` should be used in preference to this.

`is_submonoid (S : set M)` : the predicate that `S` is the underlying subset of a submonoid
of `M`. The bundled variant `submonoid M` should be used in preference to this.

## Tags
submonoid, submonoids, is_submonoid
-/


open BigOperators

variable {M : Type _} [Monoid M] {s : Set M}

variable {A : Type _} [AddMonoid A] {t : Set A}

#print IsAddSubmonoid /-
/-- `s` is an additive submonoid: a set containing 0 and closed under addition.
Note that this structure is deprecated, and the bundled variant `add_submonoid A` should be
preferred. -/
structure IsAddSubmonoid (s : Set A) : Prop where
  zero_mem : (0 : A) ∈ s
  add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s
#align is_add_submonoid IsAddSubmonoid
-/

#print IsSubmonoid /-
/-- `s` is a submonoid: a set containing 1 and closed under multiplication.
Note that this structure is deprecated, and the bundled variant `submonoid M` should be
preferred. -/
@[to_additive]
structure IsSubmonoid (s : Set M) : Prop where
  one_mem : (1 : M) ∈ s
  mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s
#align is_submonoid IsSubmonoid
#align is_add_submonoid IsAddSubmonoid
-/

#print Additive.isAddSubmonoid /-
theorem Additive.isAddSubmonoid {s : Set M} : ∀ is : IsSubmonoid s, @IsAddSubmonoid (Additive M) _ s
  | ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩
#align additive.is_add_submonoid Additive.isAddSubmonoid
-/

#print Additive.isAddSubmonoid_iff /-
theorem Additive.isAddSubmonoid_iff {s : Set M} :
    @IsAddSubmonoid (Additive M) _ s ↔ IsSubmonoid s :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩, Additive.isAddSubmonoid⟩
#align additive.is_add_submonoid_iff Additive.isAddSubmonoid_iff
-/

#print Multiplicative.isSubmonoid /-
theorem Multiplicative.isSubmonoid {s : Set A} :
    ∀ is : IsAddSubmonoid s, @IsSubmonoid (Multiplicative A) _ s
  | ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩
#align multiplicative.is_submonoid Multiplicative.isSubmonoid
-/

#print Multiplicative.isSubmonoid_iff /-
theorem Multiplicative.isSubmonoid_iff {s : Set A} :
    @IsSubmonoid (Multiplicative A) _ s ↔ IsAddSubmonoid s :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩, Multiplicative.isSubmonoid⟩
#align multiplicative.is_submonoid_iff Multiplicative.isSubmonoid_iff
-/

/- warning: is_submonoid.inter -> IsSubmonoid.inter is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s₁ : Set.{u1} M} {s₂ : Set.{u1} M}, (IsSubmonoid.{u1} M _inst_1 s₁) -> (IsSubmonoid.{u1} M _inst_1 s₂) -> (IsSubmonoid.{u1} M _inst_1 (Inter.inter.{u1} (Set.{u1} M) (Set.hasInter.{u1} M) s₁ s₂))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s₁ : Set.{u1} M} {s₂ : Set.{u1} M}, (IsSubmonoid.{u1} M _inst_1 s₁) -> (IsSubmonoid.{u1} M _inst_1 s₂) -> (IsSubmonoid.{u1} M _inst_1 (Inter.inter.{u1} (Set.{u1} M) (Set.instInterSet.{u1} M) s₁ s₂))
Case conversion may be inaccurate. Consider using '#align is_submonoid.inter IsSubmonoid.interₓ'. -/
/-- The intersection of two submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The intersection of two `add_submonoid`s of an `add_monoid` `M` is\nan `add_submonoid` of M."]
theorem IsSubmonoid.inter {s₁ s₂ : Set M} (is₁ : IsSubmonoid s₁) (is₂ : IsSubmonoid s₂) :
    IsSubmonoid (s₁ ∩ s₂) :=
  { one_mem := ⟨is₁.one_mem, is₂.one_mem⟩
    mul_mem := fun x y hx hy => ⟨is₁.mul_mem hx.1 hy.1, is₂.mul_mem hx.2 hy.2⟩ }
#align is_submonoid.inter IsSubmonoid.inter
#align is_add_submonoid.inter IsAddSubmonoid.inter

#print IsSubmonoid.interᵢ /-
/-- The intersection of an indexed set of submonoids of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The intersection of an indexed set of `add_submonoid`s of an `add_monoid` `M` is\nan `add_submonoid` of `M`."]
theorem IsSubmonoid.interᵢ {ι : Sort _} {s : ι → Set M} (h : ∀ y : ι, IsSubmonoid (s y)) :
    IsSubmonoid (Set.interᵢ s) :=
  { one_mem := Set.mem_interᵢ.2 fun y => (h y).one_mem
    mul_mem := fun x₁ x₂ h₁ h₂ =>
      Set.mem_interᵢ.2 fun y => (h y).mul_mem (Set.mem_interᵢ.1 h₁ y) (Set.mem_interᵢ.1 h₂ y) }
#align is_submonoid.Inter IsSubmonoid.interᵢ
#align is_add_submonoid.Inter IsAddSubmonoid.interᵢ
-/

#print isSubmonoid_unionᵢ_of_directed /-
/-- The union of an indexed, directed, nonempty set of submonoids of a monoid `M` is a submonoid
    of `M`. -/
@[to_additive
      "The union of an indexed, directed, nonempty set\nof `add_submonoid`s of an `add_monoid` `M` is an `add_submonoid` of `M`. "]
theorem isSubmonoid_unionᵢ_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set M}
    (hs : ∀ i, IsSubmonoid (s i)) (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubmonoid (⋃ i, s i) :=
  { one_mem :=
      let ⟨i⟩ := hι
      Set.mem_unionᵢ.2 ⟨i, (hs i).one_mem⟩
    mul_mem := fun a b ha hb =>
      let ⟨i, hi⟩ := Set.mem_unionᵢ.1 ha
      let ⟨j, hj⟩ := Set.mem_unionᵢ.1 hb
      let ⟨k, hk⟩ := Directed i j
      Set.mem_unionᵢ.2 ⟨k, (hs k).mul_mem (hk.1 hi) (hk.2 hj)⟩ }
#align is_submonoid_Union_of_directed isSubmonoid_unionᵢ_of_directed
#align is_add_submonoid_Union_of_directed isAddSubmonoid_unionᵢ_of_directed
-/

section powers

#print powers /-
/-- The set of natural number powers `1, x, x², ...` of an element `x` of a monoid. -/
@[to_additive multiples
      "The set of natural number multiples `0, x, 2x, ...` of an element `x` of an `add_monoid`."]
def powers (x : M) : Set M :=
  { y | ∃ n : ℕ, x ^ n = y }
#align powers powers
#align multiples multiples
-/

/- warning: powers.one_mem -> powers.one_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {x : M}, Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (powers.{u1} M _inst_1 x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {x : M}, Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))) (powers.{u1} M _inst_1 x)
Case conversion may be inaccurate. Consider using '#align powers.one_mem powers.one_memₓ'. -/
/-- 1 is in the set of natural number powers of an element of a monoid. -/
@[to_additive "0 is in the set of natural number multiples of an element of an `add_monoid`."]
theorem powers.one_mem {x : M} : (1 : M) ∈ powers x :=
  ⟨0, pow_zero _⟩
#align powers.one_mem powers.one_mem
#align multiples.zero_mem multiples.zero_mem

#print powers.self_mem /-
/-- An element of a monoid is in the set of that element's natural number powers. -/
@[to_additive
      "An element of an `add_monoid` is in the set of that element's natural number multiples."]
theorem powers.self_mem {x : M} : x ∈ powers x :=
  ⟨1, pow_one _⟩
#align powers.self_mem powers.self_mem
#align multiples.self_mem multiples.self_mem
-/

/- warning: powers.mul_mem -> powers.mul_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {x : M} {y : M} {z : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y (powers.{u1} M _inst_1 x)) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) z (powers.{u1} M _inst_1 x)) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y z) (powers.{u1} M _inst_1 x))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {x : M} {y : M} {z : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y (powers.{u1} M _inst_1 x)) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) z (powers.{u1} M _inst_1 x)) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y z) (powers.{u1} M _inst_1 x))
Case conversion may be inaccurate. Consider using '#align powers.mul_mem powers.mul_memₓ'. -/
/-- The set of natural number powers of an element of a monoid is closed under multiplication. -/
@[to_additive
      "The set of natural number multiples of an element of an `add_monoid` is closed under addition."]
theorem powers.mul_mem {x y z : M} : y ∈ powers x → z ∈ powers x → y * z ∈ powers x :=
  fun ⟨n₁, h₁⟩ ⟨n₂, h₂⟩ => ⟨n₁ + n₂, by simp only [pow_add, *]⟩
#align powers.mul_mem powers.mul_mem
#align multiples.add_mem multiples.add_mem

#print powers.isSubmonoid /-
/-- The set of natural number powers of an element of a monoid `M` is a submonoid of `M`. -/
@[to_additive
      "The set of natural number multiples of an element of\nan `add_monoid` `M` is an `add_submonoid` of `M`."]
theorem powers.isSubmonoid (x : M) : IsSubmonoid (powers x) :=
  { one_mem := powers.one_mem
    mul_mem := fun y z => powers.mul_mem }
#align powers.is_submonoid powers.isSubmonoid
#align multiples.is_add_submonoid multiples.isAddSubmonoid
-/

#print Univ.isSubmonoid /-
/-- A monoid is a submonoid of itself. -/
@[to_additive "An `add_monoid` is an `add_submonoid` of itself."]
theorem Univ.isSubmonoid : IsSubmonoid (@Set.univ M) := by constructor <;> simp
#align univ.is_submonoid Univ.isSubmonoid
#align univ.is_add_submonoid Univ.isAddSubmonoid
-/

#print IsSubmonoid.preimage /-
/-- The preimage of a submonoid under a monoid hom is a submonoid of the domain. -/
@[to_additive
      "The preimage of an `add_submonoid` under an `add_monoid` hom is\nan `add_submonoid` of the domain."]
theorem IsSubmonoid.preimage {N : Type _} [Monoid N] {f : M → N} (hf : IsMonoidHom f) {s : Set N}
    (hs : IsSubmonoid s) : IsSubmonoid (f ⁻¹' s) :=
  { one_mem := show f 1 ∈ s by rw [IsMonoidHom.map_one hf] <;> exact hs.one_mem
    mul_mem := fun a b (ha : f a ∈ s) (hb : f b ∈ s) =>
      show f (a * b) ∈ s by rw [IsMonoidHom.map_mul' hf] <;> exact hs.mul_mem ha hb }
#align is_submonoid.preimage IsSubmonoid.preimage
#align is_add_submonoid.preimage IsAddSubmonoid.preimage
-/

#print IsSubmonoid.image /-
/-- The image of a submonoid under a monoid hom is a submonoid of the codomain. -/
@[to_additive
      "The image of an `add_submonoid` under an `add_monoid`\nhom is an `add_submonoid` of the codomain."]
theorem IsSubmonoid.image {γ : Type _} [Monoid γ] {f : M → γ} (hf : IsMonoidHom f) {s : Set M}
    (hs : IsSubmonoid s) : IsSubmonoid (f '' s) :=
  { one_mem := ⟨1, hs.one_mem, hf.map_one⟩
    mul_mem := fun a b ⟨x, hx⟩ ⟨y, hy⟩ =>
      ⟨x * y, hs.mul_mem hx.1 hy.1, by rw [hf.map_mul, hx.2, hy.2]⟩ }
#align is_submonoid.image IsSubmonoid.image
#align is_add_submonoid.image IsAddSubmonoid.image
-/

#print Range.isSubmonoid /-
/-- The image of a monoid hom is a submonoid of the codomain. -/
@[to_additive "The image of an `add_monoid` hom is an `add_submonoid`\nof the codomain."]
theorem Range.isSubmonoid {γ : Type _} [Monoid γ] {f : M → γ} (hf : IsMonoidHom f) :
    IsSubmonoid (Set.range f) := by
  rw [← Set.image_univ]
  exact univ.is_submonoid.image hf
#align range.is_submonoid Range.isSubmonoid
#align range.is_add_submonoid Range.isAddSubmonoid
-/

#print IsSubmonoid.pow_mem /-
/-- Submonoids are closed under natural powers. -/
@[to_additive IsAddSubmonoid.smul_mem
      "An `add_submonoid` is closed under multiplication by naturals."]
theorem IsSubmonoid.pow_mem {a : M} (hs : IsSubmonoid s) (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
  | 0 => by
    rw [pow_zero]
    exact hs.one_mem
  | n + 1 => by
    rw [pow_succ]
    exact hs.mul_mem h IsSubmonoid.pow_mem
#align is_submonoid.pow_mem IsSubmonoid.pow_mem
-/

#print IsSubmonoid.power_subset /-
/-- The set of natural number powers of an element of a submonoid is a subset of the submonoid. -/
@[to_additive IsAddSubmonoid.multiples_subset
      "The set of natural number multiples of an element\nof an `add_submonoid` is a subset of the `add_submonoid`."]
theorem IsSubmonoid.power_subset {a : M} (hs : IsSubmonoid s) (h : a ∈ s) : powers a ⊆ s :=
  fun x ⟨n, hx⟩ => hx ▸ hs.pow_mem h
#align is_submonoid.power_subset IsSubmonoid.power_subset
#align is_add_submonoid.multiples_subset IsAddSubmonoid.multiples_subset
-/

end powers

namespace IsSubmonoid

/- warning: is_submonoid.list_prod_mem -> IsSubmonoid.list_prod_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M}, (IsSubmonoid.{u1} M _inst_1 s) -> (forall {l : List.{u1} M}, (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s)) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M}, (IsSubmonoid.{u1} M _inst_1 s) -> (forall {l : List.{u1} M}, (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s)) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) s))
Case conversion may be inaccurate. Consider using '#align is_submonoid.list_prod_mem IsSubmonoid.list_prod_memₓ'. -/
/-- The product of a list of elements of a submonoid is an element of the submonoid. -/
@[to_additive
      "The sum of a list of elements of an `add_submonoid` is an element of the\n`add_submonoid`."]
theorem list_prod_mem (hs : IsSubmonoid s) : ∀ {l : List M}, (∀ x ∈ l, x ∈ s) → l.Prod ∈ s
  | [], h => hs.one_mem
  | a :: l, h =>
    suffices a * l.Prod ∈ s by simpa
    have : a ∈ s ∧ ∀ x ∈ l, x ∈ s := by simpa using h
    hs.mul_mem this.1 (list_prod_mem this.2)
#align is_submonoid.list_prod_mem IsSubmonoid.list_prod_mem
#align is_add_submonoid.list_sum_mem IsAddSubmonoid.list_sum_mem

#print IsSubmonoid.multiset_prod_mem /-
/-- The product of a multiset of elements of a submonoid of a `comm_monoid` is an element of
the submonoid. -/
@[to_additive
      "The sum of a multiset of elements of an `add_submonoid` of an `add_comm_monoid`\nis an element of the `add_submonoid`. "]
theorem multiset_prod_mem {M} [CommMonoid M] {s : Set M} (hs : IsSubmonoid s) (m : Multiset M) :
    (∀ a ∈ m, a ∈ s) → m.Prod ∈ s :=
  by
  refine' Quotient.inductionOn m fun l hl => _
  rw [Multiset.quot_mk_to_coe, Multiset.coe_prod]
  exact list_prod_mem hs hl
#align is_submonoid.multiset_prod_mem IsSubmonoid.multiset_prod_mem
#align is_add_submonoid.multiset_sum_mem IsAddSubmonoid.multiset_sum_mem
-/

/- warning: is_submonoid.finset_prod_mem -> IsSubmonoid.finset_prod_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {A : Type.{u2}} [_inst_3 : CommMonoid.{u1} M] {s : Set.{u1} M}, (IsSubmonoid.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) s) -> (forall (f : A -> M) (t : Finset.{u2} A), (forall (b : A), (Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) b t) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (f b) s)) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (Finset.prod.{u1, u2} M A _inst_3 t (fun (b : A) => f b)) s))
but is expected to have type
  forall {M : Type.{u2}} {A : Type.{u1}} [_inst_3 : CommMonoid.{u2} M] {s : Set.{u2} M}, (IsSubmonoid.{u2} M (CommMonoid.toMonoid.{u2} M _inst_3) s) -> (forall (f : A -> M) (t : Finset.{u1} A), (forall (b : A), (Membership.mem.{u1, u1} A (Finset.{u1} A) (Finset.instMembershipFinset.{u1} A) b t) -> (Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) (f b) s)) -> (Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) (Finset.prod.{u2, u1} M A _inst_3 t (fun (b : A) => f b)) s))
Case conversion may be inaccurate. Consider using '#align is_submonoid.finset_prod_mem IsSubmonoid.finset_prod_memₓ'. -/
/-- The product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is an element
of the submonoid. -/
@[to_additive
      "The sum of elements of an `add_submonoid` of an `add_comm_monoid` indexed by\na `finset` is an element of the `add_submonoid`."]
theorem finset_prod_mem {M A} [CommMonoid M] {s : Set M} (hs : IsSubmonoid s) (f : A → M) :
    ∀ t : Finset A, (∀ b ∈ t, f b ∈ s) → (∏ b in t, f b) ∈ s
  | ⟨m, hm⟩, _ => multiset_prod_mem hs _ (by simpa)
#align is_submonoid.finset_prod_mem IsSubmonoid.finset_prod_mem
#align is_add_submonoid.finset_sum_mem IsAddSubmonoid.finset_sum_mem

end IsSubmonoid

namespace AddMonoid

#print AddMonoid.InClosure /-
/-- The inductively defined membership predicate for the submonoid generated by a subset of a
    monoid. -/
inductive InClosure (s : Set A) : A → Prop
  | basic {a : A} : a ∈ s → in_closure a
  | zero : in_closure 0
  | add {a b : A} : in_closure a → in_closure b → in_closure (a + b)
#align add_monoid.in_closure AddMonoid.InClosure
-/

end AddMonoid

namespace Monoid

#print Monoid.InClosure /-
/-- The inductively defined membership predicate for the `submonoid` generated by a subset of an
    monoid. -/
@[to_additive]
inductive InClosure (s : Set M) : M → Prop
  | basic {a : M} : a ∈ s → in_closure a
  | one : in_closure 1
  | mul {a b : M} : in_closure a → in_closure b → in_closure (a * b)
#align monoid.in_closure Monoid.InClosure
#align add_monoid.in_closure AddMonoid.InClosure
-/

#print Monoid.Closure /-
/-- The inductively defined submonoid generated by a subset of a monoid. -/
@[to_additive "The inductively defined `add_submonoid` genrated by a subset of an `add_monoid`."]
def Closure (s : Set M) : Set M :=
  { a | InClosure s a }
#align monoid.closure Monoid.Closure
#align add_monoid.closure AddMonoid.Closure
-/

#print Monoid.closure.isSubmonoid /-
@[to_additive]
theorem closure.isSubmonoid (s : Set M) : IsSubmonoid (Closure s) :=
  { one_mem := InClosure.one
    mul_mem := fun a b => InClosure.mul }
#align monoid.closure.is_submonoid Monoid.closure.isSubmonoid
#align add_monoid.closure.is_add_submonoid AddMonoid.closure.isAddSubmonoid
-/

#print Monoid.subset_closure /-
/-- A subset of a monoid is contained in the submonoid it generates. -/
@[to_additive "A subset of an `add_monoid` is contained in the `add_submonoid` it generates."]
theorem subset_closure {s : Set M} : s ⊆ Closure s := fun a => InClosure.basic
#align monoid.subset_closure Monoid.subset_closure
#align add_monoid.subset_closure AddMonoid.subset_closure
-/

#print Monoid.closure_subset /-
/-- The submonoid generated by a set is contained in any submonoid that contains the set. -/
@[to_additive
      "The `add_submonoid` generated by a set is contained in any `add_submonoid` that\ncontains the set."]
theorem closure_subset {s t : Set M} (ht : IsSubmonoid t) (h : s ⊆ t) : Closure s ⊆ t := fun a ha =>
  by induction ha <;> simp [h _, *, IsSubmonoid.one_mem, IsSubmonoid.mul_mem]
#align monoid.closure_subset Monoid.closure_subset
#align add_monoid.closure_subset AddMonoid.closure_subset
-/

#print Monoid.closure_mono /-
/-- Given subsets `t` and `s` of a monoid `M`, if `s ⊆ t`, the submonoid of `M` generated by `s` is
    contained in the submonoid generated by `t`. -/
@[to_additive
      "Given subsets `t` and `s` of an `add_monoid M`, if `s ⊆ t`, the `add_submonoid`\nof `M` generated by `s` is contained in the `add_submonoid` generated by `t`."]
theorem closure_mono {s t : Set M} (h : s ⊆ t) : Closure s ⊆ Closure t :=
  closure_subset (closure.isSubmonoid t) <| Set.Subset.trans h subset_closure
#align monoid.closure_mono Monoid.closure_mono
#align add_monoid.closure_mono AddMonoid.closure_mono
-/

#print Monoid.closure_singleton /-
/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
@[to_additive
      "The `add_submonoid` generated by an element of an `add_monoid` equals the set of\nnatural number multiples of the element."]
theorem closure_singleton {x : M} : Closure ({x} : Set M) = powers x :=
  Set.eq_of_subset_of_subset
      (closure_subset (powers.isSubmonoid x) <| Set.singleton_subset_iff.2 <| powers.self_mem) <|
    IsSubmonoid.power_subset (closure.isSubmonoid _) <| Set.singleton_subset_iff.1 <| subset_closure
#align monoid.closure_singleton Monoid.closure_singleton
#align add_monoid.closure_singleton AddMonoid.closure_singleton
-/

#print Monoid.image_closure /-
/-- The image under a monoid hom of the submonoid generated by a set equals the submonoid generated
    by the image of the set under the monoid hom. -/
@[to_additive
      "The image under an `add_monoid` hom of the `add_submonoid` generated by a set equals\nthe `add_submonoid` generated by the image of the set under the `add_monoid` hom."]
theorem image_closure {A : Type _} [Monoid A] {f : M → A} (hf : IsMonoidHom f) (s : Set M) :
    f '' Closure s = Closure (f '' s) :=
  le_antisymm
    (by
      rintro _ ⟨x, hx, rfl⟩
      apply in_closure.rec_on hx <;> intros
      · solve_by_elim [subset_closure, Set.mem_image_of_mem]
      · rw [hf.map_one]
        apply IsSubmonoid.one_mem (closure.is_submonoid (f '' s))
      · rw [hf.map_mul]
        solve_by_elim [(closure.is_submonoid _).mul_mem] )
    (closure_subset (IsSubmonoid.image hf (closure.isSubmonoid _)) <|
      Set.image_subset _ subset_closure)
#align monoid.image_closure Monoid.image_closure
#align add_monoid.image_closure AddMonoid.image_closure
-/

/- warning: monoid.exists_list_of_mem_closure -> Monoid.exists_list_of_mem_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {a : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a (Monoid.Closure.{u1} M _inst_1 s)) -> (Exists.{succ u1} (List.{u1} M) (fun (l : List.{u1} M) => And (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s)) (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) a)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {a : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a (Monoid.Closure.{u1} M _inst_1 s)) -> (Exists.{succ u1} (List.{u1} M) (fun (l : List.{u1} M) => And (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s)) (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) a)))
Case conversion may be inaccurate. Consider using '#align monoid.exists_list_of_mem_closure Monoid.exists_list_of_mem_closureₓ'. -/
/-- Given an element `a` of the submonoid of a monoid `M` generated by a set `s`, there exists
a list of elements of `s` whose product is `a`. -/
@[to_additive
      "Given an element `a` of the `add_submonoid` of an `add_monoid M` generated by\na set `s`, there exists a list of elements of `s` whose sum is `a`."]
theorem exists_list_of_mem_closure {s : Set M} {a : M} (h : a ∈ Closure s) :
    ∃ l : List M, (∀ x ∈ l, x ∈ s) ∧ l.Prod = a :=
  by
  induction h
  case basic a ha => exists [a]; simp [ha]
  case one => exists []; simp
  case mul a b _ _ ha hb =>
    rcases ha with ⟨la, ha, eqa⟩
    rcases hb with ⟨lb, hb, eqb⟩
    exists la ++ lb
    simp [eqa.symm, eqb.symm, or_imp]
    exact fun a => ⟨ha a, hb a⟩
#align monoid.exists_list_of_mem_closure Monoid.exists_list_of_mem_closure
#align add_monoid.exists_list_of_mem_closure AddMonoid.exists_list_of_mem_closure

/- warning: monoid.mem_closure_union_iff -> Monoid.mem_closure_union_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_3 : CommMonoid.{u1} M] {s : Set.{u1} M} {t : Set.{u1} M} {x : M}, Iff (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x (Monoid.Closure.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) (Union.union.{u1} (Set.{u1} M) (Set.hasUnion.{u1} M) s t))) (Exists.{succ u1} M (fun (y : M) => Exists.{0} (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y (Monoid.Closure.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) s)) (fun (H : Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y (Monoid.Closure.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) s)) => Exists.{succ u1} M (fun (z : M) => Exists.{0} (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) z (Monoid.Closure.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) t)) (fun (H : Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) z (Monoid.Closure.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) t)) => Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))) y z) x)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_3 : CommMonoid.{u1} M] {s : Set.{u1} M} {t : Set.{u1} M} {x : M}, Iff (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (Monoid.Closure.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) (Union.union.{u1} (Set.{u1} M) (Set.instUnionSet.{u1} M) s t))) (Exists.{succ u1} M (fun (y : M) => And (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y (Monoid.Closure.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) s)) (Exists.{succ u1} M (fun (z : M) => And (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) z (Monoid.Closure.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3) t)) (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_3)))) y z) x)))))
Case conversion may be inaccurate. Consider using '#align monoid.mem_closure_union_iff Monoid.mem_closure_union_iffₓ'. -/
/-- Given sets `s, t` of a commutative monoid `M`, `x ∈ M` is in the submonoid of `M` generated by
    `s ∪ t` iff there exists an element of the submonoid generated by `s` and an element of the
    submonoid generated by `t` whose product is `x`. -/
@[to_additive
      "Given sets `s, t` of a commutative `add_monoid M`, `x ∈ M` is in the `add_submonoid`\nof `M` generated by `s ∪ t` iff there exists an element of the `add_submonoid` generated by `s`\nand an element of the `add_submonoid` generated by `t` whose sum is `x`."]
theorem mem_closure_union_iff {M : Type _} [CommMonoid M] {s t : Set M} {x : M} :
    x ∈ Closure (s ∪ t) ↔ ∃ y ∈ Closure s, ∃ z ∈ Closure t, y * z = x :=
  ⟨fun hx =>
    let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure hx
    HL2 ▸
      List.recOn L
        (fun _ =>
          ⟨1, (closure.isSubmonoid _).one_mem, 1, (closure.isSubmonoid _).one_mem, mul_one _⟩)
        (fun hd tl ih HL1 =>
          let ⟨y, hy, z, hz, hyzx⟩ := ih (List.forall_mem_of_forall_mem_cons HL1)
          Or.cases_on (HL1 hd <| List.mem_cons_self _ _)
            (fun hs =>
              ⟨hd * y, (closure.isSubmonoid _).mul_mem (subset_closure hs) hy, z, hz, by
                rw [mul_assoc, List.prod_cons, ← hyzx] <;> rfl⟩)
            fun ht =>
            ⟨y, hy, z * hd, (closure.isSubmonoid _).mul_mem hz (subset_closure ht), by
              rw [← mul_assoc, List.prod_cons, ← hyzx, mul_comm hd] <;> rfl⟩)
        HL1,
    fun ⟨y, hy, z, hz, hyzx⟩ =>
    hyzx ▸
      (closure.isSubmonoid _).mul_mem (closure_mono (Set.subset_union_left _ _) hy)
        (closure_mono (Set.subset_union_right _ _) hz)⟩
#align monoid.mem_closure_union_iff Monoid.mem_closure_union_iff
#align add_monoid.mem_closure_union_iff AddMonoid.mem_closure_union_iff

end Monoid

#print Submonoid.of /-
/-- Create a bundled submonoid from a set `s` and `[is_submonoid s]`. -/
@[to_additive "Create a bundled additive submonoid from a set `s` and `[is_add_submonoid s]`."]
def Submonoid.of {s : Set M} (h : IsSubmonoid s) : Submonoid M :=
  ⟨s, fun _ _ => h.2, h.1⟩
#align submonoid.of Submonoid.of
#align add_submonoid.of AddSubmonoid.of
-/

/- warning: submonoid.is_submonoid -> Submonoid.isSubmonoid is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)), IsSubmonoid.{u1} M _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)), IsSubmonoid.{u1} M _inst_1 (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) S)
Case conversion may be inaccurate. Consider using '#align submonoid.is_submonoid Submonoid.isSubmonoidₓ'. -/
@[to_additive]
theorem Submonoid.isSubmonoid (S : Submonoid M) : IsSubmonoid (S : Set M) :=
  ⟨S.3, fun _ _ => S.2⟩
#align submonoid.is_submonoid Submonoid.isSubmonoid
#align add_submonoid.is_add_submonoid AddSubmonoid.isAddSubmonoid

