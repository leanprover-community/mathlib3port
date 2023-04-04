/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module set_theory.cardinal.ordinal
! leanprover-community/mathlib commit 7c2ce0c2da15516b4e65d0c9e254bb6dc93abd1f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finsupp.Multiset
import Mathbin.Order.Bounded
import Mathbin.SetTheory.Ordinal.Principal
import Mathbin.Tactic.Linarith.Default

/-!
# Cardinals and ordinals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Relationships between cardinals and ordinals, properties of cardinals that are proved
using ordinals.

## Main definitions

* The function `cardinal.aleph'` gives the cardinals listed by their ordinal
  index, and is the inverse of `cardinal.aleph_idx`.
  `aleph' n = n`, `aleph' ω = ℵ₀`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  It is an order isomorphism between ordinals and cardinals.
* The function `cardinal.aleph` gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ℵ₀`, `aleph 1 = succ ℵ₀` is the first
  uncountable cardinal, and so on.
* The function `cardinal.beth` enumerates the Beth cardinals. `beth 0 = ℵ₀`,
  `beth (succ o) = 2 ^ beth o`, and for a limit ordinal `o`, `beth o` is the supremum of `beth a`
  for `a < o`.

## Main Statements

* `cardinal.mul_eq_max` and `cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `cardinal.mk_list_eq_mk` : when `α` is infinite, `α` and `list α` have the same cardinality.
* simp lemmas for inequalities between `bit0 a` and `bit1 b` are registered, making `simp`
  able to prove inequalities about numeral cardinals.

## Tags

cardinal arithmetic (for infinite cardinals)
-/


noncomputable section

open Function Cardinal Set Equiv Order

open Classical Cardinal Ordinal

universe u v w

namespace Cardinal

section UsingOrdinals

open Ordinal

#print Cardinal.ord_isLimit /-
theorem ord_isLimit {c} (co : ℵ₀ ≤ c) : (ord c).IsLimit :=
  by
  refine' ⟨fun h => aleph_0_ne_zero _, fun a => lt_imp_lt_of_le_imp_le fun h => _⟩
  · rw [← Ordinal.le_zero, ord_le] at h
    simpa only [card_zero, nonpos_iff_eq_zero] using co.trans h
  · rw [ord_le] at h⊢
    rwa [← @add_one_of_aleph_0_le (card a), ← card_succ]
    rw [← ord_le, ← le_succ_of_is_limit, ord_le]
    · exact co.trans h
    · rw [ord_aleph_0]
      exact omega_is_limit
#align cardinal.ord_is_limit Cardinal.ord_isLimit
-/

/-! ### Aleph cardinals -/


/- warning: cardinal.aleph_idx.initial_seg -> Cardinal.alephIdx.initialSeg is a dubious translation:
lean 3 declaration is
  InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))
but is expected to have type
  InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.232 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.234 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.232 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.234) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.247 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.249 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.247 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.249)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_idx.initial_seg Cardinal.alephIdx.initialSegₓ'. -/
/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this definition, we register additionally that this function is an initial segment,
  i.e., it is order preserving and its range is an initial segment of the ordinals.
  For the basic function version, see `aleph_idx`.
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def alephIdx.initialSeg : @InitialSeg Cardinal Ordinal (· < ·) (· < ·) :=
  @RelEmbedding.collapse Cardinal Ordinal (· < ·) (· < ·) _ Cardinal.ord.orderEmbedding.ltEmbedding
#align cardinal.aleph_idx.initial_seg Cardinal.alephIdx.initialSeg

#print Cardinal.alephIdx /-
/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ω = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  For an upgraded version stating that the range is everything, see `aleph_idx.rel_iso`. -/
def alephIdx : Cardinal → Ordinal :=
  alephIdx.initialSeg
#align cardinal.aleph_idx Cardinal.alephIdx
-/

/- warning: cardinal.aleph_idx.initial_seg_coe -> Cardinal.alephIdx.initialSeg_coe is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} ((fun (_x : InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) => Cardinal.{u1} -> Ordinal.{u1}) Cardinal.alephIdx.initialSeg.{u1}) (coeFn.{succ (succ u1), succ (succ u1)} (InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) (fun (_x : InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) => Cardinal.{u1} -> Ordinal.{u1}) (FunLike.hasCoeToFun.{succ (succ u1), succ (succ u1), succ (succ u1)} (InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => Ordinal.{u1}) (EmbeddingLike.toFunLike.{succ (succ u1), succ (succ u1), succ (succ u1)} (InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) Cardinal.{u1} Ordinal.{u1} (InitialSeg.embeddingLike.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))))) Cardinal.alephIdx.initialSeg.{u1}) Cardinal.alephIdx.{u1}
but is expected to have type
  Eq.{succ (succ u1)} (forall (a : Cardinal.{u1}), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Cardinal.{u1}) => Ordinal.{u1}) a) (FunLike.coe.{succ (succ u1), succ (succ u1), succ (succ u1)} (InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.232 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.234 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.232 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.234) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.247 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.249 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.247 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.249)) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Cardinal.{u1}) => Ordinal.{u1}) _x) (EmbeddingLike.toFunLike.{succ (succ u1), succ (succ u1), succ (succ u1)} (InitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.232 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.234 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.232 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.234) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.247 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.249 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.247 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.249)) Cardinal.{u1} Ordinal.{u1} (InitialSeg.instEmbeddingLikeInitialSeg.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.232 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.234 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.232 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.234) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.247 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.249 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.247 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.249))) Cardinal.alephIdx.initialSeg.{u1}) Cardinal.alephIdx.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_idx.initial_seg_coe Cardinal.alephIdx.initialSeg_coeₓ'. -/
@[simp]
theorem alephIdx.initialSeg_coe : (alephIdx.initialSeg : Cardinal → Ordinal) = alephIdx :=
  rfl
#align cardinal.aleph_idx.initial_seg_coe Cardinal.alephIdx.initialSeg_coe

/- warning: cardinal.aleph_idx_lt -> Cardinal.alephIdx_lt is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Cardinal.alephIdx.{u1} a) (Cardinal.alephIdx.{u1} b)) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) a b)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (Cardinal.alephIdx.{u1} a) (Cardinal.alephIdx.{u1} b)) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a b)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_idx_lt Cardinal.alephIdx_ltₓ'. -/
@[simp]
theorem alephIdx_lt {a b} : alephIdx a < alephIdx b ↔ a < b :=
  alephIdx.initialSeg.toRelEmbedding.map_rel_iff
#align cardinal.aleph_idx_lt Cardinal.alephIdx_lt

#print Cardinal.alephIdx_le /-
@[simp]
theorem alephIdx_le {a b} : alephIdx a ≤ alephIdx b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, aleph_idx_lt]
#align cardinal.aleph_idx_le Cardinal.alephIdx_le
-/

#print Cardinal.alephIdx.init /-
theorem alephIdx.init {a b} : b < alephIdx a → ∃ c, alephIdx c = b :=
  alephIdx.initialSeg.dropLast
#align cardinal.aleph_idx.init Cardinal.alephIdx.init
-/

/- warning: cardinal.aleph_idx.rel_iso -> Cardinal.alephIdx.relIso is a dubious translation:
lean 3 declaration is
  RelIso.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))
but is expected to have type
  RelIso.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_idx.rel_iso Cardinal.alephIdx.relIsoₓ'. -/
/-- The `aleph'` index function, which gives the ordinal index of a cardinal.
  (The `aleph'` part is because unlike `aleph` this counts also the
  finite stages. So `aleph_idx n = n`, `aleph_idx ℵ₀ = ω`,
  `aleph_idx ℵ₁ = ω + 1` and so on.)
  In this version, we register additionally that this function is an order isomorphism
  between cardinals and ordinals.
  For the basic function version, see `aleph_idx`. -/
def alephIdx.relIso : @RelIso Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) :=
  @RelIso.ofSurjective Cardinal.{u} Ordinal.{u} (· < ·) (· < ·) alephIdx.initialSeg.{u} <|
    (InitialSeg.eq_or_principal alephIdx.initialSeg.{u}).resolve_right fun ⟨o, e⟩ =>
      by
      have : ∀ c, aleph_idx c < o := fun c => (e _).2 ⟨_, rfl⟩
      refine' Ordinal.inductionOn o _ this; intro α r _ h
      let s := ⨆ a, inv_fun aleph_idx (Ordinal.typein r a)
      apply (lt_succ s).not_le
      have I : injective aleph_idx := aleph_idx.initial_seg.to_embedding.injective
      simpa only [typein_enum, left_inverse_inv_fun I (succ s)] using
        le_csupᵢ
          (Cardinal.bddAbove_range.{u, u} fun a : α => inv_fun aleph_idx (Ordinal.typein r a))
          (Ordinal.enum r _ (h (succ s)))
#align cardinal.aleph_idx.rel_iso Cardinal.alephIdx.relIso

/- warning: cardinal.aleph_idx.rel_iso_coe -> Cardinal.alephIdx.relIso_coe is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} ((fun (_x : RelIso.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) => Cardinal.{u1} -> Ordinal.{u1}) Cardinal.alephIdx.relIso.{u1}) (coeFn.{succ (succ u1), succ (succ u1)} (RelIso.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) (fun (_x : RelIso.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) => Cardinal.{u1} -> Ordinal.{u1}) (RelIso.hasCoeToFun.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})))) Cardinal.alephIdx.relIso.{u1}) Cardinal.alephIdx.{u1}
but is expected to have type
  Eq.{succ (succ u1)} (forall (a : Cardinal.{u1}), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Cardinal.{u1}) => Ordinal.{u1}) a) (FunLike.coe.{succ (succ u1), succ (succ u1), succ (succ u1)} (Function.Embedding.{succ (succ u1), succ (succ u1)} Cardinal.{u1} Ordinal.{u1}) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Cardinal.{u1}) => Ordinal.{u1}) _x) (EmbeddingLike.toFunLike.{succ (succ u1), succ (succ u1), succ (succ u1)} (Function.Embedding.{succ (succ u1), succ (succ u1)} Cardinal.{u1} Ordinal.{u1}) Cardinal.{u1} Ordinal.{u1} (Function.instEmbeddingLikeEmbedding.{succ (succ u1), succ (succ u1)} Cardinal.{u1} Ordinal.{u1})) (RelEmbedding.toEmbedding.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465) (RelIso.toRelEmbedding.{succ u1, succ u1} Cardinal.{u1} Ordinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465) Cardinal.alephIdx.relIso.{u1}))) Cardinal.alephIdx.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_idx.rel_iso_coe Cardinal.alephIdx.relIso_coeₓ'. -/
@[simp]
theorem alephIdx.relIso_coe : (alephIdx.relIso : Cardinal → Ordinal) = alephIdx :=
  rfl
#align cardinal.aleph_idx.rel_iso_coe Cardinal.alephIdx.relIso_coe

/- warning: cardinal.type_cardinal -> Cardinal.type_cardinal is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ (succ u1))} Ordinal.{succ u1} (Ordinal.type.{succ u1} Cardinal.{u1} (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) Cardinal.wo.{u1}) Ordinal.univ.{u1, succ u1}
but is expected to have type
  Eq.{succ (succ (succ u1))} Ordinal.{succ u1} (Ordinal.type.{succ u1} Cardinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.737 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.739 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.737 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.739) Cardinal.wo.{u1}) Ordinal.univ.{u1, succ u1}
Case conversion may be inaccurate. Consider using '#align cardinal.type_cardinal Cardinal.type_cardinalₓ'. -/
@[simp]
theorem type_cardinal : @type Cardinal (· < ·) _ = Ordinal.univ.{u, u + 1} := by
  rw [Ordinal.univ_id] <;> exact Quotient.sound ⟨aleph_idx.rel_iso⟩
#align cardinal.type_cardinal Cardinal.type_cardinal

#print Cardinal.mk_cardinal /-
@[simp]
theorem mk_cardinal : (#Cardinal) = univ.{u, u + 1} := by
  simpa only [card_type, card_univ] using congr_arg card type_cardinal
#align cardinal.mk_cardinal Cardinal.mk_cardinal
-/

/- warning: cardinal.aleph'.rel_iso -> Cardinal.Aleph'.relIso is a dubious translation:
lean 3 declaration is
  RelIso.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))
but is expected to have type
  RelIso.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph'.rel_iso Cardinal.Aleph'.relIsoₓ'. -/
/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc.
  In this version, we register additionally that this function is an order isomorphism
  between ordinals and cardinals.
  For the basic function version, see `aleph'`. -/
def Aleph'.relIso :=
  Cardinal.alephIdx.relIso.symm
#align cardinal.aleph'.rel_iso Cardinal.Aleph'.relIso

#print Cardinal.aleph' /-
/-- The `aleph'` function gives the cardinals listed by their ordinal
  index, and is the inverse of `aleph_idx`.
  `aleph' n = n`, `aleph' ω = ω`, `aleph' (ω + 1) = succ ℵ₀`, etc. -/
def aleph' : Ordinal → Cardinal :=
  Aleph'.relIso
#align cardinal.aleph' Cardinal.aleph'
-/

/- warning: cardinal.aleph'.rel_iso_coe -> Cardinal.aleph'.relIso_coe is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} ((fun (_x : RelIso.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) => Ordinal.{u1} -> Cardinal.{u1}) Cardinal.Aleph'.relIso.{u1}) (coeFn.{succ (succ u1), succ (succ u1)} (RelIso.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (fun (_x : RelIso.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) => Ordinal.{u1} -> Cardinal.{u1}) (RelIso.hasCoeToFun.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}))) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) Cardinal.Aleph'.relIso.{u1}) Cardinal.aleph'.{u1}
but is expected to have type
  Eq.{succ (succ u1)} (forall (a : Ordinal.{u1}), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Ordinal.{u1}) => Cardinal.{u1}) a) (FunLike.coe.{succ (succ u1), succ (succ u1), succ (succ u1)} (Function.Embedding.{succ (succ u1), succ (succ u1)} Ordinal.{u1} Cardinal.{u1}) Ordinal.{u1} (fun (_x : Ordinal.{u1}) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Ordinal.{u1}) => Cardinal.{u1}) _x) (EmbeddingLike.toFunLike.{succ (succ u1), succ (succ u1), succ (succ u1)} (Function.Embedding.{succ (succ u1), succ (succ u1)} Ordinal.{u1} Cardinal.{u1}) Ordinal.{u1} Cardinal.{u1} (Function.instEmbeddingLikeEmbedding.{succ (succ u1), succ (succ u1)} Ordinal.{u1} Cardinal.{u1})) (RelEmbedding.toEmbedding.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450) (RelIso.toRelEmbedding.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 : Ordinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465 : Ordinal.{u1}) => LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.463 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.465) (fun (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 : Cardinal.{u1}) (x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450 : Cardinal.{u1}) => LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.448 x._@.Mathlib.SetTheory.Cardinal.Ordinal._hyg.450) Cardinal.Aleph'.relIso.{u1}))) Cardinal.aleph'.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.aleph'.rel_iso_coe Cardinal.aleph'.relIso_coeₓ'. -/
@[simp]
theorem aleph'.relIso_coe : (Aleph'.relIso : Ordinal → Cardinal) = aleph' :=
  rfl
#align cardinal.aleph'.rel_iso_coe Cardinal.aleph'.relIso_coe

/- warning: cardinal.aleph'_lt -> Cardinal.aleph'_lt is a dubious translation:
lean 3 declaration is
  forall {o₁ : Ordinal.{u1}} {o₂ : Ordinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (Cardinal.aleph'.{u1} o₁) (Cardinal.aleph'.{u1} o₂)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o₁ o₂)
but is expected to have type
  forall {o₁ : Ordinal.{u1}} {o₂ : Ordinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Cardinal.aleph'.{u1} o₁) (Cardinal.aleph'.{u1} o₂)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o₁ o₂)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph'_lt Cardinal.aleph'_ltₓ'. -/
@[simp]
theorem aleph'_lt {o₁ o₂ : Ordinal} : aleph' o₁ < aleph' o₂ ↔ o₁ < o₂ :=
  Aleph'.relIso.map_rel_iff
#align cardinal.aleph'_lt Cardinal.aleph'_lt

#print Cardinal.aleph'_le /-
@[simp]
theorem aleph'_le {o₁ o₂ : Ordinal} : aleph' o₁ ≤ aleph' o₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.2 aleph'_lt
#align cardinal.aleph'_le Cardinal.aleph'_le
-/

#print Cardinal.aleph'_alephIdx /-
@[simp]
theorem aleph'_alephIdx (c : Cardinal) : aleph' c.alephIdx = c :=
  Cardinal.alephIdx.relIso.toEquiv.symm_apply_apply c
#align cardinal.aleph'_aleph_idx Cardinal.aleph'_alephIdx
-/

#print Cardinal.alephIdx_aleph' /-
@[simp]
theorem alephIdx_aleph' (o : Ordinal) : (aleph' o).alephIdx = o :=
  Cardinal.alephIdx.relIso.toEquiv.apply_symm_apply o
#align cardinal.aleph_idx_aleph' Cardinal.alephIdx_aleph'
-/

#print Cardinal.aleph'_zero /-
@[simp]
theorem aleph'_zero : aleph' 0 = 0 :=
  by
  rw [← nonpos_iff_eq_zero, ← aleph'_aleph_idx 0, aleph'_le]
  apply Ordinal.zero_le
#align cardinal.aleph'_zero Cardinal.aleph'_zero
-/

/- warning: cardinal.aleph'_succ -> Cardinal.aleph'_succ is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph'.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))) Cardinal.succOrder.{u1} (Cardinal.aleph'.{u1} o))
but is expected to have type
  forall {o : Ordinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph'.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} (Cardinal.aleph'.{u1} o))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph'_succ Cardinal.aleph'_succₓ'. -/
@[simp]
theorem aleph'_succ {o : Ordinal} : aleph' (succ o) = succ (aleph' o) :=
  by
  apply (succ_le_of_lt <| aleph'_lt.2 <| lt_succ o).antisymm' (Cardinal.alephIdx_le.1 <| _)
  rw [aleph_idx_aleph', succ_le_iff, ← aleph'_lt, aleph'_aleph_idx]
  apply lt_succ
#align cardinal.aleph'_succ Cardinal.aleph'_succ

/- warning: cardinal.aleph'_nat -> Cardinal.aleph'_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph'.{u1} ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Ordinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Ordinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Ordinal.{u1} (Nat.castCoe.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1})))) n)) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)
but is expected to have type
  forall (n : Nat), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph'.{u1} (Nat.cast.{succ u1} Ordinal.{u1} (AddMonoidWithOne.toNatCast.{succ u1} Ordinal.{u1} Ordinal.addMonoidWithOne.{u1}) n)) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph'_nat Cardinal.aleph'_natₓ'. -/
@[simp]
theorem aleph'_nat : ∀ n : ℕ, aleph' n = n
  | 0 => aleph'_zero
  | n + 1 => show aleph' (succ n) = n.succ by rw [aleph'_succ, aleph'_nat, nat_succ]
#align cardinal.aleph'_nat Cardinal.aleph'_nat

#print Cardinal.aleph'_le_of_limit /-
theorem aleph'_le_of_limit {o : Ordinal} (l : o.IsLimit) {c} :
    aleph' o ≤ c ↔ ∀ o' < o, aleph' o' ≤ c :=
  ⟨fun h o' h' => (aleph'_le.2 <| h'.le).trans h, fun h =>
    by
    rw [← aleph'_aleph_idx c, aleph'_le, limit_le l]
    intro x h'
    rw [← aleph'_le, aleph'_aleph_idx]
    exact h _ h'⟩
#align cardinal.aleph'_le_of_limit Cardinal.aleph'_le_of_limit
-/

/- warning: cardinal.aleph'_limit -> Cardinal.aleph'_limit is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, (Ordinal.IsLimit.{u1} o) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph'.{u1} o) (supᵢ.{succ u1, succ (succ u1)} Cardinal.{u1} (ConditionallyCompleteLattice.toHasSup.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) (fun (a : coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) => Cardinal.aleph'.{u1} ((fun (a : Type.{succ u1}) (b : Type.{succ u1}) [self : HasLiftT.{succ (succ u1), succ (succ u1)} a b] => self.0) (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (HasLiftT.mk.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (CoeTCₓ.coe.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (coeBase.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (coeSubtype.{succ (succ u1)} Ordinal.{u1} (fun (x : Ordinal.{u1}) => Membership.Mem.{succ u1, succ u1} Ordinal.{u1} (Set.{succ u1} Ordinal.{u1}) (Set.hasMem.{succ u1} Ordinal.{u1}) x (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)))))) a))))
but is expected to have type
  forall {o : Ordinal.{u1}}, (Ordinal.IsLimit.{u1} o) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph'.{u1} o) (supᵢ.{succ u1, succ (succ u1)} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) (Set.Elem.{succ u1} Ordinal.{u1} (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) (fun (a : Set.Elem.{succ u1} Ordinal.{u1} (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) => Cardinal.aleph'.{u1} (Subtype.val.{succ (succ u1)} Ordinal.{u1} (fun (x : Ordinal.{u1}) => Membership.mem.{succ u1, succ u1} Ordinal.{u1} (Set.{succ u1} Ordinal.{u1}) (Set.instMembershipSet.{succ u1} Ordinal.{u1}) x (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) a))))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph'_limit Cardinal.aleph'_limitₓ'. -/
theorem aleph'_limit {o : Ordinal} (ho : o.IsLimit) : aleph' o = ⨆ a : Iio o, aleph' a :=
  by
  refine' le_antisymm _ (csupᵢ_le' fun i => aleph'_le.2 (le_of_lt i.2))
  rw [aleph'_le_of_limit ho]
  exact fun a ha => le_csupᵢ (bdd_above_of_small _) (⟨a, ha⟩ : Iio o)
#align cardinal.aleph'_limit Cardinal.aleph'_limit

#print Cardinal.aleph'_omega /-
@[simp]
theorem aleph'_omega : aleph' ω = ℵ₀ :=
  eq_of_forall_ge_iff fun c =>
    by
    simp only [aleph'_le_of_limit omega_is_limit, lt_omega, exists_imp, aleph_0_le]
    exact forall_swap.trans (forall_congr' fun n => by simp only [forall_eq, aleph'_nat])
#align cardinal.aleph'_omega Cardinal.aleph'_omega
-/

#print Cardinal.aleph'Equiv /-
/-- `aleph'` and `aleph_idx` form an equivalence between `ordinal` and `cardinal` -/
@[simp]
def aleph'Equiv : Ordinal ≃ Cardinal :=
  ⟨aleph', alephIdx, alephIdx_aleph', aleph'_alephIdx⟩
#align cardinal.aleph'_equiv Cardinal.aleph'Equiv
-/

#print Cardinal.aleph /-
/-- The `aleph` function gives the infinite cardinals listed by their
  ordinal index. `aleph 0 = ℵ₀`, `aleph 1 = succ ℵ₀` is the first
  uncountable cardinal, and so on. -/
def aleph (o : Ordinal) : Cardinal :=
  aleph' (ω + o)
#align cardinal.aleph Cardinal.aleph
-/

/- warning: cardinal.aleph_lt -> Cardinal.aleph_lt is a dubious translation:
lean 3 declaration is
  forall {o₁ : Ordinal.{u1}} {o₂ : Ordinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (Cardinal.aleph.{u1} o₁) (Cardinal.aleph.{u1} o₂)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o₁ o₂)
but is expected to have type
  forall {o₁ : Ordinal.{u1}} {o₂ : Ordinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Cardinal.aleph.{u1} o₁) (Cardinal.aleph.{u1} o₂)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o₁ o₂)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_lt Cardinal.aleph_ltₓ'. -/
@[simp]
theorem aleph_lt {o₁ o₂ : Ordinal} : aleph o₁ < aleph o₂ ↔ o₁ < o₂ :=
  aleph'_lt.trans (add_lt_add_iff_left _)
#align cardinal.aleph_lt Cardinal.aleph_lt

#print Cardinal.aleph_le /-
@[simp]
theorem aleph_le {o₁ o₂ : Ordinal} : aleph o₁ ≤ aleph o₂ ↔ o₁ ≤ o₂ :=
  le_iff_le_iff_lt_iff_lt.2 aleph_lt
#align cardinal.aleph_le Cardinal.aleph_le
-/

/- warning: cardinal.max_aleph_eq -> Cardinal.max_aleph_eq is a dubious translation:
lean 3 declaration is
  forall (o₁ : Ordinal.{u1}) (o₂ : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.aleph.{u1} o₁) (Cardinal.aleph.{u1} o₂)) (Cardinal.aleph.{u1} (LinearOrder.max.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1} o₁ o₂))
but is expected to have type
  forall (o₁ : Ordinal.{u1}) (o₂ : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.aleph.{u1} o₁) (Cardinal.aleph.{u1} o₂)) (Cardinal.aleph.{u1} (Max.max.{succ u1} Ordinal.{u1} (LinearOrder.toMax.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1}) o₁ o₂))
Case conversion may be inaccurate. Consider using '#align cardinal.max_aleph_eq Cardinal.max_aleph_eqₓ'. -/
@[simp]
theorem max_aleph_eq (o₁ o₂ : Ordinal) : max (aleph o₁) (aleph o₂) = aleph (max o₁ o₂) :=
  by
  cases' le_total (aleph o₁) (aleph o₂) with h h
  · rw [max_eq_right h, max_eq_right (aleph_le.1 h)]
  · rw [max_eq_left h, max_eq_left (aleph_le.1 h)]
#align cardinal.max_aleph_eq Cardinal.max_aleph_eq

/- warning: cardinal.aleph_succ -> Cardinal.aleph_succ is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))) Cardinal.succOrder.{u1} (Cardinal.aleph.{u1} o))
but is expected to have type
  forall {o : Ordinal.{u1}}, Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)) (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} (Cardinal.aleph.{u1} o))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_succ Cardinal.aleph_succₓ'. -/
@[simp]
theorem aleph_succ {o : Ordinal} : aleph (succ o) = succ (aleph o) := by
  rw [aleph, add_succ, aleph'_succ, aleph]
#align cardinal.aleph_succ Cardinal.aleph_succ

#print Cardinal.aleph_zero /-
@[simp]
theorem aleph_zero : aleph 0 = ℵ₀ := by rw [aleph, add_zero, aleph'_omega]
#align cardinal.aleph_zero Cardinal.aleph_zero
-/

/- warning: cardinal.aleph_limit -> Cardinal.aleph_limit is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, (Ordinal.IsLimit.{u1} o) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph.{u1} o) (supᵢ.{succ u1, succ (succ u1)} Cardinal.{u1} (ConditionallyCompleteLattice.toHasSup.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) (fun (a : coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) => Cardinal.aleph.{u1} ((fun (a : Type.{succ u1}) (b : Type.{succ u1}) [self : HasLiftT.{succ (succ u1), succ (succ u1)} a b] => self.0) (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (HasLiftT.mk.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (CoeTCₓ.coe.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (coeBase.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (coeSubtype.{succ (succ u1)} Ordinal.{u1} (fun (x : Ordinal.{u1}) => Membership.Mem.{succ u1, succ u1} Ordinal.{u1} (Set.{succ u1} Ordinal.{u1}) (Set.hasMem.{succ u1} Ordinal.{u1}) x (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)))))) a))))
but is expected to have type
  forall {o : Ordinal.{u1}}, (Ordinal.IsLimit.{u1} o) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.aleph.{u1} o) (supᵢ.{succ u1, succ (succ u1)} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) (Set.Elem.{succ u1} Ordinal.{u1} (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) (fun (a : Set.Elem.{succ u1} Ordinal.{u1} (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) => Cardinal.aleph.{u1} (Subtype.val.{succ (succ u1)} Ordinal.{u1} (fun (x : Ordinal.{u1}) => Membership.mem.{succ u1, succ u1} Ordinal.{u1} (Set.{succ u1} Ordinal.{u1}) (Set.instMembershipSet.{succ u1} Ordinal.{u1}) x (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) a))))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_limit Cardinal.aleph_limitₓ'. -/
theorem aleph_limit {o : Ordinal} (ho : o.IsLimit) : aleph o = ⨆ a : Iio o, aleph a :=
  by
  apply le_antisymm _ (csupᵢ_le' _)
  · rw [aleph, aleph'_limit (ho.add _)]
    refine' csupᵢ_mono' (bdd_above_of_small _) _
    rintro ⟨i, hi⟩
    cases lt_or_le i ω
    · rcases lt_omega.1 h with ⟨n, rfl⟩
      use ⟨0, ho.pos⟩
      simpa using (nat_lt_aleph_0 n).le
    · exact ⟨⟨_, (sub_lt_of_le h).2 hi⟩, aleph'_le.2 (le_add_sub _ _)⟩
  · exact fun i => aleph_le.2 (le_of_lt i.2)
#align cardinal.aleph_limit Cardinal.aleph_limit

#print Cardinal.aleph0_le_aleph' /-
theorem aleph0_le_aleph' {o : Ordinal} : ℵ₀ ≤ aleph' o ↔ ω ≤ o := by rw [← aleph'_omega, aleph'_le]
#align cardinal.aleph_0_le_aleph' Cardinal.aleph0_le_aleph'
-/

#print Cardinal.aleph0_le_aleph /-
theorem aleph0_le_aleph (o : Ordinal) : ℵ₀ ≤ aleph o :=
  by
  rw [aleph, aleph_0_le_aleph']
  apply Ordinal.le_add_right
#align cardinal.aleph_0_le_aleph Cardinal.aleph0_le_aleph
-/

/- warning: cardinal.aleph'_pos -> Cardinal.aleph'_pos is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (OfNat.mk.{succ u1} Ordinal.{u1} 0 (Zero.zero.{succ u1} Ordinal.{u1} Ordinal.hasZero.{u1}))) o) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1}))) (Cardinal.aleph'.{u1} o))
but is expected to have type
  forall {o : Ordinal.{u1}}, (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Ordinal.{u1} 0 (Zero.toOfNat0.{succ u1} Ordinal.{u1} Ordinal.zero.{u1})) o) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})) (Cardinal.aleph'.{u1} o))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph'_pos Cardinal.aleph'_posₓ'. -/
theorem aleph'_pos {o : Ordinal} (ho : 0 < o) : 0 < aleph' o := by rwa [← aleph'_zero, aleph'_lt]
#align cardinal.aleph'_pos Cardinal.aleph'_pos

/- warning: cardinal.aleph_pos -> Cardinal.aleph_pos is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1}))) (Cardinal.aleph.{u1} o)
but is expected to have type
  forall (o : Ordinal.{u1}), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})) (Cardinal.aleph.{u1} o)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_pos Cardinal.aleph_posₓ'. -/
theorem aleph_pos (o : Ordinal) : 0 < aleph o :=
  aleph0_pos.trans_le (aleph0_le_aleph o)
#align cardinal.aleph_pos Cardinal.aleph_pos

#print Cardinal.aleph_toNat /-
@[simp]
theorem aleph_toNat (o : Ordinal) : (aleph o).toNat = 0 :=
  toNat_apply_of_aleph0_le <| aleph0_le_aleph o
#align cardinal.aleph_to_nat Cardinal.aleph_toNat
-/

/- warning: cardinal.aleph_to_part_enat -> Cardinal.aleph_toPartENat is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), Eq.{1} PartENat (coeFn.{succ (succ u1), succ (succ u1)} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) (fun (_x : AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) => Cardinal.{u1} -> PartENat) (AddMonoidHom.hasCoeToFun.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.addCommMonoidWithOne)))) Cardinal.toPartENat.{u1} (Cardinal.aleph.{u1} o)) (Top.top.{0} PartENat PartENat.hasTop)
but is expected to have type
  forall (o : Ordinal.{u1}), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Cardinal.{u1}) => PartENat) (Cardinal.aleph.{u1} o)) (FunLike.coe.{succ (succ u1), succ (succ u1), 1} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} (fun (_x : Cardinal.{u1}) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Cardinal.{u1}) => PartENat) _x) (AddHomClass.toFunLike.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddZeroClass.toAdd.{succ u1} Cardinal.{u1} (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))))) (AddZeroClass.toAdd.{0} PartENat (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) (AddMonoidHomClass.toAddHomClass.{succ u1, succ u1, 0} (AddMonoidHom.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))) Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat))) (AddMonoidHom.addMonoidHomClass.{succ u1, 0} Cardinal.{u1} PartENat (AddMonoid.toAddZeroClass.{succ u1} Cardinal.{u1} (AddMonoidWithOne.toAddMonoid.{succ u1} Cardinal.{u1} (AddCommMonoidWithOne.toAddMonoidWithOne.{succ u1} Cardinal.{u1} (NonAssocSemiring.toAddCommMonoidWithOne.{succ u1} Cardinal.{u1} (Semiring.toNonAssocSemiring.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1})))))))) (AddMonoid.toAddZeroClass.{0} PartENat (AddMonoidWithOne.toAddMonoid.{0} PartENat (AddCommMonoidWithOne.toAddMonoidWithOne.{0} PartENat PartENat.instAddCommMonoidWithOnePartENat)))))) Cardinal.toPartENat.{u1} (Cardinal.aleph.{u1} o)) (Top.top.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : Cardinal.{u1}) => PartENat) (Cardinal.aleph.{u1} o)) PartENat.instTopPartENat)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_to_part_enat Cardinal.aleph_toPartENatₓ'. -/
@[simp]
theorem aleph_toPartENat (o : Ordinal) : (aleph o).toPartENat = ⊤ :=
  toPartENat_apply_of_aleph0_le <| aleph0_le_aleph o
#align cardinal.aleph_to_part_enat Cardinal.aleph_toPartENat

#print Cardinal.nonempty_out_aleph /-
instance nonempty_out_aleph (o : Ordinal) : Nonempty (aleph o).ord.out.α :=
  by
  rw [out_nonempty_iff_ne_zero, ← ord_zero]
  exact fun h => (ord_injective h).not_gt (aleph_pos o)
#align cardinal.nonempty_out_aleph Cardinal.nonempty_out_aleph
-/

#print Cardinal.ord_aleph_isLimit /-
theorem ord_aleph_isLimit (o : Ordinal) : (aleph o).ord.IsLimit :=
  ord_isLimit <| aleph0_le_aleph _
#align cardinal.ord_aleph_is_limit Cardinal.ord_aleph_isLimit
-/

instance (o : Ordinal) : NoMaxOrder (aleph o).ord.out.α :=
  out_no_max_of_succ_lt (ord_aleph_isLimit o).2

#print Cardinal.exists_aleph /-
theorem exists_aleph {c : Cardinal} : ℵ₀ ≤ c ↔ ∃ o, c = aleph o :=
  ⟨fun h =>
    ⟨alephIdx c - ω, by
      rw [aleph, Ordinal.add_sub_cancel_of_le, aleph'_aleph_idx]
      rwa [← aleph_0_le_aleph', aleph'_aleph_idx]⟩,
    fun ⟨o, e⟩ => e.symm ▸ aleph0_le_aleph _⟩
#align cardinal.exists_aleph Cardinal.exists_aleph
-/

#print Cardinal.aleph'_isNormal /-
theorem aleph'_isNormal : IsNormal (ord ∘ aleph') :=
  ⟨fun o => ord_lt_ord.2 <| aleph'_lt.2 <| lt_succ o, fun o l a => by
    simp only [ord_le, aleph'_le_of_limit l]⟩
#align cardinal.aleph'_is_normal Cardinal.aleph'_isNormal
-/

#print Cardinal.aleph_isNormal /-
theorem aleph_isNormal : IsNormal (ord ∘ aleph) :=
  aleph'_isNormal.trans <| add_isNormal ω
#align cardinal.aleph_is_normal Cardinal.aleph_isNormal
-/

/- warning: cardinal.succ_aleph_0 -> Cardinal.succ_aleph0 is a dubious translation:
lean 3 declaration is
  Eq.{succ (succ u1)} Cardinal.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))) Cardinal.succOrder.{u1} Cardinal.aleph0.{u1}) (Cardinal.aleph.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))
but is expected to have type
  Eq.{succ (succ u1)} Cardinal.{u1} (Order.succ.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.instSuccOrderCardinalToPreorderPartialOrder.{u1} Cardinal.aleph0.{u1}) (Cardinal.aleph.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))
Case conversion may be inaccurate. Consider using '#align cardinal.succ_aleph_0 Cardinal.succ_aleph0ₓ'. -/
theorem succ_aleph0 : succ ℵ₀ = aleph 1 := by rw [← aleph_zero, ← aleph_succ, Ordinal.succ_zero]
#align cardinal.succ_aleph_0 Cardinal.succ_aleph0

/- warning: cardinal.aleph_0_lt_aleph_one -> Cardinal.aleph0_lt_aleph_one is a dubious translation:
lean 3 declaration is
  LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) Cardinal.aleph0.{u1} (Cardinal.aleph.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1}))))
but is expected to have type
  LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) Cardinal.aleph0.{u1} (Cardinal.aleph.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1})))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_lt_aleph_one Cardinal.aleph0_lt_aleph_oneₓ'. -/
theorem aleph0_lt_aleph_one : ℵ₀ < aleph 1 :=
  by
  rw [← succ_aleph_0]
  apply lt_succ
#align cardinal.aleph_0_lt_aleph_one Cardinal.aleph0_lt_aleph_one

/- warning: cardinal.countable_iff_lt_aleph_one -> Cardinal.countable_iff_lt_aleph_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Iff (Set.Countable.{u1} α s) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Cardinal.aleph.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (OfNat.mk.{succ u1} Ordinal.{u1} 1 (One.one.{succ u1} Ordinal.{u1} Ordinal.hasOne.{u1})))))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Iff (Set.Countable.{u1} α s) (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Cardinal.mk.{u1} (Set.Elem.{u1} α s)) (Cardinal.aleph.{u1} (OfNat.ofNat.{succ u1} Ordinal.{u1} 1 (One.toOfNat1.{succ u1} Ordinal.{u1} Ordinal.one.{u1}))))
Case conversion may be inaccurate. Consider using '#align cardinal.countable_iff_lt_aleph_one Cardinal.countable_iff_lt_aleph_oneₓ'. -/
theorem countable_iff_lt_aleph_one {α : Type _} (s : Set α) : s.Countable ↔ (#s) < aleph 1 := by
  rw [← succ_aleph_0, lt_succ_iff, le_aleph_0_iff_set_countable]
#align cardinal.countable_iff_lt_aleph_one Cardinal.countable_iff_lt_aleph_one

#print Cardinal.ord_card_unbounded /-
/-- Ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded : Unbounded (· < ·) { b : Ordinal | b.card.ord = b } :=
  unbounded_lt_iff.2 fun a =>
    ⟨_,
      ⟨by
        dsimp
        rw [card_ord], (lt_ord_succ_card a).le⟩⟩
#align cardinal.ord_card_unbounded Cardinal.ord_card_unbounded
-/

#print Cardinal.eq_aleph'_of_eq_card_ord /-
theorem eq_aleph'_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) : ∃ a, (aleph' a).ord = o :=
  ⟨Cardinal.alephIdx.relIso o.card, by simpa using ho⟩
#align cardinal.eq_aleph'_of_eq_card_ord Cardinal.eq_aleph'_of_eq_card_ord
-/

#print Cardinal.ord_aleph'_eq_enum_card /-
/-- `ord ∘ aleph'` enumerates the ordinals that are cardinals. -/
theorem ord_aleph'_eq_enum_card : ord ∘ aleph' = enumOrd { b : Ordinal | b.card.ord = b } :=
  by
  rw [← eq_enum_ord _ ord_card_unbounded, range_eq_iff]
  exact
    ⟨aleph'_is_normal.strict_mono,
      ⟨fun a => by
        dsimp
        rw [card_ord], fun b hb => eq_aleph'_of_eq_card_ord hb⟩⟩
#align cardinal.ord_aleph'_eq_enum_card Cardinal.ord_aleph'_eq_enum_card
-/

#print Cardinal.ord_card_unbounded' /-
/-- Infinite ordinals that are cardinals are unbounded. -/
theorem ord_card_unbounded' : Unbounded (· < ·) { b : Ordinal | b.card.ord = b ∧ ω ≤ b } :=
  (unbounded_lt_inter_le ω).2 ord_card_unbounded
#align cardinal.ord_card_unbounded' Cardinal.ord_card_unbounded'
-/

#print Cardinal.eq_aleph_of_eq_card_ord /-
theorem eq_aleph_of_eq_card_ord {o : Ordinal} (ho : o.card.ord = o) (ho' : ω ≤ o) :
    ∃ a, (aleph a).ord = o :=
  by
  cases' eq_aleph'_of_eq_card_ord ho with a ha
  use a - ω
  unfold aleph
  rwa [Ordinal.add_sub_cancel_of_le]
  rwa [← aleph_0_le_aleph', ← ord_le_ord, ha, ord_aleph_0]
#align cardinal.eq_aleph_of_eq_card_ord Cardinal.eq_aleph_of_eq_card_ord
-/

#print Cardinal.ord_aleph_eq_enum_card /-
/-- `ord ∘ aleph` enumerates the infinite ordinals that are cardinals. -/
theorem ord_aleph_eq_enum_card : ord ∘ aleph = enumOrd { b : Ordinal | b.card.ord = b ∧ ω ≤ b } :=
  by
  rw [← eq_enum_ord _ ord_card_unbounded']
  use aleph_is_normal.strict_mono
  rw [range_eq_iff]
  refine' ⟨fun a => ⟨_, _⟩, fun b hb => eq_aleph_of_eq_card_ord hb.1 hb.2⟩
  · rw [card_ord]
  · rw [← ord_aleph_0, ord_le_ord]
    exact aleph_0_le_aleph _
#align cardinal.ord_aleph_eq_enum_card Cardinal.ord_aleph_eq_enum_card
-/

/-! ### Beth cardinals -/


#print Cardinal.beth /-
/-- Beth numbers are defined so that `beth 0 = ℵ₀`, `beth (succ o) = 2 ^ (beth o)`, and when `o` is
a limit ordinal, `beth o` is the supremum of `beth o'` for `o' < o`.

Assuming the generalized continuum hypothesis, which is undecidable in ZFC, `beth o = aleph o` for
every `o`. -/
def beth (o : Ordinal.{u}) : Cardinal.{u} :=
  limitRecOn o aleph0 (fun _ x => 2 ^ x) fun a ha IH => ⨆ b : Iio a, IH b.1 b.2
#align cardinal.beth Cardinal.beth
-/

#print Cardinal.beth_zero /-
@[simp]
theorem beth_zero : beth 0 = aleph0 :=
  limitRecOn_zero _ _ _
#align cardinal.beth_zero Cardinal.beth_zero
-/

/- warning: cardinal.beth_succ -> Cardinal.beth_succ is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.beth.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Cardinal.beth.{u1} o))
but is expected to have type
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.beth.{u1} (Order.succ.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) Ordinal.succOrder.{u1} o)) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Cardinal.beth.{u1} o))
Case conversion may be inaccurate. Consider using '#align cardinal.beth_succ Cardinal.beth_succₓ'. -/
@[simp]
theorem beth_succ (o : Ordinal) : beth (succ o) = 2 ^ beth o :=
  limitRecOn_succ _ _ _ _
#align cardinal.beth_succ Cardinal.beth_succ

/- warning: cardinal.beth_limit -> Cardinal.beth_limit is a dubious translation:
lean 3 declaration is
  forall {o : Ordinal.{u1}}, (Ordinal.IsLimit.{u1} o) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.beth.{u1} o) (supᵢ.{succ u1, succ (succ u1)} Cardinal.{u1} (ConditionallyCompleteLattice.toHasSup.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.conditionallyCompleteLinearOrderBot.{u1}))) (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) (fun (a : coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) => Cardinal.beth.{u1} ((fun (a : Type.{succ u1}) (b : Type.{succ u1}) [self : HasLiftT.{succ (succ u1), succ (succ u1)} a b] => self.0) (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (HasLiftT.mk.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (CoeTCₓ.coe.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (coeBase.{succ (succ u1), succ (succ u1)} (coeSort.{succ (succ u1), succ (succ (succ u1))} (Set.{succ u1} Ordinal.{u1}) Type.{succ u1} (Set.hasCoeToSort.{succ u1} Ordinal.{u1}) (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) Ordinal.{u1} (coeSubtype.{succ (succ u1)} Ordinal.{u1} (fun (x : Ordinal.{u1}) => Membership.Mem.{succ u1, succ u1} Ordinal.{u1} (Set.{succ u1} Ordinal.{u1}) (Set.hasMem.{succ u1} Ordinal.{u1}) x (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)))))) a))))
but is expected to have type
  forall {o : Ordinal.{u1}}, (Ordinal.IsLimit.{u1} o) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.beth.{u1} o) (supᵢ.{succ u1, succ (succ u1)} Cardinal.{u1} (ConditionallyCompleteLattice.toSupSet.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{succ u1} Cardinal.{u1} (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{succ u1} Cardinal.{u1} Cardinal.instConditionallyCompleteLinearOrderBotCardinal.{u1}))) (Set.Elem.{succ u1} Ordinal.{u1} (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) (fun (a : Set.Elem.{succ u1} Ordinal.{u1} (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) => Cardinal.beth.{u1} (Subtype.val.{succ (succ u1)} Ordinal.{u1} (fun (x : Ordinal.{u1}) => Membership.mem.{succ u1, succ u1} Ordinal.{u1} (Set.{succ u1} Ordinal.{u1}) (Set.instMembershipSet.{succ u1} Ordinal.{u1}) x (Set.Iio.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) o)) a))))
Case conversion may be inaccurate. Consider using '#align cardinal.beth_limit Cardinal.beth_limitₓ'. -/
theorem beth_limit {o : Ordinal} : o.IsLimit → beth o = ⨆ a : Iio o, beth a :=
  limitRecOn_limit _ _ _ _
#align cardinal.beth_limit Cardinal.beth_limit

/- warning: cardinal.beth_strict_mono -> Cardinal.beth_strictMono is a dubious translation:
lean 3 declaration is
  StrictMono.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))) Cardinal.beth.{u1}
but is expected to have type
  StrictMono.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.beth.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.beth_strict_mono Cardinal.beth_strictMonoₓ'. -/
theorem beth_strictMono : StrictMono beth := by
  intro a b
  induction' b using Ordinal.induction with b IH generalizing a
  intro h
  rcases zero_or_succ_or_limit b with (rfl | ⟨c, rfl⟩ | hb)
  · exact (Ordinal.not_lt_zero a h).elim
  · rw [lt_succ_iff] at h
    rw [beth_succ]
    apply lt_of_le_of_lt _ (cantor _)
    rcases eq_or_lt_of_le h with (rfl | h)
    · rfl
    exact (IH c (lt_succ c) h).le
  · apply (cantor _).trans_le
    rw [beth_limit hb, ← beth_succ]
    exact le_csupᵢ (bdd_above_of_small _) (⟨_, hb.succ_lt h⟩ : Iio b)
#align cardinal.beth_strict_mono Cardinal.beth_strictMono

/- warning: cardinal.beth_mono -> Cardinal.beth_mono is a dubious translation:
lean 3 declaration is
  Monotone.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))) Cardinal.beth.{u1}
but is expected to have type
  Monotone.{succ u1, succ u1} Ordinal.{u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1}) (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1}) Cardinal.beth.{u1}
Case conversion may be inaccurate. Consider using '#align cardinal.beth_mono Cardinal.beth_monoₓ'. -/
theorem beth_mono : Monotone beth :=
  beth_strictMono.Monotone
#align cardinal.beth_mono Cardinal.beth_mono

/- warning: cardinal.beth_lt -> Cardinal.beth_lt is a dubious translation:
lean 3 declaration is
  forall {o₁ : Ordinal.{u1}} {o₂ : Ordinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (Cardinal.beth.{u1} o₁) (Cardinal.beth.{u1} o₂)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o₁ o₂)
but is expected to have type
  forall {o₁ : Ordinal.{u1}} {o₂ : Ordinal.{u1}}, Iff (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Cardinal.beth.{u1} o₁) (Cardinal.beth.{u1} o₂)) (LT.lt.{succ u1} Ordinal.{u1} (Preorder.toLT.{succ u1} Ordinal.{u1} (PartialOrder.toPreorder.{succ u1} Ordinal.{u1} Ordinal.partialOrder.{u1})) o₁ o₂)
Case conversion may be inaccurate. Consider using '#align cardinal.beth_lt Cardinal.beth_ltₓ'. -/
@[simp]
theorem beth_lt {o₁ o₂ : Ordinal} : beth o₁ < beth o₂ ↔ o₁ < o₂ :=
  beth_strictMono.lt_iff_lt
#align cardinal.beth_lt Cardinal.beth_lt

#print Cardinal.beth_le /-
@[simp]
theorem beth_le {o₁ o₂ : Ordinal} : beth o₁ ≤ beth o₂ ↔ o₁ ≤ o₂ :=
  beth_strictMono.le_iff_le
#align cardinal.beth_le Cardinal.beth_le
-/

#print Cardinal.aleph_le_beth /-
theorem aleph_le_beth (o : Ordinal) : aleph o ≤ beth o :=
  by
  apply limit_rec_on o
  · simp
  · intro o h
    rw [aleph_succ, beth_succ, succ_le_iff]
    exact (cantor _).trans_le (power_le_power_left two_ne_zero h)
  · intro o ho IH
    rw [aleph_limit ho, beth_limit ho]
    exact csupᵢ_mono (bdd_above_of_small _) fun x => IH x.1 x.2
#align cardinal.aleph_le_beth Cardinal.aleph_le_beth
-/

#print Cardinal.aleph0_le_beth /-
theorem aleph0_le_beth (o : Ordinal) : ℵ₀ ≤ beth o :=
  (aleph0_le_aleph o).trans <| aleph_le_beth o
#align cardinal.aleph_0_le_beth Cardinal.aleph0_le_beth
-/

/- warning: cardinal.beth_pos -> Cardinal.beth_pos is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1}))) (Cardinal.beth.{u1} o)
but is expected to have type
  forall (o : Ordinal.{u1}), LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})) (Cardinal.beth.{u1} o)
Case conversion may be inaccurate. Consider using '#align cardinal.beth_pos Cardinal.beth_posₓ'. -/
theorem beth_pos (o : Ordinal) : 0 < beth o :=
  aleph0_pos.trans_le <| aleph0_le_beth o
#align cardinal.beth_pos Cardinal.beth_pos

#print Cardinal.beth_ne_zero /-
theorem beth_ne_zero (o : Ordinal) : beth o ≠ 0 :=
  (beth_pos o).ne'
#align cardinal.beth_ne_zero Cardinal.beth_ne_zero
-/

#print Cardinal.beth_normal /-
theorem beth_normal : IsNormal.{u} fun o => (beth o).ord :=
  (isNormal_iff_strictMono_limit _).2
    ⟨ord_strictMono.comp beth_strictMono, fun o ho a ha =>
      by
      rw [beth_limit ho, ord_le]
      exact csupᵢ_le' fun b => ord_le.1 (ha _ b.2)⟩
#align cardinal.beth_normal Cardinal.beth_normal
-/

/-! ### Properties of `mul` -/


/- warning: cardinal.mul_eq_self -> Cardinal.mul_eq_self is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) c c) c)
but is expected to have type
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) c c) c)
Case conversion may be inaccurate. Consider using '#align cardinal.mul_eq_self Cardinal.mul_eq_selfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
theorem mul_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c * c = c :=
  by
  refine' le_antisymm _ (by simpa only [mul_one] using mul_le_mul_left' (one_le_aleph_0.trans h) c)
  -- the only nontrivial part is `c * c ≤ c`. We prove it inductively.
  refine' Acc.recOn (cardinal.lt_wf.apply c) (fun c _ => Quotient.inductionOn c fun α IH ol => _) h
  -- consider the minimal well-order `r` on `α` (a type with cardinality `c`).
  rcases ord_eq α with ⟨r, wo, e⟩
  skip
  letI := linearOrderOfSTO r
  haveI : IsWellOrder α (· < ·) := wo
  -- Define an order `s` on `α × α` by writing `(a, b) < (c, d)` if `max a b < max c d`, or
  -- the max are equal and `a < c`, or the max are equal and `a = c` and `b < d`.
  let g : α × α → α := fun p => max p.1 p.2
  let f : α × α ↪ Ordinal × α × α :=
    ⟨fun p : α × α => (typein (· < ·) (g p), p), fun p q => congr_arg Prod.snd⟩
  let s := f ⁻¹'o Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))
  -- this is a well order on `α × α`.
  haveI : IsWellOrder _ s := (RelEmbedding.preimage _ _).IsWellOrder
  /- it suffices to show that this well order is smaller than `r`
       if it were larger, then `r` would be a strict prefix of `s`. It would be contained in
      `β × β` for some `β` of cardinality `< c`. By the inductive assumption, this set has the
      same cardinality as `β` (or it is finite if `β` is finite), so it is `< c`, which is a
      contradiction. -/
  suffices type s ≤ type r by exact card_le_card this
  refine' le_of_forall_lt fun o h => _
  rcases typein_surj s h with ⟨p, rfl⟩
  rw [← e, lt_ord]
  refine'
    lt_of_le_of_lt (_ : _ ≤ card (succ (typein (· < ·) (g p))) * card (succ (typein (· < ·) (g p))))
      _
  · have : { q | s q p } ⊆ insert (g p) { x | x < g p } ×ˢ insert (g p) { x | x < g p } :=
      by
      intro q h
      simp only [s, embedding.coe_fn_mk, Order.Preimage, typein_lt_typein, Prod.lex_def,
        typein_inj] at h
      exact max_le_iff.1 (le_iff_lt_or_eq.2 <| h.imp_right And.left)
    suffices H : (insert (g p) { x | r x (g p) } : Set α) ≃ Sum { x | r x (g p) } PUnit
    ·
      exact
        ⟨(Set.embeddingOfSubset _ _ this).trans
            ((Equiv.Set.prod _ _).trans (H.prod_congr H)).toEmbedding⟩
    refine' (Equiv.Set.insert _).trans ((Equiv.refl _).sumCongr punit_equiv_punit)
    apply @irrefl _ r
  cases' lt_or_le (card (succ (typein (· < ·) (g p)))) ℵ₀ with qo qo
  · exact (mul_lt_aleph_0 qo qo).trans_le ol
  · suffices
    · exact (IH _ this qo).trans_lt this
    rw [← lt_ord]
    apply (ord_is_limit ol).2
    rw [mk_def, e]
    apply typein_lt_type
#align cardinal.mul_eq_self Cardinal.mul_eq_self

end UsingOrdinals

/- warning: cardinal.mul_eq_max -> Cardinal.mul_eq_max is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_eq_max Cardinal.mul_eq_maxₓ'. -/
/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem mul_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b :=
  le_antisymm
      (mul_eq_self (ha.trans (le_max_left a b)) ▸
        mul_le_mul' (le_max_left _ _) (le_max_right _ _)) <|
    max_le (by simpa only [mul_one] using mul_le_mul_left' (one_le_aleph_0.trans hb) a)
      (by simpa only [one_mul] using mul_le_mul_right' (one_le_aleph_0.trans ha) b)
#align cardinal.mul_eq_max Cardinal.mul_eq_max

/- warning: cardinal.mul_mk_eq_max -> Cardinal.mul_mk_eq_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] [_inst_2 : Infinite.{succ u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] [_inst_2 : Infinite.{succ u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_mk_eq_max Cardinal.mul_mk_eq_maxₓ'. -/
@[simp]
theorem mul_mk_eq_max {α β : Type _} [Infinite α] [Infinite β] : (#α) * (#β) = max (#α) (#β) :=
  mul_eq_max (aleph0_le_mk α) (aleph0_le_mk β)
#align cardinal.mul_mk_eq_max Cardinal.mul_mk_eq_max

/- warning: cardinal.aleph_mul_aleph -> Cardinal.aleph_mul_aleph is a dubious translation:
lean 3 declaration is
  forall (o₁ : Ordinal.{u1}) (o₂ : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.aleph.{u1} o₁) (Cardinal.aleph.{u1} o₂)) (Cardinal.aleph.{u1} (LinearOrder.max.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1} o₁ o₂))
but is expected to have type
  forall (o₁ : Ordinal.{u1}) (o₂ : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.aleph.{u1} o₁) (Cardinal.aleph.{u1} o₂)) (Cardinal.aleph.{u1} (Max.max.{succ u1} Ordinal.{u1} (LinearOrder.toMax.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1}) o₁ o₂))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_mul_aleph Cardinal.aleph_mul_alephₓ'. -/
@[simp]
theorem aleph_mul_aleph (o₁ o₂ : Ordinal) : aleph o₁ * aleph o₂ = aleph (max o₁ o₂) := by
  rw [Cardinal.mul_eq_max (aleph_0_le_aleph o₁) (aleph_0_le_aleph o₂), max_aleph_eq]
#align cardinal.aleph_mul_aleph Cardinal.aleph_mul_aleph

/- warning: cardinal.aleph_0_mul_eq -> Cardinal.aleph0_mul_eq is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.aleph0.{u1} a) a)
but is expected to have type
  forall {a : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.aleph0.{u1} a) a)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_mul_eq Cardinal.aleph0_mul_eqₓ'. -/
@[simp]
theorem aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : ℵ₀ * a = a :=
  (mul_eq_max le_rfl ha).trans (max_eq_right ha)
#align cardinal.aleph_0_mul_eq Cardinal.aleph0_mul_eq

/- warning: cardinal.mul_aleph_0_eq -> Cardinal.mul_aleph0_eq is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a Cardinal.aleph0.{u1}) a)
but is expected to have type
  forall {a : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a Cardinal.aleph0.{u1}) a)
Case conversion may be inaccurate. Consider using '#align cardinal.mul_aleph_0_eq Cardinal.mul_aleph0_eqₓ'. -/
@[simp]
theorem mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a * ℵ₀ = a :=
  (mul_eq_max ha le_rfl).trans (max_eq_left ha)
#align cardinal.mul_aleph_0_eq Cardinal.mul_aleph0_eq

/- warning: cardinal.aleph_0_mul_mk_eq -> Cardinal.aleph0_mul_mk_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.aleph0.{u1} (Cardinal.mk.{u1} α)) (Cardinal.mk.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.aleph0.{u1} (Cardinal.mk.{u1} α)) (Cardinal.mk.{u1} α)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_mul_mk_eq Cardinal.aleph0_mul_mk_eqₓ'. -/
@[simp]
theorem aleph0_mul_mk_eq {α : Type _} [Infinite α] : ℵ₀ * (#α) = (#α) :=
  aleph0_mul_eq (aleph0_le_mk α)
#align cardinal.aleph_0_mul_mk_eq Cardinal.aleph0_mul_mk_eq

/- warning: cardinal.mk_mul_aleph_0_eq -> Cardinal.mk_mul_aleph0_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1}) (Cardinal.mk.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1}) (Cardinal.mk.{u1} α)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_mul_aleph_0_eq Cardinal.mk_mul_aleph0_eqₓ'. -/
@[simp]
theorem mk_mul_aleph0_eq {α : Type _} [Infinite α] : (#α) * ℵ₀ = (#α) :=
  mul_aleph0_eq (aleph0_le_mk α)
#align cardinal.mk_mul_aleph_0_eq Cardinal.mk_mul_aleph0_eq

/- warning: cardinal.aleph_0_mul_aleph -> Cardinal.aleph0_mul_aleph is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) Cardinal.aleph0.{u1} (Cardinal.aleph.{u1} o)) (Cardinal.aleph.{u1} o)
but is expected to have type
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) Cardinal.aleph0.{u1} (Cardinal.aleph.{u1} o)) (Cardinal.aleph.{u1} o)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_0_mul_aleph Cardinal.aleph0_mul_alephₓ'. -/
@[simp]
theorem aleph0_mul_aleph (o : Ordinal) : ℵ₀ * aleph o = aleph o :=
  aleph0_mul_eq (aleph0_le_aleph o)
#align cardinal.aleph_0_mul_aleph Cardinal.aleph0_mul_aleph

/- warning: cardinal.aleph_mul_aleph_0 -> Cardinal.aleph_mul_aleph0 is a dubious translation:
lean 3 declaration is
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) (Cardinal.aleph.{u1} o) Cardinal.aleph0.{u1}) (Cardinal.aleph.{u1} o)
but is expected to have type
  forall (o : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) (Cardinal.aleph.{u1} o) Cardinal.aleph0.{u1}) (Cardinal.aleph.{u1} o)
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_mul_aleph_0 Cardinal.aleph_mul_aleph0ₓ'. -/
@[simp]
theorem aleph_mul_aleph0 (o : Ordinal) : aleph o * ℵ₀ = aleph o :=
  mul_aleph0_eq (aleph0_le_aleph o)
#align cardinal.aleph_mul_aleph_0 Cardinal.aleph_mul_aleph0

/- warning: cardinal.mul_lt_of_lt -> Cardinal.mul_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) a c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) b c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) c)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) c)
Case conversion may be inaccurate. Consider using '#align cardinal.mul_lt_of_lt Cardinal.mul_lt_of_ltₓ'. -/
theorem mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a * b < c :=
  (mul_le_mul' (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_le (max a b) ℵ₀).elim (fun h => (mul_lt_aleph0 h h).trans_le hc) fun h =>
      by
      rw [mul_eq_self h]
      exact max_lt h1 h2
#align cardinal.mul_lt_of_lt Cardinal.mul_lt_of_lt

/- warning: cardinal.mul_le_max_of_aleph_0_le_left -> Cardinal.mul_le_max_of_aleph0_le_left is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_le_max_of_aleph_0_le_left Cardinal.mul_le_max_of_aleph0_le_leftₓ'. -/
theorem mul_le_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) : a * b ≤ max a b :=
  by
  convert mul_le_mul' (le_max_left a b) (le_max_right a b)
  rw [mul_eq_self]
  refine' h.trans (le_max_left a b)
#align cardinal.mul_le_max_of_aleph_0_le_left Cardinal.mul_le_max_of_aleph0_le_left

/- warning: cardinal.mul_eq_max_of_aleph_0_le_left -> Cardinal.mul_eq_max_of_aleph0_le_left is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_eq_max_of_aleph_0_le_left Cardinal.mul_eq_max_of_aleph0_le_leftₓ'. -/
theorem mul_eq_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) (h' : b ≠ 0) : a * b = max a b :=
  by
  cases' le_or_lt ℵ₀ b with hb hb
  · exact mul_eq_max h hb
  refine' (mul_le_max_of_aleph_0_le_left h).antisymm _
  have : b ≤ a := hb.le.trans h
  rw [max_eq_left this]
  convert mul_le_mul_left' (one_le_iff_ne_zero.mpr h') _
  rw [mul_one]
#align cardinal.mul_eq_max_of_aleph_0_le_left Cardinal.mul_eq_max_of_aleph0_le_left

/- warning: cardinal.mul_le_max_of_aleph_0_le_right -> Cardinal.mul_le_max_of_aleph0_le_right is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_le_max_of_aleph_0_le_right Cardinal.mul_le_max_of_aleph0_le_rightₓ'. -/
theorem mul_le_max_of_aleph0_le_right {a b : Cardinal} (h : ℵ₀ ≤ b) : a * b ≤ max a b := by
  simpa only [mul_comm, max_comm] using mul_le_max_of_aleph_0_le_left h
#align cardinal.mul_le_max_of_aleph_0_le_right Cardinal.mul_le_max_of_aleph0_le_right

/- warning: cardinal.mul_eq_max_of_aleph_0_le_right -> Cardinal.mul_eq_max_of_aleph0_le_right is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_eq_max_of_aleph_0_le_right Cardinal.mul_eq_max_of_aleph0_le_rightₓ'. -/
theorem mul_eq_max_of_aleph0_le_right {a b : Cardinal} (h' : a ≠ 0) (h : ℵ₀ ≤ b) :
    a * b = max a b := by
  rw [mul_comm, max_comm]
  exact mul_eq_max_of_aleph_0_le_left h h'
#align cardinal.mul_eq_max_of_aleph_0_le_right Cardinal.mul_eq_max_of_aleph0_le_right

/- warning: cardinal.mul_eq_max' -> Cardinal.mul_eq_max' is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b)) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b)) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_eq_max' Cardinal.mul_eq_max'ₓ'. -/
theorem mul_eq_max' {a b : Cardinal} (h : ℵ₀ ≤ a * b) : a * b = max a b :=
  by
  rcases aleph_0_le_mul_iff.mp h with ⟨ha, hb, ha' | hb'⟩
  · exact mul_eq_max_of_aleph_0_le_left ha' hb
  · exact mul_eq_max_of_aleph_0_le_right ha hb'
#align cardinal.mul_eq_max' Cardinal.mul_eq_max'

/- warning: cardinal.mul_le_max -> Cardinal.mul_le_max is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b) Cardinal.aleph0.{u1})
but is expected to have type
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.mul_le_max Cardinal.mul_le_maxₓ'. -/
theorem mul_le_max (a b : Cardinal) : a * b ≤ max (max a b) ℵ₀ :=
  by
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rcases eq_or_ne b 0 with (rfl | hb0); · simp
  cases' le_or_lt ℵ₀ a with ha ha
  · rw [mul_eq_max_of_aleph_0_le_left ha hb0]
    exact le_max_left _ _
  · cases' le_or_lt ℵ₀ b with hb hb
    · rw [mul_comm, mul_eq_max_of_aleph_0_le_left hb ha0, max_comm]
      exact le_max_left _ _
    · exact le_max_of_le_right (mul_lt_aleph_0 ha hb).le
#align cardinal.mul_le_max Cardinal.mul_le_max

/- warning: cardinal.mul_eq_left -> Cardinal.mul_eq_left is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} b a) -> (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) a)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} b a) -> (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) a)
Case conversion may be inaccurate. Consider using '#align cardinal.mul_eq_left Cardinal.mul_eq_leftₓ'. -/
theorem mul_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a := by
  rw [mul_eq_max_of_aleph_0_le_left ha hb', max_eq_left hb]
#align cardinal.mul_eq_left Cardinal.mul_eq_left

/- warning: cardinal.mul_eq_right -> Cardinal.mul_eq_right is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} a b) -> (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) b)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} a b) -> (Ne.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) b)
Case conversion may be inaccurate. Consider using '#align cardinal.mul_eq_right Cardinal.mul_eq_rightₓ'. -/
theorem mul_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b := by
  rw [mul_comm, mul_eq_left hb ha ha']
#align cardinal.mul_eq_right Cardinal.mul_eq_right

/- warning: cardinal.le_mul_left -> Cardinal.le_mul_left is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} a (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) b a))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} a (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) b a))
Case conversion may be inaccurate. Consider using '#align cardinal.le_mul_left Cardinal.le_mul_leftₓ'. -/
theorem le_mul_left {a b : Cardinal} (h : b ≠ 0) : a ≤ b * a :=
  by
  convert mul_le_mul_right' (one_le_iff_ne_zero.mpr h) _
  rw [one_mul]
#align cardinal.le_mul_left Cardinal.le_mul_left

/- warning: cardinal.le_mul_right -> Cardinal.le_mul_right is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} a (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} a (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.le_mul_right Cardinal.le_mul_rightₓ'. -/
theorem le_mul_right {a b : Cardinal} (h : b ≠ 0) : a ≤ a * b :=
  by
  rw [mul_comm]
  exact le_mul_left h
#align cardinal.le_mul_right Cardinal.le_mul_right

/- warning: cardinal.mul_eq_left_iff -> Cardinal.mul_eq_left_iff is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.hasMul.{u1}) a b) a) (Or (And (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} Cardinal.aleph0.{u1} b) a) (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1}))))) (Or (Eq.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Eq.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1}))))))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HMul.hMul.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHMul.{succ u1} Cardinal.{u1} Cardinal.instMulCardinal.{u1}) a b) a) (Or (And (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) Cardinal.aleph0.{u1} b) a) (Ne.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})))) (Or (Eq.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))) (Eq.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1})))))
Case conversion may be inaccurate. Consider using '#align cardinal.mul_eq_left_iff Cardinal.mul_eq_left_iffₓ'. -/
theorem mul_eq_left_iff {a b : Cardinal} : a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 :=
  by
  rw [max_le_iff]
  refine' ⟨fun h => _, _⟩
  · cases' le_or_lt ℵ₀ a with ha ha
    · have : a ≠ 0 := by
        rintro rfl
        exact ha.not_lt aleph_0_pos
      left
      use ha
      · rw [← not_lt]
        exact fun hb => ne_of_gt (hb.trans_le (le_mul_left this)) h
      · rintro rfl
        apply this
        rw [MulZeroClass.mul_zero] at h
        exact h.symm
    right
    by_cases h2a : a = 0
    · exact Or.inr h2a
    have hb : b ≠ 0 := by
      rintro rfl
      apply h2a
      rw [MulZeroClass.mul_zero] at h
      exact h.symm
    left
    rw [← h, mul_lt_aleph_0_iff, lt_aleph_0, lt_aleph_0] at ha
    rcases ha with (rfl | rfl | ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩)
    contradiction
    contradiction
    rw [← Ne] at h2a
    rw [← one_le_iff_ne_zero] at h2a hb
    norm_cast  at h2a hb h⊢
    apply le_antisymm _ hb
    rw [← not_lt]
    apply fun h2b => ne_of_gt _ h
    conv_lhs => rw [← mul_one n]
    rwa [mul_lt_mul_left]
    apply Nat.lt_of_succ_le h2a
  · rintro (⟨⟨ha, hab⟩, hb⟩ | rfl | rfl)
    · rw [mul_eq_max_of_aleph_0_le_left ha hb, max_eq_left hab]
    all_goals simp
#align cardinal.mul_eq_left_iff Cardinal.mul_eq_left_iff

/-! ### Properties of `add` -/


/- warning: cardinal.add_eq_self -> Cardinal.add_eq_self is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) c c) c)
but is expected to have type
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) c c) c)
Case conversion may be inaccurate. Consider using '#align cardinal.add_eq_self Cardinal.add_eq_selfₓ'. -/
/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
theorem add_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c + c = c :=
  le_antisymm
    (by
      simpa only [Nat.cast_bit0, Nat.cast_one, mul_eq_self h, two_mul] using
        mul_le_mul_right' ((nat_lt_aleph_0 2).le.trans h) c)
    (self_le_add_left c c)
#align cardinal.add_eq_self Cardinal.add_eq_self

/- warning: cardinal.add_eq_max -> Cardinal.add_eq_max is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.add_eq_max Cardinal.add_eq_maxₓ'. -/
/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
theorem add_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) : a + b = max a b :=
  le_antisymm
      (add_eq_self (ha.trans (le_max_left a b)) ▸
        add_le_add (le_max_left _ _) (le_max_right _ _)) <|
    max_le (self_le_add_right _ _) (self_le_add_left _ _)
#align cardinal.add_eq_max Cardinal.add_eq_max

/- warning: cardinal.add_eq_max' -> Cardinal.add_eq_max' is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b))
Case conversion may be inaccurate. Consider using '#align cardinal.add_eq_max' Cardinal.add_eq_max'ₓ'. -/
theorem add_eq_max' {a b : Cardinal} (ha : ℵ₀ ≤ b) : a + b = max a b := by
  rw [add_comm, max_comm, add_eq_max ha]
#align cardinal.add_eq_max' Cardinal.add_eq_max'

/- warning: cardinal.add_mk_eq_max -> Cardinal.add_mk_eq_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} [_inst_1 : Infinite.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} [_inst_1 : Infinite.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
Case conversion may be inaccurate. Consider using '#align cardinal.add_mk_eq_max Cardinal.add_mk_eq_maxₓ'. -/
@[simp]
theorem add_mk_eq_max {α β : Type _} [Infinite α] : (#α) + (#β) = max (#α) (#β) :=
  add_eq_max (aleph0_le_mk α)
#align cardinal.add_mk_eq_max Cardinal.add_mk_eq_max

/- warning: cardinal.add_mk_eq_max' -> Cardinal.add_mk_eq_max' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u1}} [_inst_1 : Infinite.{succ u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u1}} [_inst_1 : Infinite.{succ u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
Case conversion may be inaccurate. Consider using '#align cardinal.add_mk_eq_max' Cardinal.add_mk_eq_max'ₓ'. -/
@[simp]
theorem add_mk_eq_max' {α β : Type _} [Infinite β] : (#α) + (#β) = max (#α) (#β) :=
  add_eq_max' (aleph0_le_mk β)
#align cardinal.add_mk_eq_max' Cardinal.add_mk_eq_max'

/- warning: cardinal.add_le_max -> Cardinal.add_le_max is a dubious translation:
lean 3 declaration is
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} a b) Cardinal.aleph0.{u1})
but is expected to have type
  forall (a : Cardinal.{u1}) (b : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) a b) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.add_le_max Cardinal.add_le_maxₓ'. -/
theorem add_le_max (a b : Cardinal) : a + b ≤ max (max a b) ℵ₀ :=
  by
  cases' le_or_lt ℵ₀ a with ha ha
  · rw [add_eq_max ha]
    exact le_max_left _ _
  · cases' le_or_lt ℵ₀ b with hb hb
    · rw [add_comm, add_eq_max hb, max_comm]
      exact le_max_left _ _
    · exact le_max_of_le_right (add_lt_aleph_0 ha hb).le
#align cardinal.add_le_max Cardinal.add_le_max

/- warning: cardinal.add_le_of_le -> Cardinal.add_le_of_le is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} a c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} b c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) c)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} a c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} b c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) c)
Case conversion may be inaccurate. Consider using '#align cardinal.add_le_of_le Cardinal.add_le_of_leₓ'. -/
theorem add_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c :=
  (add_le_add h1 h2).trans <| le_of_eq <| add_eq_self hc
#align cardinal.add_le_of_le Cardinal.add_le_of_le

/- warning: cardinal.add_lt_of_lt -> Cardinal.add_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) a c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) b c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) c)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) c)
Case conversion may be inaccurate. Consider using '#align cardinal.add_lt_of_lt Cardinal.add_lt_of_ltₓ'. -/
theorem add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a + b < c :=
  (add_le_add (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_le (max a b) ℵ₀).elim (fun h => (add_lt_aleph0 h h).trans_le hc) fun h => by
      rw [add_eq_self h] <;> exact max_lt h1 h2
#align cardinal.add_lt_of_lt Cardinal.add_lt_of_lt

/- warning: cardinal.eq_of_add_eq_of_aleph_0_le -> Cardinal.eq_of_add_eq_of_aleph0_le is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) a c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} b c)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) c) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} b c)
Case conversion may be inaccurate. Consider using '#align cardinal.eq_of_add_eq_of_aleph_0_le Cardinal.eq_of_add_eq_of_aleph0_leₓ'. -/
theorem eq_of_add_eq_of_aleph0_le {a b c : Cardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ ≤ c) :
    b = c := by
  apply le_antisymm
  · rw [← h]
    apply self_le_add_left
  rw [← not_lt]; intro hb
  have : a + b < c := add_lt_of_lt hc ha hb
  simpa [h, lt_irrefl] using this
#align cardinal.eq_of_add_eq_of_aleph_0_le Cardinal.eq_of_add_eq_of_aleph0_le

/- warning: cardinal.add_eq_left -> Cardinal.add_eq_left is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} b a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) a)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} b a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) a)
Case conversion may be inaccurate. Consider using '#align cardinal.add_eq_left Cardinal.add_eq_leftₓ'. -/
theorem add_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) : a + b = a := by
  rw [add_eq_max ha, max_eq_left hb]
#align cardinal.add_eq_left Cardinal.add_eq_left

/- warning: cardinal.add_eq_right -> Cardinal.add_eq_right is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} b) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} a b) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) b)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} b) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} a b) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) b)
Case conversion may be inaccurate. Consider using '#align cardinal.add_eq_right Cardinal.add_eq_rightₓ'. -/
theorem add_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) : a + b = b := by
  rw [add_comm, add_eq_left hb ha]
#align cardinal.add_eq_right Cardinal.add_eq_right

/- warning: cardinal.add_eq_left_iff -> Cardinal.add_eq_left_iff is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) a) (Or (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} Cardinal.aleph0.{u1} b) a) (Eq.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) a) (Or (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) Cardinal.aleph0.{u1} b) a) (Eq.{succ (succ u1)} Cardinal.{u1} b (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))))
Case conversion may be inaccurate. Consider using '#align cardinal.add_eq_left_iff Cardinal.add_eq_left_iffₓ'. -/
theorem add_eq_left_iff {a b : Cardinal} : a + b = a ↔ max ℵ₀ b ≤ a ∨ b = 0 :=
  by
  rw [max_le_iff]
  refine' ⟨fun h => _, _⟩
  · cases' le_or_lt ℵ₀ a with ha ha
    · left
      use ha
      rw [← not_lt]
      apply fun hb => ne_of_gt _ h
      exact hb.trans_le (self_le_add_left b a)
    right
    rw [← h, add_lt_aleph_0_iff, lt_aleph_0, lt_aleph_0] at ha
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩
    norm_cast  at h⊢
    rw [← add_right_inj, h, add_zero]
  · rintro (⟨h1, h2⟩ | h3)
    · rw [add_eq_max h1, max_eq_left h2]
    · rw [h3, add_zero]
#align cardinal.add_eq_left_iff Cardinal.add_eq_left_iff

/- warning: cardinal.add_eq_right_iff -> Cardinal.add_eq_right_iff is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) b) (Or (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} Cardinal.aleph0.{u1} a) b) (Eq.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (OfNat.mk.{succ u1} Cardinal.{u1} 0 (Zero.zero.{succ u1} Cardinal.{u1} Cardinal.hasZero.{u1})))))
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) b) (Or (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) Cardinal.aleph0.{u1} a) b) (Eq.{succ (succ u1)} Cardinal.{u1} a (OfNat.ofNat.{succ u1} Cardinal.{u1} 0 (Zero.toOfNat0.{succ u1} Cardinal.{u1} Cardinal.instZeroCardinal.{u1}))))
Case conversion may be inaccurate. Consider using '#align cardinal.add_eq_right_iff Cardinal.add_eq_right_iffₓ'. -/
theorem add_eq_right_iff {a b : Cardinal} : a + b = b ↔ max ℵ₀ a ≤ b ∨ a = 0 := by
  rw [add_comm, add_eq_left_iff]
#align cardinal.add_eq_right_iff Cardinal.add_eq_right_iff

/- warning: cardinal.add_nat_eq -> Cardinal.add_nat_eq is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} (n : Nat), (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) a)
but is expected to have type
  forall {a : Cardinal.{u1}} (n : Nat), (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) a)
Case conversion may be inaccurate. Consider using '#align cardinal.add_nat_eq Cardinal.add_nat_eqₓ'. -/
theorem add_nat_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : a + n = a :=
  add_eq_left ha ((nat_lt_aleph0 _).le.trans ha)
#align cardinal.add_nat_eq Cardinal.add_nat_eq

/- warning: cardinal.add_one_eq -> Cardinal.add_one_eq is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) a)
but is expected to have type
  forall {a : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} a) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))) a)
Case conversion may be inaccurate. Consider using '#align cardinal.add_one_eq Cardinal.add_one_eqₓ'. -/
theorem add_one_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a + 1 = a :=
  add_eq_left ha (one_le_aleph0.trans ha)
#align cardinal.add_one_eq Cardinal.add_one_eq

/- warning: cardinal.mk_add_one_eq -> Cardinal.mk_add_one_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.mk.{u1} α) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (Cardinal.mk.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.mk.{u1} α) (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))) (Cardinal.mk.{u1} α)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_add_one_eq Cardinal.mk_add_one_eqₓ'. -/
@[simp]
theorem mk_add_one_eq {α : Type _} [Infinite α] : (#α) + 1 = (#α) :=
  add_one_eq (aleph0_le_mk α)
#align cardinal.mk_add_one_eq Cardinal.mk_add_one_eq

/- warning: cardinal.eq_of_add_eq_add_left -> Cardinal.eq_of_add_eq_add_left is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a c)) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) a Cardinal.aleph0.{u1}) -> (Eq.{succ (succ u1)} Cardinal.{u1} b c)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a c)) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) a Cardinal.aleph0.{u1}) -> (Eq.{succ (succ u1)} Cardinal.{u1} b c)
Case conversion may be inaccurate. Consider using '#align cardinal.eq_of_add_eq_add_left Cardinal.eq_of_add_eq_add_leftₓ'. -/
protected theorem eq_of_add_eq_add_left {a b c : Cardinal} (h : a + b = a + c) (ha : a < ℵ₀) :
    b = c := by
  cases' le_or_lt ℵ₀ b with hb hb
  · have : a < b := ha.trans_le hb
    rw [add_eq_right hb this.le, eq_comm] at h
    rw [eq_of_add_eq_of_aleph_0_le h this hb]
  · have hc : c < ℵ₀ := by
      rw [← not_le]
      intro hc
      apply lt_irrefl ℵ₀
      apply (hc.trans (self_le_add_left _ a)).trans_lt
      rw [← h]
      apply add_lt_aleph_0 ha hb
    rw [lt_aleph_0] at *
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    rcases hc with ⟨k, rfl⟩
    norm_cast  at h⊢
    apply add_left_cancel h
#align cardinal.eq_of_add_eq_add_left Cardinal.eq_of_add_eq_add_left

/- warning: cardinal.eq_of_add_eq_add_right -> Cardinal.eq_of_add_eq_add_right is a dubious translation:
lean 3 declaration is
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) a b) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) c b)) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) b Cardinal.aleph0.{u1}) -> (Eq.{succ (succ u1)} Cardinal.{u1} a c)
but is expected to have type
  forall {a : Cardinal.{u1}} {b : Cardinal.{u1}} {c : Cardinal.{u1}}, (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) a b) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) c b)) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) b Cardinal.aleph0.{u1}) -> (Eq.{succ (succ u1)} Cardinal.{u1} a c)
Case conversion may be inaccurate. Consider using '#align cardinal.eq_of_add_eq_add_right Cardinal.eq_of_add_eq_add_rightₓ'. -/
protected theorem eq_of_add_eq_add_right {a b c : Cardinal} (h : a + b = c + b) (hb : b < ℵ₀) :
    a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact Cardinal.eq_of_add_eq_add_left h hb
#align cardinal.eq_of_add_eq_add_right Cardinal.eq_of_add_eq_add_right

/- warning: cardinal.aleph_add_aleph -> Cardinal.aleph_add_aleph is a dubious translation:
lean 3 declaration is
  forall (o₁ : Ordinal.{u1}) (o₂ : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) (Cardinal.aleph.{u1} o₁) (Cardinal.aleph.{u1} o₂)) (Cardinal.aleph.{u1} (LinearOrder.max.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1} o₁ o₂))
but is expected to have type
  forall (o₁ : Ordinal.{u1}) (o₂ : Ordinal.{u1}), Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) (Cardinal.aleph.{u1} o₁) (Cardinal.aleph.{u1} o₂)) (Cardinal.aleph.{u1} (Max.max.{succ u1} Ordinal.{u1} (LinearOrder.toMax.{succ u1} Ordinal.{u1} Ordinal.linearOrder.{u1}) o₁ o₂))
Case conversion may be inaccurate. Consider using '#align cardinal.aleph_add_aleph Cardinal.aleph_add_alephₓ'. -/
@[simp]
theorem aleph_add_aleph (o₁ o₂ : Ordinal) : aleph o₁ + aleph o₂ = aleph (max o₁ o₂) := by
  rw [Cardinal.add_eq_max (aleph_0_le_aleph o₁), max_aleph_eq]
#align cardinal.aleph_add_aleph Cardinal.aleph_add_aleph

#print Cardinal.principal_add_ord /-
theorem principal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : Ordinal.Principal (· + ·) c.ord :=
  fun a b ha hb => by
  rw [lt_ord, Ordinal.card_add] at *
  exact add_lt_of_lt hc ha hb
#align cardinal.principal_add_ord Cardinal.principal_add_ord
-/

#print Cardinal.principal_add_aleph /-
theorem principal_add_aleph (o : Ordinal) : Ordinal.Principal (· + ·) (aleph o).ord :=
  principal_add_ord <| aleph0_le_aleph o
#align cardinal.principal_add_aleph Cardinal.principal_add_aleph
-/

/- warning: cardinal.add_right_inj_of_lt_aleph_0 -> Cardinal.add_right_inj_of_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}} {γ : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) γ Cardinal.aleph0.{u1}) -> (Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) α γ) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) β γ)) (Eq.{succ (succ u1)} Cardinal.{u1} α β))
but is expected to have type
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}} {γ : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) γ Cardinal.aleph0.{u1}) -> (Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) α γ) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) β γ)) (Eq.{succ (succ u1)} Cardinal.{u1} α β))
Case conversion may be inaccurate. Consider using '#align cardinal.add_right_inj_of_lt_aleph_0 Cardinal.add_right_inj_of_lt_aleph0ₓ'. -/
theorem add_right_inj_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β :=
  ⟨fun h => Cardinal.eq_of_add_eq_add_right h γ₀, fun h => congr_fun (congr_arg (· + ·) h) γ⟩
#align cardinal.add_right_inj_of_lt_aleph_0 Cardinal.add_right_inj_of_lt_aleph0

/- warning: cardinal.add_nat_inj -> Cardinal.add_nat_inj is a dubious translation:
lean 3 declaration is
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}} (n : Nat), Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) α ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) β ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n))) (Eq.{succ (succ u1)} Cardinal.{u1} α β)
but is expected to have type
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}} (n : Nat), Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) α (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) β (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n))) (Eq.{succ (succ u1)} Cardinal.{u1} α β)
Case conversion may be inaccurate. Consider using '#align cardinal.add_nat_inj Cardinal.add_nat_injₓ'. -/
@[simp]
theorem add_nat_inj {α β : Cardinal} (n : ℕ) : α + n = β + n ↔ α = β :=
  add_right_inj_of_lt_aleph0 (nat_lt_aleph0 _)
#align cardinal.add_nat_inj Cardinal.add_nat_inj

/- warning: cardinal.add_one_inj -> Cardinal.add_one_inj is a dubious translation:
lean 3 declaration is
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) α (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) β (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))))) (Eq.{succ (succ u1)} Cardinal.{u1} α β)
but is expected to have type
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}}, Iff (Eq.{succ (succ u1)} Cardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) α (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) β (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1})))) (Eq.{succ (succ u1)} Cardinal.{u1} α β)
Case conversion may be inaccurate. Consider using '#align cardinal.add_one_inj Cardinal.add_one_injₓ'. -/
@[simp]
theorem add_one_inj {α β : Cardinal} : α + 1 = β + 1 ↔ α = β :=
  add_right_inj_of_lt_aleph0 one_lt_aleph0
#align cardinal.add_one_inj Cardinal.add_one_inj

/- warning: cardinal.add_le_add_iff_of_lt_aleph_0 -> Cardinal.add_le_add_iff_of_lt_aleph0 is a dubious translation:
lean 3 declaration is
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}} {γ : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) γ Cardinal.aleph0.{u1}) -> (Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) α γ) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) β γ)) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} α β))
but is expected to have type
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}} {γ : Cardinal.{u1}}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) γ Cardinal.aleph0.{u1}) -> (Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) α γ) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) β γ)) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} α β))
Case conversion may be inaccurate. Consider using '#align cardinal.add_le_add_iff_of_lt_aleph_0 Cardinal.add_le_add_iff_of_lt_aleph0ₓ'. -/
theorem add_le_add_iff_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < Cardinal.aleph0) :
    α + γ ≤ β + γ ↔ α ≤ β :=
  by
  refine' ⟨fun h => _, fun h => add_le_add_right h γ⟩
  contrapose h
  rw [not_le, lt_iff_le_and_ne, Ne] at h⊢
  exact ⟨add_le_add_right h.1 γ, mt (add_right_inj_of_lt_aleph_0 γ₀).1 h.2⟩
#align cardinal.add_le_add_iff_of_lt_aleph_0 Cardinal.add_le_add_iff_of_lt_aleph0

/- warning: cardinal.add_nat_le_add_nat_iff_of_lt_aleph_0 -> Cardinal.add_nat_le_add_nat_iff_of_lt_aleph_0 is a dubious translation:
lean 3 declaration is
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}} (n : Nat), Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) α ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) β ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n))) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} α β)
but is expected to have type
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}} (n : Nat), Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) α (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) β (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n))) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} α β)
Case conversion may be inaccurate. Consider using '#align cardinal.add_nat_le_add_nat_iff_of_lt_aleph_0 Cardinal.add_nat_le_add_nat_iff_of_lt_aleph_0ₓ'. -/
@[simp]
theorem add_nat_le_add_nat_iff_of_lt_aleph_0 {α β : Cardinal} (n : ℕ) : α + n ≤ β + n ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 (nat_lt_aleph0 n)
#align cardinal.add_nat_le_add_nat_iff_of_lt_aleph_0 Cardinal.add_nat_le_add_nat_iff_of_lt_aleph_0

/- warning: cardinal.add_one_le_add_one_iff_of_lt_aleph_0 -> Cardinal.add_one_le_add_one_iff_of_lt_aleph_0 is a dubious translation:
lean 3 declaration is
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) α (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1}) β (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))))) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} α β)
but is expected to have type
  forall {α : Cardinal.{u1}} {β : Cardinal.{u1}}, Iff (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) α (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1}))) (HAdd.hAdd.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHAdd.{succ u1} Cardinal.{u1} Cardinal.instAddCardinal.{u1}) β (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1})))) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} α β)
Case conversion may be inaccurate. Consider using '#align cardinal.add_one_le_add_one_iff_of_lt_aleph_0 Cardinal.add_one_le_add_one_iff_of_lt_aleph_0ₓ'. -/
@[simp]
theorem add_one_le_add_one_iff_of_lt_aleph_0 {α β : Cardinal} : α + 1 ≤ β + 1 ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 one_lt_aleph0
#align cardinal.add_one_le_add_one_iff_of_lt_aleph_0 Cardinal.add_one_le_add_one_iff_of_lt_aleph_0

/-! ### Properties about power -/


/- warning: cardinal.pow_le -> Cardinal.pow_le is a dubious translation:
lean 3 declaration is
  forall {κ : Cardinal.{u1}} {μ : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} κ) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) μ Cardinal.aleph0.{u1}) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) κ μ) κ)
but is expected to have type
  forall {κ : Cardinal.{u1}} {μ : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} κ) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) μ Cardinal.aleph0.{u1}) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) κ μ) κ)
Case conversion may be inaccurate. Consider using '#align cardinal.pow_le Cardinal.pow_leₓ'. -/
theorem pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : μ < ℵ₀) : κ ^ μ ≤ κ :=
  let ⟨n, H3⟩ := lt_aleph0.1 H2
  H3.symm ▸
    Quotient.inductionOn κ
      (fun α H1 =>
        Nat.recOn n
          (lt_of_lt_of_le
              (by
                rw [Nat.cast_zero, power_zero]
                exact one_lt_aleph_0)
              H1).le
          fun n ih =>
          trans_rel_left _
            (by
              rw [Nat.cast_succ, power_add, power_one]
              exact mul_le_mul_right' ih _)
            (mul_eq_self H1))
      H1
#align cardinal.pow_le Cardinal.pow_le

/- warning: cardinal.pow_eq -> Cardinal.pow_eq is a dubious translation:
lean 3 declaration is
  forall {κ : Cardinal.{u1}} {μ : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} κ) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (OfNat.mk.{succ u1} Cardinal.{u1} 1 (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1}))) μ) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) μ Cardinal.aleph0.{u1}) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) κ μ) κ)
but is expected to have type
  forall {κ : Cardinal.{u1}} {μ : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} κ) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 1 (One.toOfNat1.{succ u1} Cardinal.{u1} Cardinal.instOneCardinal.{u1})) μ) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) μ Cardinal.aleph0.{u1}) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) κ μ) κ)
Case conversion may be inaccurate. Consider using '#align cardinal.pow_eq Cardinal.pow_eqₓ'. -/
theorem pow_eq {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : 1 ≤ μ) (H3 : μ < ℵ₀) : κ ^ μ = κ :=
  (pow_le H1 H3).antisymm <| self_le_power κ H2
#align cardinal.pow_eq Cardinal.pow_eq

/- warning: cardinal.power_self_eq -> Cardinal.power_self_eq is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) c c) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) c))
but is expected to have type
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) c c) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) c))
Case conversion may be inaccurate. Consider using '#align cardinal.power_self_eq Cardinal.power_self_eqₓ'. -/
theorem power_self_eq {c : Cardinal} (h : ℵ₀ ≤ c) : c ^ c = 2 ^ c :=
  by
  apply ((power_le_power_right <| (cantor c).le).trans _).antisymm
  · convert power_le_power_right ((nat_lt_aleph_0 2).le.trans h)
    apply nat.cast_two.symm
  · rw [← power_mul, mul_eq_self h]
#align cardinal.power_self_eq Cardinal.power_self_eq

/- warning: cardinal.prod_eq_two_power -> Cardinal.prod_eq_two_power is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Infinite.{succ u1} ι] {c : ι -> Cardinal.{u2}}, (forall (i : ι), LE.le.{succ u2} Cardinal.{u2} Cardinal.hasLe.{u2} (OfNat.ofNat.{succ u2} Cardinal.{u2} 2 (OfNat.mk.{succ u2} Cardinal.{u2} 2 (bit0.{succ u2} Cardinal.{u2} Cardinal.hasAdd.{u2} (One.one.{succ u2} Cardinal.{u2} Cardinal.hasOne.{u2})))) (c i)) -> (forall (i : ι), LE.le.{succ (max u2 u1)} Cardinal.{max u2 u1} Cardinal.hasLe.{max u2 u1} (Cardinal.lift.{u1, u2} (c i)) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} ι))) -> (Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.prod.{u1, u2} ι c) (HPow.hPow.{succ (max u1 u2), succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHPow.{succ (max u1 u2), succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.hasPow.{max u1 u2}) (OfNat.ofNat.{succ (max u1 u2)} Cardinal.{max u1 u2} 2 (OfNat.mk.{succ (max u1 u2)} Cardinal.{max u1 u2} 2 (bit0.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasAdd.{max u1 u2} (One.one.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.hasOne.{max u1 u2})))) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} ι))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Infinite.{succ u1} ι] {c : ι -> Cardinal.{u2}}, (forall (i : ι), LE.le.{succ u2} Cardinal.{u2} Cardinal.instLECardinal.{u2} (OfNat.ofNat.{succ u2} Cardinal.{u2} 2 (instOfNat.{succ u2} Cardinal.{u2} 2 Cardinal.instNatCastCardinal.{u2} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (c i)) -> (forall (i : ι), LE.le.{max (succ u1) (succ u2)} Cardinal.{max u2 u1} Cardinal.instLECardinal.{max u1 u2} (Cardinal.lift.{u1, u2} (c i)) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} ι))) -> (Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u1 u2} (Cardinal.prod.{u1, u2} ι c) (HPow.hPow.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.{max u1 u2} (instHPow.{max (succ u1) (succ u2), max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.{max u1 u2} Cardinal.instPowCardinal.{max u1 u2}) (OfNat.ofNat.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} 2 (instOfNat.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} 2 Cardinal.instNatCastCardinal.{max u1 u2} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} ι))))
Case conversion may be inaccurate. Consider using '#align cardinal.prod_eq_two_power Cardinal.prod_eq_two_powerₓ'. -/
theorem prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι → Cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
    (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} (#ι)) : prod c = 2 ^ lift.{v} (#ι) :=
  by
  rw [← lift_id' (Prod c), lift_prod, ← lift_two_power]
  apply le_antisymm
  · refine' (prod_le_prod _ _ h₂).trans_eq _
    rw [prod_const, lift_lift, ← lift_power, power_self_eq (aleph_0_le_mk ι), lift_umax.{u, v}]
  · rw [← prod_const', lift_prod]
    refine' prod_le_prod _ _ fun i => _
    rw [lift_two, ← lift_two.{u, v}, lift_le]
    exact h₁ i
#align cardinal.prod_eq_two_power Cardinal.prod_eq_two_power

/- warning: cardinal.power_eq_two_power -> Cardinal.power_eq_two_power is a dubious translation:
lean 3 declaration is
  forall {c₁ : Cardinal.{u1}} {c₂ : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c₁) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) c₂) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} c₂ c₁) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) c₂ c₁) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) c₁))
but is expected to have type
  forall {c₁ : Cardinal.{u1}} {c₂ : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c₁) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) c₂) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} c₂ c₁) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) c₂ c₁) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) c₁))
Case conversion may be inaccurate. Consider using '#align cardinal.power_eq_two_power Cardinal.power_eq_two_powerₓ'. -/
theorem power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ℵ₀ ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) :
    c₂ ^ c₁ = 2 ^ c₁ :=
  le_antisymm (power_self_eq h₁ ▸ power_le_power_right h₂') (power_le_power_right h₂)
#align cardinal.power_eq_two_power Cardinal.power_eq_two_power

/- warning: cardinal.nat_power_eq -> Cardinal.nat_power_eq is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (forall {n : Nat}, (LE.le.{0} Nat Nat.hasLe (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))) n) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n) c) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (OfNat.mk.{succ u1} Cardinal.{u1} 2 (bit0.{succ u1} Cardinal.{u1} Cardinal.hasAdd.{u1} (One.one.{succ u1} Cardinal.{u1} Cardinal.hasOne.{u1})))) c)))
but is expected to have type
  forall {c : Cardinal.{u1}}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (forall {n : Nat}, (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) n) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n) c) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (OfNat.ofNat.{succ u1} Cardinal.{u1} 2 (instOfNat.{succ u1} Cardinal.{u1} 2 Cardinal.instNatCastCardinal.{u1} (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) c)))
Case conversion may be inaccurate. Consider using '#align cardinal.nat_power_eq Cardinal.nat_power_eqₓ'. -/
theorem nat_power_eq {c : Cardinal.{u}} (h : ℵ₀ ≤ c) {n : ℕ} (hn : 2 ≤ n) :
    (n : Cardinal.{u}) ^ c = 2 ^ c :=
  power_eq_two_power h (by assumption_mod_cast) ((nat_lt_aleph0 n).le.trans h)
#align cardinal.nat_power_eq Cardinal.nat_power_eq

/- warning: cardinal.power_nat_le -> Cardinal.power_nat_le is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}} {n : Nat}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) c n) c)
but is expected to have type
  forall {c : Cardinal.{u1}} {n : Nat}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))) c n) c)
Case conversion may be inaccurate. Consider using '#align cardinal.power_nat_le Cardinal.power_nat_leₓ'. -/
theorem power_nat_le {c : Cardinal.{u}} {n : ℕ} (h : ℵ₀ ≤ c) : c ^ n ≤ c :=
  pow_le h (nat_lt_aleph0 n)
#align cardinal.power_nat_le Cardinal.power_nat_le

/- warning: cardinal.power_nat_eq -> Cardinal.power_nat_eq is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}} {n : Nat}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} Cardinal.aleph0.{u1} c) -> (LE.le.{0} Nat Nat.hasLe (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) n) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1}))))))) c n) c)
but is expected to have type
  forall {c : Cardinal.{u1}} {n : Nat}, (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} Cardinal.aleph0.{u1} c) -> (LE.le.{0} Nat instLENat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) n) -> (Eq.{succ (succ u1)} Cardinal.{u1} (HPow.hPow.{succ u1, 0, succ u1} Cardinal.{u1} Nat Cardinal.{u1} (instHPow.{succ u1, 0} Cardinal.{u1} Nat (Monoid.Pow.{succ u1} Cardinal.{u1} (MonoidWithZero.toMonoid.{succ u1} Cardinal.{u1} (Semiring.toMonoidWithZero.{succ u1} Cardinal.{u1} (OrderedSemiring.toSemiring.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyOrderedCommSemiringCardinal.{u1}))))))) c n) c)
Case conversion may be inaccurate. Consider using '#align cardinal.power_nat_eq Cardinal.power_nat_eqₓ'. -/
theorem power_nat_eq {c : Cardinal.{u}} {n : ℕ} (h1 : ℵ₀ ≤ c) (h2 : 1 ≤ n) : c ^ n = c :=
  pow_eq h1 (by exact_mod_cast h2) (nat_lt_aleph0 n)
#align cardinal.power_nat_eq Cardinal.power_nat_eq

/- warning: cardinal.power_nat_le_max -> Cardinal.power_nat_le_max is a dubious translation:
lean 3 declaration is
  forall {c : Cardinal.{u1}} {n : Nat}, LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) c ((fun (a : Type) (b : Type.{succ u1}) [self : HasLiftT.{1, succ (succ u1)} a b] => self.0) Nat Cardinal.{u1} (HasLiftT.mk.{1, succ (succ u1)} Nat Cardinal.{u1} (CoeTCₓ.coe.{1, succ (succ u1)} Nat Cardinal.{u1} (Nat.castCoe.{succ u1} Cardinal.{u1} Cardinal.hasNatCast.{u1}))) n)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} c Cardinal.aleph0.{u1})
but is expected to have type
  forall {c : Cardinal.{u1}} {n : Nat}, LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) c (Nat.cast.{succ u1} Cardinal.{u1} Cardinal.instNatCastCardinal.{u1} n)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) c Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.power_nat_le_max Cardinal.power_nat_le_maxₓ'. -/
theorem power_nat_le_max {c : Cardinal.{u}} {n : ℕ} : c ^ (n : Cardinal.{u}) ≤ max c ℵ₀ :=
  by
  cases' le_or_lt ℵ₀ c with hc hc
  · exact le_max_of_le_left (power_nat_le hc)
  · exact le_max_of_le_right (power_lt_aleph_0 hc (nat_lt_aleph_0 _)).le
#align cardinal.power_nat_le_max Cardinal.power_nat_le_max

#print Cardinal.powerlt_aleph0 /-
theorem powerlt_aleph0 {c : Cardinal} (h : ℵ₀ ≤ c) : c ^< ℵ₀ = c :=
  by
  apply le_antisymm
  · rw [powerlt_le]
    intro c'
    rw [lt_aleph_0]
    rintro ⟨n, rfl⟩
    apply power_nat_le h
  convert le_powerlt c one_lt_aleph_0; rw [power_one]
#align cardinal.powerlt_aleph_0 Cardinal.powerlt_aleph0
-/

/- warning: cardinal.powerlt_aleph_0_le -> Cardinal.powerlt_aleph0_le is a dubious translation:
lean 3 declaration is
  forall (c : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.powerlt.{u1} c Cardinal.aleph0.{u1}) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} c Cardinal.aleph0.{u1})
but is expected to have type
  forall (c : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.powerlt.{u1} c Cardinal.aleph0.{u1}) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) c Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.powerlt_aleph_0_le Cardinal.powerlt_aleph0_leₓ'. -/
theorem powerlt_aleph0_le (c : Cardinal) : c ^< ℵ₀ ≤ max c ℵ₀ :=
  by
  cases le_or_lt ℵ₀ c
  · rw [powerlt_aleph_0 h]
    apply le_max_left
  rw [powerlt_le]
  exact fun c' hc' => (power_lt_aleph_0 h hc').le.trans (le_max_right _ _)
#align cardinal.powerlt_aleph_0_le Cardinal.powerlt_aleph0_le

/-! ### Computing cardinality of various types -/


#print Cardinal.mk_list_eq_mk /-
@[simp]
theorem mk_list_eq_mk (α : Type u) [Infinite α] : (#List α) = (#α) :=
  have H1 : ℵ₀ ≤ (#α) := aleph0_le_mk α
  Eq.symm <|
    le_antisymm ⟨⟨fun x => [x], fun x y H => (List.cons.inj H).1⟩⟩ <|
      calc
        (#List α) = sum fun n : ℕ => (#α) ^ (n : Cardinal.{u}) := mk_list_eq_sum_pow α
        _ ≤ sum fun n : ℕ => #α := (sum_le_sum _ _ fun n => pow_le H1 <| nat_lt_aleph0 n)
        _ = (#α) := by simp [H1]
        
#align cardinal.mk_list_eq_mk Cardinal.mk_list_eq_mk
-/

#print Cardinal.mk_list_eq_aleph0 /-
theorem mk_list_eq_aleph0 (α : Type u) [Countable α] [Nonempty α] : (#List α) = ℵ₀ :=
  mk_le_aleph0.antisymm (aleph0_le_mk _)
#align cardinal.mk_list_eq_aleph_0 Cardinal.mk_list_eq_aleph0
-/

/- warning: cardinal.mk_list_eq_max_mk_aleph_0 -> Cardinal.mk_list_eq_max_mk_aleph0 is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Nonempty.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (List.{u1} α)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1})
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Nonempty.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (List.{u1} α)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.mk_list_eq_max_mk_aleph_0 Cardinal.mk_list_eq_max_mk_aleph0ₓ'. -/
theorem mk_list_eq_max_mk_aleph0 (α : Type u) [Nonempty α] : (#List α) = max (#α) ℵ₀ :=
  by
  cases finite_or_infinite α
  · rw [mk_list_eq_aleph_0, eq_comm, max_eq_right]
    exact mk_le_aleph_0
  · rw [mk_list_eq_mk, eq_comm, max_eq_left]
    exact aleph_0_le_mk α
#align cardinal.mk_list_eq_max_mk_aleph_0 Cardinal.mk_list_eq_max_mk_aleph0

/- warning: cardinal.mk_list_le_max -> Cardinal.mk_list_le_max is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (List.{u1} α)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} Cardinal.aleph0.{u1} (Cardinal.mk.{u1} α))
but is expected to have type
  forall (α : Type.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (List.{u1} α)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) Cardinal.aleph0.{u1} (Cardinal.mk.{u1} α))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_list_le_max Cardinal.mk_list_le_maxₓ'. -/
theorem mk_list_le_max (α : Type u) : (#List α) ≤ max ℵ₀ (#α) :=
  by
  cases finite_or_infinite α
  · exact mk_le_aleph_0.trans (le_max_left _ _)
  · rw [mk_list_eq_mk]
    apply le_max_right
#align cardinal.mk_list_le_max Cardinal.mk_list_le_max

#print Cardinal.mk_finset_of_infinite /-
@[simp]
theorem mk_finset_of_infinite (α : Type u) [Infinite α] : (#Finset α) = (#α) :=
  Eq.symm <|
    le_antisymm (mk_le_of_injective fun x y => Finset.singleton_inj.1) <|
      calc
        (#Finset α) ≤ (#List α) := mk_le_of_surjective List.toFinset_surjective
        _ = (#α) := mk_list_eq_mk α
        
#align cardinal.mk_finset_of_infinite Cardinal.mk_finset_of_infinite
-/

/- warning: cardinal.mk_finsupp_lift_of_infinite -> Cardinal.mk_finsupp_lift_of_infinite is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Infinite.{succ u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : Nontrivial.{u2} β], Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (Finsupp.{u1, u2} α β _inst_2)) (LinearOrder.max.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.linearOrder.{max u1 u2} (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Infinite.{succ u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : Nontrivial.{u2} β], Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.mk.{max u2 u1} (Finsupp.{u1, u2} α β _inst_2)) (Max.max.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} (CanonicallyLinearOrderedAddMonoid.toMax.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_finsupp_lift_of_infinite Cardinal.mk_finsupp_lift_of_infiniteₓ'. -/
@[simp]
theorem mk_finsupp_lift_of_infinite (α : Type u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] :
    (#α →₀ β) = max (lift.{v} (#α)) (lift.{u} (#β)) :=
  by
  apply le_antisymm
  ·
    calc
      (#α →₀ β) ≤ (#Finset (α × β)) := mk_le_of_injective (Finsupp.graph_injective α β)
      _ = (#α × β) := (mk_finset_of_infinite _)
      _ = max (lift.{v} (#α)) (lift.{u} (#β)) := by
        rw [mk_prod, mul_eq_max_of_aleph_0_le_left] <;> simp
      
  · apply max_le <;> rw [← lift_id (#α →₀ β), ← lift_umax]
    · cases' exists_ne (0 : β) with b hb
      exact lift_mk_le.{u, max u v, v}.2 ⟨⟨_, Finsupp.single_left_injective hb⟩⟩
    · inhabit α
      exact lift_mk_le.{v, max u v, u}.2 ⟨⟨_, Finsupp.single_injective default⟩⟩
#align cardinal.mk_finsupp_lift_of_infinite Cardinal.mk_finsupp_lift_of_infinite

/- warning: cardinal.mk_finsupp_of_infinite -> Cardinal.mk_finsupp_of_infinite is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u1}) [_inst_1 : Infinite.{succ u1} α] [_inst_2 : Zero.{u1} β] [_inst_3 : Nontrivial.{u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finsupp.{u1, u1} α β _inst_2)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u1}) [_inst_1 : Infinite.{succ u1} α] [_inst_2 : Zero.{u1} β] [_inst_3 : Nontrivial.{u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finsupp.{u1, u1} α β _inst_2)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_finsupp_of_infinite Cardinal.mk_finsupp_of_infiniteₓ'. -/
theorem mk_finsupp_of_infinite (α β : Type u) [Infinite α] [Zero β] [Nontrivial β] :
    (#α →₀ β) = max (#α) (#β) := by simp
#align cardinal.mk_finsupp_of_infinite Cardinal.mk_finsupp_of_infinite

/- warning: cardinal.mk_finsupp_lift_of_infinite' -> Cardinal.mk_finsupp_lift_of_infinite' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : Infinite.{succ u2} β], Eq.{succ (succ (max u1 u2))} Cardinal.{max u1 u2} (Cardinal.mk.{max u1 u2} (Finsupp.{u1, u2} α β _inst_2)) (LinearOrder.max.{succ (max u1 u2)} Cardinal.{max u1 u2} Cardinal.linearOrder.{max u1 u2} (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : Infinite.{succ u2} β], Eq.{max (succ (succ u1)) (succ (succ u2))} Cardinal.{max u2 u1} (Cardinal.mk.{max u2 u1} (Finsupp.{u1, u2} α β _inst_2)) (Max.max.{max (succ u2) (succ u1)} Cardinal.{max u1 u2} (CanonicallyLinearOrderedAddMonoid.toMax.{max (succ u1) (succ u2)} Cardinal.{max u1 u2} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{max u1 u2}) (Cardinal.lift.{u2, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{u1, u2} (Cardinal.mk.{u2} β)))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_finsupp_lift_of_infinite' Cardinal.mk_finsupp_lift_of_infinite'ₓ'. -/
@[simp]
theorem mk_finsupp_lift_of_infinite' (α : Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] :
    (#α →₀ β) = max (lift.{v} (#α)) (lift.{u} (#β)) :=
  by
  cases fintypeOrInfinite α
  · rw [mk_finsupp_lift_of_fintype]
    have : ℵ₀ ≤ (#β).lift := aleph_0_le_lift.2 (aleph_0_le_mk β)
    rw [max_eq_right (le_trans _ this), power_nat_eq this]
    exacts[Fintype.card_pos, lift_le_aleph_0.2 (lt_aleph_0_of_finite _).le]
  · apply mk_finsupp_lift_of_infinite
#align cardinal.mk_finsupp_lift_of_infinite' Cardinal.mk_finsupp_lift_of_infinite'

/- warning: cardinal.mk_finsupp_of_infinite' -> Cardinal.mk_finsupp_of_infinite' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u1}) [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : Zero.{u1} β] [_inst_3 : Infinite.{succ u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finsupp.{u1, u1} α β _inst_2)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u1}) [_inst_1 : Nonempty.{succ u1} α] [_inst_2 : Zero.{u1} β] [_inst_3 : Infinite.{succ u1} β], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finsupp.{u1, u1} α β _inst_2)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) (Cardinal.mk.{u1} β))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_finsupp_of_infinite' Cardinal.mk_finsupp_of_infinite'ₓ'. -/
theorem mk_finsupp_of_infinite' (α β : Type u) [Nonempty α] [Zero β] [Infinite β] :
    (#α →₀ β) = max (#α) (#β) := by simp
#align cardinal.mk_finsupp_of_infinite' Cardinal.mk_finsupp_of_infinite'

/- warning: cardinal.mk_finsupp_nat -> Cardinal.mk_finsupp_nat is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Nonempty.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finsupp.{u1, 0} α Nat Nat.hasZero)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1})
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Nonempty.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Finsupp.{u1, 0} α Nat (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero))) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.mk_finsupp_nat Cardinal.mk_finsupp_natₓ'. -/
theorem mk_finsupp_nat (α : Type u) [Nonempty α] : (#α →₀ ℕ) = max (#α) ℵ₀ := by simp
#align cardinal.mk_finsupp_nat Cardinal.mk_finsupp_nat

/- warning: cardinal.mk_multiset_of_nonempty -> Cardinal.mk_multiset_of_nonempty is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Nonempty.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Multiset.{u1} α)) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1})
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Nonempty.{succ u1} α], Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Multiset.{u1} α)) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1})
Case conversion may be inaccurate. Consider using '#align cardinal.mk_multiset_of_nonempty Cardinal.mk_multiset_of_nonemptyₓ'. -/
@[simp]
theorem mk_multiset_of_nonempty (α : Type u) [Nonempty α] : (#Multiset α) = max (#α) ℵ₀ :=
  Multiset.toFinsupp.toEquiv.cardinal_eq.trans (mk_finsupp_nat α)
#align cardinal.mk_multiset_of_nonempty Cardinal.mk_multiset_of_nonempty

#print Cardinal.mk_multiset_of_infinite /-
theorem mk_multiset_of_infinite (α : Type u) [Infinite α] : (#Multiset α) = (#α) := by simp
#align cardinal.mk_multiset_of_infinite Cardinal.mk_multiset_of_infinite
-/

#print Cardinal.mk_multiset_of_isEmpty /-
@[simp]
theorem mk_multiset_of_isEmpty (α : Type u) [IsEmpty α] : (#Multiset α) = 1 :=
  Multiset.toFinsupp.toEquiv.cardinal_eq.trans (by simp)
#align cardinal.mk_multiset_of_is_empty Cardinal.mk_multiset_of_isEmpty
-/

#print Cardinal.mk_multiset_of_countable /-
theorem mk_multiset_of_countable (α : Type u) [Countable α] [Nonempty α] : (#Multiset α) = ℵ₀ :=
  Multiset.toFinsupp.toEquiv.cardinal_eq.trans (by simp)
#align cardinal.mk_multiset_of_countable Cardinal.mk_multiset_of_countable
-/

#print Cardinal.mk_bounded_set_le_of_infinite /-
theorem mk_bounded_set_le_of_infinite (α : Type u) [Infinite α] (c : Cardinal) :
    (#{ t : Set α // (#t) ≤ c }) ≤ (#α) ^ c :=
  by
  refine' le_trans _ (by rw [← add_one_eq (aleph_0_le_mk α)])
  induction' c using Cardinal.inductionOn with β
  fapply mk_le_of_surjective
  · intro f
    use Sum.inl ⁻¹' range f
    refine' le_trans (mk_preimage_of_injective _ _ fun x y => Sum.inl.inj) _
    apply mk_range_le
  rintro ⟨s, ⟨g⟩⟩
  use fun y => if h : ∃ x : s, g x = y then Sum.inl (Classical.choose h).val else Sum.inr ⟨⟩
  apply Subtype.eq; ext
  constructor
  · rintro ⟨y, h⟩
    dsimp only at h
    by_cases h' : ∃ z : s, g z = y
    · rw [dif_pos h'] at h
      cases Sum.inl.inj h
      exact (Classical.choose h').2
    · rw [dif_neg h'] at h
      cases h
  · intro h
    have : ∃ z : s, g z = g ⟨x, h⟩ := ⟨⟨x, h⟩, rfl⟩
    use g ⟨x, h⟩
    dsimp only
    rw [dif_pos this]
    congr
    suffices : Classical.choose this = ⟨x, h⟩
    exact congr_arg Subtype.val this
    apply g.2
    exact Classical.choose_spec this
#align cardinal.mk_bounded_set_le_of_infinite Cardinal.mk_bounded_set_le_of_infinite
-/

/- warning: cardinal.mk_bounded_set_le -> Cardinal.mk_bounded_set_le is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (c : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)) c))) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1}) c)
but is expected to have type
  forall (α : Type.{u1}) (c : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α t)) c))) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} α) Cardinal.aleph0.{u1}) c)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_bounded_set_le Cardinal.mk_bounded_set_leₓ'. -/
theorem mk_bounded_set_le (α : Type u) (c : Cardinal) :
    (#{ t : Set α // (#t) ≤ c }) ≤ max (#α) ℵ₀ ^ c :=
  by
  trans #{ t : Set (Sum (ULift.{u} ℕ) α) // (#t) ≤ c }
  · refine' ⟨embedding.subtype_map _ _⟩
    apply embedding.image
    use Sum.inr
    apply Sum.inr.inj
    intro s hs
    exact mk_image_le.trans hs
  apply (mk_bounded_set_le_of_infinite (Sum (ULift.{u} ℕ) α) c).trans
  rw [max_comm, ← add_eq_max] <;> rfl
#align cardinal.mk_bounded_set_le Cardinal.mk_bounded_set_le

/- warning: cardinal.mk_bounded_subset_le -> Cardinal.mk_bounded_subset_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (c : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) (LE.le.{succ u1} Cardinal.{u1} Cardinal.hasLe.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)) c)))) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.hasPow.{u1}) (LinearOrder.max.{succ u1} Cardinal.{u1} Cardinal.linearOrder.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) Cardinal.aleph0.{u1}) c)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (c : Cardinal.{u1}), LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Subtype.{succ u1} (Set.{u1} α) (fun (t : Set.{u1} α) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) (LE.le.{succ u1} Cardinal.{u1} Cardinal.instLECardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α t)) c)))) (HPow.hPow.{succ u1, succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.{u1} (instHPow.{succ u1, succ u1} Cardinal.{u1} Cardinal.{u1} Cardinal.instPowCardinal.{u1}) (Max.max.{succ u1} Cardinal.{u1} (CanonicallyLinearOrderedAddMonoid.toMax.{succ u1} Cardinal.{u1} Cardinal.instCanonicallyLinearOrderedAddMonoidCardinal.{u1}) (Cardinal.mk.{u1} (Set.Elem.{u1} α s)) Cardinal.aleph0.{u1}) c)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_bounded_subset_le Cardinal.mk_bounded_subset_leₓ'. -/
theorem mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) :
    (#{ t : Set α // t ⊆ s ∧ (#t) ≤ c }) ≤ max (#s) ℵ₀ ^ c :=
  by
  refine' le_trans _ (mk_bounded_set_le s c)
  refine' ⟨Embedding.codRestrict _ _ _⟩
  use fun t => coe ⁻¹' t.1
  · rintro ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h
    apply Subtype.eq
    dsimp only at h⊢
    refine' (preimage_eq_preimage' _ _).1 h <;> rw [Subtype.range_coe] <;> assumption
  rintro ⟨t, h1t, h2t⟩; exact (mk_preimage_of_injective _ _ Subtype.val_injective).trans h2t
#align cardinal.mk_bounded_subset_le Cardinal.mk_bounded_subset_le

/-! ### Properties of `compl` -/


/- warning: cardinal.mk_compl_of_infinite -> Cardinal.mk_compl_of_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] (s : Set.{u1} α), (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Cardinal.mk.{u1} α)) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Cardinal.mk.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] (s : Set.{u1} α), (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Cardinal.mk.{u1} (Set.Elem.{u1} α s)) (Cardinal.mk.{u1} α)) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Cardinal.mk.{u1} α))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_compl_of_infinite Cardinal.mk_compl_of_infiniteₓ'. -/
theorem mk_compl_of_infinite {α : Type _} [Infinite α] (s : Set α) (h2 : (#s) < (#α)) :
    (#(sᶜ : Set α)) = (#α) :=
  by
  refine' eq_of_add_eq_of_aleph_0_le _ h2 (aleph_0_le_mk α)
  exact mk_sum_compl s
#align cardinal.mk_compl_of_infinite Cardinal.mk_compl_of_infinite

/- warning: cardinal.mk_compl_finset_of_infinite -> Cardinal.mk_compl_finset_of_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] (s : Finset.{u1} α), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)))) (Cardinal.mk.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] (s : Finset.{u1} α), Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Finset.toSet.{u1} α s)))) (Cardinal.mk.{u1} α)
Case conversion may be inaccurate. Consider using '#align cardinal.mk_compl_finset_of_infinite Cardinal.mk_compl_finset_of_infiniteₓ'. -/
theorem mk_compl_finset_of_infinite {α : Type _} [Infinite α] (s : Finset α) :
    (#(↑sᶜ : Set α)) = (#α) := by
  apply mk_compl_of_infinite
  exact (finset_card_lt_aleph_0 s).trans_le (aleph_0_le_mk α)
#align cardinal.mk_compl_finset_of_infinite Cardinal.mk_compl_finset_of_infinite

/- warning: cardinal.mk_compl_eq_mk_compl_infinite -> Cardinal.mk_compl_eq_mk_compl_infinite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Cardinal.mk.{u1} α)) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t)) (Cardinal.mk.{u1} α)) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Infinite.{succ u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Cardinal.mk.{u1} (Set.Elem.{u1} α s)) (Cardinal.mk.{u1} α)) -> (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} Cardinal.partialOrder.{u1})) (Cardinal.mk.{u1} (Set.Elem.{u1} α t)) (Cardinal.mk.{u1} α)) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Cardinal.mk.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_compl_eq_mk_compl_infinite Cardinal.mk_compl_eq_mk_compl_infiniteₓ'. -/
theorem mk_compl_eq_mk_compl_infinite {α : Type _} [Infinite α] {s t : Set α} (hs : (#s) < (#α))
    (ht : (#t) < (#α)) : (#(sᶜ : Set α)) = (#(tᶜ : Set α)) := by
  rw [mk_compl_of_infinite s hs, mk_compl_of_infinite t ht]
#align cardinal.mk_compl_eq_mk_compl_infinite Cardinal.mk_compl_eq_mk_compl_infinite

/- warning: cardinal.mk_compl_eq_mk_compl_finite_lift -> Cardinal.mk_compl_eq_mk_compl_finite_lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u1} α] {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{succ (succ (max u1 u2 u3))} Cardinal.{max u1 u2 u3} (Cardinal.lift.{max u2 u3, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{max u1 u3, u2} (Cardinal.mk.{u2} β))) -> (Eq.{succ (succ (max u1 u2 u3))} Cardinal.{max u1 u2 u3} (Cardinal.lift.{max u2 u3, u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s))) (Cardinal.lift.{max u1 u3, u2} (Cardinal.mk.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t)))) -> (Eq.{succ (succ (max u1 u2 u3))} Cardinal.{max u1 u2 u3} (Cardinal.lift.{max u2 u3, u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)))) (Cardinal.lift.{max u1 u3, u2} (Cardinal.mk.{u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Finite.{succ u1} α] {s : Set.{u1} α} {t : Set.{u2} β}, (Eq.{max (max (succ (succ u1)) (succ (succ u2))) (succ (succ u3))} Cardinal.{max u1 u2 u3} (Cardinal.lift.{max u2 u3, u1} (Cardinal.mk.{u1} α)) (Cardinal.lift.{max u1 u3, u2} (Cardinal.mk.{u2} β))) -> (Eq.{max (max (succ (succ u1)) (succ (succ u2))) (succ (succ u3))} Cardinal.{max u1 u2 u3} (Cardinal.lift.{max u2 u3, u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α s))) (Cardinal.lift.{max u1 u3, u2} (Cardinal.mk.{u2} (Set.Elem.{u2} β t)))) -> (Eq.{max (max (succ (succ u1)) (succ (succ u2))) (succ (succ u3))} Cardinal.{max u1 u2 u3} (Cardinal.lift.{max u2 u3, u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)))) (Cardinal.lift.{max u1 u3, u2} (Cardinal.mk.{u2} (Set.Elem.{u2} β (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)) t)))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_compl_eq_mk_compl_finite_lift Cardinal.mk_compl_eq_mk_compl_finite_liftₓ'. -/
theorem mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [Finite α] {s : Set α}
    {t : Set β} (h1 : lift.{max v w} (#α) = lift.{max u w} (#β))
    (h2 : lift.{max v w} (#s) = lift.{max u w} (#t)) :
    lift.{max v w} (#(sᶜ : Set α)) = lift.{max u w} (#(tᶜ : Set β)) :=
  by
  cases nonempty_fintype α
  rcases lift_mk_eq.1 h1 with ⟨e⟩; letI : Fintype β := Fintype.ofEquiv α e
  replace h1 : Fintype.card α = Fintype.card β := (Fintype.ofEquiv_card _).symm
  classical
    lift s to Finset α using s.to_finite
    lift t to Finset β using t.to_finite
    simp only [Finset.coe_sort_coe, mk_coe_finset, lift_nat_cast, Nat.cast_inj] at h2
    simp only [← Finset.coe_compl, Finset.coe_sort_coe, mk_coe_finset, Finset.card_compl,
      lift_nat_cast, Nat.cast_inj, h1, h2]
#align cardinal.mk_compl_eq_mk_compl_finite_lift Cardinal.mk_compl_eq_mk_compl_finite_lift

/- warning: cardinal.mk_compl_eq_mk_compl_finite -> Cardinal.mk_compl_eq_mk_compl_finite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} {β : Type.{u}} [_inst_1 : Finite.{succ u} α] {s : Set.{u} α} {t : Set.{u} β}, (Eq.{succ (succ u)} Cardinal.{u} (Cardinal.mk.{u} α) (Cardinal.mk.{u} β)) -> (Eq.{succ (succ u)} Cardinal.{u} (Cardinal.mk.{u} (coeSort.{max (succ u) 1, succ (succ u)} (Set.{u} α) Type.{u} (Set.hasCoeToSort.{u} α) s)) (Cardinal.mk.{u} (coeSort.{max (succ u) 1, succ (succ u)} (Set.{u} β) Type.{u} (Set.hasCoeToSort.{u} β) t))) -> (Eq.{succ (succ u)} Cardinal.{u} (Cardinal.mk.{u} (coeSort.{max (succ u) 1, succ (succ u)} (Set.{u} α) Type.{u} (Set.hasCoeToSort.{u} α) (HasCompl.compl.{u} (Set.{u} α) (BooleanAlgebra.toHasCompl.{u} (Set.{u} α) (Set.booleanAlgebra.{u} α)) s))) (Cardinal.mk.{u} (coeSort.{max (succ u) 1, succ (succ u)} (Set.{u} β) Type.{u} (Set.hasCoeToSort.{u} β) (HasCompl.compl.{u} (Set.{u} β) (BooleanAlgebra.toHasCompl.{u} (Set.{u} β) (Set.booleanAlgebra.{u} β)) t))))
but is expected to have type
  forall {α : Type.{u}} {β : Type.{u}} [_inst_1 : Finite.{succ u} α] {s : Set.{u} α} {t : Set.{u} β}, (Eq.{succ (succ u)} Cardinal.{u} (Cardinal.mk.{u} α) (Cardinal.mk.{u} β)) -> (Eq.{succ (succ u)} Cardinal.{u} (Cardinal.mk.{u} (Set.Elem.{u} α s)) (Cardinal.mk.{u} (Set.Elem.{u} β t))) -> (Eq.{succ (succ u)} Cardinal.{u} (Cardinal.mk.{u} (Set.Elem.{u} α (HasCompl.compl.{u} (Set.{u} α) (BooleanAlgebra.toHasCompl.{u} (Set.{u} α) (Set.instBooleanAlgebraSet.{u} α)) s))) (Cardinal.mk.{u} (Set.Elem.{u} β (HasCompl.compl.{u} (Set.{u} β) (BooleanAlgebra.toHasCompl.{u} (Set.{u} β) (Set.instBooleanAlgebraSet.{u} β)) t))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_compl_eq_mk_compl_finite Cardinal.mk_compl_eq_mk_compl_finiteₓ'. -/
theorem mk_compl_eq_mk_compl_finite {α β : Type u} [Finite α] {s : Set α} {t : Set β}
    (h1 : (#α) = (#β)) (h : (#s) = (#t)) : (#(sᶜ : Set α)) = (#(tᶜ : Set β)) :=
  by
  rw [← lift_inj]
  apply mk_compl_eq_mk_compl_finite_lift <;> rwa [lift_inj]
#align cardinal.mk_compl_eq_mk_compl_finite Cardinal.mk_compl_eq_mk_compl_finite

/- warning: cardinal.mk_compl_eq_mk_compl_finite_same -> Cardinal.mk_compl_eq_mk_compl_finite_same is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Finite.{succ u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) t))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Finite.{succ u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α s)) (Cardinal.mk.{u1} (Set.Elem.{u1} α t))) -> (Eq.{succ (succ u1)} Cardinal.{u1} (Cardinal.mk.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Cardinal.mk.{u1} (Set.Elem.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))))
Case conversion may be inaccurate. Consider using '#align cardinal.mk_compl_eq_mk_compl_finite_same Cardinal.mk_compl_eq_mk_compl_finite_sameₓ'. -/
theorem mk_compl_eq_mk_compl_finite_same {α : Type _} [Finite α] {s t : Set α} (h : (#s) = (#t)) :
    (#(sᶜ : Set α)) = (#(tᶜ : Set α)) :=
  mk_compl_eq_mk_compl_finite rfl h
#align cardinal.mk_compl_eq_mk_compl_finite_same Cardinal.mk_compl_eq_mk_compl_finite_same

/-! ### Extending an injection to an equiv -/


/- warning: cardinal.extend_function -> Cardinal.extend_function is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} (f : Function.Embedding.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β), (Nonempty.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (HasCompl.compl.{u2} (Set.{u2} β) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (Set.range.{u2, succ u1} β (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) (fun (_x : Function.Embedding.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) f)))))) -> (Exists.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α β) (fun (g : Equiv.{succ u1, succ u2} α β) => forall (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), Eq.{succ u2} β (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) (fun (_x : Function.Embedding.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} (f : Function.Embedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β), (Nonempty.{max (succ u1) (succ u2)} (Equiv.{succ u2, succ u1} (Set.Elem.{u2} α (HasCompl.compl.{u2} (Set.{u2} α) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} α) (Set.instBooleanAlgebraSet.{u2} α)) s)) (Set.Elem.{u1} β (HasCompl.compl.{u1} (Set.{u1} β) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)) (Set.range.{u1, succ u2} β (Set.Elem.{u2} α s) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β) (Set.Elem.{u2} α s) (fun (_x : Set.Elem.{u2} α s) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Set.Elem.{u2} α s) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β) (Set.Elem.{u2} α s) β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β)) f)))))) -> (Exists.{max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} α β) (fun (g : Equiv.{succ u2, succ u1} α β) => forall (x : Set.Elem.{u2} α s), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => β) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) g (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β) (Set.Elem.{u2} α s) (fun (_x : Set.Elem.{u2} α s) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Set.Elem.{u2} α s) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β) (Set.Elem.{u2} α s) β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β)) f x)))
Case conversion may be inaccurate. Consider using '#align cardinal.extend_function Cardinal.extend_functionₓ'. -/
theorem extend_function {α β : Type _} {s : Set α} (f : s ↪ β)
    (h : Nonempty ((sᶜ : Set α) ≃ (range fᶜ : Set β))) : ∃ g : α ≃ β, ∀ x : s, g x = f x :=
  by
  intros ; have := h; cases' this with g
  let h : α ≃ β :=
    (set.sum_compl (s : Set α)).symm.trans
      ((sum_congr (Equiv.ofInjective f f.2) g).trans (set.sum_compl (range f)))
  refine' ⟨h, _⟩; rintro ⟨x, hx⟩; simp [set.sum_compl_symm_apply_of_mem, hx]
#align cardinal.extend_function Cardinal.extend_function

#print Cardinal.extend_function_finite /-
theorem extend_function_finite {α β : Type _} [Finite α] {s : Set α} (f : s ↪ β)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x :=
  by
  apply extend_function f
  cases' id h with g
  rw [← lift_mk_eq] at h
  rw [← lift_mk_eq, mk_compl_eq_mk_compl_finite_lift h]
  rw [mk_range_eq_lift]; exact f.2
#align cardinal.extend_function_finite Cardinal.extend_function_finite
-/

/- warning: cardinal.extend_function_of_lt -> Cardinal.extend_function_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} (f : Function.Embedding.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β), (LT.lt.{succ u1} Cardinal.{u1} (Preorder.toLT.{succ u1} Cardinal.{u1} (PartialOrder.toPreorder.{succ u1} Cardinal.{u1} (OrderedAddCommMonoid.toPartialOrder.{succ u1} Cardinal.{u1} (OrderedSemiring.toOrderedAddCommMonoid.{succ u1} Cardinal.{u1} (OrderedCommSemiring.toOrderedSemiring.{succ u1} Cardinal.{u1} (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{succ u1} Cardinal.{u1} Cardinal.canonicallyOrderedCommSemiring.{u1})))))) (Cardinal.mk.{u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s)) (Cardinal.mk.{u1} α)) -> (Nonempty.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α β)) -> (Exists.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α β) (fun (g : Equiv.{succ u1, succ u2} α β) => forall (x : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s), Eq.{succ u2} β (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))) x)) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) (fun (_x : Function.Embedding.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) β) f x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} (f : Function.Embedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β), (LT.lt.{succ u2} Cardinal.{u2} (Preorder.toLT.{succ u2} Cardinal.{u2} (PartialOrder.toPreorder.{succ u2} Cardinal.{u2} Cardinal.partialOrder.{u2})) (Cardinal.mk.{u2} (Set.Elem.{u2} α s)) (Cardinal.mk.{u2} α)) -> (Nonempty.{max (succ u1) (succ u2)} (Equiv.{succ u2, succ u1} α β)) -> (Exists.{max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} α β) (fun (g : Equiv.{succ u2, succ u1} α β) => forall (x : Set.Elem.{u2} α s), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => β) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) g (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β) (Set.Elem.{u2} α s) (fun (_x : Set.Elem.{u2} α s) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Set.Elem.{u2} α s) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β) (Set.Elem.{u2} α s) β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} (Set.Elem.{u2} α s) β)) f x)))
Case conversion may be inaccurate. Consider using '#align cardinal.extend_function_of_lt Cardinal.extend_function_of_ltₓ'. -/
theorem extend_function_of_lt {α β : Type _} {s : Set α} (f : s ↪ β) (hs : (#s) < (#α))
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x :=
  by
  cases fintypeOrInfinite α
  · exact extend_function_finite f h
  · apply extend_function f
    cases' id h with g
    haveI := Infinite.of_injective _ g.injective
    rw [← lift_mk_eq'] at h⊢
    rwa [mk_compl_of_infinite s hs, mk_compl_of_infinite]
    rwa [← lift_lt, mk_range_eq_of_injective f.injective, ← h, lift_lt]
#align cardinal.extend_function_of_lt Cardinal.extend_function_of_lt

section Bit

/-!
This section proves inequalities for `bit0` and `bit1`, enabling `simp` to solve inequalities
for numeral cardinals. The complexity of the resulting algorithm is not good, as in some cases
`simp` reduces an inequality to a disjunction of two situations, depending on whether a cardinal
is finite or infinite. Since the evaluation of the branches is not lazy, this is bad. It is good
enough for practical situations, though.

For specific numbers, these inequalities could also be deduced from the corresponding
inequalities of natural numbers using `norm_cast`:
```
example : (37 : cardinal) < 42 :=
by { norm_cast, norm_num }
```
-/


theorem bit0_ne_zero (a : Cardinal) : ¬bit0 a = 0 ↔ ¬a = 0 := by simp [bit0]
#align cardinal.bit0_ne_zero Cardinal.bit0_ne_zero

@[simp]
theorem bit1_ne_zero (a : Cardinal) : ¬bit1 a = 0 := by simp [bit1]
#align cardinal.bit1_ne_zero Cardinal.bit1_ne_zero

@[simp]
theorem zero_lt_bit0 (a : Cardinal) : 0 < bit0 a ↔ 0 < a :=
  by
  rw [← not_iff_not]
  simp [bit0]
#align cardinal.zero_lt_bit0 Cardinal.zero_lt_bit0

@[simp]
theorem zero_lt_bit1 (a : Cardinal) : 0 < bit1 a :=
  zero_lt_one.trans_le (self_le_add_left _ _)
#align cardinal.zero_lt_bit1 Cardinal.zero_lt_bit1

@[simp]
theorem one_le_bit0 (a : Cardinal) : 1 ≤ bit0 a ↔ 0 < a :=
  ⟨fun h => (zero_lt_bit0 a).mp (zero_lt_one.trans_le h), fun h =>
    (one_le_iff_pos.mpr h).trans (self_le_add_left a a)⟩
#align cardinal.one_le_bit0 Cardinal.one_le_bit0

@[simp]
theorem one_le_bit1 (a : Cardinal) : 1 ≤ bit1 a :=
  self_le_add_left _ _
#align cardinal.one_le_bit1 Cardinal.one_le_bit1

theorem bit0_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : bit0 c = c :=
  add_eq_self h
#align cardinal.bit0_eq_self Cardinal.bit0_eq_self

@[simp]
theorem bit0_lt_aleph0 {c : Cardinal} : bit0 c < ℵ₀ ↔ c < ℵ₀ := by simp [bit0, add_lt_aleph_0_iff]
#align cardinal.bit0_lt_aleph_0 Cardinal.bit0_lt_aleph0

@[simp]
theorem aleph0_le_bit0 {c : Cardinal} : ℵ₀ ≤ bit0 c ↔ ℵ₀ ≤ c :=
  by
  rw [← not_iff_not]
  simp
#align cardinal.aleph_0_le_bit0 Cardinal.aleph0_le_bit0

@[simp]
theorem bit1_eq_self_iff {c : Cardinal} : bit1 c = c ↔ ℵ₀ ≤ c :=
  by
  by_cases h : ℵ₀ ≤ c
  · simp only [bit1, bit0_eq_self h, h, eq_self_iff_true, add_one_of_aleph_0_le]
  · refine' iff_of_false (ne_of_gt _) h
    rcases lt_aleph_0.1 (not_le.1 h) with ⟨n, rfl⟩
    norm_cast
    dsimp [bit1, bit0]
    linarith
#align cardinal.bit1_eq_self_iff Cardinal.bit1_eq_self_iff

@[simp]
theorem bit1_lt_aleph0 {c : Cardinal} : bit1 c < ℵ₀ ↔ c < ℵ₀ := by
  simp [bit1, bit0, add_lt_aleph_0_iff, one_lt_aleph_0]
#align cardinal.bit1_lt_aleph_0 Cardinal.bit1_lt_aleph0

@[simp]
theorem aleph0_le_bit1 {c : Cardinal} : ℵ₀ ≤ bit1 c ↔ ℵ₀ ≤ c :=
  by
  rw [← not_iff_not]
  simp
#align cardinal.aleph_0_le_bit1 Cardinal.aleph0_le_bit1

@[simp]
theorem bit0_le_bit0 {a b : Cardinal} : bit0 a ≤ bit0 b ↔ a ≤ b :=
  by
  cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
  · rw [bit0_eq_self ha, bit0_eq_self hb]
  · rw [bit0_eq_self ha]
    refine' iff_of_false (fun h => _) (hb.trans_le ha).not_le
    have A : bit0 b < ℵ₀ := by simpa using hb
    exact lt_irrefl _ ((A.trans_le ha).trans_le h)
  · rw [bit0_eq_self hb]
    exact iff_of_true ((bit0_lt_aleph_0.2 ha).le.trans hb) (ha.le.trans hb)
  · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
    norm_cast
    exact bit0_le_bit0
#align cardinal.bit0_le_bit0 Cardinal.bit0_le_bit0

@[simp]
theorem bit0_le_bit1 {a b : Cardinal} : bit0 a ≤ bit1 b ↔ a ≤ b :=
  by
  cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
  · rw [bit0_eq_self ha, bit1_eq_self_iff.2 hb]
  · rw [bit0_eq_self ha]
    refine' iff_of_false (fun h => _) (hb.trans_le ha).not_le
    have A : bit1 b < ℵ₀ := by simpa using hb
    exact lt_irrefl _ ((A.trans_le ha).trans_le h)
  · rw [bit1_eq_self_iff.2 hb]
    exact iff_of_true ((bit0_lt_aleph_0.2 ha).le.trans hb) (ha.le.trans hb)
  · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
    norm_cast
    exact Nat.bit0_le_bit1_iff
#align cardinal.bit0_le_bit1 Cardinal.bit0_le_bit1

@[simp]
theorem bit1_le_bit1 {a b : Cardinal} : bit1 a ≤ bit1 b ↔ a ≤ b :=
  ⟨fun h => bit0_le_bit1.1 ((self_le_add_right (bit0 a) 1).trans h), fun h =>
    (add_le_add_right (add_le_add_left h a) 1).trans (add_le_add_right (add_le_add_right h b) 1)⟩
#align cardinal.bit1_le_bit1 Cardinal.bit1_le_bit1

@[simp]
theorem bit1_le_bit0 {a b : Cardinal} : bit1 a ≤ bit0 b ↔ a < b ∨ a ≤ b ∧ ℵ₀ ≤ a :=
  by
  cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
  · simp only [bit1_eq_self_iff.mpr ha, bit0_eq_self hb, ha, and_true_iff]
    refine' ⟨fun h => Or.inr h, fun h => _⟩
    cases h
    · exact le_of_lt h
    · exact h
  · rw [bit1_eq_self_iff.2 ha]
    refine' iff_of_false (fun h => _) fun h => _
    · have A : bit0 b < ℵ₀ := by simpa using hb
      exact lt_irrefl _ ((A.trans_le ha).trans_le h)
    · exact not_le_of_lt (hb.trans_le ha) (h.elim le_of_lt And.left)
  · rw [bit0_eq_self hb]
    exact iff_of_true ((bit1_lt_aleph_0.2 ha).le.trans hb) (Or.inl <| ha.trans_le hb)
  · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
    norm_cast
    simp [not_le.mpr ha]
#align cardinal.bit1_le_bit0 Cardinal.bit1_le_bit0

@[simp]
theorem bit0_lt_bit0 {a b : Cardinal} : bit0 a < bit0 b ↔ a < b :=
  by
  cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
  · rw [bit0_eq_self ha, bit0_eq_self hb]
  · rw [bit0_eq_self ha]
    refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
    have A : bit0 b < ℵ₀ := by simpa using hb
    exact lt_irrefl _ ((A.trans_le ha).trans h)
  · rw [bit0_eq_self hb]
    exact iff_of_true ((bit0_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
  · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
    norm_cast
    exact bit0_lt_bit0
#align cardinal.bit0_lt_bit0 Cardinal.bit0_lt_bit0

@[simp]
theorem bit1_lt_bit0 {a b : Cardinal} : bit1 a < bit0 b ↔ a < b :=
  by
  cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
  · rw [bit1_eq_self_iff.2 ha, bit0_eq_self hb]
  · rw [bit1_eq_self_iff.2 ha]
    refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
    have A : bit0 b < ℵ₀ := by simpa using hb
    exact lt_irrefl _ ((A.trans_le ha).trans h)
  · rw [bit0_eq_self hb]
    exact iff_of_true ((bit1_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
  · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
    norm_cast
    exact Nat.bit1_lt_bit0_iff
#align cardinal.bit1_lt_bit0 Cardinal.bit1_lt_bit0

@[simp]
theorem bit1_lt_bit1 {a b : Cardinal} : bit1 a < bit1 b ↔ a < b :=
  by
  cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
  · rw [bit1_eq_self_iff.2 ha, bit1_eq_self_iff.2 hb]
  · rw [bit1_eq_self_iff.2 ha]
    refine' iff_of_false (fun h => _) (hb.le.trans ha).not_lt
    have A : bit1 b < ℵ₀ := by simpa using hb
    exact lt_irrefl _ ((A.trans_le ha).trans h)
  · rw [bit1_eq_self_iff.2 hb]
    exact iff_of_true ((bit1_lt_aleph_0.2 ha).trans_le hb) (ha.trans_le hb)
  · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
    norm_cast
    exact bit1_lt_bit1
#align cardinal.bit1_lt_bit1 Cardinal.bit1_lt_bit1

@[simp]
theorem bit0_lt_bit1 {a b : Cardinal} : bit0 a < bit1 b ↔ a < b ∨ a ≤ b ∧ a < ℵ₀ :=
  by
  cases' le_or_lt ℵ₀ a with ha ha <;> cases' le_or_lt ℵ₀ b with hb hb
  · simp [bit0_eq_self ha, bit1_eq_self_iff.2 hb, not_lt.mpr ha]
  · rw [bit0_eq_self ha]
    refine' iff_of_false (fun h => _) fun h => _
    · have A : bit1 b < ℵ₀ := by simpa using hb
      exact lt_irrefl _ ((A.trans_le ha).trans h)
    · exact (hb.trans_le ha).not_le (h.elim le_of_lt And.left)
  · rw [bit1_eq_self_iff.2 hb]
    exact iff_of_true ((bit0_lt_aleph_0.2 ha).trans_le hb) (Or.inl <| ha.trans_le hb)
  · rcases lt_aleph_0.1 ha with ⟨m, rfl⟩
    rcases lt_aleph_0.1 hb with ⟨n, rfl⟩
    norm_cast
    simp only [ha, and_true_iff, Nat.bit0_lt_bit1_iff, or_iff_right_of_imp le_of_lt]
#align cardinal.bit0_lt_bit1 Cardinal.bit0_lt_bit1

theorem one_lt_two : (1 : Cardinal) < 2 :=
  by
  -- This strategy works generally to prove inequalities between numerals in `cardinality`.
  norm_cast
  norm_num
#align cardinal.one_lt_two Cardinal.one_lt_two

@[simp]
theorem one_lt_bit0 {a : Cardinal} : 1 < bit0 a ↔ 0 < a := by simp [← bit1_zero]
#align cardinal.one_lt_bit0 Cardinal.one_lt_bit0

@[simp]
theorem one_lt_bit1 (a : Cardinal) : 1 < bit1 a ↔ 0 < a := by simp [← bit1_zero]
#align cardinal.one_lt_bit1 Cardinal.one_lt_bit1

end Bit

end Cardinal

