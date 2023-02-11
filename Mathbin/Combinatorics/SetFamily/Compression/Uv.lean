/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.set_family.compression.uv
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Card

/-!
# UV-compressions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines UV-compression. It is an operation on a set family that reduces its shadow.

UV-compressing `a : α` along `u v : α` means replacing `a` by `(a ⊔ u) \ v` if `a` and `u` are
disjoint and `v ≤ a`. In some sense, it's moving `a` from `v` to `u`.

UV-compressions are immensely useful to prove the Kruskal-Katona theorem. The idea is that
compressing a set family might decrease the size of its shadow, so iterated compressions hopefully
minimise the shadow.

## Main declarations

* `uv.compress`: `compress u v a` is `a` compressed along `u` and `v`.
* `uv.compression`: `compression u v s` is the compression of the set family `s` along `u` and `v`.
  It is the compressions of the elements of `s` whose compression is not already in `s` along with
  the element whose compression is already in `s`. This way of splitting into what moves and what
  does not ensures the compression doesn't squash the set family, which is proved by
  `uv.card_compress`.

## Notation

`𝓒` (typed with `\MCC`) is notation for `uv.compression` in locale `finset_family`.

## Notes

Even though our emphasis is on `finset α`, we define UV-compressions more generally in a generalized
boolean algebra, so that one can use it for `set α`.

## TODO

Prove that compressing reduces the size of shadow. This result and some more already exist on the
branch `combinatorics`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/


open Finset

variable {α : Type _}

/- warning: sup_sdiff_inj_on -> sup_sdiff_injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (u : α) (v : α), Set.InjOn.{u1, u1} α α (fun (x : α) => SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) x u) v) (setOf.{u1} α (fun (x : α) => And (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u x) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (u : α) (v : α), Set.InjOn.{u1, u1} α α (fun (x : α) => SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) x u) v) (setOf.{u1} α (fun (x : α) => And (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u x) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v x)))
Case conversion may be inaccurate. Consider using '#align sup_sdiff_inj_on sup_sdiff_injOnₓ'. -/
/-- UV-compression is injective on the elements it moves. See `uv.compress`. -/
theorem sup_sdiff_injOn [GeneralizedBooleanAlgebra α] (u v : α) :
    { x | Disjoint u x ∧ v ≤ x }.InjOn fun x => (x ⊔ u) \ v :=
  by
  rintro a ha b hb hab
  have h : ((a ⊔ u) \ v) \ u ⊔ v = ((b ⊔ u) \ v) \ u ⊔ v :=
    by
    dsimp at hab
    rw [hab]
  rwa [sdiff_sdiff_comm, ha.1.symm.sup_sdiff_cancel_right, sdiff_sdiff_comm,
    hb.1.symm.sup_sdiff_cancel_right, sdiff_sup_cancel ha.2, sdiff_sup_cancel hb.2] at h
#align sup_sdiff_inj_on sup_sdiff_injOn

-- The namespace is here to distinguish from other compressions.
namespace Uv

/-! ### UV-compression in generalized boolean algebras -/


section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] [DecidableRel (@Disjoint α _ _)]
  [DecidableRel ((· ≤ ·) : α → α → Prop)] {s : Finset α} {u v a b : α}

attribute [local instance] decidableEqOfDecidableLe

#print UV.compress /-
/-- To UV-compress `a`, if it doesn't touch `U` and does contain `V`, we remove `V` and
put `U` in. We'll only really use this when `|U| = |V|` and `U ∩ V = ∅`. -/
def compress (u v a : α) : α :=
  if Disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a
#align uv.compress UV.compress
-/

#print UV.compression /-
/-- To UV-compress a set family, we compress each of its elements, except that we don't want to
reduce the cardinality, so we keep all elements whose compression is already present. -/
def compression (u v : α) (s : Finset α) :=
  (s.filterₓ fun a => compress u v a ∈ s) ∪ (s.image <| compress u v).filterₓ fun a => a ∉ s
#align uv.compression UV.compression
-/

-- mathport name: uv.compression
scoped[FinsetFamily] notation "𝓒 " => UV.compression

#print UV.IsCompressed /-
/-- `is_compressed u v s` expresses that `s` is UV-compressed. -/
def IsCompressed (u v : α) (s : Finset α) :=
  𝓒 u v s = s
#align uv.is_compressed UV.IsCompressed
-/

/- warning: uv.compress_of_disjoint_of_le -> UV.compress_of_disjoint_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {u : α} {v : α} {a : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> (Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a u) v))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1017 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1019 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1017 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1019)] {u : α} {v : α} {a : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> (Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a u) v))
Case conversion may be inaccurate. Consider using '#align uv.compress_of_disjoint_of_le UV.compress_of_disjoint_of_leₓ'. -/
theorem compress_of_disjoint_of_le (hua : Disjoint u a) (hva : v ≤ a) :
    compress u v a = (a ⊔ u) \ v :=
  if_pos ⟨hua, hva⟩
#align uv.compress_of_disjoint_of_le UV.compress_of_disjoint_of_le

/- warning: uv.mem_compression -> UV.mem_compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) (Or (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s)) (And (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) => Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v b) a)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1090 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1092 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1090 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1092)] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) (Or (And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s)) (And (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b s) (Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v b) a)))))
Case conversion may be inaccurate. Consider using '#align uv.mem_compression UV.mem_compressionₓ'. -/
/-- `a` is in the UV-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
theorem mem_compression :
    a ∈ 𝓒 u v s ↔ a ∈ s ∧ compress u v a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, compress u v b = a := by
  simp_rw [compression, mem_union, mem_filter, mem_image, and_comm' (a ∉ s)]
#align uv.mem_compression UV.mem_compression

#print UV.compress_self /-
@[simp]
theorem compress_self (u a : α) : compress u u a = a :=
  by
  unfold compress
  split_ifs
  · exact h.1.symm.sup_sdiff_cancel_right
  · rfl
#align uv.compress_self UV.compress_self
-/

#print UV.compression_self /-
@[simp]
theorem compression_self (u : α) (s : Finset α) : 𝓒 u u s = s :=
  by
  unfold compression
  convert union_empty s
  · ext a
    rw [mem_filter, compress_self, and_self_iff]
  · refine' eq_empty_of_forall_not_mem fun a ha => _
    simp_rw [mem_filter, mem_image, compress_self] at ha
    obtain ⟨⟨b, hb, rfl⟩, hb'⟩ := ha
    exact hb' hb
#align uv.compression_self UV.compression_self
-/

#print UV.is_compressed_self /-
/-- Any family is compressed along two identical elements. -/
theorem is_compressed_self (u : α) (s : Finset α) : IsCompressed u u s :=
  compression_self u s
#align uv.is_compressed_self UV.is_compressed_self
-/

/- warning: uv.compress_disjoint -> UV.compress_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} (u : α) (v : α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.filter.{u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s) (fun (a : α) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => decidableEqOfDecidableLe.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s) s) (Finset.filter.{u1} α (fun (a : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (fun (a : α) => Not.decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => decidableEqOfDecidableLe.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) a s)) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => decidableEqOfDecidableLe.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1449 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1451 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1449 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1451)] {s : Finset.{u1} α} (u : α) (v : α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.filter.{u1} α (fun (a : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s) (fun (a : α) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => decidableEq_of_decidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s) s) (Finset.filter.{u1} α (fun (a : α) => Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) (fun (a : α) => instDecidableNot (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => decidableEq_of_decidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) a s)) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => decidableEq_of_decidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v) s))
Case conversion may be inaccurate. Consider using '#align uv.compress_disjoint UV.compress_disjointₓ'. -/
theorem compress_disjoint (u v : α) :
    Disjoint (s.filterₓ fun a => compress u v a ∈ s)
      ((s.image <| compress u v).filterₓ fun a => a ∉ s) :=
  disjoint_left.2 fun a ha₁ ha₂ => (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1
#align uv.compress_disjoint UV.compress_disjoint

#print UV.compress_idem /-
/-- Compressing an element is idempotent. -/
@[simp]
theorem compress_idem (u v a : α) : compress u v (compress u v a) = compress u v a :=
  by
  unfold compress
  split_ifs with h h'
  · rw [le_sdiff_iff.1 h'.2, sdiff_bot, sdiff_bot, sup_assoc, sup_idem]
  · rfl
  · rfl
#align uv.compress_idem UV.compress_idem
-/

#print UV.compress_mem_compression /-
theorem compress_mem_compression (ha : a ∈ s) : compress u v a ∈ 𝓒 u v s :=
  by
  rw [mem_compression]
  by_cases compress u v a ∈ s
  · rw [compress_idem]
    exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, a, ha, rfl⟩
#align uv.compress_mem_compression UV.compress_mem_compression
-/

#print UV.compress_mem_compression_of_mem_compression /-
-- This is a special case of `compress_mem_compression` once we have `compression_idem`.
theorem compress_mem_compression_of_mem_compression (ha : a ∈ 𝓒 u v s) : compress u v a ∈ 𝓒 u v s :=
  by
  rw [mem_compression] at ha⊢
  simp only [compress_idem, exists_prop]
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨by rwa [compress_idem], b, hb, (compress_idem _ _ _).symm⟩
#align uv.compress_mem_compression_of_mem_compression UV.compress_mem_compression_of_mem_compression
-/

#print UV.compression_idem /-
/-- Compressing a family is idempotent. -/
@[simp]
theorem compression_idem (u v : α) (s : Finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s :=
  by
  have h : Filter (fun a => compress u v a ∉ 𝓒 u v s) (𝓒 u v s) = ∅ :=
    filter_false_of_mem fun a ha h => h <| compress_mem_compression_of_mem_compression ha
  rw [compression, image_filter, h, image_empty, ← h]
  exact filter_union_filter_neg_eq _ (compression u v s)
#align uv.compression_idem UV.compression_idem
-/

#print UV.card_compression /-
/-- Compressing a family doesn't change its size. -/
theorem card_compression (u v : α) (s : Finset α) : (𝓒 u v s).card = s.card :=
  by
  rw [compression, card_disjoint_union (compress_disjoint _ _), image_filter, card_image_of_inj_on,
    ← card_disjoint_union, filter_union_filter_neg_eq]
  · rw [disjoint_iff_inter_eq_empty]
    exact filter_inter_filter_neg_eq _ _ _
  intro a ha b hb hab
  dsimp at hab
  rw [mem_coe, mem_filter, Function.comp_apply] at ha hb
  rw [compress] at ha hab
  split_ifs  at ha hab with has
  · rw [compress] at hb hab
    split_ifs  at hb hab with hbs
    · exact sup_sdiff_injOn u v has hbs hab
    · exact (hb.2 hb.1).elim
  · exact (ha.2 ha.1).elim
#align uv.card_compression UV.card_compression
-/

/- warning: uv.sup_sdiff_mem_of_mem_compression -> UV.sup_sdiff_mem_of_mem_compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u a) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a u) v) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2566 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2568 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2566 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2568)] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u a) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a u) v) s)
Case conversion may be inaccurate. Consider using '#align uv.sup_sdiff_mem_of_mem_compression UV.sup_sdiff_mem_of_mem_compressionₓ'. -/
/-- If `a` is in the family compression and can be compressed, then its compression is in the
original family. -/
theorem sup_sdiff_mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hua : Disjoint u a) :
    (a ⊔ u) \ v ∈ s :=
  by
  rw [mem_compression, compress_of_disjoint_of_le hua hva] at ha
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact ha
  have hu : u = ⊥ :=
    by
    suffices Disjoint u (u \ v) by rwa [(hua.mono_right hva).sdiff_eq_left, disjoint_self] at this
    refine' hua.mono_right _
    rw [← compress_idem, compress_of_disjoint_of_le hua hva]
    exact sdiff_le_sdiff_right le_sup_right
  have hv : v = ⊥ := by
    rw [← disjoint_self]
    apply Disjoint.mono_right hva
    rw [← compress_idem, compress_of_disjoint_of_le hua hva]
    exact disjoint_sdiff_self_right
  rwa [hu, hv, compress_self, sup_bot_eq, sdiff_bot]
#align uv.sup_sdiff_mem_of_mem_compression UV.sup_sdiff_mem_of_mem_compression

/- warning: uv.mem_of_mem_compression -> UV.mem_of_mem_compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> ((Eq.{succ u1} α v (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toHasBot.{u1} α _inst_1))) -> (Eq.{succ u1} α u (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toHasBot.{u1} α _inst_1)))) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2956 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2958 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2956 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2958)] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> ((Eq.{succ u1} α v (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toBot.{u1} α _inst_1))) -> (Eq.{succ u1} α u (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toBot.{u1} α _inst_1)))) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align uv.mem_of_mem_compression UV.mem_of_mem_compressionₓ'. -/
/-- If `a` is in the `u, v`-compression but `v ≤ a`, then `a` must have been in the original
family. -/
theorem mem_of_mem_compression (ha : a ∈ 𝓒 u v s) (hva : v ≤ a) (hvu : v = ⊥ → u = ⊥) : a ∈ s :=
  by
  rw [mem_compression] at ha
  obtain ha | ⟨_, b, hb, h⟩ := ha
  · exact ha.1
  unfold compress at h
  split_ifs  at h
  · rw [← h, le_sdiff_iff] at hva
    rw [hvu hva, hva, sup_bot_eq, sdiff_bot] at h
    rwa [← h]
  · rwa [← h]
#align uv.mem_of_mem_compression UV.mem_of_mem_compression

end GeneralizedBooleanAlgebra

/-! ### UV-compression on finsets -/


open FinsetFamily

variable [DecidableEq α] {𝒜 : Finset (Finset α)} {U V A : Finset α}

/- warning: uv.card_compress -> UV.card_compress is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {U : Finset.{u1} α} {V : Finset.{u1} α}, (Eq.{1} Nat (Finset.card.{u1} α U) (Finset.card.{u1} α V)) -> (forall (A : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (UV.compress.{u1} (Finset.{u1} α) (Finset.generalizedBooleanAlgebra.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableDisjoint.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableDforallFinset.{u1} α a (fun (a_1 : α) (ᾰ : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 b) (fun (a_1 : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 b)) U V A)) (Finset.card.{u1} α A))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {U : Finset.{u1} α} {V : Finset.{u1} α}, (Eq.{1} Nat (Finset.card.{u1} α U) (Finset.card.{u1} α V)) -> (forall (A : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (UV.compress.{u1} (Finset.{u1} α) (Finset.instGeneralizedBooleanAlgebraFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableDisjoint.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableDforallFinset.{u1} α a (fun (a_1 : α) (ᾰ : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 a) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 b) (fun (a_1 : α) (h : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 a) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 b)) U V A)) (Finset.card.{u1} α A))
Case conversion may be inaccurate. Consider using '#align uv.card_compress UV.card_compressₓ'. -/
/-- Compressing a finset doesn't change its size. -/
theorem card_compress (hUV : U.card = V.card) (A : Finset α) : (compress U V A).card = A.card :=
  by
  unfold compress
  split_ifs
  ·
    rw [card_sdiff (h.2.trans le_sup_left), sup_eq_union, card_disjoint_union h.1.symm, hUV,
      add_tsub_cancel_right]
  · rfl
#align uv.card_compress UV.card_compress

end Uv

