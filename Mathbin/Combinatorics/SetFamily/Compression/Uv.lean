/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module combinatorics.set_family.compression.uv
! leanprover-community/mathlib commit 6f8ab7de1c4b78a68ab8cf7dd83d549eb78a68a1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SetFamily.Shadow
import Mathbin.Data.Finset.Sort

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
  `uv.card_compression`.
* `uv.card_shadow_compression_le`: Compressing reduces the size of the shadow. This is a key fact in
  the proof of Kruskal-Katona.

## Notation

`𝓒` (typed with `\MCC`) is notation for `uv.compression` in locale `finset_family`.

## Notes

Even though our emphasis is on `finset α`, we define UV-compressions more generally in a generalized
boolean algebra, so that one can use it for `set α`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

compression, UV-compression, shadow
-/


open Finset

variable {α : Type _}

/- warning: sup_sdiff_inj_on -> sup_sdiff_injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (u : α) (v : α), Set.InjOn.{u1, u1} α α (fun (x : α) => SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) x u) v) (setOf.{u1} α (fun (x : α) => And (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u x) (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] (u : α) (v : α), Set.InjOn.{u1, u1} α α (fun (x : α) => SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) x u) v) (setOf.{u1} α (fun (x : α) => And (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u x) (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v x)))
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

attribute [local instance] decidableEqOfDecidableLE

/- warning: uv.compress -> UV.compress is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))], α -> α -> α -> α
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.256 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.258 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.256 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.258)], α -> α -> α -> α
Case conversion may be inaccurate. Consider using '#align uv.compress UV.compressₓ'. -/
/-- UV-compressing `a` means removing `v` from it and adding `u` if `a` and `u` are disjoint and
`v ≤ a` (it replaces the `v` part of `a` by the `u` part). Else, UV-compressing `a` doesn't do
anything. This is most useful when `u` and `v` are disjoint finsets of the same size. -/
def compress (u v a : α) : α :=
  if Disjoint u a ∧ v ≤ a then (a ⊔ u) \ v else a
#align uv.compress UV.compress

/- warning: uv.compression -> UV.compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))], α -> α -> (Finset.{u1} α) -> (Finset.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.335 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.337 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.335 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.337)], α -> α -> (Finset.{u1} α) -> (Finset.{u1} α)
Case conversion may be inaccurate. Consider using '#align uv.compression UV.compressionₓ'. -/
/-- To UV-compress a set family, we compress each of its elements, except that we don't want to
reduce the cardinality, so we keep all elements whose compression is already present. -/
def compression (u v : α) (s : Finset α) :=
  (s.filterₓ fun a => compress u v a ∈ s) ∪ (s.image <| compress u v).filterₓ fun a => a ∉ s
#align uv.compression UV.compression

-- mathport name: uv.compression
scoped[FinsetFamily] notation "𝓒 " => UV.compression

/- warning: uv.is_compressed -> UV.IsCompressed is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))], α -> α -> (Finset.{u1} α) -> Prop
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.959 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.961 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.959 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.961)], α -> α -> (Finset.{u1} α) -> Prop
Case conversion may be inaccurate. Consider using '#align uv.is_compressed UV.IsCompressedₓ'. -/
/-- `is_compressed u v s` expresses that `s` is UV-compressed. -/
def IsCompressed (u v : α) (s : Finset α) :=
  𝓒 u v s = s
#align uv.is_compressed UV.IsCompressed

/- warning: uv.compress_of_disjoint_of_le -> UV.compress_of_disjoint_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {u : α} {v : α} {a : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u a) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> (Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a u) v))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1017 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1019 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1017 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1019)] {u : α} {v : α} {a : α}, (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u a) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> (Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a u) v))
Case conversion may be inaccurate. Consider using '#align uv.compress_of_disjoint_of_le UV.compress_of_disjoint_of_leₓ'. -/
theorem compress_of_disjoint_of_le (hua : Disjoint u a) (hva : v ≤ a) :
    compress u v a = (a ⊔ u) \ v :=
  if_pos ⟨hua, hva⟩
#align uv.compress_of_disjoint_of_le UV.compress_of_disjoint_of_le

theorem compress_of_disjoint_of_le' (hva : Disjoint v a) (hua : u ≤ a) :
    compress u v ((a ⊔ v) \ u) = a := by
  rw [compress_of_disjoint_of_le disjoint_sdiff_self_right
      (le_sdiff.2 ⟨(le_sup_right : v ≤ a ⊔ v), hva.mono_right hua⟩),
    sdiff_sup_cancel (le_sup_of_le_left hua), hva.symm.sup_sdiff_cancel_right]
#align uv.compress_of_disjoint_of_le' Uv.compress_of_disjoint_of_le'

/- warning: uv.mem_compression -> UV.mem_compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, Iff (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) (Or (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s)) (And (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (Exists.{succ u1} α (fun (b : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) b s) => Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v b) a)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1090 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1092 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1090 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1092)] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, Iff (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) (Or (And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s)) (And (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) (Exists.{succ u1} α (fun (b : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) b s) (Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v b) a)))))
Case conversion may be inaccurate. Consider using '#align uv.mem_compression UV.mem_compressionₓ'. -/
/-- `a` is in the UV-compressed family iff it's in the original and its compression is in the
original, or it's not in the original but it's the compression of something in the original. -/
theorem mem_compression :
    a ∈ 𝓒 u v s ↔ a ∈ s ∧ compress u v a ∈ s ∨ a ∉ s ∧ ∃ b ∈ s, compress u v b = a := by
  simp_rw [compression, mem_union, mem_filter, mem_image, and_comm' (a ∉ s)]
#align uv.mem_compression UV.mem_compression

protected theorem IsCompressed.eq (h : IsCompressed u v s) : 𝓒 u v s = s :=
  h
#align uv.is_compressed.eq UV.IsCompressed.eq

/- warning: uv.compress_self -> UV.compress_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] (u : α) (a : α), Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u u a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1210 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1212 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1210 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1212)] (u : α) (a : α), Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u u a) a
Case conversion may be inaccurate. Consider using '#align uv.compress_self UV.compress_selfₓ'. -/
@[simp]
theorem compress_self (u a : α) : compress u u a = a :=
  by
  unfold compress
  split_ifs
  · exact h.1.symm.sup_sdiff_cancel_right
  · rfl
#align uv.compress_self UV.compress_self

/- warning: uv.compression_self -> UV.compression_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] (u : α) (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u u s) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1300 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1302 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1300 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1302)] (u : α) (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u u s) s
Case conversion may be inaccurate. Consider using '#align uv.compression_self UV.compression_selfₓ'. -/
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

/- warning: uv.is_compressed_self -> UV.is_compressed_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] (u : α) (s : Finset.{u1} α), UV.IsCompressed.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u u s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1478 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1480 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1478 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1480)] (u : α) (s : Finset.{u1} α), UV.IsCompressed.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u u s
Case conversion may be inaccurate. Consider using '#align uv.is_compressed_self UV.is_compressed_selfₓ'. -/
/-- Any family is compressed along two identical elements. -/
theorem is_compressed_self (u : α) (s : Finset α) : IsCompressed u u s :=
  compression_self u s
#align uv.is_compressed_self UV.is_compressed_self

/-- An element can be compressed to any other element by removing/adding the differences. -/
@[simp]
theorem compress_sdiff_sdiff (a b : α) : compress (a \ b) (b \ a) b = a :=
  by
  refine' (compress_of_disjoint_of_le disjoint_sdiff_self_left sdiff_le).trans _
  rw [sup_sdiff_self_right, sup_sdiff, disjoint_sdiff_self_right.sdiff_eq_left, sup_eq_right]
  exact sdiff_sdiff_le
#align uv.compress_sdiff_sdiff Uv.compress_sdiff_sdiff

/- warning: uv.compress_disjoint -> UV.compress_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} (u : α) (v : α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) (Finset.filter.{u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s) (fun (a : α) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => decidableEqOfDecidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s) s) (Finset.filter.{u1} α (fun (a : α) => Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (fun (a : α) => Not.decidable (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => decidableEqOfDecidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) a s)) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => decidableEqOfDecidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1530 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1532 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1530 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1532)] {s : Finset.{u1} α} (u : α) (v : α), Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.filter.{u1} α (fun (a : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s) (fun (a : α) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => decidableEqOfDecidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) s) s) (Finset.filter.{u1} α (fun (a : α) => Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) (fun (a : α) => instDecidableNot (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Finset.decidableMem.{u1} α (fun (a : α) (b : α) => decidableEqOfDecidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) a s)) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => decidableEqOfDecidableLE.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (fun (a : α) (b : α) => _inst_3 a b) a b) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v) s))
Case conversion may be inaccurate. Consider using '#align uv.compress_disjoint UV.compress_disjointₓ'. -/
theorem compress_disjoint (u v : α) :
    Disjoint (s.filterₓ fun a => compress u v a ∈ s)
      ((s.image <| compress u v).filterₓ fun a => a ∉ s) :=
  disjoint_left.2 fun a ha₁ ha₂ => (mem_filter.1 ha₂).2 (mem_filter.1 ha₁).1
#align uv.compress_disjoint UV.compress_disjoint

/- warning: uv.compress_idem -> UV.compress_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] (u : α) (v : α) (a : α), Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a)) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1631 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1633 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1631 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1633)] (u : α) (v : α) (a : α), Eq.{succ u1} α (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a)) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a)
Case conversion may be inaccurate. Consider using '#align uv.compress_idem UV.compress_idemₓ'. -/
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

/- warning: uv.compress_mem_compression -> UV.compress_mem_compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1776 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1778 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1776 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1778)] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s))
Case conversion may be inaccurate. Consider using '#align uv.compress_mem_compression UV.compress_mem_compressionₓ'. -/
theorem compress_mem_compression (ha : a ∈ s) : compress u v a ∈ 𝓒 u v s :=
  by
  rw [mem_compression]
  by_cases compress u v a ∈ s
  · rw [compress_idem]
    exact Or.inl ⟨h, h⟩
  · exact Or.inr ⟨h, a, ha, rfl⟩
#align uv.compress_mem_compression UV.compress_mem_compression

/- warning: uv.compress_mem_compression_of_mem_compression -> UV.compress_mem_compression_of_mem_compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1951 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1953 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1951 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.1953)] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (UV.compress.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v a) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s))
Case conversion may be inaccurate. Consider using '#align uv.compress_mem_compression_of_mem_compression UV.compress_mem_compression_of_mem_compressionₓ'. -/
-- This is a special case of `compress_mem_compression` once we have `compression_idem`.
theorem compress_mem_compression_of_mem_compression (ha : a ∈ 𝓒 u v s) : compress u v a ∈ 𝓒 u v s :=
  by
  rw [mem_compression] at ha⊢
  simp only [compress_idem, exists_prop]
  obtain ⟨_, ha⟩ | ⟨_, b, hb, rfl⟩ := ha
  · exact Or.inl ⟨ha, ha⟩
  · exact Or.inr ⟨by rwa [compress_idem], b, hb, (compress_idem _ _ _).symm⟩
#align uv.compress_mem_compression_of_mem_compression UV.compress_mem_compression_of_mem_compression

/- warning: uv.compression_idem -> UV.compression_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] (u : α) (v : α) (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2122 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2124 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2122 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2124)] (u : α) (v : α) (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)
Case conversion may be inaccurate. Consider using '#align uv.compression_idem UV.compression_idemₓ'. -/
/-- Compressing a family is idempotent. -/
@[simp]
theorem compression_idem (u v : α) (s : Finset α) : 𝓒 u v (𝓒 u v s) = 𝓒 u v s :=
  by
  have h : Filter (fun a => compress u v a ∉ 𝓒 u v s) (𝓒 u v s) = ∅ :=
    filter_false_of_mem fun a ha h => h <| compress_mem_compression_of_mem_compression ha
  rw [compression, image_filter, h, image_empty, ← h]
  exact filter_union_filter_neg_eq _ (compression u v s)
#align uv.compression_idem UV.compression_idem

/- warning: uv.card_compression -> UV.card_compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] (u : α) (v : α) (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) (Finset.card.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2336 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2338 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2336 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2338)] (u : α) (v : α) (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) (Finset.card.{u1} α s)
Case conversion may be inaccurate. Consider using '#align uv.card_compression UV.card_compressionₓ'. -/
/-- Compressing a family doesn't change its size. -/
@[simp]
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

theorem le_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : u ≤ a :=
  by
  rw [mem_compression] at h
  obtain _ | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs  at hba
  · rw [← hba, le_sdiff]
    exact ⟨le_sup_right, h.1.mono_right h.2⟩
  · cases ne_of_mem_of_not_mem hb ha hba
#align uv.le_of_mem_compression_of_not_mem Uv.le_of_mem_compression_of_not_mem

theorem disjoint_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) : Disjoint v a :=
  by
  rw [mem_compression] at h
  obtain _ | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs  at hba
  · rw [← hba]
    exact disjoint_sdiff_self_right
  · cases ne_of_mem_of_not_mem hb ha hba
#align uv.disjoint_of_mem_compression_of_not_mem Uv.disjoint_of_mem_compression_of_not_mem

theorem sup_sdiff_mem_of_mem_compression_of_not_mem (h : a ∈ 𝓒 u v s) (ha : a ∉ s) :
    (a ⊔ v) \ u ∈ s := by
  rw [mem_compression] at h
  obtain _ | ⟨-, b, hb, hba⟩ := h
  · cases ha h.1
  unfold compress at hba
  split_ifs  at hba
  ·
    rwa [← hba, sdiff_sup_cancel (le_sup_of_le_left h.2), sup_sdiff_right_self,
      h.1.symm.sdiff_eq_left]
  · cases ne_of_mem_of_not_mem hb ha hba
#align uv.sup_sdiff_mem_of_mem_compression_of_not_mem Uv.sup_sdiff_mem_of_mem_compression_of_not_mem

/- warning: uv.sup_sdiff_mem_of_mem_compression -> UV.sup_sdiff_mem_of_mem_compression is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u a) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toHasSdiff.{u1} α _inst_1) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a u) v) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2641 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2643 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2641 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.2643)] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1) u a) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) (SDiff.sdiff.{u1} α (GeneralizedBooleanAlgebra.toSDiff.{u1} α _inst_1) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) a u) v) s)
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
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))))] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> ((Eq.{succ u1} α v (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toHasBot.{u1} α _inst_1))) -> (Eq.{succ u1} α u (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toHasBot.{u1} α _inst_1)))) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : GeneralizedBooleanAlgebra.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (Disjoint.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} α _inst_1))] [_inst_3 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.3031 : α) (x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.3033 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.3031 x._@.Mathlib.Combinatorics.SetFamily.Compression.UV._hyg.3033)] {s : Finset.{u1} α} {u : α} {v : α} {a : α}, (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a (UV.compression.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b) (fun (a : α) (b : α) => _inst_3 a b) u v s)) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α (GeneralizedCoheytingAlgebra.toLattice.{u1} α (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} α _inst_1)))))) v a) -> ((Eq.{succ u1} α v (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toBot.{u1} α _inst_1))) -> (Eq.{succ u1} α u (Bot.bot.{u1} α (GeneralizedBooleanAlgebra.toBot.{u1} α _inst_1)))) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)
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
    rwa [← h, hvu hva, hva, sup_bot_eq, sdiff_bot]
  · rwa [← h]
#align uv.mem_of_mem_compression UV.mem_of_mem_compression

end GeneralizedBooleanAlgebra

/-! ### UV-compression on finsets -/


open FinsetFamily

variable [DecidableEq α] {𝒜 : Finset (Finset α)} {u v a : Finset α}

/- warning: uv.card_compress -> UV.card_compress is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {u : Finset.{u1} α} {v : Finset.{u1} α}, (Eq.{1} Nat (Finset.card.{u1} α u) (Finset.card.{u1} α v)) -> (forall (A : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (UV.compress.{u1} (Finset.{u1} α) (Finset.generalizedBooleanAlgebra.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableDisjoint.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableDforallFinset.{u1} α a (fun (a_1 : α) (ᾰ : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 b) (fun (a_1 : α) (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 a) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 b)) u v A)) (Finset.card.{u1} α A))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {u : Finset.{u1} α} {v : Finset.{u1} α}, (Eq.{1} Nat (Finset.card.{u1} α u) (Finset.card.{u1} α v)) -> (forall (A : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} α (UV.compress.{u1} (Finset.{u1} α) (Finset.instGeneralizedBooleanAlgebraFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableDisjoint.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a b) (fun (a : Finset.{u1} α) (b : Finset.{u1} α) => Finset.decidableDforallFinset.{u1} α a (fun (a_1 : α) (ᾰ : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 a) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 b) (fun (a_1 : α) (h : Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a_1 a) => Finset.decidableMem.{u1} α (fun (a : α) (b : α) => _inst_1 a b) a_1 b)) u v A)) (Finset.card.{u1} α A))
Case conversion may be inaccurate. Consider using '#align uv.card_compress UV.card_compressₓ'. -/
/-- Compressing a finset doesn't change its size. -/
theorem card_compress (hUV : u.card = v.card) (A : Finset α) : (compress u v A).card = A.card :=
  by
  unfold compress
  split_ifs
  ·
    rw [card_sdiff (h.2.trans le_sup_left), sup_eq_union, card_disjoint_union h.1.symm, hUV,
      add_tsub_cancel_right]
  · rfl
#align uv.card_compress UV.card_compress

private theorem aux (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.eraseₓ x) (v.eraseₓ y) 𝒜) :
    v = ∅ → u = ∅ := by rintro rfl; refine' eq_empty_of_forall_not_mem fun a ha => _;
  obtain ⟨_, ⟨⟩, -⟩ := huv a ha

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (y «expr ∉ » s) -/
/-- UV-compression reduces the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v` such
that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key fact about compression for
Kruskal-Katona. -/
theorem shadow_compression_subset_compression_shadow (u v : Finset α)
    (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.eraseₓ x) (v.eraseₓ y) 𝒜) :
    (∂ ) (𝓒 u v 𝒜) ⊆ 𝓒 u v ((∂ ) 𝒜) := by
  set 𝒜' := 𝓒 u v 𝒜
  suffices H :
    ∀ s,
      s ∈ (∂ ) 𝒜' → s ∉ (∂ ) 𝒜 → u ⊆ s ∧ Disjoint v s ∧ (s ∪ v) \ u ∈ (∂ ) 𝒜 ∧ (s ∪ v) \ u ∉ (∂ ) 𝒜'
  · rintro s hs'
    rw [mem_compression]
    by_cases hs : s ∈ 𝒜.shadow; swap
    · obtain ⟨hus, hvs, h, _⟩ := H _ hs' hs
      exact Or.inr ⟨hs, _, h, compress_of_disjoint_of_le' hvs hus⟩
    refine' Or.inl ⟨hs, _⟩
    rw [compress]
    split_ifs with huvs; swap
    · exact hs
    rw [mem_shadow_iff] at hs'
    obtain ⟨t, Ht, a, hat, rfl⟩ := hs'
    have hav : a ∉ v := not_mem_mono huvs.2 (not_mem_erase a t)
    have hvt : v ≤ t := huvs.2.trans (erase_subset _ t)
    have ht : t ∈ 𝒜 := mem_of_mem_compression Ht hvt (aux huv)
    by_cases hau : a ∈ u
    · obtain ⟨b, hbv, Hcomp⟩ := huv a hau
      refine' mem_shadow_iff_insert_mem.2 ⟨b, not_mem_sdiff_of_mem_right hbv, _⟩
      rw [← Hcomp.eq] at ht
      have hsb :=
        sup_sdiff_mem_of_mem_compression ht ((erase_subset _ _).trans hvt)
          (disjoint_erase_comm.2 huvs.1)
      rwa [sup_eq_union, sdiff_erase (mem_union_left _ <| hvt hbv), union_erase_of_mem hat, ←
        erase_union_of_mem hau] at hsb
    · refine'
        mem_shadow_iff.2
          ⟨(t ⊔ u) \ v,
            sup_sdiff_mem_of_mem_compression Ht hvt <| disjoint_of_erase_right hau huvs.1, a, _, _⟩
      · rw [sup_eq_union, mem_sdiff, mem_union]
        exact ⟨Or.inl hat, hav⟩
      · rw [← erase_sdiff_comm, sup_eq_union, erase_union_distrib, erase_eq_of_not_mem hau]
  intro s hs𝒜' hs𝒜
  -- This is gonna be useful a couple of times so let's name it.
  have m : ∀ (y) (_ : y ∉ s), insert y s ∉ 𝒜 := fun y h a =>
    hs𝒜 (mem_shadow_iff_insert_mem.2 ⟨y, h, a⟩)
  obtain ⟨x, _, _⟩ := mem_shadow_iff_insert_mem.1 hs𝒜'
  have hus : u ⊆ insert x s := le_of_mem_compression_of_not_mem ‹_ ∈ 𝒜'› (m _ ‹x ∉ s›)
  have hvs : Disjoint v (insert x s) := disjoint_of_mem_compression_of_not_mem ‹_› (m _ ‹x ∉ s›)
  have : (insert x s ∪ v) \ u ∈ 𝒜 := sup_sdiff_mem_of_mem_compression_of_not_mem ‹_› (m _ ‹x ∉ s›)
  have hsv : Disjoint s v := hvs.symm.mono_left (subset_insert _ _)
  have hvu : Disjoint v u := disjoint_of_subset_right hus hvs
  have hxv : x ∉ v := disjoint_right.1 hvs (mem_insert_self _ _)
  have : v \ u = v := ‹Disjoint v u›.sdiff_eq_left
  -- The first key part is that `x ∉ u`
  have : x ∉ u := by
    intro hxu
    obtain ⟨y, hyv, hxy⟩ := huv x hxu
    -- If `x ∈ u`, we can get `y ∈ v` so that `𝒜` is `(u.erase x, v.erase y)`-compressed
    apply m y (disjoint_right.1 hsv hyv)
    -- and we will use this `y` to contradict `m`, so we would like to show `insert y s ∈ 𝒜`.
    -- We do this by showing the below
    have : ((insert x s ∪ v) \ u ∪ erase u x) \ erase v y ∈ 𝒜 :=
      by
      refine'
        sup_sdiff_mem_of_mem_compression (by rwa [hxy.eq]) _
          (disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff)
      rw [union_sdiff_distrib, ‹v \ u = v›]
      exact (erase_subset _ _).trans (subset_union_right _ _)
    -- and then arguing that it's the same
    convert this
    rw [sdiff_union_erase_cancel (hus.trans <| subset_union_left _ _) ‹x ∈ u›, erase_union_distrib,
      erase_insert ‹x ∉ s›, erase_eq_of_not_mem ‹x ∉ v›, sdiff_erase (mem_union_right _ hyv),
      union_sdiff_cancel_right hsv]
  -- Now that this is done, it's immediate that `u ⊆ s`
  have hus : u ⊆ s := by rwa [← erase_eq_of_not_mem ‹x ∉ u›, ← subset_insert_iff]
  -- and we already had that `v` and `s` are disjoint,
  -- so it only remains to get `(s ∪ v) \ u ∈ ∂ 𝒜 \ ∂ 𝒜'`
  simp_rw [mem_shadow_iff_insert_mem]
  refine' ⟨hus, hsv.symm, ⟨x, _, _⟩, _⟩
  -- `(s ∪ v) \ u ∈ ∂ 𝒜` is pretty direct:
  · exact not_mem_sdiff_of_not_mem_left (not_mem_union.2 ⟨‹x ∉ s›, ‹x ∉ v›⟩)
  · rwa [← insert_sdiff_of_not_mem _ ‹x ∉ u›, ← insert_union]
  -- For (s ∪ v) \ u ∉ ∂ 𝒜', we split up based on w ∈ u
  rintro ⟨w, hwB, hw𝒜'⟩
  have : v ⊆ insert w ((s ∪ v) \ u) :=
    (subset_sdiff.2 ⟨subset_union_right _ _, hvu⟩).trans (subset_insert _ _)
  by_cases hwu : w ∈ u
  -- If `w ∈ u`, we find `z ∈ v`, and contradict `m` again
  · obtain ⟨z, hz, hxy⟩ := huv w hwu
    apply m z (disjoint_right.1 hsv hz)
    have : insert w ((s ∪ v) \ u) ∈ 𝒜 := mem_of_mem_compression hw𝒜' ‹_› (aux huv)
    have : (insert w ((s ∪ v) \ u) ∪ erase u w) \ erase v z ∈ 𝒜 :=
      by
      refine' sup_sdiff_mem_of_mem_compression (by rwa [hxy.eq]) ((erase_subset _ _).trans ‹_›) _
      rw [← sdiff_erase (mem_union_left _ <| hus hwu)]
      exact disjoint_sdiff
    convert this
    rw [insert_union_comm, insert_erase ‹w ∈ u›,
      sdiff_union_of_subset (hus.trans <| subset_union_left _ _),
      sdiff_erase (mem_union_right _ ‹z ∈ v›), union_sdiff_cancel_right hsv]
  -- If `w ∉ u`, we contradict `m` again
  rw [mem_sdiff, ← not_imp, Classical.not_not] at hwB
  apply m w (hwu ∘ hwB ∘ mem_union_left _)
  have : (insert w ((s ∪ v) \ u) ∪ u) \ v ∈ 𝒜 :=
    sup_sdiff_mem_of_mem_compression ‹insert w ((s ∪ v) \ u) ∈ 𝒜'› ‹_›
      (disjoint_insert_right.2 ⟨‹_›, disjoint_sdiff⟩)
  convert this
  rw [insert_union, sdiff_union_of_subset (hus.trans <| subset_union_left _ _),
    insert_sdiff_of_not_mem _ (hwu ∘ hwB ∘ mem_union_right _), union_sdiff_cancel_right hsv]
#align uv.shadow_compression_subset_compression_shadow Uv.shadow_compression_subset_compression_shadow

/-- UV-compression reduces the size of the shadow of `𝒜` if, for all `x ∈ u` there is `y ∈ v`
such that `𝒜` is `(u.erase x, v.erase y)`-compressed. This is the key UV-compression fact needed for
Kruskal-Katona. -/
theorem card_shadow_compression_le (u v : Finset α)
    (huv : ∀ x ∈ u, ∃ y ∈ v, IsCompressed (u.eraseₓ x) (v.eraseₓ y) 𝒜) :
    ((∂ ) (𝓒 u v 𝒜)).card ≤ ((∂ ) 𝒜).card :=
  (card_le_of_subset <| shadow_compression_subset_compression_shadow _ _ huv).trans
    (card_compression _ _ _).le
#align uv.card_shadow_compression_le Uv.card_shadow_compression_le

end Uv

