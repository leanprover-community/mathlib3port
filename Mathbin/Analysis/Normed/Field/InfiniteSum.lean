/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module analysis.normed.field.infinite_sum
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Field.Basic
import Mathbin.Analysis.Normed.Group.InfiniteSum

/-! # Multiplying two infinite sums in a normed ring

In this file, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `topology/algebra/infinite_sum` (e.g `tsum_mul_tsum`),
but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `β` and `γ`, and then we specialize to
`β = γ = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).
!-/


variable {α : Type _} {ι : Type _} {ι' : Type _} [NormedRing α]

open BigOperators Classical

open Finset

/-! ### Arbitrary index types -/


/- warning: summable.mul_of_nonneg -> Summable.mul_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {ι' : Type.{u2}} {f : ι -> Real} {g : ι' -> Real}, (Summable.{0, u1} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Summable.{0, u2} Real ι' Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (LE.le.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.hasLe)) (OfNat.ofNat.{u1} (ι -> Real) 0 (OfNat.mk.{u1} (ι -> Real) 0 (Zero.zero.{u1} (ι -> Real) (Pi.instZero.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.hasZero))))) f) -> (LE.le.{u2} (ι' -> Real) (Pi.hasLe.{u2, 0} ι' (fun (ᾰ : ι') => Real) (fun (i : ι') => Real.hasLe)) (OfNat.ofNat.{u2} (ι' -> Real) 0 (OfNat.mk.{u2} (ι' -> Real) 0 (Zero.zero.{u2} (ι' -> Real) (Pi.instZero.{u2, 0} ι' (fun (ᾰ : ι') => Real) (fun (i : ι') => Real.hasZero))))) g) -> (Summable.{0, max u1 u2} Real (Prod.{u1, u2} ι ι') Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Prod.{u1, u2} ι ι') => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (f (Prod.fst.{u1, u2} ι ι' x)) (g (Prod.snd.{u1, u2} ι ι' x))))
but is expected to have type
  forall {ι : Type.{u2}} {ι' : Type.{u1}} {f : ι -> Real} {g : ι' -> Real}, (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (Summable.{0, u1} Real ι' Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) g) -> (LE.le.{u2} (ι -> Real) (Pi.hasLe.{u2, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.instLEReal)) (OfNat.ofNat.{u2} (ι -> Real) 0 (Zero.toOfNat0.{u2} (ι -> Real) (Pi.instZero.{u2, 0} ι (fun (a._@.Mathlib.Analysis.Normed.Field.InfiniteSum._hyg.27 : ι) => Real) (fun (i : ι) => Real.instZeroReal)))) f) -> (LE.le.{u1} (ι' -> Real) (Pi.hasLe.{u1, 0} ι' (fun (ᾰ : ι') => Real) (fun (i : ι') => Real.instLEReal)) (OfNat.ofNat.{u1} (ι' -> Real) 0 (Zero.toOfNat0.{u1} (ι' -> Real) (Pi.instZero.{u1, 0} ι' (fun (a._@.Mathlib.Analysis.Normed.Field.InfiniteSum._hyg.32 : ι') => Real) (fun (i : ι') => Real.instZeroReal)))) g) -> (Summable.{0, max u2 u1} Real (Prod.{u2, u1} ι ι') Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Prod.{u2, u1} ι ι') => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (f (Prod.fst.{u2, u1} ι ι' x)) (g (Prod.snd.{u2, u1} ι ι' x))))
Case conversion may be inaccurate. Consider using '#align summable.mul_of_nonneg Summable.mul_of_nonnegₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Summable.mul_of_nonneg {f : ι → ℝ} {g : ι' → ℝ} (hf : Summable f) (hg : Summable g)
    (hf' : 0 ≤ f) (hg' : 0 ≤ g) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  let ⟨s, hf⟩ := hf
  let ⟨t, hg⟩ := hg
  suffices this : ∀ u : Finset (ι × ι'), (∑ x in u, f x.1 * g x.2) ≤ s * t from
    summable_of_sum_le (fun x => mul_nonneg (hf' _) (hg' _)) this
  fun u =>
  calc
    (∑ x in u, f x.1 * g x.2) ≤ ∑ x in u.image Prod.fst ×ˢ u.image Prod.snd, f x.1 * g x.2 :=
      sum_mono_set_of_nonneg (fun x => mul_nonneg (hf' _) (hg' _)) subset_product
    _ = ∑ x in u.image Prod.fst, ∑ y in u.image Prod.snd, f x * g y := sum_product
    _ = ∑ x in u.image Prod.fst, f x * ∑ y in u.image Prod.snd, g y :=
      (sum_congr rfl fun x _ => mul_sum.symm)
    _ ≤ ∑ x in u.image Prod.fst, f x * t :=
      (sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left (sum_le_hasSum _ (fun _ _ => hg' _) hg) (hf' _))
    _ = (∑ x in u.image Prod.fst, f x) * t := sum_mul.symm
    _ ≤ s * t :=
      mul_le_mul_of_nonneg_right (sum_le_hasSum _ (fun _ _ => hf' _) hf) (hg.NonNeg fun _ => hg' _)
    
#align summable.mul_of_nonneg Summable.mul_of_nonneg

/- warning: summable.mul_norm -> Summable.mul_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : NormedRing.{u1} α] {f : ι -> α} {g : ι' -> α}, (Summable.{0, u2} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, u3} Real ι' Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι') => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (g x))) -> (Summable.{0, max u2 u3} Real (Prod.{u2, u3} ι ι') Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Prod.{u2, u3} ι ι') => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' x)) (g (Prod.snd.{u2, u3} ι ι' x)))))
but is expected to have type
  forall {α : Type.{u2}} {ι : Type.{u3}} {ι' : Type.{u1}} [_inst_1 : NormedRing.{u2} α] {f : ι -> α} {g : ι' -> α}, (Summable.{0, u3} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι) => Norm.norm.{u2} α (NormedRing.toNorm.{u2} α _inst_1) (f x))) -> (Summable.{0, u1} Real ι' Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι') => Norm.norm.{u2} α (NormedRing.toNorm.{u2} α _inst_1) (g x))) -> (Summable.{0, max u3 u1} Real (Prod.{u3, u1} ι ι') Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Prod.{u3, u1} ι ι') => Norm.norm.{u2} α (NormedRing.toNorm.{u2} α _inst_1) (HMul.hMul.{u2, u2, u2} α α α (instHMul.{u2} α (NonUnitalNonAssocRing.toMul.{u2} α (NonAssocRing.toNonUnitalNonAssocRing.{u2} α (Ring.toNonAssocRing.{u2} α (NormedRing.toRing.{u2} α _inst_1))))) (f (Prod.fst.{u3, u1} ι ι' x)) (g (Prod.snd.{u3, u1} ι ι' x)))))
Case conversion may be inaccurate. Consider using '#align summable.mul_norm Summable.mul_normₓ'. -/
theorem Summable.mul_norm {f : ι → α} {g : ι' → α} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun x : ι × ι' => ‖f x.1 * g x.2‖ :=
  summable_of_nonneg_of_le (fun x => norm_nonneg (f x.1 * g x.2))
    (fun x => norm_mul_le (f x.1) (g x.2))
    (hf.mul_of_nonneg hg (fun x => norm_nonneg <| f x) fun x => norm_nonneg <| g x : _)
#align summable.mul_norm Summable.mul_norm

/- warning: summable_mul_of_summable_norm -> summable_mul_of_summable_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))] {f : ι -> α} {g : ι' -> α}, (Summable.{0, u2} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, u3} Real ι' Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι') => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (g x))) -> (Summable.{u1, max u2 u3} α (Prod.{u2, u3} ι ι') (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) (fun (x : Prod.{u2, u3} ι ι') => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' x)) (g (Prod.snd.{u2, u3} ι ι' x))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {ι' : Type.{u1}} [_inst_1 : NormedRing.{u3} α] [_inst_2 : CompleteSpace.{u3} α (PseudoMetricSpace.toUniformSpace.{u3} α (SeminormedRing.toPseudoMetricSpace.{u3} α (NormedRing.toSeminormedRing.{u3} α _inst_1)))] {f : ι -> α} {g : ι' -> α}, (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι) => Norm.norm.{u3} α (NormedRing.toNorm.{u3} α _inst_1) (f x))) -> (Summable.{0, u1} Real ι' Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι') => Norm.norm.{u3} α (NormedRing.toNorm.{u3} α _inst_1) (g x))) -> (Summable.{u3, max u2 u1} α (Prod.{u2, u1} ι ι') (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α (NonAssocRing.toNonUnitalNonAssocRing.{u3} α (Ring.toNonAssocRing.{u3} α (NormedRing.toRing.{u3} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u3} α (PseudoMetricSpace.toUniformSpace.{u3} α (SeminormedRing.toPseudoMetricSpace.{u3} α (NormedRing.toSeminormedRing.{u3} α _inst_1)))) (fun (x : Prod.{u2, u1} ι ι') => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocRing.toMul.{u3} α (NonAssocRing.toNonUnitalNonAssocRing.{u3} α (Ring.toNonAssocRing.{u3} α (NormedRing.toRing.{u3} α _inst_1))))) (f (Prod.fst.{u2, u1} ι ι' x)) (g (Prod.snd.{u2, u1} ι ι' x))))
Case conversion may be inaccurate. Consider using '#align summable_mul_of_summable_norm summable_mul_of_summable_normₓ'. -/
theorem summable_mul_of_summable_norm [CompleteSpace α] {f : ι → α} {g : ι' → α}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun x : ι × ι' => f x.1 * g x.2 :=
  summable_of_summable_norm (hf.mul_norm hg)
#align summable_mul_of_summable_norm summable_mul_of_summable_norm

/- warning: tsum_mul_tsum_of_summable_norm -> tsum_mul_tsum_of_summable_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Type.{u2}} {ι' : Type.{u3}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))] {f : ι -> α} {g : ι' -> α}, (Summable.{0, u2} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, u3} Real ι' Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι') => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (g x))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (tsum.{u1, u2} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) ι (fun (x : ι) => f x)) (tsum.{u1, u3} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) ι' (fun (y : ι') => g y))) (tsum.{u1, max u2 u3} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) (Prod.{u2, u3} ι ι') (fun (z : Prod.{u2, u3} ι ι') => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (f (Prod.fst.{u2, u3} ι ι' z)) (g (Prod.snd.{u2, u3} ι ι' z)))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Type.{u2}} {ι' : Type.{u1}} [_inst_1 : NormedRing.{u3} α] [_inst_2 : CompleteSpace.{u3} α (PseudoMetricSpace.toUniformSpace.{u3} α (SeminormedRing.toPseudoMetricSpace.{u3} α (NormedRing.toSeminormedRing.{u3} α _inst_1)))] {f : ι -> α} {g : ι' -> α}, (Summable.{0, u2} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι) => Norm.norm.{u3} α (NormedRing.toNorm.{u3} α _inst_1) (f x))) -> (Summable.{0, u1} Real ι' Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : ι') => Norm.norm.{u3} α (NormedRing.toNorm.{u3} α _inst_1) (g x))) -> (Eq.{succ u3} α (HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocRing.toMul.{u3} α (NonAssocRing.toNonUnitalNonAssocRing.{u3} α (Ring.toNonAssocRing.{u3} α (NormedRing.toRing.{u3} α _inst_1))))) (tsum.{u3, u2} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α (NonAssocRing.toNonUnitalNonAssocRing.{u3} α (Ring.toNonAssocRing.{u3} α (NormedRing.toRing.{u3} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u3} α (PseudoMetricSpace.toUniformSpace.{u3} α (SeminormedRing.toPseudoMetricSpace.{u3} α (NormedRing.toSeminormedRing.{u3} α _inst_1)))) ι (fun (x : ι) => f x)) (tsum.{u3, u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α (NonAssocRing.toNonUnitalNonAssocRing.{u3} α (Ring.toNonAssocRing.{u3} α (NormedRing.toRing.{u3} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u3} α (PseudoMetricSpace.toUniformSpace.{u3} α (SeminormedRing.toPseudoMetricSpace.{u3} α (NormedRing.toSeminormedRing.{u3} α _inst_1)))) ι' (fun (y : ι') => g y))) (tsum.{u3, max u2 u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} α (NonAssocRing.toNonUnitalNonAssocRing.{u3} α (Ring.toNonAssocRing.{u3} α (NormedRing.toRing.{u3} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u3} α (PseudoMetricSpace.toUniformSpace.{u3} α (SeminormedRing.toPseudoMetricSpace.{u3} α (NormedRing.toSeminormedRing.{u3} α _inst_1)))) (Prod.{u2, u1} ι ι') (fun (z : Prod.{u2, u1} ι ι') => HMul.hMul.{u3, u3, u3} α α α (instHMul.{u3} α (NonUnitalNonAssocRing.toMul.{u3} α (NonAssocRing.toNonUnitalNonAssocRing.{u3} α (Ring.toNonAssocRing.{u3} α (NormedRing.toRing.{u3} α _inst_1))))) (f (Prod.fst.{u2, u1} ι ι' z)) (g (Prod.snd.{u2, u1} ι ι' z)))))
Case conversion may be inaccurate. Consider using '#align tsum_mul_tsum_of_summable_norm tsum_mul_tsum_of_summable_normₓ'. -/
/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/
theorem tsum_mul_tsum_of_summable_norm [CompleteSpace α] {f : ι → α} {g : ι' → α}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × ι', f z.1 * g z.2 :=
  tsum_mul_tsum (summable_of_summable_norm hf) (summable_of_summable_norm hg)
    (summable_mul_of_summable_norm hf hg)
#align tsum_mul_tsum_of_summable_norm tsum_mul_tsum_of_summable_norm

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`finset.range (n+1)` involving `nat` subtraction.
In order to avoid `nat` subtraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n`. -/


section Nat

open Finset.Nat

#print summable_norm_sum_mul_antidiagonal_of_summable_norm /-
theorem summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : ℕ → α}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    Summable fun n => ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ :=
  by
  have :=
    summable_sum_mul_antidiagonal_of_summable_mul
      (Summable.mul_of_nonneg hf hg (fun _ => norm_nonneg _) fun _ => norm_nonneg _)
  refine' summable_of_nonneg_of_le (fun _ => norm_nonneg _) _ this
  intro n
  calc
    ‖∑ kl in antidiagonal n, f kl.1 * g kl.2‖ ≤ ∑ kl in antidiagonal n, ‖f kl.1 * g kl.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ kl in antidiagonal n, ‖f kl.1‖ * ‖g kl.2‖ := sum_le_sum fun i _ => norm_mul_le _ _
    
#align summable_norm_sum_mul_antidiagonal_of_summable_norm summable_norm_sum_mul_antidiagonal_of_summable_norm
-/

/- warning: tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm -> tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))] {f : Nat -> α} {g : Nat -> α}, (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (g x))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => f n)) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => g n))) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => Finset.sum.{u1, 0} α (Prod.{0, 0} Nat Nat) (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (Finset.Nat.antidiagonal n) (fun (kl : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (f (Prod.fst.{0, 0} Nat Nat kl)) (g (Prod.snd.{0, 0} Nat Nat kl))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))] {f : Nat -> α} {g : Nat -> α}, (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toNorm.{u1} α _inst_1) (g x))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => f n)) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => g n))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => Finset.sum.{u1, 0} α (Prod.{0, 0} Nat Nat) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (Finset.Nat.antidiagonal n) (fun (kl : Prod.{0, 0} Nat Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (f (Prod.fst.{0, 0} Nat Nat kl)) (g (Prod.snd.{0, 0} Nat Nat kl))))))
Case conversion may be inaccurate. Consider using '#align tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_normₓ'. -/
/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `finset.nat.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [CompleteSpace α] {f g : ℕ → α}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
  tsum_mul_tsum_eq_tsum_sum_antidiagonal (summable_of_summable_norm hf)
    (summable_of_summable_norm hg) (summable_mul_of_summable_norm hf hg)
#align tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm

/- warning: summable_norm_sum_mul_range_of_summable_norm -> summable_norm_sum_mul_range_of_summable_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] {f : Nat -> α} {g : Nat -> α}, (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (g x))) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (f k) (g (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] {f : Nat -> α} {g : Nat -> α}, (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toNorm.{u1} α _inst_1) (g x))) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (n : Nat) => Norm.norm.{u1} α (NormedRing.toNorm.{u1} α _inst_1) (Finset.sum.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (f k) (g (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k))))))
Case conversion may be inaccurate. Consider using '#align summable_norm_sum_mul_range_of_summable_norm summable_norm_sum_mul_range_of_summable_normₓ'. -/
theorem summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → α} (hf : Summable fun x => ‖f x‖)
    (hg : Summable fun x => ‖g x‖) : Summable fun n => ‖∑ k in range (n + 1), f k * g (n - k)‖ :=
  by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
#align summable_norm_sum_mul_range_of_summable_norm summable_norm_sum_mul_range_of_summable_norm

/- warning: tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm -> tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))] {f : Nat -> α} {g : Nat -> α}, (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, 0} Real Nat Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toHasNorm.{u1} α _inst_1) (g x))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => f n)) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => g n))) (tsum.{u1, 0} α (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (AddCommGroup.toAddCommMonoid.{u1} α (NormedAddCommGroup.toAddCommGroup.{u1} α (NonUnitalNormedRing.toNormedAddCommGroup.{u1} α (NormedRing.toNonUnitalNormedRing.{u1} α _inst_1)))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (k : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (Ring.toDistrib.{u1} α (NormedRing.toRing.{u1} α _inst_1)))) (f k) (g (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat Nat.hasSub) n k))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NormedRing.{u1} α] [_inst_2 : CompleteSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))] {f : Nat -> α} {g : Nat -> α}, (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toNorm.{u1} α _inst_1) (f x))) -> (Summable.{0, 0} Real Nat Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Nat) => Norm.norm.{u1} α (NormedRing.toNorm.{u1} α _inst_1) (g x))) -> (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => f n)) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => g n))) (tsum.{u1, 0} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (UniformSpace.toTopologicalSpace.{u1} α (PseudoMetricSpace.toUniformSpace.{u1} α (SeminormedRing.toPseudoMetricSpace.{u1} α (NormedRing.toSeminormedRing.{u1} α _inst_1)))) Nat (fun (n : Nat) => Finset.sum.{u1, 0} α Nat (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (k : Nat) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (NormedRing.toRing.{u1} α _inst_1))))) (f k) (g (HSub.hSub.{0, 0, 0} Nat Nat Nat (instHSub.{0} Nat instSubNat) n k))))))
Case conversion may be inaccurate. Consider using '#align tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm tsum_mul_tsum_eq_tsum_sum_range_of_summable_normₓ'. -/
/-- The Cauchy product formula for the product of two infinite sums indexed by `ℕ`,
    expressed by summing on `finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
    *not* absolutely summable. -/
theorem tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [CompleteSpace α] {f g : ℕ → α}
    (hf : Summable fun x => ‖f x‖) (hg : Summable fun x => ‖g x‖) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) :=
  by
  simp_rw [← sum_antidiagonal_eq_sum_range_succ fun k l => f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
#align tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm

end Nat

