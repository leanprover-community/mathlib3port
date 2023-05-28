/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.algebra.module.multilinear
! leanprover-community/mathlib commit f2b757fc5c341d88741b9c4630b1e8ba973c5726
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Module.Basic
import Mathbin.LinearAlgebra.Multilinear.Basic

/-!
# Continuous multilinear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define continuous multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are multilinear
and continuous, by extending the space of multilinear maps with a continuity assumption.
Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type, and all these
spaces are also topological spaces.

## Main definitions

* `continuous_multilinear_map R M₁ M₂` is the space of continuous multilinear maps from
  `Π(i : ι), M₁ i` to `M₂`. We show that it is an `R`-module.

## Implementation notes

We mostly follow the API of multilinear maps.

## Notation

We introduce the notation `M [×n]→L[R] M'` for the space of continuous `n`-multilinear maps from
`M^n` to `M'`. This is a particular case of the general notion (where we allow varying dependent
types as the arguments of our continuous multilinear maps), but arguably the most important one,
especially when defining iterated derivatives.
-/


open Function Fin Set

open BigOperators

universe u v w w₁ w₁' w₂ w₃ w₄

variable {R : Type u} {ι : Type v} {n : ℕ} {M : Fin n.succ → Type w} {M₁ : ι → Type w₁}
  {M₁' : ι → Type w₁'} {M₂ : Type w₂} {M₃ : Type w₃} {M₄ : Type w₄}

#print ContinuousMultilinearMap /-
/-- Continuous multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂`
are modules over `R` with a topological structure. In applications, there will be compatibility
conditions between the algebraic and the topological structures, but this is not needed for the
definition. -/
structure ContinuousMultilinearMap (R : Type u) {ι : Type v} (M₁ : ι → Type w₁) (M₂ : Type w₂)
  [Semiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] extends MultilinearMap R M₁ M₂ where
  cont : Continuous to_fun
#align continuous_multilinear_map ContinuousMultilinearMap
-/

-- mathport name: «expr [× ]→L[ ] »
notation:25 M "[×" n "]→L[" R "] " M' => ContinuousMultilinearMap R (fun i : Fin n => M) M'

namespace ContinuousMultilinearMap

section Semiring

variable [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M₁ i)]
  [∀ i, AddCommMonoid (M₁' i)] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
  [∀ i, Module R (M i)] [∀ i, Module R (M₁ i)] [∀ i, Module R (M₁' i)] [Module R M₂] [Module R M₃]
  [Module R M₄] [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (M₁ i)]
  [∀ i, TopologicalSpace (M₁' i)] [TopologicalSpace M₂] [TopologicalSpace M₃] [TopologicalSpace M₄]
  (f f' : ContinuousMultilinearMap R M₁ M₂)

#print ContinuousMultilinearMap.toMultilinearMap_injective /-
theorem toMultilinearMap_injective :
    Function.Injective
      (ContinuousMultilinearMap.toMultilinearMap :
        ContinuousMultilinearMap R M₁ M₂ → MultilinearMap R M₁ M₂)
  | ⟨f, hf⟩, ⟨g, hg⟩, rfl => rfl
#align continuous_multilinear_map.to_multilinear_map_injective ContinuousMultilinearMap.toMultilinearMap_injective
-/

#print ContinuousMultilinearMap.continuousMapClass /-
instance continuousMapClass : ContinuousMapClass (ContinuousMultilinearMap R M₁ M₂) (∀ i, M₁ i) M₂
    where
  coe f := f.toFun
  coe_injective' f g h := toMultilinearMap_injective <| MultilinearMap.coe_injective h
  map_continuous := ContinuousMultilinearMap.cont
#align continuous_multilinear_map.continuous_map_class ContinuousMultilinearMap.continuousMapClass
-/

instance : CoeFun (ContinuousMultilinearMap R M₁ M₂) fun _ => (∀ i, M₁ i) → M₂ :=
  ⟨fun f => f⟩

#print ContinuousMultilinearMap.Simps.apply /-
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (L₁ : ContinuousMultilinearMap R M₁ M₂) (v : ∀ i, M₁ i) : M₂ :=
  L₁ v
#align continuous_multilinear_map.simps.apply ContinuousMultilinearMap.Simps.apply
-/

initialize_simps_projections ContinuousMultilinearMap (-toMultilinearMap,
  to_multilinear_map_to_fun → apply)

#print ContinuousMultilinearMap.coe_continuous /-
@[continuity]
theorem coe_continuous : Continuous (f : (∀ i, M₁ i) → M₂) :=
  f.cont
#align continuous_multilinear_map.coe_continuous ContinuousMultilinearMap.coe_continuous
-/

#print ContinuousMultilinearMap.coe_coe /-
@[simp]
theorem coe_coe : (f.toMultilinearMap : (∀ i, M₁ i) → M₂) = f :=
  rfl
#align continuous_multilinear_map.coe_coe ContinuousMultilinearMap.coe_coe
-/

#print ContinuousMultilinearMap.ext /-
@[ext]
theorem ext {f f' : ContinuousMultilinearMap R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
  FunLike.ext _ _ H
#align continuous_multilinear_map.ext ContinuousMultilinearMap.ext
-/

#print ContinuousMultilinearMap.ext_iff /-
theorem ext_iff {f f' : ContinuousMultilinearMap R M₁ M₂} : f = f' ↔ ∀ x, f x = f' x := by
  rw [← to_multilinear_map_injective.eq_iff, MultilinearMap.ext_iff] <;> rfl
#align continuous_multilinear_map.ext_iff ContinuousMultilinearMap.ext_iff
-/

/- warning: continuous_multilinear_map.map_add -> ContinuousMultilinearMap.map_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.map_add ContinuousMultilinearMap.map_addₓ'. -/
@[simp]
theorem map_add [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
  f.map_add' m i x y
#align continuous_multilinear_map.map_add ContinuousMultilinearMap.map_add

#print ContinuousMultilinearMap.map_smul /-
@[simp]
theorem map_smul [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (c : R) (x : M₁ i) :
    f (update m i (c • x)) = c • f (update m i x) :=
  f.map_smul' m i c x
#align continuous_multilinear_map.map_smul ContinuousMultilinearMap.map_smul
-/

/- warning: continuous_multilinear_map.map_coord_zero -> ContinuousMultilinearMap.map_coord_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.map_coord_zero ContinuousMultilinearMap.map_coord_zeroₓ'. -/
theorem map_coord_zero {m : ∀ i, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
  f.toMultilinearMap.map_coord_zero i h
#align continuous_multilinear_map.map_coord_zero ContinuousMultilinearMap.map_coord_zero

/- warning: continuous_multilinear_map.map_zero -> ContinuousMultilinearMap.map_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.map_zero ContinuousMultilinearMap.map_zeroₓ'. -/
@[simp]
theorem map_zero [Nonempty ι] : f 0 = 0 :=
  f.toMultilinearMap.map_zero
#align continuous_multilinear_map.map_zero ContinuousMultilinearMap.map_zero

instance : Zero (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨{ (0 : MultilinearMap R M₁ M₂) with cont := continuous_const }⟩

instance : Inhabited (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨0⟩

/- warning: continuous_multilinear_map.zero_apply -> ContinuousMultilinearMap.zero_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.zero_apply ContinuousMultilinearMap.zero_applyₓ'. -/
@[simp]
theorem zero_apply (m : ∀ i, M₁ i) : (0 : ContinuousMultilinearMap R M₁ M₂) m = 0 :=
  rfl
#align continuous_multilinear_map.zero_apply ContinuousMultilinearMap.zero_apply

/- warning: continuous_multilinear_map.to_multilinear_map_zero -> ContinuousMultilinearMap.toMultilinearMap_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} {M₁ : ι -> Type.{u3}} {M₂ : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_3 : forall (i : ι), AddCommMonoid.{u3} (M₁ i)] [_inst_5 : AddCommMonoid.{u4} M₂] [_inst_9 : forall (i : ι), Module.{u1, u3} R (M₁ i) _inst_1 (_inst_3 i)] [_inst_11 : Module.{u1, u4} R M₂ _inst_1 _inst_5] [_inst_15 : forall (i : ι), TopologicalSpace.{u3} (M₁ i)] [_inst_17 : TopologicalSpace.{u4} M₂], Eq.{max (succ u2) (succ u3) (succ u4)} (MultilinearMap.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11) (ContinuousMultilinearMap.toMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17 (OfNat.ofNat.{max u2 u3 u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) 0 (OfNat.mk.{max u2 u3 u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) 0 (Zero.zero.{max u2 u3 u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) (ContinuousMultilinearMap.hasZero.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17))))) (OfNat.ofNat.{max u2 u3 u4} (MultilinearMap.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11) 0 (OfNat.mk.{max u2 u3 u4} (MultilinearMap.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11) 0 (Zero.zero.{max u2 u3 u4} (MultilinearMap.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11) (MultilinearMap.hasZero.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11))))
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} {M₁ : ι -> Type.{u3}} {M₂ : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_3 : forall (i : ι), AddCommMonoid.{u3} (M₁ i)] [_inst_5 : AddCommMonoid.{u4} M₂] [_inst_9 : forall (i : ι), Module.{u1, u3} R (M₁ i) _inst_1 (_inst_3 i)] [_inst_11 : Module.{u1, u4} R M₂ _inst_1 _inst_5] [_inst_15 : forall (i : ι), TopologicalSpace.{u3} (M₁ i)] [_inst_17 : TopologicalSpace.{u4} M₂], Eq.{max (max (succ u2) (succ u3)) (succ u4)} (MultilinearMap.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11) (ContinuousMultilinearMap.toMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17 (OfNat.ofNat.{max (max u2 u3) u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) 0 (Zero.toOfNat0.{max (max u2 u3) u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) (ContinuousMultilinearMap.instZeroContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17)))) (OfNat.ofNat.{max (max u2 u3) u4} (MultilinearMap.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11) 0 (Zero.toOfNat0.{max (max u2 u3) u4} (MultilinearMap.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11) (MultilinearMap.instZeroMultilinearMap.{u1, u3, u4, u2} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11)))
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.to_multilinear_map_zero ContinuousMultilinearMap.toMultilinearMap_zeroₓ'. -/
@[simp]
theorem toMultilinearMap_zero : (0 : ContinuousMultilinearMap R M₁ M₂).toMultilinearMap = 0 :=
  rfl
#align continuous_multilinear_map.to_multilinear_map_zero ContinuousMultilinearMap.toMultilinearMap_zero

section SMul

variable {R' R'' A : Type _} [Monoid R'] [Monoid R''] [Semiring A] [∀ i, Module A (M₁ i)]
  [Module A M₂] [DistribMulAction R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
  [DistribMulAction R'' M₂] [ContinuousConstSMul R'' M₂] [SMulCommClass A R'' M₂]

instance : SMul R' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c f => { c • f.toMultilinearMap with cont := f.cont.const_smul c }⟩

/- warning: continuous_multilinear_map.smul_apply -> ContinuousMultilinearMap.smul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.smul_apply ContinuousMultilinearMap.smul_applyₓ'. -/
@[simp]
theorem smul_apply (f : ContinuousMultilinearMap A M₁ M₂) (c : R') (m : ∀ i, M₁ i) :
    (c • f) m = c • f m :=
  rfl
#align continuous_multilinear_map.smul_apply ContinuousMultilinearMap.smul_apply

/- warning: continuous_multilinear_map.to_multilinear_map_smul -> ContinuousMultilinearMap.toMultilinearMap_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.to_multilinear_map_smul ContinuousMultilinearMap.toMultilinearMap_smulₓ'. -/
@[simp]
theorem toMultilinearMap_smul (c : R') (f : ContinuousMultilinearMap A M₁ M₂) :
    (c • f).toMultilinearMap = c • f.toMultilinearMap :=
  rfl
#align continuous_multilinear_map.to_multilinear_map_smul ContinuousMultilinearMap.toMultilinearMap_smul

instance [SMulCommClass R' R'' M₂] : SMulCommClass R' R'' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c₁ c₂ f => ext fun x => smul_comm _ _ _⟩

instance [SMul R' R''] [IsScalarTower R' R'' M₂] :
    IsScalarTower R' R'' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c₁ c₂ f => ext fun x => smul_assoc _ _ _⟩

instance [DistribMulAction R'ᵐᵒᵖ M₂] [IsCentralScalar R' M₂] :
    IsCentralScalar R' (ContinuousMultilinearMap A M₁ M₂) :=
  ⟨fun c₁ f => ext fun x => op_smul_eq_smul _ _⟩

instance : MulAction R' (ContinuousMultilinearMap A M₁ M₂) :=
  Function.Injective.mulAction toMultilinearMap toMultilinearMap_injective fun _ _ => rfl

end SMul

section ContinuousAdd

variable [ContinuousAdd M₂]

instance : Add (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f f' => ⟨f.toMultilinearMap + f'.toMultilinearMap, f.cont.add f'.cont⟩⟩

/- warning: continuous_multilinear_map.add_apply -> ContinuousMultilinearMap.add_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.add_apply ContinuousMultilinearMap.add_applyₓ'. -/
@[simp]
theorem add_apply (m : ∀ i, M₁ i) : (f + f') m = f m + f' m :=
  rfl
#align continuous_multilinear_map.add_apply ContinuousMultilinearMap.add_apply

/- warning: continuous_multilinear_map.to_multilinear_map_add -> ContinuousMultilinearMap.toMultilinearMap_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.to_multilinear_map_add ContinuousMultilinearMap.toMultilinearMap_addₓ'. -/
@[simp]
theorem toMultilinearMap_add (f g : ContinuousMultilinearMap R M₁ M₂) :
    (f + g).toMultilinearMap = f.toMultilinearMap + g.toMultilinearMap :=
  rfl
#align continuous_multilinear_map.to_multilinear_map_add ContinuousMultilinearMap.toMultilinearMap_add

/- warning: continuous_multilinear_map.add_comm_monoid -> ContinuousMultilinearMap.addCommMonoid is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} {M₁ : ι -> Type.{u3}} {M₂ : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_3 : forall (i : ι), AddCommMonoid.{u3} (M₁ i)] [_inst_5 : AddCommMonoid.{u4} M₂] [_inst_9 : forall (i : ι), Module.{u1, u3} R (M₁ i) _inst_1 (_inst_3 i)] [_inst_11 : Module.{u1, u4} R M₂ _inst_1 _inst_5] [_inst_15 : forall (i : ι), TopologicalSpace.{u3} (M₁ i)] [_inst_17 : TopologicalSpace.{u4} M₂] [_inst_20 : ContinuousAdd.{u4} M₂ _inst_17 (AddZeroClass.toHasAdd.{u4} M₂ (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_5)))], AddCommMonoid.{max u2 u3 u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17)
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} {M₁ : ι -> Type.{u3}} {M₂ : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_3 : forall (i : ι), AddCommMonoid.{u3} (M₁ i)] [_inst_5 : AddCommMonoid.{u4} M₂] [_inst_9 : forall (i : ι), Module.{u1, u3} R (M₁ i) _inst_1 (_inst_3 i)] [_inst_11 : Module.{u1, u4} R M₂ _inst_1 _inst_5] [_inst_15 : forall (i : ι), TopologicalSpace.{u3} (M₁ i)] [_inst_17 : TopologicalSpace.{u4} M₂] [_inst_20 : ContinuousAdd.{u4} M₂ _inst_17 (AddZeroClass.toAdd.{u4} M₂ (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_5)))], AddCommMonoid.{max (max u4 u3) u2} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17)
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.add_comm_monoid ContinuousMultilinearMap.addCommMonoidₓ'. -/
instance addCommMonoid : AddCommMonoid (ContinuousMultilinearMap R M₁ M₂) :=
  toMultilinearMap_injective.AddCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl
#align continuous_multilinear_map.add_comm_monoid ContinuousMultilinearMap.addCommMonoid

/- warning: continuous_multilinear_map.apply_add_hom -> ContinuousMultilinearMap.applyAddHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} {M₁ : ι -> Type.{u3}} {M₂ : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_3 : forall (i : ι), AddCommMonoid.{u3} (M₁ i)] [_inst_5 : AddCommMonoid.{u4} M₂] [_inst_9 : forall (i : ι), Module.{u1, u3} R (M₁ i) _inst_1 (_inst_3 i)] [_inst_11 : Module.{u1, u4} R M₂ _inst_1 _inst_5] [_inst_15 : forall (i : ι), TopologicalSpace.{u3} (M₁ i)] [_inst_17 : TopologicalSpace.{u4} M₂] [_inst_20 : ContinuousAdd.{u4} M₂ _inst_17 (AddZeroClass.toHasAdd.{u4} M₂ (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_5)))], (forall (i : ι), M₁ i) -> (AddMonoidHom.{max u2 u3 u4, u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) M₂ (AddMonoid.toAddZeroClass.{max u2 u3 u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) (AddCommMonoid.toAddMonoid.{max u2 u3 u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) (ContinuousMultilinearMap.addCommMonoid.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17 _inst_20))) (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_5)))
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} {M₁ : ι -> Type.{u3}} {M₂ : Type.{u4}} [_inst_1 : Semiring.{u1} R] [_inst_3 : forall (i : ι), AddCommMonoid.{u3} (M₁ i)] [_inst_5 : AddCommMonoid.{u4} M₂] [_inst_9 : forall (i : ι), Module.{u1, u3} R (M₁ i) _inst_1 (_inst_3 i)] [_inst_11 : Module.{u1, u4} R M₂ _inst_1 _inst_5] [_inst_15 : forall (i : ι), TopologicalSpace.{u3} (M₁ i)] [_inst_17 : TopologicalSpace.{u4} M₂] [_inst_20 : ContinuousAdd.{u4} M₂ _inst_17 (AddZeroClass.toAdd.{u4} M₂ (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_5)))], (forall (i : ι), M₁ i) -> (AddMonoidHom.{max (max u4 u3) u2, u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) M₂ (AddMonoid.toAddZeroClass.{max (max u2 u3) u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) (AddCommMonoid.toAddMonoid.{max (max u2 u3) u4} (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) (ContinuousMultilinearMap.addCommMonoid.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17 _inst_20))) (AddMonoid.toAddZeroClass.{u4} M₂ (AddCommMonoid.toAddMonoid.{u4} M₂ _inst_5)))
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.apply_add_hom ContinuousMultilinearMap.applyAddHomₓ'. -/
/-- Evaluation of a `continuous_multilinear_map` at a vector as an `add_monoid_hom`. -/
def applyAddHom (m : ∀ i, M₁ i) : ContinuousMultilinearMap R M₁ M₂ →+ M₂ :=
  ⟨fun f => f m, rfl, fun _ _ => rfl⟩
#align continuous_multilinear_map.apply_add_hom ContinuousMultilinearMap.applyAddHom

/- warning: continuous_multilinear_map.sum_apply -> ContinuousMultilinearMap.sum_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.sum_apply ContinuousMultilinearMap.sum_applyₓ'. -/
@[simp]
theorem sum_apply {α : Type _} (f : α → ContinuousMultilinearMap R M₁ M₂) (m : ∀ i, M₁ i)
    {s : Finset α} : (∑ a in s, f a) m = ∑ a in s, f a m :=
  (applyAddHom m).map_sum f s
#align continuous_multilinear_map.sum_apply ContinuousMultilinearMap.sum_apply

end ContinuousAdd

#print ContinuousMultilinearMap.toContinuousLinearMap /-
/-- If `f` is a continuous multilinear map, then `f.to_continuous_linear_map m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
def toContinuousLinearMap [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) : M₁ i →L[R] M₂ :=
  { f.toMultilinearMap.toLinearMap m i with
    cont := f.cont.comp (continuous_const.update i continuous_id) }
#align continuous_multilinear_map.to_continuous_linear_map ContinuousMultilinearMap.toContinuousLinearMap
-/

/- warning: continuous_multilinear_map.prod -> ContinuousMultilinearMap.prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {ι : Type.{u2}} {M₁ : ι -> Type.{u3}} {M₂ : Type.{u4}} {M₃ : Type.{u5}} [_inst_1 : Semiring.{u1} R] [_inst_3 : forall (i : ι), AddCommMonoid.{u3} (M₁ i)] [_inst_5 : AddCommMonoid.{u4} M₂] [_inst_6 : AddCommMonoid.{u5} M₃] [_inst_9 : forall (i : ι), Module.{u1, u3} R (M₁ i) _inst_1 (_inst_3 i)] [_inst_11 : Module.{u1, u4} R M₂ _inst_1 _inst_5] [_inst_12 : Module.{u1, u5} R M₃ _inst_1 _inst_6] [_inst_15 : forall (i : ι), TopologicalSpace.{u3} (M₁ i)] [_inst_17 : TopologicalSpace.{u4} M₂] [_inst_18 : TopologicalSpace.{u5} M₃], (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) -> (ContinuousMultilinearMap.{u1, u2, u3, u5} R ι M₁ M₃ _inst_1 (fun (i : ι) => _inst_3 i) _inst_6 (fun (i : ι) => _inst_9 i) _inst_12 (fun (i : ι) => _inst_15 i) _inst_18) -> (ContinuousMultilinearMap.{u1, u2, u3, max u4 u5} R ι M₁ (Prod.{u4, u5} M₂ M₃) _inst_1 (fun (i : ι) => _inst_3 i) (Prod.addCommMonoid.{u4, u5} M₂ M₃ _inst_5 _inst_6) (fun (i : ι) => _inst_9 i) (Prod.module.{u1, u4, u5} R M₂ M₃ _inst_1 _inst_5 _inst_6 _inst_11 _inst_12) (fun (i : ι) => _inst_15 i) (Prod.topologicalSpace.{u4, u5} M₂ M₃ _inst_17 _inst_18))
but is expected to have type
  forall {R : Type.{u1}} {ι : Type.{u2}} {M₁ : ι -> Type.{u3}} {M₂ : Type.{u4}} {M₃ : Type.{u5}} [_inst_1 : Semiring.{u1} R] [_inst_3 : forall (i : ι), AddCommMonoid.{u3} (M₁ i)] [_inst_5 : AddCommMonoid.{u4} M₂] [_inst_6 : AddCommMonoid.{u5} M₃] [_inst_9 : forall (i : ι), Module.{u1, u3} R (M₁ i) _inst_1 (_inst_3 i)] [_inst_11 : Module.{u1, u4} R M₂ _inst_1 _inst_5] [_inst_12 : Module.{u1, u5} R M₃ _inst_1 _inst_6] [_inst_15 : forall (i : ι), TopologicalSpace.{u3} (M₁ i)] [_inst_17 : TopologicalSpace.{u4} M₂] [_inst_18 : TopologicalSpace.{u5} M₃], (ContinuousMultilinearMap.{u1, u2, u3, u4} R ι M₁ M₂ _inst_1 (fun (i : ι) => _inst_3 i) _inst_5 (fun (i : ι) => _inst_9 i) _inst_11 (fun (i : ι) => _inst_15 i) _inst_17) -> (ContinuousMultilinearMap.{u1, u2, u3, u5} R ι M₁ M₃ _inst_1 (fun (i : ι) => _inst_3 i) _inst_6 (fun (i : ι) => _inst_9 i) _inst_12 (fun (i : ι) => _inst_15 i) _inst_18) -> (ContinuousMultilinearMap.{u1, u2, u3, max u5 u4} R ι M₁ (Prod.{u4, u5} M₂ M₃) _inst_1 (fun (i : ι) => _inst_3 i) (Prod.instAddCommMonoidSum.{u4, u5} M₂ M₃ _inst_5 _inst_6) (fun (i : ι) => _inst_9 i) (Prod.module.{u1, u4, u5} R M₂ M₃ _inst_1 _inst_5 _inst_6 _inst_11 _inst_12) (fun (i : ι) => _inst_15 i) (instTopologicalSpaceProd.{u4, u5} M₂ M₃ _inst_17 _inst_18))
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.prod ContinuousMultilinearMap.prodₓ'. -/
/-- The cartesian product of two continuous multilinear maps, as a continuous multilinear map. -/
def prod (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃) :
    ContinuousMultilinearMap R M₁ (M₂ × M₃) :=
  { f.toMultilinearMap.Prod g.toMultilinearMap with cont := f.cont.prod_mk g.cont }
#align continuous_multilinear_map.prod ContinuousMultilinearMap.prod

#print ContinuousMultilinearMap.prod_apply /-
@[simp]
theorem prod_apply (f : ContinuousMultilinearMap R M₁ M₂) (g : ContinuousMultilinearMap R M₁ M₃)
    (m : ∀ i, M₁ i) : (f.Prod g) m = (f m, g m) :=
  rfl
#align continuous_multilinear_map.prod_apply ContinuousMultilinearMap.prod_apply
-/

#print ContinuousMultilinearMap.pi /-
/-- Combine a family of continuous multilinear maps with the same domain and codomains `M' i` into a
continuous multilinear map taking values in the space of functions `Π i, M' i`. -/
def pi {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)] [∀ i, TopologicalSpace (M' i)]
    [∀ i, Module R (M' i)] (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) :
    ContinuousMultilinearMap R M₁ (∀ i, M' i)
    where
  cont := continuous_pi fun i => (f i).coe_continuous
  toMultilinearMap := MultilinearMap.pi fun i => (f i).toMultilinearMap
#align continuous_multilinear_map.pi ContinuousMultilinearMap.pi
-/

/- warning: continuous_multilinear_map.coe_pi -> ContinuousMultilinearMap.coe_pi is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.coe_pi ContinuousMultilinearMap.coe_piₓ'. -/
@[simp]
theorem coe_pi {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) : ⇑(pi f) = fun m j => f j m :=
  rfl
#align continuous_multilinear_map.coe_pi ContinuousMultilinearMap.coe_pi

/- warning: continuous_multilinear_map.pi_apply -> ContinuousMultilinearMap.pi_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.pi_apply ContinuousMultilinearMap.pi_applyₓ'. -/
theorem pi_apply {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)]
    (f : ∀ i, ContinuousMultilinearMap R M₁ (M' i)) (m : ∀ i, M₁ i) (j : ι') : pi f m j = f j m :=
  rfl
#align continuous_multilinear_map.pi_apply ContinuousMultilinearMap.pi_apply

section

variable (R M₂)

#print ContinuousMultilinearMap.ofSubsingleton /-
/-- The evaluation map from `ι → M₂` to `M₂` is multilinear at a given `i` when `ι` is subsingleton.
-/
@[simps toMultilinearMap apply]
def ofSubsingleton [Subsingleton ι] (i' : ι) : ContinuousMultilinearMap R (fun _ : ι => M₂) M₂
    where
  toMultilinearMap := MultilinearMap.ofSubsingleton R _ i'
  cont := continuous_apply _
#align continuous_multilinear_map.of_subsingleton ContinuousMultilinearMap.ofSubsingleton
-/

variable (M₁) {M₂}

#print ContinuousMultilinearMap.constOfIsEmpty /-
/-- The constant map is multilinear when `ι` is empty. -/
@[simps toMultilinearMap apply]
def constOfIsEmpty [IsEmpty ι] (m : M₂) : ContinuousMultilinearMap R M₁ M₂
    where
  toMultilinearMap := MultilinearMap.constOfIsEmpty R _ m
  cont := continuous_const
#align continuous_multilinear_map.const_of_is_empty ContinuousMultilinearMap.constOfIsEmpty
-/

end

#print ContinuousMultilinearMap.compContinuousLinearMap /-
/-- If `g` is continuous multilinear and `f` is a collection of continuous linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a continuous multilinear map, that we call
`g.comp_continuous_linear_map f`. -/
def compContinuousLinearMap (g : ContinuousMultilinearMap R M₁' M₄)
    (f : ∀ i : ι, M₁ i →L[R] M₁' i) : ContinuousMultilinearMap R M₁ M₄ :=
  { g.toMultilinearMap.compLinearMap fun i => (f i).toLinearMap with
    cont := g.cont.comp <| continuous_pi fun j => (f j).cont.comp <| continuous_apply _ }
#align continuous_multilinear_map.comp_continuous_linear_map ContinuousMultilinearMap.compContinuousLinearMap
-/

/- warning: continuous_multilinear_map.comp_continuous_linear_map_apply -> ContinuousMultilinearMap.compContinuousLinearMap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.comp_continuous_linear_map_apply ContinuousMultilinearMap.compContinuousLinearMap_applyₓ'. -/
@[simp]
theorem compContinuousLinearMap_apply (g : ContinuousMultilinearMap R M₁' M₄)
    (f : ∀ i : ι, M₁ i →L[R] M₁' i) (m : ∀ i, M₁ i) :
    g.compContinuousLinearMap f m = g fun i => f i <| m i :=
  rfl
#align continuous_multilinear_map.comp_continuous_linear_map_apply ContinuousMultilinearMap.compContinuousLinearMap_apply

#print ContinuousLinearMap.compContinuousMultilinearMap /-
/-- Composing a continuous multilinear map with a continuous linear map gives again a
continuous multilinear map. -/
def ContinuousLinearMap.compContinuousMultilinearMap (g : M₂ →L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) : ContinuousMultilinearMap R M₁ M₃ :=
  { g.toLinearMap.compMultilinearMap f.toMultilinearMap with cont := g.cont.comp f.cont }
#align continuous_linear_map.comp_continuous_multilinear_map ContinuousLinearMap.compContinuousMultilinearMap
-/

/- warning: continuous_linear_map.comp_continuous_multilinear_map_coe -> ContinuousLinearMap.compContinuousMultilinearMap_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.comp_continuous_multilinear_map_coe ContinuousLinearMap.compContinuousMultilinearMap_coeₓ'. -/
@[simp]
theorem ContinuousLinearMap.compContinuousMultilinearMap_coe (g : M₂ →L[R] M₃)
    (f : ContinuousMultilinearMap R M₁ M₂) :
    (g.compContinuousMultilinearMap f : (∀ i, M₁ i) → M₃) =
      (g : M₂ → M₃) ∘ (f : (∀ i, M₁ i) → M₂) :=
  by
  ext m
  rfl
#align continuous_linear_map.comp_continuous_multilinear_map_coe ContinuousLinearMap.compContinuousMultilinearMap_coe

#print ContinuousMultilinearMap.piEquiv /-
/-- `continuous_multilinear_map.pi` as an `equiv`. -/
@[simps]
def piEquiv {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, Module R (M' i)] :
    (∀ i, ContinuousMultilinearMap R M₁ (M' i)) ≃ ContinuousMultilinearMap R M₁ (∀ i, M' i)
    where
  toFun := ContinuousMultilinearMap.pi
  invFun f i := (ContinuousLinearMap.proj i : _ →L[R] M' i).compContinuousMultilinearMap f
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    rfl
#align continuous_multilinear_map.pi_equiv ContinuousMultilinearMap.piEquiv
-/

/- warning: continuous_multilinear_map.cons_add -> ContinuousMultilinearMap.cons_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.cons_add ContinuousMultilinearMap.cons_addₓ'. -/
/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
theorem cons_add (f : ContinuousMultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (x y : M 0) :
    f (cons (x + y) m) = f (cons x m) + f (cons y m) :=
  f.toMultilinearMap.cons_add m x y
#align continuous_multilinear_map.cons_add ContinuousMultilinearMap.cons_add

/- warning: continuous_multilinear_map.cons_smul -> ContinuousMultilinearMap.cons_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.cons_smul ContinuousMultilinearMap.cons_smulₓ'. -/
/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a multilinear map along the first variable. -/
theorem cons_smul (f : ContinuousMultilinearMap R M M₂) (m : ∀ i : Fin n, M i.succ) (c : R)
    (x : M 0) : f (cons (c • x) m) = c • f (cons x m) :=
  f.toMultilinearMap.cons_smul m c x
#align continuous_multilinear_map.cons_smul ContinuousMultilinearMap.cons_smul

/- warning: continuous_multilinear_map.map_piecewise_add -> ContinuousMultilinearMap.map_piecewise_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.map_piecewise_add ContinuousMultilinearMap.map_piecewise_addₓ'. -/
theorem map_piecewise_add [DecidableEq ι] (m m' : ∀ i, M₁ i) (t : Finset ι) :
    f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
  f.toMultilinearMap.map_piecewise_add _ _ _
#align continuous_multilinear_map.map_piecewise_add ContinuousMultilinearMap.map_piecewise_add

/- warning: continuous_multilinear_map.map_add_univ -> ContinuousMultilinearMap.map_add_univ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.map_add_univ ContinuousMultilinearMap.map_add_univₓ'. -/
/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
theorem map_add_univ [DecidableEq ι] [Fintype ι] (m m' : ∀ i, M₁ i) :
    f (m + m') = ∑ s : Finset ι, f (s.piecewise m m') :=
  f.toMultilinearMap.map_add_univ _ _
#align continuous_multilinear_map.map_add_univ ContinuousMultilinearMap.map_add_univ

section ApplySum

open Fintype Finset

variable {α : ι → Type _} [Fintype ι] (g : ∀ i, α i → M₁ i) (A : ∀ i, Finset (α i))

/- warning: continuous_multilinear_map.map_sum_finset -> ContinuousMultilinearMap.map_sum_finset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.map_sum_finset ContinuousMultilinearMap.map_sum_finsetₓ'. -/
/-- If `f` is continuous multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
theorem map_sum_finset [DecidableEq ι] :
    (f fun i => ∑ j in A i, g i j) = ∑ r in piFinset A, f fun i => g i (r i) :=
  f.toMultilinearMap.map_sum_finset _ _
#align continuous_multilinear_map.map_sum_finset ContinuousMultilinearMap.map_sum_finset

/- warning: continuous_multilinear_map.map_sum -> ContinuousMultilinearMap.map_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.map_sum ContinuousMultilinearMap.map_sumₓ'. -/
/-- If `f` is continuous multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
theorem map_sum [DecidableEq ι] [∀ i, Fintype (α i)] :
    (f fun i => ∑ j, g i j) = ∑ r : ∀ i, α i, f fun i => g i (r i) :=
  f.toMultilinearMap.map_sum _
#align continuous_multilinear_map.map_sum ContinuousMultilinearMap.map_sum

end ApplySum

section RestrictScalar

variable (R) {A : Type _} [Semiring A] [SMul R A] [∀ i : ι, Module A (M₁ i)] [Module A M₂]
  [∀ i, IsScalarTower R A (M₁ i)] [IsScalarTower R A M₂]

#print ContinuousMultilinearMap.restrictScalars /-
/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ContinuousMultilinearMap R M₁ M₂
    where
  toMultilinearMap := f.toMultilinearMap.restrictScalars R
  cont := f.cont
#align continuous_multilinear_map.restrict_scalars ContinuousMultilinearMap.restrictScalars
-/

/- warning: continuous_multilinear_map.coe_restrict_scalars -> ContinuousMultilinearMap.coe_restrictScalars is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.coe_restrict_scalars ContinuousMultilinearMap.coe_restrictScalarsₓ'. -/
@[simp]
theorem coe_restrictScalars (f : ContinuousMultilinearMap A M₁ M₂) : ⇑(f.restrictScalars R) = f :=
  rfl
#align continuous_multilinear_map.coe_restrict_scalars ContinuousMultilinearMap.coe_restrictScalars

end RestrictScalar

end Semiring

section Ring

variable [Ring R] [∀ i, AddCommGroup (M₁ i)] [AddCommGroup M₂] [∀ i, Module R (M₁ i)] [Module R M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] (f f' : ContinuousMultilinearMap R M₁ M₂)

/- warning: continuous_multilinear_map.map_sub -> ContinuousMultilinearMap.map_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.map_sub ContinuousMultilinearMap.map_subₓ'. -/
@[simp]
theorem map_sub [DecidableEq ι] (m : ∀ i, M₁ i) (i : ι) (x y : M₁ i) :
    f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
  f.toMultilinearMap.map_sub _ _ _ _
#align continuous_multilinear_map.map_sub ContinuousMultilinearMap.map_sub

section TopologicalAddGroup

variable [TopologicalAddGroup M₂]

instance : Neg (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f => { -f.toMultilinearMap with cont := f.cont.neg }⟩

/- warning: continuous_multilinear_map.neg_apply -> ContinuousMultilinearMap.neg_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.neg_apply ContinuousMultilinearMap.neg_applyₓ'. -/
@[simp]
theorem neg_apply (m : ∀ i, M₁ i) : (-f) m = -f m :=
  rfl
#align continuous_multilinear_map.neg_apply ContinuousMultilinearMap.neg_apply

instance : Sub (ContinuousMultilinearMap R M₁ M₂) :=
  ⟨fun f g => { f.toMultilinearMap - g.toMultilinearMap with cont := f.cont.sub g.cont }⟩

/- warning: continuous_multilinear_map.sub_apply -> ContinuousMultilinearMap.sub_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.sub_apply ContinuousMultilinearMap.sub_applyₓ'. -/
@[simp]
theorem sub_apply (m : ∀ i, M₁ i) : (f - f') m = f m - f' m :=
  rfl
#align continuous_multilinear_map.sub_apply ContinuousMultilinearMap.sub_apply

instance : AddCommGroup (ContinuousMultilinearMap R M₁ M₂) :=
  toMultilinearMap_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

end TopologicalAddGroup

end Ring

section CommSemiring

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂]
  (f : ContinuousMultilinearMap R M₁ M₂)

#print ContinuousMultilinearMap.map_piecewise_smul /-
theorem map_piecewise_smul [DecidableEq ι] (c : ι → R) (m : ∀ i, M₁ i) (s : Finset ι) :
    f (s.piecewise (fun i => c i • m i) m) = (∏ i in s, c i) • f m :=
  f.toMultilinearMap.map_piecewise_smul _ _ _
#align continuous_multilinear_map.map_piecewise_smul ContinuousMultilinearMap.map_piecewise_smul
-/

#print ContinuousMultilinearMap.map_smul_univ /-
/-- Multiplicativity of a continuous multilinear map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `(∏ i, c i) • f m`. -/
theorem map_smul_univ [Fintype ι] (c : ι → R) (m : ∀ i, M₁ i) :
    (f fun i => c i • m i) = (∏ i, c i) • f m :=
  f.toMultilinearMap.map_smul_univ _ _
#align continuous_multilinear_map.map_smul_univ ContinuousMultilinearMap.map_smul_univ
-/

end CommSemiring

section DistribMulAction

variable {R' R'' A : Type _} [Monoid R'] [Monoid R''] [Semiring A] [∀ i, AddCommMonoid (M₁ i)]
  [AddCommMonoid M₂] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] [∀ i, Module A (M₁ i)]
  [Module A M₂] [DistribMulAction R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]
  [DistribMulAction R'' M₂] [ContinuousConstSMul R'' M₂] [SMulCommClass A R'' M₂]

instance [ContinuousAdd M₂] : DistribMulAction R' (ContinuousMultilinearMap A M₁ M₂) :=
  Function.Injective.distribMulAction
    ⟨toMultilinearMap, toMultilinearMap_zero, toMultilinearMap_add⟩ toMultilinearMap_injective
    fun _ _ => rfl

end DistribMulAction

section Module

variable {R' A : Type _} [Semiring R'] [Semiring A] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂]
  [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂] [ContinuousAdd M₂] [∀ i, Module A (M₁ i)]
  [Module A M₂] [Module R' M₂] [ContinuousConstSMul R' M₂] [SMulCommClass A R' M₂]

/-- The space of continuous multilinear maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
instance : Module R' (ContinuousMultilinearMap A M₁ M₂) :=
  Function.Injective.module _ ⟨toMultilinearMap, toMultilinearMap_zero, toMultilinearMap_add⟩
    toMultilinearMap_injective fun _ _ => rfl

/- warning: continuous_multilinear_map.to_multilinear_map_linear -> ContinuousMultilinearMap.toMultilinearMapLinear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.to_multilinear_map_linear ContinuousMultilinearMap.toMultilinearMapLinearₓ'. -/
/-- Linear map version of the map `to_multilinear_map` associating to a continuous multilinear map
the corresponding multilinear map. -/
@[simps]
def toMultilinearMapLinear : ContinuousMultilinearMap A M₁ M₂ →ₗ[R'] MultilinearMap A M₁ M₂
    where
  toFun := toMultilinearMap
  map_add' := toMultilinearMap_add
  map_smul' := toMultilinearMap_smul
#align continuous_multilinear_map.to_multilinear_map_linear ContinuousMultilinearMap.toMultilinearMapLinear

/- warning: continuous_multilinear_map.pi_linear_equiv -> ContinuousMultilinearMap.piLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.pi_linear_equiv ContinuousMultilinearMap.piLinearEquivₓ'. -/
/-- `continuous_multilinear_map.pi` as a `linear_equiv`. -/
@[simps (config := { simpRhs := true })]
def piLinearEquiv {ι' : Type _} {M' : ι' → Type _} [∀ i, AddCommMonoid (M' i)]
    [∀ i, TopologicalSpace (M' i)] [∀ i, ContinuousAdd (M' i)] [∀ i, Module R' (M' i)]
    [∀ i, Module A (M' i)] [∀ i, SMulCommClass A R' (M' i)] [∀ i, ContinuousConstSMul R' (M' i)] :
    (∀ i, ContinuousMultilinearMap A M₁ (M' i)) ≃ₗ[R'] ContinuousMultilinearMap A M₁ (∀ i, M' i) :=
  { piEquiv with
    map_add' := fun x y => rfl
    map_smul' := fun c x => rfl }
#align continuous_multilinear_map.pi_linear_equiv ContinuousMultilinearMap.piLinearEquiv

end Module

section CommAlgebra

variable (R ι) (A : Type _) [Fintype ι] [CommSemiring R] [CommSemiring A] [Algebra R A]
  [TopologicalSpace A] [ContinuousMul A]

/- warning: continuous_multilinear_map.mk_pi_algebra -> ContinuousMultilinearMap.mkPiAlgebra is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (ι : Type.{u2}) (A : Type.{u3}) [_inst_1 : Fintype.{u2} ι] [_inst_2 : CommSemiring.{u1} R] [_inst_3 : CommSemiring.{u3} A] [_inst_4 : Algebra.{u1, u3} R A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3)] [_inst_5 : TopologicalSpace.{u3} A] [_inst_6 : ContinuousMul.{u3} A _inst_5 (Distrib.toHasMul.{u3} A (NonUnitalNonAssocSemiring.toDistrib.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3)))))], ContinuousMultilinearMap.{u1, u2, u3, u3} R ι (fun (i : ι) => A) A (CommSemiring.toSemiring.{u1} R _inst_2) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3)))) (fun (i : ι) => Algebra.toModule.{u1, u3} R A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_4) (Algebra.toModule.{u1, u3} R A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_4) (fun (i : ι) => _inst_5) _inst_5
but is expected to have type
  forall (R : Type.{u1}) (ι : Type.{u2}) (A : Type.{u3}) [_inst_1 : Fintype.{u2} ι] [_inst_2 : CommSemiring.{u1} R] [_inst_3 : CommSemiring.{u3} A] [_inst_4 : Algebra.{u1, u3} R A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3)] [_inst_5 : TopologicalSpace.{u3} A] [_inst_6 : ContinuousMul.{u3} A _inst_5 (NonUnitalNonAssocSemiring.toMul.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3))))], ContinuousMultilinearMap.{u1, u2, u3, u3} R ι (fun (i : ι) => A) A (CommSemiring.toSemiring.{u1} R _inst_2) (fun (i : ι) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} ((fun (x._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22059 : ι) => A) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} ((fun (x._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22059 : ι) => A) i) (Semiring.toNonAssocSemiring.{u3} ((fun (x._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22059 : ι) => A) i) (CommSemiring.toSemiring.{u3} ((fun (x._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22059 : ι) => A) i) _inst_3)))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3)))) (fun (i : ι) => Algebra.toModule.{u1, u3} R ((fun (x._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22059 : ι) => A) i) _inst_2 (CommSemiring.toSemiring.{u3} ((fun (x._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22059 : ι) => A) i) _inst_3) _inst_4) (Algebra.toModule.{u1, u3} R A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_4) (fun (i : ι) => _inst_5) _inst_5
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.mk_pi_algebra ContinuousMultilinearMap.mkPiAlgebraₓ'. -/
/-- The continuous multilinear map on `A^ι`, where `A` is a normed commutative algebra
over `𝕜`, associating to `m` the product of all the `m i`.

See also `continuous_multilinear_map.mk_pi_algebra_fin`. -/
protected def mkPiAlgebra : ContinuousMultilinearMap R (fun i : ι => A) A
    where
  cont := continuous_finset_prod _ fun i hi => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebra R ι A
#align continuous_multilinear_map.mk_pi_algebra ContinuousMultilinearMap.mkPiAlgebra

/- warning: continuous_multilinear_map.mk_pi_algebra_apply -> ContinuousMultilinearMap.mkPiAlgebra_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.mk_pi_algebra_apply ContinuousMultilinearMap.mkPiAlgebra_applyₓ'. -/
@[simp]
theorem mkPiAlgebra_apply (m : ι → A) : ContinuousMultilinearMap.mkPiAlgebra R ι A m = ∏ i, m i :=
  rfl
#align continuous_multilinear_map.mk_pi_algebra_apply ContinuousMultilinearMap.mkPiAlgebra_apply

end CommAlgebra

section Algebra

variable (R n) (A : Type _) [CommSemiring R] [Semiring A] [Algebra R A] [TopologicalSpace A]
  [ContinuousMul A]

/- warning: continuous_multilinear_map.mk_pi_algebra_fin -> ContinuousMultilinearMap.mkPiAlgebraFin is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (n : Nat) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u2} A] [_inst_5 : ContinuousMul.{u2} A _inst_4 (Distrib.toHasMul.{u2} A (NonUnitalNonAssocSemiring.toDistrib.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))))], ContinuousMultilinearMap.{u1, 0, u2, u2} R (Fin n) (fun (i : Fin n) => A) A (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (fun (i : Fin n) => Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (fun (i : Fin n) => _inst_4) _inst_4
but is expected to have type
  forall (R : Type.{u1}) (n : Nat) (A : Type.{u2}) [_inst_1 : CommSemiring.{u1} R] [_inst_2 : Semiring.{u2} A] [_inst_3 : Algebra.{u1, u2} R A _inst_1 _inst_2] [_inst_4 : TopologicalSpace.{u2} A] [_inst_5 : ContinuousMul.{u2} A _inst_4 (NonUnitalNonAssocSemiring.toMul.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2)))], ContinuousMultilinearMap.{u1, 0, u2, u2} R (Fin n) (fun (i : Fin n) => A) A (CommSemiring.toSemiring.{u1} R _inst_1) (fun (i : Fin n) => NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} ((fun (i._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22228 : Fin n) => A) i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (i._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22228 : Fin n) => A) i) (Semiring.toNonAssocSemiring.{u2} ((fun (i._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22228 : Fin n) => A) i) _inst_2))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} A (Semiring.toNonAssocSemiring.{u2} A _inst_2))) (fun (i : Fin n) => Algebra.toModule.{u1, u2} R ((fun (i._@.Mathlib.Topology.Algebra.Module.Multilinear._hyg.22228 : Fin n) => A) i) _inst_1 _inst_2 _inst_3) (Algebra.toModule.{u1, u2} R A _inst_1 _inst_2 _inst_3) (fun (i : Fin n) => _inst_4) _inst_4
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.mk_pi_algebra_fin ContinuousMultilinearMap.mkPiAlgebraFinₓ'. -/
/-- The continuous multilinear map on `A^n`, where `A` is a normed algebra over `𝕜`, associating to
`m` the product of all the `m i`.

See also: `continuous_multilinear_map.mk_pi_algebra`. -/
protected def mkPiAlgebraFin : A[×n]→L[R] A
    where
  cont := by
    change Continuous fun m => (List.ofFn m).Prod
    simp_rw [List.ofFn_eq_map]
    exact continuous_list_prod _ fun i hi => continuous_apply _
  toMultilinearMap := MultilinearMap.mkPiAlgebraFin R n A
#align continuous_multilinear_map.mk_pi_algebra_fin ContinuousMultilinearMap.mkPiAlgebraFin

variable {R n A}

/- warning: continuous_multilinear_map.mk_pi_algebra_fin_apply -> ContinuousMultilinearMap.mkPiAlgebraFin_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_multilinear_map.mk_pi_algebra_fin_apply ContinuousMultilinearMap.mkPiAlgebraFin_applyₓ'. -/
@[simp]
theorem mkPiAlgebraFin_apply (m : Fin n → A) :
    ContinuousMultilinearMap.mkPiAlgebraFin R n A m = (List.ofFn m).Prod :=
  rfl
#align continuous_multilinear_map.mk_pi_algebra_fin_apply ContinuousMultilinearMap.mkPiAlgebraFin_apply

end Algebra

section SmulRight

variable [CommSemiring R] [∀ i, AddCommMonoid (M₁ i)] [AddCommMonoid M₂] [∀ i, Module R (M₁ i)]
  [Module R M₂] [TopologicalSpace R] [∀ i, TopologicalSpace (M₁ i)] [TopologicalSpace M₂]
  [ContinuousSMul R M₂] (f : ContinuousMultilinearMap R M₁ R) (z : M₂)

#print ContinuousMultilinearMap.smulRight /-
/-- Given a continuous `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the
continuous multilinear map sending `m` to `f m • z`. -/
@[simps toMultilinearMap apply]
def smulRight : ContinuousMultilinearMap R M₁ M₂
    where
  toMultilinearMap := f.toMultilinearMap.smul_right z
  cont := f.cont.smul continuous_const
#align continuous_multilinear_map.smul_right ContinuousMultilinearMap.smulRight
-/

end SmulRight

end ContinuousMultilinearMap

