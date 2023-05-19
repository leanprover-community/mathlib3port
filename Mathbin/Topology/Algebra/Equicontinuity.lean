/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker

! This file was ported from Lean 3 source module topology.algebra.equicontinuity
! leanprover-community/mathlib commit 781cb2eed038c4caf53bdbd8d20a95e5822d77df
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.UniformConvergence

/-!
# Algebra-related equicontinuity criterions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

open UniformConvergence

/- warning: equicontinuous_of_equicontinuous_at_one -> equicontinuous_of_equicontinuousAt_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} {M : Type.{u3}} {hom : Type.{u4}} [_inst_1 : TopologicalSpace.{u2} G] [_inst_2 : UniformSpace.{u3} M] [_inst_3 : Group.{u2} G] [_inst_4 : Group.{u3} M] [_inst_5 : TopologicalGroup.{u2} G _inst_1 _inst_3] [_inst_6 : UniformGroup.{u3} M _inst_2 _inst_4] [_inst_7 : MonoidHomClass.{u4, u2, u3} hom G M (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4)))] (F : ι -> hom), (EquicontinuousAt.{u1, u2, u3} ι G M _inst_1 _inst_2 (Function.comp.{succ u1, succ u4, max (succ u2) (succ u3)} ι hom (G -> M) (coeFn.{succ u4, max (succ u2) (succ u3)} hom (fun (ᾰ : hom) => G -> M) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} hom G (fun (_x : G) => M) (MulHomClass.toFunLike.{u4, u2, u3} hom G M (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4)))) (MonoidHomClass.toMulHomClass.{u4, u2, u3} hom G M (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4))) _inst_7)))) F) (OfNat.ofNat.{u2} G 1 (OfNat.mk.{u2} G 1 (One.one.{u2} G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))))))) -> (Equicontinuous.{u1, u2, u3} ι G M _inst_1 _inst_2 (Function.comp.{succ u1, succ u4, max (succ u2) (succ u3)} ι hom (G -> M) (coeFn.{succ u4, max (succ u2) (succ u3)} hom (fun (ᾰ : hom) => G -> M) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} hom G (fun (_x : G) => M) (MulHomClass.toFunLike.{u4, u2, u3} hom G M (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4)))) (MonoidHomClass.toMulHomClass.{u4, u2, u3} hom G M (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4))) _inst_7)))) F))
but is expected to have type
  forall {ι : Type.{u4}} {G : Type.{u3}} {M : Type.{u2}} {hom : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} G] [_inst_2 : UniformSpace.{u2} M] [_inst_3 : Group.{u3} G] [_inst_4 : Group.{u2} M] [_inst_5 : TopologicalGroup.{u3} G _inst_1 _inst_3] [_inst_6 : UniformGroup.{u2} M _inst_2 _inst_4] [_inst_7 : MonoidHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4)))] (F : ι -> hom), (EquicontinuousAt.{u4, u3, u2} ι G M _inst_1 _inst_2 (Function.comp.{succ u4, succ u1, max (succ u2) (succ u3)} ι hom (G -> M) (FunLike.coe.{succ u1, succ u3, succ u2} hom G (fun (ᾰ : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => M) ᾰ) (MulHomClass.toFunLike.{u1, u3, u2} hom G M (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4))) _inst_7))) F) (OfNat.ofNat.{u3} G 1 (One.toOfNat1.{u3} G (InvOneClass.toOne.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_3))))))) -> (Equicontinuous.{u4, u3, u2} ι G M _inst_1 _inst_2 (Function.comp.{succ u4, succ u1, max (succ u2) (succ u3)} ι hom (G -> M) (FunLike.coe.{succ u1, succ u3, succ u2} hom G (fun (ᾰ : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => M) ᾰ) (MulHomClass.toFunLike.{u1, u3, u2} hom G M (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4))) _inst_7))) F))
Case conversion may be inaccurate. Consider using '#align equicontinuous_of_equicontinuous_at_one equicontinuous_of_equicontinuousAt_oneₓ'. -/
@[to_additive]
theorem equicontinuous_of_equicontinuousAt_one {ι G M hom : Type _} [TopologicalSpace G]
    [UniformSpace M] [Group G] [Group M] [TopologicalGroup G] [UniformGroup M]
    [MonoidHomClass hom G M] (F : ι → hom) (hf : EquicontinuousAt (coeFn ∘ F) (1 : G)) :
    Equicontinuous (coeFn ∘ F) :=
  by
  letI : CoeFun hom fun _ => G → M := FunLike.hasCoeToFun
  rw [equicontinuous_iff_continuous]
  rw [equicontinuousAt_iff_continuousAt] at hf
  let φ : G →* ι → M :=
    { toFun := swap (coeFn ∘ F)
      map_one' := by ext <;> exact map_one _
      map_mul' := fun a b => by ext <;> exact map_mul _ _ _ }
  exact continuous_of_continuousAt_one φ hf
#align equicontinuous_of_equicontinuous_at_one equicontinuous_of_equicontinuousAt_one
#align equicontinuous_of_equicontinuous_at_zero equicontinuous_of_equicontinuousAt_zero

/- warning: uniform_equicontinuous_of_equicontinuous_at_one -> uniformEquicontinuous_of_equicontinuousAt_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} {M : Type.{u3}} {hom : Type.{u4}} [_inst_1 : UniformSpace.{u2} G] [_inst_2 : UniformSpace.{u3} M] [_inst_3 : Group.{u2} G] [_inst_4 : Group.{u3} M] [_inst_5 : UniformGroup.{u2} G _inst_1 _inst_3] [_inst_6 : UniformGroup.{u3} M _inst_2 _inst_4] [_inst_7 : MonoidHomClass.{u4, u2, u3} hom G M (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4)))] (F : ι -> hom), (EquicontinuousAt.{u1, u2, u3} ι G M (UniformSpace.toTopologicalSpace.{u2} G _inst_1) _inst_2 (Function.comp.{succ u1, succ u4, max (succ u2) (succ u3)} ι hom (G -> M) (coeFn.{succ u4, max (succ u2) (succ u3)} hom (fun (ᾰ : hom) => G -> M) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} hom G (fun (_x : G) => M) (MulHomClass.toFunLike.{u4, u2, u3} hom G M (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4)))) (MonoidHomClass.toMulHomClass.{u4, u2, u3} hom G M (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4))) _inst_7)))) F) (OfNat.ofNat.{u2} G 1 (OfNat.mk.{u2} G 1 (One.one.{u2} G (MulOneClass.toHasOne.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))))))) -> (UniformEquicontinuous.{u1, u3, u2} ι M G _inst_2 _inst_1 (Function.comp.{succ u1, succ u4, max (succ u2) (succ u3)} ι hom (G -> M) (coeFn.{succ u4, max (succ u2) (succ u3)} hom (fun (ᾰ : hom) => G -> M) (FunLike.hasCoeToFun.{succ u4, succ u2, succ u3} hom G (fun (_x : G) => M) (MulHomClass.toFunLike.{u4, u2, u3} hom G M (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3)))) (MulOneClass.toHasMul.{u3} M (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4)))) (MonoidHomClass.toMulHomClass.{u4, u2, u3} hom G M (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_3))) (Monoid.toMulOneClass.{u3} M (DivInvMonoid.toMonoid.{u3} M (Group.toDivInvMonoid.{u3} M _inst_4))) _inst_7)))) F))
but is expected to have type
  forall {ι : Type.{u4}} {G : Type.{u3}} {M : Type.{u2}} {hom : Type.{u1}} [_inst_1 : UniformSpace.{u3} G] [_inst_2 : UniformSpace.{u2} M] [_inst_3 : Group.{u3} G] [_inst_4 : Group.{u2} M] [_inst_5 : UniformGroup.{u3} G _inst_1 _inst_3] [_inst_6 : UniformGroup.{u2} M _inst_2 _inst_4] [_inst_7 : MonoidHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4)))] (F : ι -> hom), (EquicontinuousAt.{u4, u3, u2} ι G M (UniformSpace.toTopologicalSpace.{u3} G _inst_1) _inst_2 (Function.comp.{succ u4, succ u1, max (succ u2) (succ u3)} ι hom (G -> M) (FunLike.coe.{succ u1, succ u3, succ u2} hom G (fun (ᾰ : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => M) ᾰ) (MulHomClass.toFunLike.{u1, u3, u2} hom G M (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4))) _inst_7))) F) (OfNat.ofNat.{u3} G 1 (One.toOfNat1.{u3} G (InvOneClass.toOne.{u3} G (DivInvOneMonoid.toInvOneClass.{u3} G (DivisionMonoid.toDivInvOneMonoid.{u3} G (Group.toDivisionMonoid.{u3} G _inst_3))))))) -> (UniformEquicontinuous.{u4, u2, u3} ι M G _inst_2 _inst_1 (Function.comp.{succ u4, succ u1, max (succ u3) (succ u2)} ι hom (G -> M) (FunLike.coe.{succ u1, succ u3, succ u2} hom G (fun (ᾰ : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => M) ᾰ) (MulHomClass.toFunLike.{u1, u3, u2} hom G M (MulOneClass.toMul.{u3} G (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3)))) (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4)))) (MonoidHomClass.toMulHomClass.{u1, u3, u2} hom G M (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} M (DivInvMonoid.toMonoid.{u2} M (Group.toDivInvMonoid.{u2} M _inst_4))) _inst_7))) F))
Case conversion may be inaccurate. Consider using '#align uniform_equicontinuous_of_equicontinuous_at_one uniformEquicontinuous_of_equicontinuousAt_oneₓ'. -/
@[to_additive]
theorem uniformEquicontinuous_of_equicontinuousAt_one {ι G M hom : Type _} [UniformSpace G]
    [UniformSpace M] [Group G] [Group M] [UniformGroup G] [UniformGroup M] [MonoidHomClass hom G M]
    (F : ι → hom) (hf : EquicontinuousAt (coeFn ∘ F) (1 : G)) : UniformEquicontinuous (coeFn ∘ F) :=
  by
  letI : CoeFun hom fun _ => G → M := FunLike.hasCoeToFun
  rw [uniformEquicontinuous_iff_uniformContinuous]
  rw [equicontinuousAt_iff_continuousAt] at hf
  let φ : G →* ι → M :=
    { toFun := swap (coeFn ∘ F)
      map_one' := by ext <;> exact map_one _
      map_mul' := fun a b => by ext <;> exact map_mul _ _ _ }
  exact uniformContinuous_of_continuousAt_one φ hf
#align uniform_equicontinuous_of_equicontinuous_at_one uniformEquicontinuous_of_equicontinuousAt_one
#align uniform_equicontinuous_of_equicontinuous_at_zero uniformEquicontinuous_of_equicontinuousAt_zero

