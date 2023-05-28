/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser

! This file was ported from Lean 3 source module algebra.module.submodule.bilinear
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Span
import Mathbin.LinearAlgebra.BilinearMap

/-!
# Images of pairs of submodules under bilinear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides `submodule.map₂`, which is later used to implement `submodule.has_mul`.

## Main results

* `submodule.map₂_eq_span_image2`: the image of two submodules under a bilinear map is the span of
  their `set.image2`.

## Notes

This file is quite similar to the n-ary section of `data.set.basic` and to `order.filter.n_ary`.
Please keep them in sync.
-/


universe uι u v

open Set

open BigOperators

open Pointwise

namespace Submodule

variable {ι : Sort uι} {R M N P : Type _}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

#print Submodule.map₂ /-
/-- Map a pair of submodules under a bilinear map.

This is the submodule version of `set.image2`.  -/
def map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) : Submodule R P :=
  ⨆ s : p, q.map <| f s
#align submodule.map₂ Submodule.map₂
-/

/- warning: submodule.apply_mem_map₂ -> Submodule.apply_mem_map₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.apply_mem_map₂ Submodule.apply_mem_map₂ₓ'. -/
theorem apply_mem_map₂ (f : M →ₗ[R] N →ₗ[R] P) {m : M} {n : N} {p : Submodule R M}
    {q : Submodule R N} (hm : m ∈ p) (hn : n ∈ q) : f m n ∈ map₂ f p q :=
  (le_iSup _ ⟨m, hm⟩ : _ ≤ map₂ f p q) ⟨n, hn, rfl⟩
#align submodule.apply_mem_map₂ Submodule.apply_mem_map₂

/- warning: submodule.map₂_le -> Submodule.map₂_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_le Submodule.map₂_leₓ'. -/
theorem map₂_le {f : M →ₗ[R] N →ₗ[R] P} {p : Submodule R M} {q : Submodule R N}
    {r : Submodule R P} : map₂ f p q ≤ r ↔ ∀ m ∈ p, ∀ n ∈ q, f m n ∈ r :=
  ⟨fun H m hm n hn => H <| apply_mem_map₂ _ hm hn, fun H =>
    iSup_le fun ⟨m, hm⟩ => map_le_iff_le_comap.2 fun n hn => H m hm n hn⟩
#align submodule.map₂_le Submodule.map₂_le

variable (R)

/- warning: submodule.map₂_span_span -> Submodule.map₂_span_span is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_span_span Submodule.map₂_span_spanₓ'. -/
theorem map₂_span_span (f : M →ₗ[R] N →ₗ[R] P) (s : Set M) (t : Set N) :
    map₂ f (span R s) (span R t) = span R (Set.image2 (fun m n => f m n) s t) :=
  by
  apply le_antisymm
  · rw [map₂_le]; intro a ha b hb
    apply span_induction ha
    on_goal 1 =>
      intros ; apply span_induction hb
      on_goal 1 => intros ; exact subset_span ⟨_, _, ‹_›, ‹_›, rfl⟩
    all_goals
      intros
      simp only [LinearMap.map_zero, LinearMap.zero_apply, zero_mem, LinearMap.map_add,
        LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply]
    all_goals
      solve_by_elim (config :=
        { max_depth := 4
          discharger := tactic.interactive.apply_instance }) [add_mem _ _, zero_mem _,
        smul_mem _ _ _]
  · rw [span_le]; rintro _ ⟨a, b, ha, hb, rfl⟩
    exact apply_mem_map₂ _ (subset_span ha) (subset_span hb)
#align submodule.map₂_span_span Submodule.map₂_span_span

variable {R}

/- warning: submodule.map₂_bot_right -> Submodule.map₂_bot_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} {P : Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u3} N] [_inst_4 : AddCommMonoid.{u4} P] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2] [_inst_6 : Module.{u1, u3} R N (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3] [_inst_7 : Module.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4] (f : LinearMap.{u1, u1, u2, max u3 u4} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M (LinearMap.{u1, u1, u3, u4} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) N P _inst_3 _inst_4 _inst_6 _inst_7) _inst_2 (LinearMap.addCommMonoid.{u1, u1, u3, u4} R R N P (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 _inst_4 _inst_6 _inst_7 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) _inst_5 (LinearMap.module.{u1, u1, u1, u3, u4} R R R N P (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 _inst_4 _inst_6 _inst_7 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (CommSemiring.toSemiring.{u1} R _inst_1) _inst_7 (smulCommClass_self.{u1, u4} R P (CommSemiring.toCommMonoid.{u1} R _inst_1) (MulActionWithZero.toMulAction.{u1, u4} R P (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u4} P (AddMonoid.toAddZeroClass.{u4} P (AddCommMonoid.toAddMonoid.{u4} P _inst_4))) (Module.toMulActionWithZero.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_7))))) (p : Submodule.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 _inst_5), Eq.{succ u4} (Submodule.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_7) (Submodule.map₂.{u1, u2, u3, u4} R M N P _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f p (Bot.bot.{u3} (Submodule.{u1, u3} R N (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 _inst_6) (Submodule.hasBot.{u1, u3} R N (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 _inst_6))) (Bot.bot.{u4} (Submodule.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_7) (Submodule.hasBot.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_7))
but is expected to have type
  forall {R : Type.{u4}} {M : Type.{u3}} {N : Type.{u1}} {P : Type.{u2}} [_inst_1 : CommSemiring.{u4} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : AddCommMonoid.{u1} N] [_inst_4 : AddCommMonoid.{u2} P] [_inst_5 : Module.{u4, u3} R M (CommSemiring.toSemiring.{u4} R _inst_1) _inst_2] [_inst_6 : Module.{u4, u1} R N (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3] [_inst_7 : Module.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4] (f : LinearMap.{u4, u4, u3, max u2 u1} R R (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1))) M (LinearMap.{u4, u4, u1, u2} R R (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1))) N P _inst_3 _inst_4 _inst_6 _inst_7) _inst_2 (LinearMap.addCommMonoid.{u4, u4, u1, u2} R R N P (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_4 _inst_6 _inst_7 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1)))) _inst_5 (LinearMap.instModuleLinearMapAddCommMonoid.{u4, u4, u4, u1, u2} R R R N P (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_4 _inst_6 _inst_7 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1))) (CommSemiring.toSemiring.{u4} R _inst_1) _inst_7 (smulCommClass_self.{u4, u2} R P (CommSemiring.toCommMonoid.{u4} R _inst_1) (MulActionWithZero.toMulAction.{u4, u2} R P (Semiring.toMonoidWithZero.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1)) (AddMonoid.toZero.{u2} P (AddCommMonoid.toAddMonoid.{u2} P _inst_4)) (Module.toMulActionWithZero.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4 _inst_7))))) (p : Submodule.{u4, u3} R M (CommSemiring.toSemiring.{u4} R _inst_1) _inst_2 _inst_5), Eq.{succ u2} (Submodule.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4 _inst_7) (Submodule.map₂.{u4, u3, u1, u2} R M N P _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f p (Bot.bot.{u1} (Submodule.{u4, u1} R N (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_6) (Submodule.instBotSubmodule.{u4, u1} R N (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_6))) (Bot.bot.{u2} (Submodule.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4 _inst_7) (Submodule.instBotSubmodule.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4 _inst_7))
Case conversion may be inaccurate. Consider using '#align submodule.map₂_bot_right Submodule.map₂_bot_rightₓ'. -/
@[simp]
theorem map₂_bot_right (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) : map₂ f p ⊥ = ⊥ :=
  eq_bot_iff.2 <|
    map₂_le.2 fun m hm n hn => by rw [Submodule.mem_bot] at hn⊢; rw [hn, LinearMap.map_zero]
#align submodule.map₂_bot_right Submodule.map₂_bot_right

/- warning: submodule.map₂_bot_left -> Submodule.map₂_bot_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} {P : Type.{u4}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : AddCommMonoid.{u2} M] [_inst_3 : AddCommMonoid.{u3} N] [_inst_4 : AddCommMonoid.{u4} P] [_inst_5 : Module.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2] [_inst_6 : Module.{u1, u3} R N (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3] [_inst_7 : Module.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4] (f : LinearMap.{u1, u1, u2, max u3 u4} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) M (LinearMap.{u1, u1, u3, u4} R R (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) N P _inst_3 _inst_4 _inst_6 _inst_7) _inst_2 (LinearMap.addCommMonoid.{u1, u1, u3, u4} R R N P (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 _inst_4 _inst_6 _inst_7 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) _inst_5 (LinearMap.module.{u1, u1, u1, u3, u4} R R R N P (CommSemiring.toSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 _inst_4 _inst_6 _inst_7 (RingHom.id.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (CommSemiring.toSemiring.{u1} R _inst_1) _inst_7 (smulCommClass_self.{u1, u4} R P (CommSemiring.toCommMonoid.{u1} R _inst_1) (MulActionWithZero.toMulAction.{u1, u4} R P (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u4} P (AddMonoid.toAddZeroClass.{u4} P (AddCommMonoid.toAddMonoid.{u4} P _inst_4))) (Module.toMulActionWithZero.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_7))))) (q : Submodule.{u1, u3} R N (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3 _inst_6), Eq.{succ u4} (Submodule.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_7) (Submodule.map₂.{u1, u2, u3, u4} R M N P _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f (Bot.bot.{u2} (Submodule.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 _inst_5) (Submodule.hasBot.{u1, u2} R M (CommSemiring.toSemiring.{u1} R _inst_1) _inst_2 _inst_5)) q) (Bot.bot.{u4} (Submodule.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_7) (Submodule.hasBot.{u1, u4} R P (CommSemiring.toSemiring.{u1} R _inst_1) _inst_4 _inst_7))
but is expected to have type
  forall {R : Type.{u4}} {M : Type.{u3}} {N : Type.{u1}} {P : Type.{u2}} [_inst_1 : CommSemiring.{u4} R] [_inst_2 : AddCommMonoid.{u3} M] [_inst_3 : AddCommMonoid.{u1} N] [_inst_4 : AddCommMonoid.{u2} P] [_inst_5 : Module.{u4, u3} R M (CommSemiring.toSemiring.{u4} R _inst_1) _inst_2] [_inst_6 : Module.{u4, u1} R N (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3] [_inst_7 : Module.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4] (f : LinearMap.{u4, u4, u3, max u2 u1} R R (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1))) M (LinearMap.{u4, u4, u1, u2} R R (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1))) N P _inst_3 _inst_4 _inst_6 _inst_7) _inst_2 (LinearMap.addCommMonoid.{u4, u4, u1, u2} R R N P (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_4 _inst_6 _inst_7 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1)))) _inst_5 (LinearMap.instModuleLinearMapAddCommMonoid.{u4, u4, u4, u1, u2} R R R N P (CommSemiring.toSemiring.{u4} R _inst_1) (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_4 _inst_6 _inst_7 (RingHom.id.{u4} R (Semiring.toNonAssocSemiring.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1))) (CommSemiring.toSemiring.{u4} R _inst_1) _inst_7 (smulCommClass_self.{u4, u2} R P (CommSemiring.toCommMonoid.{u4} R _inst_1) (MulActionWithZero.toMulAction.{u4, u2} R P (Semiring.toMonoidWithZero.{u4} R (CommSemiring.toSemiring.{u4} R _inst_1)) (AddMonoid.toZero.{u2} P (AddCommMonoid.toAddMonoid.{u2} P _inst_4)) (Module.toMulActionWithZero.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4 _inst_7))))) (q : Submodule.{u4, u1} R N (CommSemiring.toSemiring.{u4} R _inst_1) _inst_3 _inst_6), Eq.{succ u2} (Submodule.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4 _inst_7) (Submodule.map₂.{u4, u3, u1, u2} R M N P _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 f (Bot.bot.{u3} (Submodule.{u4, u3} R M (CommSemiring.toSemiring.{u4} R _inst_1) _inst_2 _inst_5) (Submodule.instBotSubmodule.{u4, u3} R M (CommSemiring.toSemiring.{u4} R _inst_1) _inst_2 _inst_5)) q) (Bot.bot.{u2} (Submodule.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4 _inst_7) (Submodule.instBotSubmodule.{u4, u2} R P (CommSemiring.toSemiring.{u4} R _inst_1) _inst_4 _inst_7))
Case conversion may be inaccurate. Consider using '#align submodule.map₂_bot_left Submodule.map₂_bot_leftₓ'. -/
@[simp]
theorem map₂_bot_left (f : M →ₗ[R] N →ₗ[R] P) (q : Submodule R N) : map₂ f ⊥ q = ⊥ :=
  eq_bot_iff.2 <|
    map₂_le.2 fun m hm n hn => by rw [Submodule.mem_bot] at hm⊢; rw [hm, LinearMap.map_zero₂]
#align submodule.map₂_bot_left Submodule.map₂_bot_left

/- warning: submodule.map₂_le_map₂ -> Submodule.map₂_le_map₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_le_map₂ Submodule.map₂_le_map₂ₓ'. -/
@[mono]
theorem map₂_le_map₂ {f : M →ₗ[R] N →ₗ[R] P} {p₁ p₂ : Submodule R M} {q₁ q₂ : Submodule R N}
    (hp : p₁ ≤ p₂) (hq : q₁ ≤ q₂) : map₂ f p₁ q₁ ≤ map₂ f p₂ q₂ :=
  map₂_le.2 fun m hm n hn => apply_mem_map₂ _ (hp hm) (hq hn)
#align submodule.map₂_le_map₂ Submodule.map₂_le_map₂

/- warning: submodule.map₂_le_map₂_left -> Submodule.map₂_le_map₂_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_le_map₂_left Submodule.map₂_le_map₂_leftₓ'. -/
theorem map₂_le_map₂_left {f : M →ₗ[R] N →ₗ[R] P} {p₁ p₂ : Submodule R M} {q : Submodule R N}
    (h : p₁ ≤ p₂) : map₂ f p₁ q ≤ map₂ f p₂ q :=
  map₂_le_map₂ h (le_refl q)
#align submodule.map₂_le_map₂_left Submodule.map₂_le_map₂_left

/- warning: submodule.map₂_le_map₂_right -> Submodule.map₂_le_map₂_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_le_map₂_right Submodule.map₂_le_map₂_rightₓ'. -/
theorem map₂_le_map₂_right {f : M →ₗ[R] N →ₗ[R] P} {p : Submodule R M} {q₁ q₂ : Submodule R N}
    (h : q₁ ≤ q₂) : map₂ f p q₁ ≤ map₂ f p q₂ :=
  map₂_le_map₂ (le_refl p) h
#align submodule.map₂_le_map₂_right Submodule.map₂_le_map₂_right

/- warning: submodule.map₂_sup_right -> Submodule.map₂_sup_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_sup_right Submodule.map₂_sup_rightₓ'. -/
theorem map₂_sup_right (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q₁ q₂ : Submodule R N) :
    map₂ f p (q₁ ⊔ q₂) = map₂ f p q₁ ⊔ map₂ f p q₂ :=
  le_antisymm
    (map₂_le.2 fun m hm np hnp =>
      let ⟨n, hn, p, hp, hnp⟩ := mem_sup.1 hnp
      mem_sup.2 ⟨_, apply_mem_map₂ _ hm hn, _, apply_mem_map₂ _ hm hp, hnp ▸ (map_add _ _ _).symm⟩)
    (sup_le (map₂_le_map₂_right le_sup_left) (map₂_le_map₂_right le_sup_right))
#align submodule.map₂_sup_right Submodule.map₂_sup_right

/- warning: submodule.map₂_sup_left -> Submodule.map₂_sup_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_sup_left Submodule.map₂_sup_leftₓ'. -/
theorem map₂_sup_left (f : M →ₗ[R] N →ₗ[R] P) (p₁ p₂ : Submodule R M) (q : Submodule R N) :
    map₂ f (p₁ ⊔ p₂) q = map₂ f p₁ q ⊔ map₂ f p₂ q :=
  le_antisymm
    (map₂_le.2 fun mn hmn p hp =>
      let ⟨m, hm, n, hn, hmn⟩ := mem_sup.1 hmn
      mem_sup.2
        ⟨_, apply_mem_map₂ _ hm hp, _, apply_mem_map₂ _ hn hp,
          hmn ▸ (LinearMap.map_add₂ _ _ _ _).symm⟩)
    (sup_le (map₂_le_map₂_left le_sup_left) (map₂_le_map₂_left le_sup_right))
#align submodule.map₂_sup_left Submodule.map₂_sup_left

/- warning: submodule.image2_subset_map₂ -> Submodule.image2_subset_map₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.image2_subset_map₂ Submodule.image2_subset_map₂ₓ'. -/
theorem image2_subset_map₂ (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    Set.image2 (fun m n => f m n) (↑p : Set M) (↑q : Set N) ⊆ (↑(map₂ f p q) : Set P) := by
  rintro _ ⟨i, j, hi, hj, rfl⟩; exact apply_mem_map₂ _ hi hj
#align submodule.image2_subset_map₂ Submodule.image2_subset_map₂

/- warning: submodule.map₂_eq_span_image2 -> Submodule.map₂_eq_span_image2 is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_eq_span_image2 Submodule.map₂_eq_span_image2ₓ'. -/
theorem map₂_eq_span_image2 (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    map₂ f p q = span R (Set.image2 (fun m n => f m n) (p : Set M) (q : Set N)) := by
  rw [← map₂_span_span, span_eq, span_eq]
#align submodule.map₂_eq_span_image2 Submodule.map₂_eq_span_image2

/- warning: submodule.map₂_flip -> Submodule.map₂_flip is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_flip Submodule.map₂_flipₓ'. -/
theorem map₂_flip (f : M →ₗ[R] N →ₗ[R] P) (p : Submodule R M) (q : Submodule R N) :
    map₂ f.flip q p = map₂ f p q := by
  rw [map₂_eq_span_image2, map₂_eq_span_image2, Set.image2_swap]; rfl
#align submodule.map₂_flip Submodule.map₂_flip

/- warning: submodule.map₂_supr_left -> Submodule.map₂_iSup_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_supr_left Submodule.map₂_iSup_leftₓ'. -/
theorem map₂_iSup_left (f : M →ₗ[R] N →ₗ[R] P) (s : ι → Submodule R M) (t : Submodule R N) :
    map₂ f (⨆ i, s i) t = ⨆ i, map₂ f (s i) t :=
  by
  suffices map₂ f (⨆ i, span R (s i : Set M)) (span R t) = ⨆ i, map₂ f (span R (s i)) (span R t) by
    simpa only [span_eq] using this
  simp_rw [map₂_span_span, ← span_Union, map₂_span_span, Set.image2_iUnion_left]
#align submodule.map₂_supr_left Submodule.map₂_iSup_left

/- warning: submodule.map₂_supr_right -> Submodule.map₂_iSup_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_supr_right Submodule.map₂_iSup_rightₓ'. -/
theorem map₂_iSup_right (f : M →ₗ[R] N →ₗ[R] P) (s : Submodule R M) (t : ι → Submodule R N) :
    map₂ f s (⨆ i, t i) = ⨆ i, map₂ f s (t i) :=
  by
  suffices map₂ f (span R s) (⨆ i, span R (t i : Set N)) = ⨆ i, map₂ f (span R s) (span R (t i)) by
    simpa only [span_eq] using this
  simp_rw [map₂_span_span, ← span_Union, map₂_span_span, Set.image2_iUnion_right]
#align submodule.map₂_supr_right Submodule.map₂_iSup_right

/- warning: submodule.map₂_span_singleton_eq_map -> Submodule.map₂_span_singleton_eq_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_span_singleton_eq_map Submodule.map₂_span_singleton_eq_mapₓ'. -/
theorem map₂_span_singleton_eq_map (f : M →ₗ[R] N →ₗ[R] P) (m : M) :
    map₂ f (span R {m}) = map (f m) := by
  funext; rw [map₂_eq_span_image2]; apply le_antisymm
  · rw [span_le, Set.image2_subset_iff]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := mem_span_singleton.1 hx
    rw [f.map_smul]
    exact smul_mem _ a (mem_map_of_mem hy)
  · rintro _ ⟨n, hn, rfl⟩
    exact subset_span ⟨m, n, mem_span_singleton_self m, hn, rfl⟩
#align submodule.map₂_span_singleton_eq_map Submodule.map₂_span_singleton_eq_map

/- warning: submodule.map₂_span_singleton_eq_map_flip -> Submodule.map₂_span_singleton_eq_map_flip is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.map₂_span_singleton_eq_map_flip Submodule.map₂_span_singleton_eq_map_flipₓ'. -/
theorem map₂_span_singleton_eq_map_flip (f : M →ₗ[R] N →ₗ[R] P) (s : Submodule R M) (n : N) :
    map₂ f s (span R {n}) = map (f.flip n) s := by rw [← map₂_span_singleton_eq_map, map₂_flip]
#align submodule.map₂_span_singleton_eq_map_flip Submodule.map₂_span_singleton_eq_map_flip

end Submodule

