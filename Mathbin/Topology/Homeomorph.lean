/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton

! This file was ported from Lean 3 source module topology.homeomorph
! leanprover-community/mathlib commit 3b267e70a936eebb21ab546f49a8df34dd300b25
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Fin
import Mathbin.Topology.DenseEmbedding
import Mathbin.Topology.Support

/-!
# Homeomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

# Main definitions

* `homeomorph α β`: The type of homeomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ₜ β`.

# Main results

* Pretty much every topological property is preserved under homeomorphisms.
* `homeomorph.homeomorph_of_continuous_open`: A continuous bijection that is
  an open map is a homeomorphism.

-/


open Set Filter

open Topology

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

#print Homeomorph /-
-- not all spaces are homeomorphic to each other
/-- Homeomorphism between `α` and `β`, also called topological isomorphism -/
@[nolint has_nonempty_instance]
structure Homeomorph (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] extends
  α ≃ β where
  continuous_toFun : Continuous to_fun := by continuity
  continuous_invFun : Continuous inv_fun := by continuity
#align homeomorph Homeomorph
-/

-- mathport name: «expr ≃ₜ »
infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

instance : CoeFun (α ≃ₜ β) fun _ => α → β :=
  ⟨fun e => e.toEquiv⟩

/- warning: homeomorph.homeomorph_mk_coe -> Homeomorph.homeomorph_mk_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (a : Equiv.{succ u1, succ u2} α β) (b : autoParamₓ.{0} (Continuous.{u1, u2} α β _inst_1 _inst_2 (Equiv.toFun.{succ u1, succ u2} α β a)) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 39 (OfNat.mk.{0} Nat 39 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)))) (c : autoParamₓ.{0} (Continuous.{u2, u1} β α _inst_2 _inst_1 (Equiv.invFun.{succ u1, succ u2} α β a)) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 39 (OfNat.mk.{0} Nat 39 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)))), Eq.{max (succ u1) (succ u2)} ((fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.mk.{u1, u2} α β _inst_1 _inst_2 a b c)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (Homeomorph.mk.{u1, u2} α β _inst_1 _inst_2 a b c)) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (a : Equiv.{succ u2, succ u1} α β) (b : Continuous.{u2, u1} α β _inst_1 _inst_2 (Equiv.toFun.{succ u2, succ u1} α β a)) (c : Continuous.{u1, u2} β α _inst_2 _inst_1 (Equiv.invFun.{succ u2, succ u1} α β a)), Eq.{max (succ u2) (succ u1)} (α -> β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) (Homeomorph.mk.{u2, u1} α β _inst_1 _inst_2 a b c)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) a)
Case conversion may be inaccurate. Consider using '#align homeomorph.homeomorph_mk_coe Homeomorph.homeomorph_mk_coeₓ'. -/
@[simp]
theorem homeomorph_mk_coe (a : Equiv α β) (b c) : (Homeomorph.mk a b c : α → β) = a :=
  rfl
#align homeomorph.homeomorph_mk_coe Homeomorph.homeomorph_mk_coe

#print Homeomorph.symm /-
/-- Inverse of a homeomorphism. -/
protected def symm (h : α ≃ₜ β) : β ≃ₜ α
    where
  continuous_toFun := h.continuous_invFun
  continuous_invFun := h.continuous_toFun
  toEquiv := h.toEquiv.symm
#align homeomorph.symm Homeomorph.symm
-/

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ₜ β) : α → β :=
  h
#align homeomorph.simps.apply Homeomorph.Simps.apply

#print Homeomorph.Simps.symm_apply /-
/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ₜ β) : β → α :=
  h.symm
#align homeomorph.simps.symm_apply Homeomorph.Simps.symm_apply
-/

initialize_simps_projections Homeomorph (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply,
  -toEquiv)

/- warning: homeomorph.coe_to_equiv -> Homeomorph.coe_toEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) (Homeomorph.toEquiv.{u1, u2} α β _inst_1 _inst_2 h)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) (Homeomorph.toEquiv.{u2, u1} α β _inst_1 _inst_2 h)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_to_equiv Homeomorph.coe_toEquivₓ'. -/
@[simp]
theorem coe_toEquiv (h : α ≃ₜ β) : ⇑h.toEquiv = h :=
  rfl
#align homeomorph.coe_to_equiv Homeomorph.coe_toEquiv

/- warning: homeomorph.coe_symm_to_equiv -> Homeomorph.coe_symm_toEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (β -> α) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β (Homeomorph.toEquiv.{u1, u2} α β _inst_1 _inst_2 h))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : β), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β (Homeomorph.toEquiv.{u2, u1} α β _inst_1 _inst_2 h))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h))
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_symm_to_equiv Homeomorph.coe_symm_toEquivₓ'. -/
@[simp]
theorem coe_symm_toEquiv (h : α ≃ₜ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl
#align homeomorph.coe_symm_to_equiv Homeomorph.coe_symm_toEquiv

/- warning: homeomorph.to_equiv_injective -> Homeomorph.toEquiv_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Function.Injective.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (Equiv.{succ u1, succ u2} α β) (Homeomorph.toEquiv.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) (Equiv.{succ u2, succ u1} α β) (Homeomorph.toEquiv.{u2, u1} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.to_equiv_injective Homeomorph.toEquiv_injectiveₓ'. -/
theorem toEquiv_injective : Function.Injective (toEquiv : α ≃ₜ β → α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, rfl => rfl
#align homeomorph.to_equiv_injective Homeomorph.toEquiv_injective

/- warning: homeomorph.ext -> Homeomorph.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {h : Homeomorph.{u1, u2} α β _inst_1 _inst_2} {h' : Homeomorph.{u1, u2} α β _inst_1 _inst_2}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h' x)) -> (Eq.{max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) h h')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {h : Homeomorph.{u2, u1} α β _inst_1 _inst_2} {h' : Homeomorph.{u2, u1} α β _inst_1 _inst_2}, (forall (x : α), Eq.{succ u1} β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h' x)) -> (Eq.{max (succ u2) (succ u1)} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) h h')
Case conversion may be inaccurate. Consider using '#align homeomorph.ext Homeomorph.extₓ'. -/
@[ext]
theorem ext {h h' : α ≃ₜ β} (H : ∀ x, h x = h' x) : h = h' :=
  toEquiv_injective <| Equiv.ext H
#align homeomorph.ext Homeomorph.ext

/- warning: homeomorph.symm_symm -> Homeomorph.symm_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (Homeomorph.symm.{u2, u1} β α _inst_2 _inst_1 (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h)) h
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) (Homeomorph.symm.{u1, u2} β α _inst_2 _inst_1 (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h)) h
Case conversion may be inaccurate. Consider using '#align homeomorph.symm_symm Homeomorph.symm_symmₓ'. -/
@[simp]
theorem symm_symm (h : α ≃ₜ β) : h.symm.symm = h :=
  ext fun _ => rfl
#align homeomorph.symm_symm Homeomorph.symm_symm

#print Homeomorph.refl /-
/-- Identity map as a homeomorphism. -/
@[simps (config := { fullyApplied := false }) apply]
protected def refl (α : Type _) [TopologicalSpace α] : α ≃ₜ α
    where
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id
  toEquiv := Equiv.refl α
#align homeomorph.refl Homeomorph.refl
-/

#print Homeomorph.trans /-
/-- Composition of two homeomorphisms. -/
protected def trans (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ
    where
  continuous_toFun := h₂.continuous_toFun.comp h₁.continuous_toFun
  continuous_invFun := h₁.continuous_invFun.comp h₂.continuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
#align homeomorph.trans Homeomorph.trans
-/

/- warning: homeomorph.trans_apply -> Homeomorph.trans_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h₁ : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (h₂ : Homeomorph.{u2, u3} β γ _inst_2 _inst_3) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (Homeomorph.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : Homeomorph.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (Homeomorph.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (Homeomorph.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 h₁ h₂) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (Homeomorph.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : Homeomorph.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (Homeomorph.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) h₂ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h₁ a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h₁ : Homeomorph.{u3, u2} α β _inst_1 _inst_2) (h₂ : Homeomorph.{u2, u1} β γ _inst_2 _inst_3) (a : α), Eq.{succ u1} γ (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (Homeomorph.{u3, u1} α γ _inst_1 _inst_3) α (fun (_x : α) => γ) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (Homeomorph.{u3, u1} α γ _inst_1 _inst_3) α γ (EquivLike.toEmbeddingLike.{max (succ u3) (succ u1), succ u3, succ u1} (Homeomorph.{u3, u1} α γ _inst_1 _inst_3) α γ (Homeomorph.instEquivLikeHomeomorph.{u3, u1} α γ _inst_1 _inst_3))) (Homeomorph.trans.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 h₁ h₂) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} β γ _inst_2 _inst_3) β (fun (_x : β) => γ) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} β γ _inst_2 _inst_3) β γ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} β γ _inst_2 _inst_3) β γ (Homeomorph.instEquivLikeHomeomorph.{u2, u1} β γ _inst_2 _inst_3))) h₂ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h₁ a))
Case conversion may be inaccurate. Consider using '#align homeomorph.trans_apply Homeomorph.trans_applyₓ'. -/
@[simp]
theorem trans_apply (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl
#align homeomorph.trans_apply Homeomorph.trans_apply

/- warning: homeomorph.homeomorph_mk_coe_symm -> Homeomorph.homeomorph_mk_coe_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (a : Equiv.{succ u1, succ u2} α β) (b : autoParamₓ.{0} (Continuous.{u1, u2} α β _inst_1 _inst_2 (Equiv.toFun.{succ u1, succ u2} α β a)) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 39 (OfNat.mk.{0} Nat 39 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)))) (c : autoParamₓ.{0} (Continuous.{u2, u1} β α _inst_2 _inst_1 (Equiv.invFun.{succ u1, succ u2} α β a)) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 111 (OfNat.mk.{0} Nat 111 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 117 (OfNat.mk.{0} Nat 117 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 121 (OfNat.mk.{0} Nat 121 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 39 (OfNat.mk.{0} Nat 39 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 110 (OfNat.mk.{0} Nat 110 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 114 (OfNat.mk.{0} Nat 114 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 118 (OfNat.mk.{0} Nat 118 (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 101 (OfNat.mk.{0} Nat 101 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Name.mk_string (String.str (String.str (String.str (String.str (String.str (String.str String.empty (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 97 (OfNat.mk.{0} Nat 97 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 116 (OfNat.mk.{0} Nat 116 (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 105 (OfNat.mk.{0} Nat 105 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) (Char.ofNat (OfNat.ofNat.{0} Nat 99 (OfNat.mk.{0} Nat 99 (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit0.{0} Nat Nat.hasAdd (bit1.{0} Nat Nat.hasOne Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))))) Name.anonymous)))), Eq.{max (succ u2) (succ u1)} ((fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 (Homeomorph.mk.{u1, u2} α β _inst_1 _inst_2 a b c))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 (Homeomorph.mk.{u1, u2} α β _inst_1 _inst_2 a b c))) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (a : Equiv.{succ u2, succ u1} α β) (b : Continuous.{u2, u1} α β _inst_1 _inst_2 (Equiv.toFun.{succ u2, succ u1} α β a)) (c : Continuous.{u1, u2} β α _inst_2 _inst_1 (Equiv.invFun.{succ u2, succ u1} α β a)), Eq.{max (succ u2) (succ u1)} (β -> α) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 (Homeomorph.mk.{u2, u1} α β _inst_1 _inst_2 a b c))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β a))
Case conversion may be inaccurate. Consider using '#align homeomorph.homeomorph_mk_coe_symm Homeomorph.homeomorph_mk_coe_symmₓ'. -/
@[simp]
theorem homeomorph_mk_coe_symm (a : Equiv α β) (b c) :
    ((Homeomorph.mk a b c).symm : β → α) = a.symm :=
  rfl
#align homeomorph.homeomorph_mk_coe_symm Homeomorph.homeomorph_mk_coe_symm

#print Homeomorph.refl_symm /-
@[simp]
theorem refl_symm : (Homeomorph.refl α).symm = Homeomorph.refl α :=
  rfl
#align homeomorph.refl_symm Homeomorph.refl_symm
-/

/- warning: homeomorph.continuous -> Homeomorph.continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Continuous.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Continuous.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.continuous Homeomorph.continuousₓ'. -/
@[continuity]
protected theorem continuous (h : α ≃ₜ β) : Continuous h :=
  h.continuous_toFun
#align homeomorph.continuous Homeomorph.continuous

/- warning: homeomorph.continuous_symm -> Homeomorph.continuous_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Continuous.{u2, u1} β α _inst_2 _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Continuous.{u1, u2} β α _inst_2 _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h))
Case conversion may be inaccurate. Consider using '#align homeomorph.continuous_symm Homeomorph.continuous_symmₓ'. -/
-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : α ≃ₜ β) : Continuous h.symm :=
  h.continuous_invFun
#align homeomorph.continuous_symm Homeomorph.continuous_symm

/- warning: homeomorph.apply_symm_apply -> Homeomorph.apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (x : β), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h) x)) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (x : β), Eq.{succ u1} β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h) x)) x
Case conversion may be inaccurate. Consider using '#align homeomorph.apply_symm_apply Homeomorph.apply_symm_applyₓ'. -/
@[simp]
theorem apply_symm_apply (h : α ≃ₜ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x
#align homeomorph.apply_symm_apply Homeomorph.apply_symm_apply

/- warning: homeomorph.symm_apply_apply -> Homeomorph.symm_apply_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h x)) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h x)) x
Case conversion may be inaccurate. Consider using '#align homeomorph.symm_apply_apply Homeomorph.symm_apply_applyₓ'. -/
@[simp]
theorem symm_apply_apply (h : α ≃ₜ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
#align homeomorph.symm_apply_apply Homeomorph.symm_apply_apply

/- warning: homeomorph.self_trans_symm -> Homeomorph.self_trans_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (Homeomorph.{u1, u1} α α _inst_1 _inst_1) (Homeomorph.trans.{u1, u2, u1} α β α _inst_1 _inst_2 _inst_1 h (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h)) (Homeomorph.refl.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (Homeomorph.{u2, u2} α α _inst_1 _inst_1) (Homeomorph.trans.{u2, u1, u2} α β α _inst_1 _inst_2 _inst_1 h (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h)) (Homeomorph.refl.{u2} α _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.self_trans_symm Homeomorph.self_trans_symmₓ'. -/
@[simp]
theorem self_trans_symm (h : α ≃ₜ β) : h.trans h.symm = Homeomorph.refl α :=
  by
  ext
  apply symm_apply_apply
#align homeomorph.self_trans_symm Homeomorph.self_trans_symm

/- warning: homeomorph.symm_trans_self -> Homeomorph.symm_trans_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (Homeomorph.{u2, u2} β β _inst_2 _inst_2) (Homeomorph.trans.{u2, u1, u2} β α β _inst_2 _inst_1 _inst_2 (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h) h) (Homeomorph.refl.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (Homeomorph.{u1, u1} β β _inst_2 _inst_2) (Homeomorph.trans.{u1, u2, u1} β α β _inst_2 _inst_1 _inst_2 (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h) h) (Homeomorph.refl.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.symm_trans_self Homeomorph.symm_trans_selfₓ'. -/
@[simp]
theorem symm_trans_self (h : α ≃ₜ β) : h.symm.trans h = Homeomorph.refl β :=
  by
  ext
  apply apply_symm_apply
#align homeomorph.symm_trans_self Homeomorph.symm_trans_self

/- warning: homeomorph.bijective -> Homeomorph.bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Function.Bijective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Function.Bijective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.bijective Homeomorph.bijectiveₓ'. -/
protected theorem bijective (h : α ≃ₜ β) : Function.Bijective h :=
  h.toEquiv.Bijective
#align homeomorph.bijective Homeomorph.bijective

/- warning: homeomorph.injective -> Homeomorph.injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Function.Injective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Function.Injective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.injective Homeomorph.injectiveₓ'. -/
protected theorem injective (h : α ≃ₜ β) : Function.Injective h :=
  h.toEquiv.Injective
#align homeomorph.injective Homeomorph.injective

/- warning: homeomorph.surjective -> Homeomorph.surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Function.Surjective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.surjective Homeomorph.surjectiveₓ'. -/
protected theorem surjective (h : α ≃ₜ β) : Function.Surjective h :=
  h.toEquiv.Surjective
#align homeomorph.surjective Homeomorph.surjective

/- warning: homeomorph.change_inv -> Homeomorph.changeInv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (g : β -> α), (Function.RightInverse.{succ u1, succ u2} α β g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Homeomorph.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (f : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (g : β -> α), (Function.RightInverse.{succ u1, succ u2} α β g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u1, u2} α β _inst_1 _inst_2))) f)) -> (Homeomorph.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.change_inv Homeomorph.changeInvₓ'. -/
/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : α ≃ₜ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ₜ β :=
  have : g = f.symm :=
    funext fun x =>
      calc
        g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
        _ = f.symm x := by rw [hg x]
        
  { toFun := f
    invFun := g
    left_inv := by convert f.left_inv
    right_inv := by convert f.right_inv
    continuous_toFun := f.Continuous
    continuous_invFun := by convert f.symm.continuous }
#align homeomorph.change_inv Homeomorph.changeInv

/- warning: homeomorph.symm_comp_self -> Homeomorph.symm_comp_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (α -> α) (Function.comp.{succ u1, succ u2, succ u1} α β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)) (id.{succ u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (α -> α) (Function.comp.{succ u2, succ u1, succ u2} α β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)) (id.{succ u2} α)
Case conversion may be inaccurate. Consider using '#align homeomorph.symm_comp_self Homeomorph.symm_comp_selfₓ'. -/
@[simp]
theorem symm_comp_self (h : α ≃ₜ β) : ⇑h.symm ∘ ⇑h = id :=
  funext h.symm_apply_apply
#align homeomorph.symm_comp_self Homeomorph.symm_comp_self

/- warning: homeomorph.self_comp_symm -> Homeomorph.self_comp_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (β -> β) (Function.comp.{succ u2, succ u1, succ u2} β α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h))) (id.{succ u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (β -> β) (Function.comp.{succ u1, succ u2, succ u1} β α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h))) (id.{succ u1} β)
Case conversion may be inaccurate. Consider using '#align homeomorph.self_comp_symm Homeomorph.self_comp_symmₓ'. -/
@[simp]
theorem self_comp_symm (h : α ≃ₜ β) : ⇑h ∘ ⇑h.symm = id :=
  funext h.apply_symm_apply
#align homeomorph.self_comp_symm Homeomorph.self_comp_symm

/- warning: homeomorph.range_coe -> Homeomorph.range_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)) (Set.univ.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)) (Set.univ.{u1} β)
Case conversion may be inaccurate. Consider using '#align homeomorph.range_coe Homeomorph.range_coeₓ'. -/
@[simp]
theorem range_coe (h : α ≃ₜ β) : range h = univ :=
  h.Surjective.range_eq
#align homeomorph.range_coe Homeomorph.range_coe

/- warning: homeomorph.image_symm -> Homeomorph.image_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} ((Set.{u2} β) -> (Set.{u1} α)) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h))) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} ((Set.{u1} β) -> (Set.{u2} α)) (Set.image.{u1, u2} β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h))) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h))
Case conversion may be inaccurate. Consider using '#align homeomorph.image_symm Homeomorph.image_symmₓ'. -/
theorem image_symm (h : α ≃ₜ β) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage
#align homeomorph.image_symm Homeomorph.image_symm

/- warning: homeomorph.preimage_symm -> Homeomorph.preimage_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((Set.{u1} α) -> (Set.{u2} β)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h))) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} ((Set.{u2} α) -> (Set.{u1} β)) (Set.preimage.{u1, u2} β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h))) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h))
Case conversion may be inaccurate. Consider using '#align homeomorph.preimage_symm Homeomorph.preimage_symmₓ'. -/
theorem preimage_symm (h : α ≃ₜ β) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage).symm
#align homeomorph.preimage_symm Homeomorph.preimage_symm

/- warning: homeomorph.image_preimage -> Homeomorph.image_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s)) s
Case conversion may be inaccurate. Consider using '#align homeomorph.image_preimage Homeomorph.image_preimageₓ'. -/
@[simp]
theorem image_preimage (h : α ≃ₜ β) (s : Set β) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s
#align homeomorph.image_preimage Homeomorph.image_preimage

/- warning: homeomorph.preimage_image -> Homeomorph.preimage_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s)) s
Case conversion may be inaccurate. Consider using '#align homeomorph.preimage_image Homeomorph.preimage_imageₓ'. -/
@[simp]
theorem preimage_image (h : α ≃ₜ β) (s : Set α) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s
#align homeomorph.preimage_image Homeomorph.preimage_image

/- warning: homeomorph.inducing -> Homeomorph.inducing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Inducing.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Inducing.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.inducing Homeomorph.inducingₓ'. -/
protected theorem inducing (h : α ≃ₜ β) : Inducing h :=
  inducing_of_inducing_compose h.Continuous h.symm.Continuous <| by
    simp only [symm_comp_self, inducing_id]
#align homeomorph.inducing Homeomorph.inducing

/- warning: homeomorph.induced_eq -> Homeomorph.induced_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (TopologicalSpace.{u1} α) (TopologicalSpace.induced.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) _inst_2) _inst_1
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (TopologicalSpace.{u2} α) (TopologicalSpace.induced.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) _inst_2) _inst_1
Case conversion may be inaccurate. Consider using '#align homeomorph.induced_eq Homeomorph.induced_eqₓ'. -/
theorem induced_eq (h : α ≃ₜ β) : TopologicalSpace.induced h ‹_› = ‹_› :=
  h.Inducing.1.symm
#align homeomorph.induced_eq Homeomorph.induced_eq

/- warning: homeomorph.quotient_map -> Homeomorph.quotientMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), QuotientMap.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), QuotientMap.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.quotient_map Homeomorph.quotientMapₓ'. -/
protected theorem quotientMap (h : α ≃ₜ β) : QuotientMap h :=
  QuotientMap.of_quotientMap_compose h.symm.Continuous h.Continuous <| by
    simp only [self_comp_symm, QuotientMap.id]
#align homeomorph.quotient_map Homeomorph.quotientMap

/- warning: homeomorph.coinduced_eq -> Homeomorph.coinduced_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (TopologicalSpace.{u2} β) (TopologicalSpace.coinduced.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) _inst_1) _inst_2
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (TopologicalSpace.{u1} β) (TopologicalSpace.coinduced.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) _inst_1) _inst_2
Case conversion may be inaccurate. Consider using '#align homeomorph.coinduced_eq Homeomorph.coinduced_eqₓ'. -/
theorem coinduced_eq (h : α ≃ₜ β) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.QuotientMap.2.symm
#align homeomorph.coinduced_eq Homeomorph.coinduced_eq

/- warning: homeomorph.embedding -> Homeomorph.embedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Embedding.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Embedding.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.embedding Homeomorph.embeddingₓ'. -/
protected theorem embedding (h : α ≃ₜ β) : Embedding h :=
  ⟨h.Inducing, h.Injective⟩
#align homeomorph.embedding Homeomorph.embedding

#print Homeomorph.ofEmbedding /-
/-- Homeomorphism given an embedding. -/
noncomputable def ofEmbedding (f : α → β) (hf : Embedding f) : α ≃ₜ Set.range f
    where
  continuous_toFun := hf.Continuous.subtype_mk _
  continuous_invFun := by simp [hf.continuous_iff, continuous_subtype_val]
  toEquiv := Equiv.ofInjective f hf.inj
#align homeomorph.of_embedding Homeomorph.ofEmbedding
-/

#print Homeomorph.secondCountableTopology /-
protected theorem secondCountableTopology [TopologicalSpace.SecondCountableTopology β]
    (h : α ≃ₜ β) : TopologicalSpace.SecondCountableTopology α :=
  h.Inducing.SecondCountableTopology
#align homeomorph.second_countable_topology Homeomorph.secondCountableTopology
-/

/- warning: homeomorph.is_compact_image -> Homeomorph.isCompact_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u1} α} (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Iff (IsCompact.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) (IsCompact.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] {s : Set.{u2} α} (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Iff (IsCompact.{u1} β _inst_2 (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s)) (IsCompact.{u2} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align homeomorph.is_compact_image Homeomorph.isCompact_imageₓ'. -/
theorem isCompact_image {s : Set α} (h : α ≃ₜ β) : IsCompact (h '' s) ↔ IsCompact s :=
  h.Embedding.isCompact_iff_isCompact_image.symm
#align homeomorph.is_compact_image Homeomorph.isCompact_image

/- warning: homeomorph.is_compact_preimage -> Homeomorph.isCompact_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u2} β} (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Iff (IsCompact.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) (IsCompact.{u2} β _inst_2 s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {s : Set.{u2} β} (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Iff (IsCompact.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u1, u2} α β _inst_1 _inst_2))) h) s)) (IsCompact.{u2} β _inst_2 s)
Case conversion may be inaccurate. Consider using '#align homeomorph.is_compact_preimage Homeomorph.isCompact_preimageₓ'. -/
theorem isCompact_preimage {s : Set β} (h : α ≃ₜ β) : IsCompact (h ⁻¹' s) ↔ IsCompact s := by
  rw [← image_symm] <;> exact h.symm.is_compact_image
#align homeomorph.is_compact_preimage Homeomorph.isCompact_preimage

/- warning: homeomorph.comap_cocompact -> Homeomorph.comap_cocompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (Filter.cocompact.{u2} β _inst_2)) (Filter.cocompact.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (Filter.{u2} α) (Filter.comap.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (Filter.cocompact.{u1} β _inst_2)) (Filter.cocompact.{u2} α _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.comap_cocompact Homeomorph.comap_cocompactₓ'. -/
@[simp]
theorem comap_cocompact (h : α ≃ₜ β) : comap h (cocompact β) = cocompact α :=
  (comap_cocompact_le h.Continuous).antisymm <|
    (hasBasis_cocompact.le_basis_iffₓ (hasBasis_cocompact.comap h)).2 fun K hK =>
      ⟨h ⁻¹' K, h.isCompact_preimage.2 hK, Subset.rfl⟩
#align homeomorph.comap_cocompact Homeomorph.comap_cocompact

/- warning: homeomorph.map_cocompact -> Homeomorph.map_cocompact is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (Filter.cocompact.{u1} α _inst_1)) (Filter.cocompact.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (Filter.cocompact.{u2} α _inst_1)) (Filter.cocompact.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.map_cocompact Homeomorph.map_cocompactₓ'. -/
@[simp]
theorem map_cocompact (h : α ≃ₜ β) : map h (cocompact α) = cocompact β := by
  rw [← h.comap_cocompact, map_comap_of_surjective h.surjective]
#align homeomorph.map_cocompact Homeomorph.map_cocompact

/- warning: homeomorph.compact_space -> Homeomorph.compactSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : CompactSpace.{u1} α _inst_1], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (CompactSpace.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : CompactSpace.{u2} α _inst_1], (Homeomorph.{u2, u1} α β _inst_1 _inst_2) -> (CompactSpace.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.compact_space Homeomorph.compactSpaceₓ'. -/
protected theorem compactSpace [CompactSpace α] (h : α ≃ₜ β) : CompactSpace β :=
  {
    isCompact_univ :=
      by
      rw [← image_univ_of_surjective h.surjective, h.is_compact_image]
      apply CompactSpace.isCompact_univ }
#align homeomorph.compact_space Homeomorph.compactSpace

/- warning: homeomorph.t0_space -> Homeomorph.t0Space is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : T0Space.{u1} α _inst_1], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (T0Space.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : T0Space.{u2} α _inst_1], (Homeomorph.{u2, u1} α β _inst_1 _inst_2) -> (T0Space.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.t0_space Homeomorph.t0Spaceₓ'. -/
protected theorem t0Space [T0Space α] (h : α ≃ₜ β) : T0Space β :=
  h.symm.Embedding.T0Space
#align homeomorph.t0_space Homeomorph.t0Space

/- warning: homeomorph.t1_space -> Homeomorph.t1Space is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : T1Space.{u1} α _inst_1], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (T1Space.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : T1Space.{u2} α _inst_1], (Homeomorph.{u2, u1} α β _inst_1 _inst_2) -> (T1Space.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.t1_space Homeomorph.t1Spaceₓ'. -/
protected theorem t1Space [T1Space α] (h : α ≃ₜ β) : T1Space β :=
  h.symm.Embedding.T1Space
#align homeomorph.t1_space Homeomorph.t1Space

/- warning: homeomorph.t2_space -> Homeomorph.t2Space is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : T2Space.{u1} α _inst_1], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (T2Space.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : T2Space.{u2} α _inst_1], (Homeomorph.{u2, u1} α β _inst_1 _inst_2) -> (T2Space.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.t2_space Homeomorph.t2Spaceₓ'. -/
protected theorem t2Space [T2Space α] (h : α ≃ₜ β) : T2Space β :=
  h.symm.Embedding.T2Space
#align homeomorph.t2_space Homeomorph.t2Space

/- warning: homeomorph.t3_space -> Homeomorph.t3Space is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : T3Space.{u1} α _inst_1], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (T3Space.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : T3Space.{u2} α _inst_1], (Homeomorph.{u2, u1} α β _inst_1 _inst_2) -> (T3Space.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.t3_space Homeomorph.t3Spaceₓ'. -/
protected theorem t3Space [T3Space α] (h : α ≃ₜ β) : T3Space β :=
  h.symm.Embedding.T3Space
#align homeomorph.t3_space Homeomorph.t3Space

/- warning: homeomorph.dense_embedding -> Homeomorph.denseEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), DenseEmbedding.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), DenseEmbedding.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.dense_embedding Homeomorph.denseEmbeddingₓ'. -/
protected theorem denseEmbedding (h : α ≃ₜ β) : DenseEmbedding h :=
  { h.Embedding with dense := h.Surjective.DenseRange }
#align homeomorph.dense_embedding Homeomorph.denseEmbedding

/- warning: homeomorph.is_open_preimage -> Homeomorph.isOpen_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β}, Iff (IsOpen.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) (IsOpen.{u2} β _inst_2 s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u1} β}, Iff (IsOpen.{u2} α _inst_1 (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s)) (IsOpen.{u1} β _inst_2 s)
Case conversion may be inaccurate. Consider using '#align homeomorph.is_open_preimage Homeomorph.isOpen_preimageₓ'. -/
@[simp]
theorem isOpen_preimage (h : α ≃ₜ β) {s : Set β} : IsOpen (h ⁻¹' s) ↔ IsOpen s :=
  h.QuotientMap.isOpen_preimage
#align homeomorph.is_open_preimage Homeomorph.isOpen_preimage

/- warning: homeomorph.is_open_image -> Homeomorph.isOpen_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α}, Iff (IsOpen.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) (IsOpen.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α}, Iff (IsOpen.{u1} β _inst_2 (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s)) (IsOpen.{u2} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align homeomorph.is_open_image Homeomorph.isOpen_imageₓ'. -/
@[simp]
theorem isOpen_image (h : α ≃ₜ β) {s : Set α} : IsOpen (h '' s) ↔ IsOpen s := by
  rw [← preimage_symm, is_open_preimage]
#align homeomorph.is_open_image Homeomorph.isOpen_image

/- warning: homeomorph.is_open_map -> Homeomorph.isOpenMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), IsOpenMap.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), IsOpenMap.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.is_open_map Homeomorph.isOpenMapₓ'. -/
protected theorem isOpenMap (h : α ≃ₜ β) : IsOpenMap h := fun s => h.isOpen_image.2
#align homeomorph.is_open_map Homeomorph.isOpenMap

/- warning: homeomorph.is_closed_preimage -> Homeomorph.isClosed_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u2} β}, Iff (IsClosed.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) (IsClosed.{u2} β _inst_2 s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u1} β}, Iff (IsClosed.{u2} α _inst_1 (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s)) (IsClosed.{u1} β _inst_2 s)
Case conversion may be inaccurate. Consider using '#align homeomorph.is_closed_preimage Homeomorph.isClosed_preimageₓ'. -/
@[simp]
theorem isClosed_preimage (h : α ≃ₜ β) {s : Set β} : IsClosed (h ⁻¹' s) ↔ IsClosed s := by
  simp only [← isOpen_compl_iff, ← preimage_compl, is_open_preimage]
#align homeomorph.is_closed_preimage Homeomorph.isClosed_preimage

/- warning: homeomorph.is_closed_image -> Homeomorph.isClosed_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {s : Set.{u1} α}, Iff (IsClosed.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) (IsClosed.{u1} α _inst_1 s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) {s : Set.{u2} α}, Iff (IsClosed.{u1} β _inst_2 (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s)) (IsClosed.{u2} α _inst_1 s)
Case conversion may be inaccurate. Consider using '#align homeomorph.is_closed_image Homeomorph.isClosed_imageₓ'. -/
@[simp]
theorem isClosed_image (h : α ≃ₜ β) {s : Set α} : IsClosed (h '' s) ↔ IsClosed s := by
  rw [← preimage_symm, is_closed_preimage]
#align homeomorph.is_closed_image Homeomorph.isClosed_image

/- warning: homeomorph.is_closed_map -> Homeomorph.isClosedMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), IsClosedMap.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), IsClosedMap.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.is_closed_map Homeomorph.isClosedMapₓ'. -/
protected theorem isClosedMap (h : α ≃ₜ β) : IsClosedMap h := fun s => h.isClosed_image.2
#align homeomorph.is_closed_map Homeomorph.isClosedMap

/- warning: homeomorph.open_embedding -> Homeomorph.openEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), OpenEmbedding.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), OpenEmbedding.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.open_embedding Homeomorph.openEmbeddingₓ'. -/
protected theorem openEmbedding (h : α ≃ₜ β) : OpenEmbedding h :=
  openEmbedding_of_embedding_open h.Embedding h.IsOpenMap
#align homeomorph.open_embedding Homeomorph.openEmbedding

/- warning: homeomorph.closed_embedding -> Homeomorph.closedEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2), ClosedEmbedding.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2), ClosedEmbedding.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align homeomorph.closed_embedding Homeomorph.closedEmbeddingₓ'. -/
protected theorem closedEmbedding (h : α ≃ₜ β) : ClosedEmbedding h :=
  closedEmbedding_of_embedding_closed h.Embedding h.IsClosedMap
#align homeomorph.closed_embedding Homeomorph.closedEmbedding

/- warning: homeomorph.normal_space -> Homeomorph.normalSpace is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_5 : NormalSpace.{u1} α _inst_1], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (NormalSpace.{u2} β _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_5 : NormalSpace.{u2} α _inst_1], (Homeomorph.{u2, u1} α β _inst_1 _inst_2) -> (NormalSpace.{u1} β _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.normal_space Homeomorph.normalSpaceₓ'. -/
protected theorem normalSpace [NormalSpace α] (h : α ≃ₜ β) : NormalSpace β :=
  h.symm.ClosedEmbedding.NormalSpace
#align homeomorph.normal_space Homeomorph.normalSpace

/- warning: homeomorph.preimage_closure -> Homeomorph.preimage_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (closure.{u2} β _inst_2 s)) (closure.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (closure.{u1} β _inst_2 s)) (closure.{u2} α _inst_1 (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s))
Case conversion may be inaccurate. Consider using '#align homeomorph.preimage_closure Homeomorph.preimage_closureₓ'. -/
theorem preimage_closure (h : α ≃ₜ β) (s : Set β) : h ⁻¹' closure s = closure (h ⁻¹' s) :=
  h.IsOpenMap.preimage_closure_eq_closure_preimage h.Continuous _
#align homeomorph.preimage_closure Homeomorph.preimage_closure

/- warning: homeomorph.image_closure -> Homeomorph.image_closure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (closure.{u1} α _inst_1 s)) (closure.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (closure.{u2} α _inst_1 s)) (closure.{u1} β _inst_2 (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s))
Case conversion may be inaccurate. Consider using '#align homeomorph.image_closure Homeomorph.image_closureₓ'. -/
theorem image_closure (h : α ≃ₜ β) (s : Set α) : h '' closure s = closure (h '' s) := by
  rw [← preimage_symm, preimage_closure]
#align homeomorph.image_closure Homeomorph.image_closure

/- warning: homeomorph.preimage_interior -> Homeomorph.preimage_interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (interior.{u2} β _inst_2 s)) (interior.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (interior.{u1} β _inst_2 s)) (interior.{u2} α _inst_1 (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s))
Case conversion may be inaccurate. Consider using '#align homeomorph.preimage_interior Homeomorph.preimage_interiorₓ'. -/
theorem preimage_interior (h : α ≃ₜ β) (s : Set β) : h ⁻¹' interior s = interior (h ⁻¹' s) :=
  h.IsOpenMap.preimage_interior_eq_interior_preimage h.Continuous _
#align homeomorph.preimage_interior Homeomorph.preimage_interior

/- warning: homeomorph.image_interior -> Homeomorph.image_interior is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (interior.{u1} α _inst_1 s)) (interior.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (interior.{u2} α _inst_1 s)) (interior.{u1} β _inst_2 (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s))
Case conversion may be inaccurate. Consider using '#align homeomorph.image_interior Homeomorph.image_interiorₓ'. -/
theorem image_interior (h : α ≃ₜ β) (s : Set α) : h '' interior s = interior (h '' s) := by
  rw [← preimage_symm, preimage_interior]
#align homeomorph.image_interior Homeomorph.image_interior

/- warning: homeomorph.preimage_frontier -> Homeomorph.preimage_frontier is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (frontier.{u2} β _inst_2 s)) (frontier.{u1} α _inst_1 (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (frontier.{u1} β _inst_2 s)) (frontier.{u2} α _inst_1 (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s))
Case conversion may be inaccurate. Consider using '#align homeomorph.preimage_frontier Homeomorph.preimage_frontierₓ'. -/
theorem preimage_frontier (h : α ≃ₜ β) (s : Set β) : h ⁻¹' frontier s = frontier (h ⁻¹' s) :=
  h.IsOpenMap.preimage_frontier_eq_frontier_preimage h.Continuous _
#align homeomorph.preimage_frontier Homeomorph.preimage_frontier

/- warning: homeomorph.image_frontier -> Homeomorph.image_frontier is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (frontier.{u1} α _inst_1 s)) (frontier.{u2} β _inst_2 (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (frontier.{u2} α _inst_1 s)) (frontier.{u1} β _inst_2 (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) s))
Case conversion may be inaccurate. Consider using '#align homeomorph.image_frontier Homeomorph.image_frontierₓ'. -/
theorem image_frontier (h : α ≃ₜ β) (s : Set α) : h '' frontier s = frontier (h '' s) := by
  rw [← preimage_symm, preimage_frontier]
#align homeomorph.image_frontier Homeomorph.image_frontier

/- warning: has_compact_mul_support.comp_homeomorph -> HasCompactMulSupport.comp_homeomorph is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {M : Type.{u3}} [_inst_5 : One.{u3} M] {f : β -> M}, (HasCompactMulSupport.{u2, u3} β M _inst_2 _inst_5 f) -> (forall (φ : Homeomorph.{u1, u2} α β _inst_1 _inst_2), HasCompactMulSupport.{u1, u3} α M _inst_1 _inst_5 (Function.comp.{succ u1, succ u2, succ u3} α β M f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) φ)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] {M : Type.{u3}} [_inst_5 : One.{u3} M] {f : β -> M}, (HasCompactMulSupport.{u2, u3} β M _inst_2 _inst_5 f) -> (forall (φ : Homeomorph.{u1, u2} α β _inst_1 _inst_2), HasCompactMulSupport.{u1, u3} α M _inst_1 _inst_5 (Function.comp.{succ u1, succ u2, succ u3} α β M f (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u1, u2} α β _inst_1 _inst_2))) φ)))
Case conversion may be inaccurate. Consider using '#align has_compact_mul_support.comp_homeomorph HasCompactMulSupport.comp_homeomorphₓ'. -/
@[to_additive]
theorem HasCompactMulSupport.comp_homeomorph {M} [One M] {f : β → M} (hf : HasCompactMulSupport f)
    (φ : α ≃ₜ β) : HasCompactMulSupport (f ∘ φ) :=
  hf.comp_closedEmbedding φ.ClosedEmbedding
#align has_compact_mul_support.comp_homeomorph HasCompactMulSupport.comp_homeomorph
#align has_compact_support.comp_homeomorph HasCompactSupport.comp_homeomorph

/- warning: homeomorph.map_nhds_eq -> Homeomorph.map_nhds_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} (Filter.{u2} β) (Filter.map.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (nhds.{u1} α _inst_1 x)) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (x : α), Eq.{succ u1} (Filter.{u1} β) (Filter.map.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (nhds.{u2} α _inst_1 x)) (nhds.{u1} β _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h x))
Case conversion may be inaccurate. Consider using '#align homeomorph.map_nhds_eq Homeomorph.map_nhds_eqₓ'. -/
@[simp]
theorem map_nhds_eq (h : α ≃ₜ β) (x : α) : map h (𝓝 x) = 𝓝 (h x) :=
  h.Embedding.map_nhds_of_mem _ (by simp)
#align homeomorph.map_nhds_eq Homeomorph.map_nhds_eq

/- warning: homeomorph.symm_map_nhds_eq -> Homeomorph.symm_map_nhds_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u1} (Filter.{u1} α) (Filter.map.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h)) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h x))) (nhds.{u1} α _inst_1 x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} (Filter.{u2} α) (Filter.map.{u1, u2} β α (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h)) (nhds.{u1} β _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h x))) (nhds.{u2} α _inst_1 x)
Case conversion may be inaccurate. Consider using '#align homeomorph.symm_map_nhds_eq Homeomorph.symm_map_nhds_eqₓ'. -/
theorem symm_map_nhds_eq (h : α ≃ₜ β) (x : α) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  rw [h.symm.map_nhds_eq, h.symm_apply_apply]
#align homeomorph.symm_map_nhds_eq Homeomorph.symm_map_nhds_eq

/- warning: homeomorph.nhds_eq_comap -> Homeomorph.nhds_eq_comap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u1} (Filter.{u1} α) (nhds.{u1} α _inst_1 x) (Filter.comap.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (nhds.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h x)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} (Filter.{u2} α) (nhds.{u2} α _inst_1 x) (Filter.comap.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (nhds.{u1} β _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h x)))
Case conversion may be inaccurate. Consider using '#align homeomorph.nhds_eq_comap Homeomorph.nhds_eq_comapₓ'. -/
theorem nhds_eq_comap (h : α ≃ₜ β) (x : α) : 𝓝 x = comap h (𝓝 (h x)) :=
  h.Embedding.to_inducing.nhds_eq_comap x
#align homeomorph.nhds_eq_comap Homeomorph.nhds_eq_comap

/- warning: homeomorph.comap_nhds_eq -> Homeomorph.comap_nhds_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (y : β), Eq.{succ u1} (Filter.{u1} α) (Filter.comap.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (nhds.{u2} β _inst_2 y)) (nhds.{u1} α _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (Homeomorph.{u2, u1} β α _inst_2 _inst_1) (fun (_x : Homeomorph.{u2, u1} β α _inst_2 _inst_1) => β -> α) (Homeomorph.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h) y))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] (h : Homeomorph.{u2, u1} α β _inst_1 _inst_2) (y : β), Eq.{succ u2} (Filter.{u2} α) (Filter.comap.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u2, u1} α β _inst_1 _inst_2))) h) (nhds.{u1} β _inst_2 y)) (nhds.{u2} α _inst_1 (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => α) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} β α _inst_2 _inst_1) β α (Homeomorph.instEquivLikeHomeomorph.{u1, u2} β α _inst_2 _inst_1))) (Homeomorph.symm.{u2, u1} α β _inst_1 _inst_2 h) y))
Case conversion may be inaccurate. Consider using '#align homeomorph.comap_nhds_eq Homeomorph.comap_nhds_eqₓ'. -/
@[simp]
theorem comap_nhds_eq (h : α ≃ₜ β) (y : β) : comap h (𝓝 y) = 𝓝 (h.symm y) := by
  rw [h.nhds_eq_comap, h.apply_symm_apply]
#align homeomorph.comap_nhds_eq Homeomorph.comap_nhds_eq

#print Homeomorph.homeomorphOfContinuousOpen /-
/-- If an bijective map `e : α ≃ β` is continuous and open, then it is a homeomorphism. -/
def homeomorphOfContinuousOpen (e : α ≃ β) (h₁ : Continuous e) (h₂ : IsOpenMap e) : α ≃ₜ β
    where
  continuous_toFun := h₁
  continuous_invFun := by
    rw [continuous_def]
    intro s hs
    convert← h₂ s hs using 1
    apply e.image_eq_preimage
  toEquiv := e
#align homeomorph.homeomorph_of_continuous_open Homeomorph.homeomorphOfContinuousOpen
-/

/- warning: homeomorph.comp_continuous_on_iff -> Homeomorph.comp_continuousOn_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (f : γ -> α) (s : Set.{u3} γ), Iff (ContinuousOn.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) f) s) (ContinuousOn.{u3, u1} γ α _inst_3 _inst_1 f s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h : Homeomorph.{u3, u2} α β _inst_1 _inst_2) (f : γ -> α) (s : Set.{u1} γ), Iff (ContinuousOn.{u1, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u3, succ u2} γ α β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h) f) s) (ContinuousOn.{u1, u3} γ α _inst_3 _inst_1 f s)
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_continuous_on_iff Homeomorph.comp_continuousOn_iffₓ'. -/
@[simp]
theorem comp_continuousOn_iff (h : α ≃ₜ β) (f : γ → α) (s : Set γ) :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.Inducing.continuousOn_iff.symm
#align homeomorph.comp_continuous_on_iff Homeomorph.comp_continuousOn_iff

/- warning: homeomorph.comp_continuous_iff -> Homeomorph.comp_continuous_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {f : γ -> α}, Iff (Continuous.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) f)) (Continuous.{u3, u1} γ α _inst_3 _inst_1 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h : Homeomorph.{u3, u2} α β _inst_1 _inst_2) {f : γ -> α}, Iff (Continuous.{u1, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u3, succ u2} γ α β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h) f)) (Continuous.{u1, u3} γ α _inst_3 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_continuous_iff Homeomorph.comp_continuous_iffₓ'. -/
@[simp]
theorem comp_continuous_iff (h : α ≃ₜ β) {f : γ → α} : Continuous (h ∘ f) ↔ Continuous f :=
  h.Inducing.continuous_iff.symm
#align homeomorph.comp_continuous_iff Homeomorph.comp_continuous_iff

/- warning: homeomorph.comp_continuous_iff' -> Homeomorph.comp_continuous_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {f : β -> γ}, Iff (Continuous.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h))) (Continuous.{u2, u3} β γ _inst_2 _inst_3 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h : Homeomorph.{u3, u2} α β _inst_1 _inst_2) {f : β -> γ}, Iff (Continuous.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h))) (Continuous.{u2, u1} β γ _inst_2 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_continuous_iff' Homeomorph.comp_continuous_iff'ₓ'. -/
@[simp]
theorem comp_continuous_iff' (h : α ≃ₜ β) {f : β → γ} : Continuous (f ∘ h) ↔ Continuous f :=
  h.QuotientMap.continuous_iff.symm
#align homeomorph.comp_continuous_iff' Homeomorph.comp_continuous_iff'

/- warning: homeomorph.comp_continuous_at_iff -> Homeomorph.comp_continuousAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (f : γ -> α) (x : γ), Iff (ContinuousAt.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) f) x) (ContinuousAt.{u3, u1} γ α _inst_3 _inst_1 f x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h : Homeomorph.{u3, u2} α β _inst_1 _inst_2) (f : γ -> α) (x : γ), Iff (ContinuousAt.{u1, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u3, succ u2} γ α β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h) f) x) (ContinuousAt.{u1, u3} γ α _inst_3 _inst_1 f x)
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_continuous_at_iff Homeomorph.comp_continuousAt_iffₓ'. -/
theorem comp_continuousAt_iff (h : α ≃ₜ β) (f : γ → α) (x : γ) :
    ContinuousAt (h ∘ f) x ↔ ContinuousAt f x :=
  h.Inducing.continuousAt_iff.symm
#align homeomorph.comp_continuous_at_iff Homeomorph.comp_continuousAt_iff

/- warning: homeomorph.comp_continuous_at_iff' -> Homeomorph.comp_continuousAt_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (f : β -> γ) (x : α), Iff (ContinuousAt.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)) x) (ContinuousAt.{u2, u3} β γ _inst_2 _inst_3 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h x))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h : Homeomorph.{u3, u2} α β _inst_1 _inst_2) (f : β -> γ) (x : α), Iff (ContinuousAt.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h)) x) (ContinuousAt.{u2, u1} β γ _inst_2 _inst_3 f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h x))
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_continuous_at_iff' Homeomorph.comp_continuousAt_iff'ₓ'. -/
theorem comp_continuousAt_iff' (h : α ≃ₜ β) (f : β → γ) (x : α) :
    ContinuousAt (f ∘ h) x ↔ ContinuousAt f (h x) :=
  h.Inducing.continuousAt_iff' (by simp)
#align homeomorph.comp_continuous_at_iff' Homeomorph.comp_continuousAt_iff'

/- warning: homeomorph.comp_continuous_within_at_iff -> Homeomorph.comp_continuousWithinAt_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (f : γ -> α) (s : Set.{u3} γ) (x : γ), Iff (ContinuousWithinAt.{u3, u1} γ α _inst_3 _inst_1 f s x) (ContinuousWithinAt.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) f) s x)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h : Homeomorph.{u3, u2} α β _inst_1 _inst_2) (f : γ -> α) (s : Set.{u1} γ) (x : γ), Iff (ContinuousWithinAt.{u1, u3} γ α _inst_3 _inst_1 f s x) (ContinuousWithinAt.{u1, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u3, succ u2} γ α β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h) f) s x)
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_continuous_within_at_iff Homeomorph.comp_continuousWithinAt_iffₓ'. -/
theorem comp_continuousWithinAt_iff (h : α ≃ₜ β) (f : γ → α) (s : Set γ) (x : γ) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (h ∘ f) s x :=
  h.Inducing.continuousWithinAt_iff
#align homeomorph.comp_continuous_within_at_iff Homeomorph.comp_continuousWithinAt_iff

/- warning: homeomorph.comp_is_open_map_iff -> Homeomorph.comp_isOpenMap_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {f : γ -> α}, Iff (IsOpenMap.{u3, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u3, succ u1, succ u2} γ α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) f)) (IsOpenMap.{u3, u1} γ α _inst_3 _inst_1 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h : Homeomorph.{u3, u2} α β _inst_1 _inst_2) {f : γ -> α}, Iff (IsOpenMap.{u1, u2} γ β _inst_3 _inst_2 (Function.comp.{succ u1, succ u3, succ u2} γ α β (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h) f)) (IsOpenMap.{u1, u3} γ α _inst_3 _inst_1 f)
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_is_open_map_iff Homeomorph.comp_isOpenMap_iffₓ'. -/
@[simp]
theorem comp_isOpenMap_iff (h : α ≃ₜ β) {f : γ → α} : IsOpenMap (h ∘ f) ↔ IsOpenMap f :=
  by
  refine' ⟨_, fun hf => h.is_open_map.comp hf⟩
  intro hf
  rw [← Function.comp.left_id f, ← h.symm_comp_self, Function.comp.assoc]
  exact h.symm.is_open_map.comp hf
#align homeomorph.comp_is_open_map_iff Homeomorph.comp_isOpenMap_iff

/- warning: homeomorph.comp_is_open_map_iff' -> Homeomorph.comp_isOpenMap_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] (h : Homeomorph.{u1, u2} α β _inst_1 _inst_2) {f : β -> γ}, Iff (IsOpenMap.{u1, u3} α γ _inst_1 _inst_3 (Function.comp.{succ u1, succ u2, succ u3} α β γ f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h))) (IsOpenMap.{u2, u3} β γ _inst_2 _inst_3 f)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : TopologicalSpace.{u3} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u1} γ] (h : Homeomorph.{u3, u2} α β _inst_1 _inst_2) {f : β -> γ}, Iff (IsOpenMap.{u3, u1} α γ _inst_1 _inst_3 (Function.comp.{succ u3, succ u2, succ u1} α β γ f (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (Homeomorph.{u3, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u3, u2} α β _inst_1 _inst_2))) h))) (IsOpenMap.{u2, u1} β γ _inst_2 _inst_3 f)
Case conversion may be inaccurate. Consider using '#align homeomorph.comp_is_open_map_iff' Homeomorph.comp_isOpenMap_iff'ₓ'. -/
@[simp]
theorem comp_isOpenMap_iff' (h : α ≃ₜ β) {f : β → γ} : IsOpenMap (f ∘ h) ↔ IsOpenMap f :=
  by
  refine' ⟨_, fun hf => hf.comp h.is_open_map⟩
  intro hf
  rw [← Function.comp.right_id f, ← h.self_comp_symm, ← Function.comp.assoc]
  exact hf.comp h.symm.is_open_map
#align homeomorph.comp_is_open_map_iff' Homeomorph.comp_isOpenMap_iff'

#print Homeomorph.setCongr /-
/-- If two sets are equal, then they are homeomorphic. -/
def setCongr {s t : Set α} (h : s = t) : s ≃ₜ t
    where
  continuous_toFun := continuous_inclusion h.Subset
  continuous_invFun := continuous_inclusion h.symm.Subset
  toEquiv := Equiv.setCongr h
#align homeomorph.set_congr Homeomorph.setCongr
-/

/- warning: homeomorph.sum_congr -> Homeomorph.sumCongr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (Homeomorph.{u3, u4} γ δ _inst_3 _inst_4) -> (Homeomorph.{max u1 u3, max u2 u4} (Sum.{u1, u3} α γ) (Sum.{u2, u4} β δ) (Sum.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Sum.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (Homeomorph.{u3, u4} γ δ _inst_3 _inst_4) -> (Homeomorph.{max u3 u1, max u4 u2} (Sum.{u1, u3} α γ) (Sum.{u2, u4} β δ) (instTopologicalSpaceSum.{u1, u3} α γ _inst_1 _inst_3) (instTopologicalSpaceSum.{u2, u4} β δ _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align homeomorph.sum_congr Homeomorph.sumCongrₓ'. -/
/-- Sum of two homeomorphisms. -/
def sumCongr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : Sum α γ ≃ₜ Sum β δ
    where
  continuous_toFun := h₁.Continuous.sum_map h₂.Continuous
  continuous_invFun := h₁.symm.Continuous.sum_map h₂.symm.Continuous
  toEquiv := h₁.toEquiv.sumCongr h₂.toEquiv
#align homeomorph.sum_congr Homeomorph.sumCongr

/- warning: homeomorph.prod_congr -> Homeomorph.prodCongr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (Homeomorph.{u3, u4} γ δ _inst_3 _inst_4) -> (Homeomorph.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ], (Homeomorph.{u1, u2} α β _inst_1 _inst_2) -> (Homeomorph.{u3, u4} γ δ _inst_3 _inst_4) -> (Homeomorph.{max u3 u1, max u4 u2} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (instTopologicalSpaceProd.{u1, u3} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u2, u4} β δ _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align homeomorph.prod_congr Homeomorph.prodCongrₓ'. -/
/-- Product of two homeomorphisms. -/
def prodCongr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α × γ ≃ₜ β × δ
    where
  continuous_toFun :=
    (h₁.Continuous.comp continuous_fst).prod_mk (h₂.Continuous.comp continuous_snd)
  continuous_invFun :=
    (h₁.symm.Continuous.comp continuous_fst).prod_mk (h₂.symm.Continuous.comp continuous_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv
#align homeomorph.prod_congr Homeomorph.prodCongr

/- warning: homeomorph.prod_congr_symm -> Homeomorph.prodCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (h₁ : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (h₂ : Homeomorph.{u3, u4} γ δ _inst_3 _inst_4), Eq.{max (succ (max u2 u4)) (succ (max u1 u3))} (Homeomorph.{max u2 u4, max u1 u3} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3)) (Homeomorph.symm.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4) (Homeomorph.prodCongr.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 h₁ h₂)) (Homeomorph.prodCongr.{u2, u1, u4, u3} β α δ γ _inst_2 _inst_1 _inst_4 _inst_3 (Homeomorph.symm.{u1, u2} α β _inst_1 _inst_2 h₁) (Homeomorph.symm.{u3, u4} γ δ _inst_3 _inst_4 h₂))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] (h₁ : Homeomorph.{u4, u3} α β _inst_1 _inst_2) (h₂ : Homeomorph.{u2, u1} γ δ _inst_3 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (Homeomorph.{max u3 u1, max u4 u2} (Prod.{u3, u1} β δ) (Prod.{u4, u2} α γ) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3)) (Homeomorph.symm.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (Homeomorph.prodCongr.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 h₁ h₂)) (Homeomorph.prodCongr.{u3, u4, u1, u2} β α δ γ _inst_2 _inst_1 _inst_4 _inst_3 (Homeomorph.symm.{u4, u3} α β _inst_1 _inst_2 h₁) (Homeomorph.symm.{u2, u1} γ δ _inst_3 _inst_4 h₂))
Case conversion may be inaccurate. Consider using '#align homeomorph.prod_congr_symm Homeomorph.prodCongr_symmₓ'. -/
@[simp]
theorem prodCongr_symm (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl
#align homeomorph.prod_congr_symm Homeomorph.prodCongr_symm

/- warning: homeomorph.coe_prod_congr -> Homeomorph.coe_prodCongr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ] [_inst_4 : TopologicalSpace.{u4} δ] (h₁ : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (h₂ : Homeomorph.{u3, u4} γ δ _inst_3 _inst_4), Eq.{max (succ (max u1 u3)) (succ (max u2 u4))} ((Prod.{u1, u3} α γ) -> (Prod.{u2, u4} β δ)) (coeFn.{max (succ (max u1 u3)) (succ (max u2 u4)), max (succ (max u1 u3)) (succ (max u2 u4))} (Homeomorph.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4)) (fun (_x : Homeomorph.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4)) => (Prod.{u1, u3} α γ) -> (Prod.{u2, u4} β δ)) (Homeomorph.hasCoeToFun.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u4} β δ _inst_2 _inst_4)) (Homeomorph.prodCongr.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 h₁ h₂)) (Prod.map.{u1, u2, u3, u4} α β γ δ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h₁) (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (Homeomorph.{u3, u4} γ δ _inst_3 _inst_4) (fun (_x : Homeomorph.{u3, u4} γ δ _inst_3 _inst_4) => γ -> δ) (Homeomorph.hasCoeToFun.{u3, u4} γ δ _inst_3 _inst_4) h₂))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : TopologicalSpace.{u4} α] [_inst_2 : TopologicalSpace.{u3} β] [_inst_3 : TopologicalSpace.{u2} γ] [_inst_4 : TopologicalSpace.{u1} δ] (h₁ : Homeomorph.{u4, u3} α β _inst_1 _inst_2) (h₂ : Homeomorph.{u2, u1} γ δ _inst_3 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} ((Prod.{u4, u2} α γ) -> (Prod.{u3, u1} β δ)) (FunLike.coe.{max (succ (max u4 u2)) (succ (max u3 u1)), succ (max u4 u2), succ (max u3 u1)} (Homeomorph.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4)) (Prod.{u4, u2} α γ) (fun (_x : Prod.{u4, u2} α γ) => Prod.{u3, u1} β δ) (EmbeddingLike.toFunLike.{max (succ (max u4 u2)) (succ (max u3 u1)), succ (max u4 u2), succ (max u3 u1)} (Homeomorph.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4)) (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (EquivLike.toEmbeddingLike.{max (succ (max u4 u2)) (succ (max u3 u1)), succ (max u4 u2), succ (max u3 u1)} (Homeomorph.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4)) (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (Homeomorph.instEquivLikeHomeomorph.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instTopologicalSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u3, u1} β δ _inst_2 _inst_4)))) (Homeomorph.prodCongr.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 h₁ h₂)) (Prod.map.{u4, u3, u2, u1} α β γ δ (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u4) (succ u3), succ u4, succ u3} (Homeomorph.{u4, u3} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u4, u3} α β _inst_1 _inst_2))) h₁) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} γ δ _inst_3 _inst_4) γ (fun (_x : γ) => δ) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} γ δ _inst_3 _inst_4) γ δ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (Homeomorph.{u2, u1} γ δ _inst_3 _inst_4) γ δ (Homeomorph.instEquivLikeHomeomorph.{u2, u1} γ δ _inst_3 _inst_4))) h₂))
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_prod_congr Homeomorph.coe_prodCongrₓ'. -/
@[simp]
theorem coe_prodCongr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl
#align homeomorph.coe_prod_congr Homeomorph.coe_prodCongr

section

variable (α β γ)

/- warning: homeomorph.prod_comm -> Homeomorph.prodComm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Homeomorph.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Homeomorph.{max u2 u1, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u2, u1} β α _inst_2 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.prod_comm Homeomorph.prodCommₓ'. -/
/-- `α × β` is homeomorphic to `β × α`. -/
def prodComm : α × β ≃ₜ β × α
    where
  continuous_toFun := continuous_snd.prod_mk continuous_fst
  continuous_invFun := continuous_snd.prod_mk continuous_fst
  toEquiv := Equiv.prodComm α β
#align homeomorph.prod_comm Homeomorph.prodComm

/- warning: homeomorph.prod_comm_symm -> Homeomorph.prodComm_symm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Eq.{max (succ (max u2 u1)) (succ (max u1 u2))} (Homeomorph.{max u2 u1, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Homeomorph.symm.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1) (Homeomorph.prodComm.{u1, u2} α β _inst_1 _inst_2)) (Homeomorph.prodComm.{u2, u1} β α _inst_2 _inst_1)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β], Eq.{max (succ u2) (succ u1)} (Homeomorph.{max u2 u1, max u2 u1} (Prod.{u1, u2} β α) (Prod.{u2, u1} α β) (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (Homeomorph.symm.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1) (Homeomorph.prodComm.{u2, u1} α β _inst_1 _inst_2)) (Homeomorph.prodComm.{u1, u2} β α _inst_2 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.prod_comm_symm Homeomorph.prodComm_symmₓ'. -/
@[simp]
theorem prodComm_symm : (prodComm α β).symm = prodComm β α :=
  rfl
#align homeomorph.prod_comm_symm Homeomorph.prodComm_symm

/- warning: homeomorph.coe_prod_comm -> Homeomorph.coe_prodComm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β], Eq.{max (succ (max u1 u2)) (succ (max u2 u1))} ((Prod.{u1, u2} α β) -> (Prod.{u2, u1} β α)) (coeFn.{max (succ (max u1 u2)) (succ (max u2 u1)), max (succ (max u1 u2)) (succ (max u2 u1))} (Homeomorph.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)) (fun (_x : Homeomorph.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)) => (Prod.{u1, u2} α β) -> (Prod.{u2, u1} β α)) (Homeomorph.hasCoeToFun.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u2, u1} β α _inst_2 _inst_1)) (Homeomorph.prodComm.{u1, u2} α β _inst_1 _inst_2)) (Prod.swap.{u1, u2} α β)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β], Eq.{max (succ u2) (succ u1)} ((Prod.{u2, u1} α β) -> (Prod.{u1, u2} β α)) (FunLike.coe.{succ (max u2 u1), succ (max u2 u1), succ (max u2 u1)} (Homeomorph.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1)) (Prod.{u2, u1} α β) (fun (_x : Prod.{u2, u1} α β) => Prod.{u1, u2} β α) (EmbeddingLike.toFunLike.{succ (max u2 u1), succ (max u2 u1), succ (max u2 u1)} (Homeomorph.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1)) (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (EquivLike.toEmbeddingLike.{succ (max u2 u1), succ (max u2 u1), succ (max u2 u1)} (Homeomorph.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1)) (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Homeomorph.instEquivLikeHomeomorph.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instTopologicalSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u2} β α _inst_2 _inst_1)))) (Homeomorph.prodComm.{u2, u1} α β _inst_1 _inst_2)) (Prod.swap.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_prod_comm Homeomorph.coe_prodCommₓ'. -/
@[simp]
theorem coe_prodComm : ⇑(prodComm α β) = Prod.swap :=
  rfl
#align homeomorph.coe_prod_comm Homeomorph.coe_prodComm

/- warning: homeomorph.prod_assoc -> Homeomorph.prodAssoc is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) (γ : Type.{u3}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], Homeomorph.{max (max u1 u2) u3, max u1 u2 u3} (Prod.{max u1 u2, u3} (Prod.{u1, u2} α β) γ) (Prod.{u1, max u2 u3} α (Prod.{u2, u3} β γ)) (Prod.topologicalSpace.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (Prod.topologicalSpace.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) (γ : Type.{u3}) [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], Homeomorph.{max u3 u2 u1, max (max u3 u2) u1} (Prod.{max u2 u1, u3} (Prod.{u1, u2} α β) γ) (Prod.{u1, max u3 u2} α (Prod.{u2, u3} β γ)) (instTopologicalSpaceProd.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3) (instTopologicalSpaceProd.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (instTopologicalSpaceProd.{u2, u3} β γ _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align homeomorph.prod_assoc Homeomorph.prodAssocₓ'. -/
/-- `(α × β) × γ` is homeomorphic to `α × (β × γ)`. -/
def prodAssoc : (α × β) × γ ≃ₜ α × β × γ
    where
  continuous_toFun :=
    (continuous_fst.comp continuous_fst).prod_mk
      ((continuous_snd.comp continuous_fst).prod_mk continuous_snd)
  continuous_invFun :=
    (continuous_fst.prod_mk (continuous_fst.comp continuous_snd)).prod_mk
      (continuous_snd.comp continuous_snd)
  toEquiv := Equiv.prodAssoc α β γ
#align homeomorph.prod_assoc Homeomorph.prodAssoc

/- warning: homeomorph.prod_punit -> Homeomorph.prodPUnit is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Homeomorph.{max u1 u2, u1} (Prod.{u1, u2} α PUnit.{succ u2}) α (Prod.topologicalSpace.{u1, u2} α PUnit.{succ u2} _inst_1 PUnit.topologicalSpace.{u2}) _inst_1
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Homeomorph.{max u2 u1, u1} (Prod.{u1, u2} α PUnit.{succ u2}) α (instTopologicalSpaceProd.{u1, u2} α PUnit.{succ u2} _inst_1 instTopologicalSpacePUnit.{u2}) _inst_1
Case conversion may be inaccurate. Consider using '#align homeomorph.prod_punit Homeomorph.prodPUnitₓ'. -/
/-- `α × {*}` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false }) apply]
def prodPUnit : α × PUnit ≃ₜ α where
  toEquiv := Equiv.prodPUnit α
  continuous_toFun := continuous_fst
  continuous_invFun := continuous_id.prod_mk continuous_const
#align homeomorph.prod_punit Homeomorph.prodPUnit

/- warning: homeomorph.punit_prod -> Homeomorph.punitProd is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Homeomorph.{max u2 u1, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (Prod.topologicalSpace.{u2, u1} PUnit.{succ u2} α PUnit.topologicalSpace.{u2} _inst_1) _inst_1
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Homeomorph.{max u1 u2, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (instTopologicalSpaceProd.{u2, u1} PUnit.{succ u2} α instTopologicalSpacePUnit.{u2} _inst_1) _inst_1
Case conversion may be inaccurate. Consider using '#align homeomorph.punit_prod Homeomorph.punitProdₓ'. -/
/-- `{*} × α` is homeomorphic to `α`. -/
def punitProd : PUnit × α ≃ₜ α :=
  (prodComm _ _).trans (prodPUnit _)
#align homeomorph.punit_prod Homeomorph.punitProd

/- warning: homeomorph.coe_punit_prod -> Homeomorph.coe_punitProd is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : TopologicalSpace.{u1} α], Eq.{max (succ (max u2 u1)) (succ u1)} ((Prod.{u2, u1} PUnit.{succ u2} α) -> α) (coeFn.{max (succ (max u2 u1)) (succ u1), max (succ (max u2 u1)) (succ u1)} (Homeomorph.{max u2 u1, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (Prod.topologicalSpace.{u2, u1} PUnit.{succ u2} α PUnit.topologicalSpace.{u2} _inst_1) _inst_1) (fun (_x : Homeomorph.{max u2 u1, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (Prod.topologicalSpace.{u2, u1} PUnit.{succ u2} α PUnit.topologicalSpace.{u2} _inst_1) _inst_1) => (Prod.{u2, u1} PUnit.{succ u2} α) -> α) (Homeomorph.hasCoeToFun.{max u2 u1, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (Prod.topologicalSpace.{u2, u1} PUnit.{succ u2} α PUnit.topologicalSpace.{u2} _inst_1) _inst_1) (Homeomorph.punitProd.{u1, u2} α _inst_1)) (Prod.snd.{u2, u1} PUnit.{succ u2} α)
but is expected to have type
  forall (α : Type.{u2}) [_inst_1 : TopologicalSpace.{u2} α], Eq.{max (succ u2) (succ u1)} ((Prod.{u1, u2} PUnit.{succ u1} α) -> α) (FunLike.coe.{max (succ (max u2 u1)) (succ u2), succ (max u2 u1), succ u2} (Homeomorph.{max u2 u1, u2} (Prod.{u1, u2} PUnit.{succ u1} α) α (instTopologicalSpaceProd.{u1, u2} PUnit.{succ u1} α instTopologicalSpacePUnit.{u1} _inst_1) _inst_1) (Prod.{u1, u2} PUnit.{succ u1} α) (fun (_x : Prod.{u1, u2} PUnit.{succ u1} α) => α) (EmbeddingLike.toFunLike.{max (succ (max u2 u1)) (succ u2), succ (max u2 u1), succ u2} (Homeomorph.{max u2 u1, u2} (Prod.{u1, u2} PUnit.{succ u1} α) α (instTopologicalSpaceProd.{u1, u2} PUnit.{succ u1} α instTopologicalSpacePUnit.{u1} _inst_1) _inst_1) (Prod.{u1, u2} PUnit.{succ u1} α) α (EquivLike.toEmbeddingLike.{max (succ (max u2 u1)) (succ u2), succ (max u2 u1), succ u2} (Homeomorph.{max u2 u1, u2} (Prod.{u1, u2} PUnit.{succ u1} α) α (instTopologicalSpaceProd.{u1, u2} PUnit.{succ u1} α instTopologicalSpacePUnit.{u1} _inst_1) _inst_1) (Prod.{u1, u2} PUnit.{succ u1} α) α (Homeomorph.instEquivLikeHomeomorph.{max u2 u1, u2} (Prod.{u1, u2} PUnit.{succ u1} α) α (instTopologicalSpaceProd.{u1, u2} PUnit.{succ u1} α instTopologicalSpacePUnit.{u1} _inst_1) _inst_1))) (Homeomorph.punitProd.{u2, u1} α _inst_1)) (Prod.snd.{u1, u2} PUnit.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align homeomorph.coe_punit_prod Homeomorph.coe_punitProdₓ'. -/
@[simp]
theorem coe_punitProd : ⇑(punitProd α) = Prod.snd :=
  rfl
#align homeomorph.coe_punit_prod Homeomorph.coe_punitProd

#print Homeomorph.homeomorphOfUnique /-
/-- If both `α` and `β` have a unique element, then `α ≃ₜ β`. -/
@[simps]
def Homeomorph.homeomorphOfUnique [Unique α] [Unique β] : α ≃ₜ β :=
  {
    Equiv.equivOfUnique α
      β with
    continuous_toFun := @continuous_const α β _ _ default
    continuous_invFun := @continuous_const β α _ _ default }
#align homeomorph.homeomorph_of_unique Homeomorph.homeomorphOfUnique
-/

end

#print Homeomorph.piCongrRight /-
/-- If each `β₁ i` is homeomorphic to `β₂ i`, then `Π i, β₁ i` is homeomorphic to `Π i, β₂ i`. -/
@[simps apply toEquiv]
def piCongrRight {ι : Type _} {β₁ β₂ : ι → Type _} [∀ i, TopologicalSpace (β₁ i)]
    [∀ i, TopologicalSpace (β₂ i)] (F : ∀ i, β₁ i ≃ₜ β₂ i) : (∀ i, β₁ i) ≃ₜ ∀ i, β₂ i
    where
  continuous_toFun := continuous_pi fun i => (F i).Continuous.comp <| continuous_apply i
  continuous_invFun := continuous_pi fun i => (F i).symm.Continuous.comp <| continuous_apply i
  toEquiv := Equiv.piCongrRight fun i => (F i).toEquiv
#align homeomorph.Pi_congr_right Homeomorph.piCongrRight
-/

/- warning: homeomorph.Pi_congr_right_symm -> Homeomorph.piCongrRight_symm is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {β₁ : ι -> Type.{u2}} {β₂ : ι -> Type.{u3}} [_inst_5 : forall (i : ι), TopologicalSpace.{u2} (β₁ i)] [_inst_6 : forall (i : ι), TopologicalSpace.{u3} (β₂ i)] (F : forall (i : ι), Homeomorph.{u2, u3} (β₁ i) (β₂ i) (_inst_5 i) (_inst_6 i)), Eq.{max (succ (max u1 u3)) (succ (max u1 u2))} (Homeomorph.{max u1 u3, max u1 u2} (forall (i : ι), β₂ i) (forall (i : ι), β₁ i) (Pi.topologicalSpace.{u1, u3} ι (fun (i : ι) => β₂ i) (fun (a : ι) => _inst_6 a)) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => β₁ i) (fun (a : ι) => _inst_5 a))) (Homeomorph.symm.{max u1 u2, max u1 u3} (forall (i : ι), β₁ i) (forall (i : ι), β₂ i) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => β₁ i) (fun (a : ι) => _inst_5 a)) (Pi.topologicalSpace.{u1, u3} ι (fun (i : ι) => β₂ i) (fun (a : ι) => _inst_6 a)) (Homeomorph.piCongrRight.{u1, u2, u3} ι (fun (i : ι) => β₁ i) (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_6 i) F)) (Homeomorph.piCongrRight.{u1, u3, u2} ι (fun (i : ι) => β₂ i) (fun (i : ι) => β₁ i) (fun (a : ι) => _inst_6 a) (fun (a : ι) => _inst_5 a) (fun (i : ι) => Homeomorph.symm.{u2, u3} (β₁ i) (β₂ i) (_inst_5 i) (_inst_6 i) (F i)))
but is expected to have type
  forall {ι : Type.{u3}} {β₁ : ι -> Type.{u2}} {β₂ : ι -> Type.{u1}} [_inst_5 : forall (i : ι), TopologicalSpace.{u2} (β₁ i)] [_inst_6 : forall (i : ι), TopologicalSpace.{u1} (β₂ i)] (F : forall (i : ι), Homeomorph.{u2, u1} (β₁ i) (β₂ i) (_inst_5 i) (_inst_6 i)), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (Homeomorph.{max u3 u1, max u3 u2} (forall (i : ι), β₂ i) (forall (i : ι), β₁ i) (Pi.topologicalSpace.{u3, u1} ι (fun (i : ι) => β₂ i) (fun (a : ι) => _inst_6 a)) (Pi.topologicalSpace.{u3, u2} ι (fun (i : ι) => β₁ i) (fun (a : ι) => _inst_5 a))) (Homeomorph.symm.{max u3 u2, max u3 u1} (forall (i : ι), β₁ i) (forall (i : ι), β₂ i) (Pi.topologicalSpace.{u3, u2} ι (fun (i : ι) => β₁ i) (fun (a : ι) => _inst_5 a)) (Pi.topologicalSpace.{u3, u1} ι (fun (i : ι) => β₂ i) (fun (a : ι) => _inst_6 a)) (Homeomorph.piCongrRight.{u3, u2, u1} ι (fun (i : ι) => β₁ i) (fun (i : ι) => β₂ i) (fun (i : ι) => _inst_5 i) (fun (i : ι) => _inst_6 i) F)) (Homeomorph.piCongrRight.{u3, u1, u2} ι (fun (i : ι) => β₂ i) (fun (i : ι) => β₁ i) (fun (a : ι) => _inst_6 a) (fun (a : ι) => _inst_5 a) (fun (i : ι) => Homeomorph.symm.{u2, u1} (β₁ i) (β₂ i) (_inst_5 i) (_inst_6 i) (F i)))
Case conversion may be inaccurate. Consider using '#align homeomorph.Pi_congr_right_symm Homeomorph.piCongrRight_symmₓ'. -/
@[simp]
theorem piCongrRight_symm {ι : Type _} {β₁ β₂ : ι → Type _} [∀ i, TopologicalSpace (β₁ i)]
    [∀ i, TopologicalSpace (β₂ i)] (F : ∀ i, β₁ i ≃ₜ β₂ i) :
    (piCongrRight F).symm = piCongrRight fun i => (F i).symm :=
  rfl
#align homeomorph.Pi_congr_right_symm Homeomorph.piCongrRight_symm

#print Homeomorph.ulift /-
/-- `ulift α` is homeomorphic to `α`. -/
def ulift.{u, v} {α : Type u} [TopologicalSpace α] : ULift.{v, u} α ≃ₜ α
    where
  continuous_toFun := continuous_uLift_down
  continuous_invFun := continuous_uLift_up
  toEquiv := Equiv.ulift
#align homeomorph.ulift Homeomorph.ulift
-/

section Distrib

/- warning: homeomorph.sum_prod_distrib -> Homeomorph.sumProdDistrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], Homeomorph.{max (max u1 u2) u3, max (max u1 u3) u2 u3} (Prod.{max u1 u2, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (Prod.topologicalSpace.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (Sum.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (Sum.topologicalSpace.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], Homeomorph.{max u3 u2 u1, max (max u3 u2) u3 u1} (Prod.{max u2 u1, u3} (Sum.{u1, u2} α β) γ) (Sum.{max u3 u1, max u3 u2} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ)) (instTopologicalSpaceProd.{max u1 u2, u3} (Sum.{u1, u2} α β) γ (instTopologicalSpaceSum.{u1, u2} α β _inst_1 _inst_2) _inst_3) (instTopologicalSpaceSum.{max u1 u3, max u2 u3} (Prod.{u1, u3} α γ) (Prod.{u2, u3} β γ) (instTopologicalSpaceProd.{u1, u3} α γ _inst_1 _inst_3) (instTopologicalSpaceProd.{u2, u3} β γ _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align homeomorph.sum_prod_distrib Homeomorph.sumProdDistribₓ'. -/
/-- `(α ⊕ β) × γ` is homeomorphic to `α × γ ⊕ β × γ`. -/
def sumProdDistrib : Sum α β × γ ≃ₜ Sum (α × γ) (β × γ) :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equiv.sumProdDistrib α β γ).symm
        ((continuous_inl.Prod_map continuous_id).sum_elim
          (continuous_inr.Prod_map continuous_id)) <|
      (isOpenMap_inl.Prod IsOpenMap.id).sum_elim (isOpenMap_inr.Prod IsOpenMap.id)
#align homeomorph.sum_prod_distrib Homeomorph.sumProdDistrib

/- warning: homeomorph.prod_sum_distrib -> Homeomorph.prodSumDistrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], Homeomorph.{max u1 u2 u3, max (max u1 u2) u1 u3} (Prod.{u1, max u2 u3} α (Sum.{u2, u3} β γ)) (Sum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (Prod.topologicalSpace.{u1, max u2 u3} α (Sum.{u2, u3} β γ) _inst_1 (Sum.topologicalSpace.{u2, u3} β γ _inst_2 _inst_3)) (Sum.topologicalSpace.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.topologicalSpace.{u1, u3} α γ _inst_1 _inst_3))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : TopologicalSpace.{u3} γ], Homeomorph.{max (max u3 u2) u1, max (max u3 u1) u2 u1} (Prod.{u1, max u3 u2} α (Sum.{u2, u3} β γ)) (Sum.{max u2 u1, max u3 u1} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ)) (instTopologicalSpaceProd.{u1, max u2 u3} α (Sum.{u2, u3} β γ) _inst_1 (instTopologicalSpaceSum.{u2, u3} β γ _inst_2 _inst_3)) (instTopologicalSpaceSum.{max u1 u2, max u1 u3} (Prod.{u1, u2} α β) (Prod.{u1, u3} α γ) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2) (instTopologicalSpaceProd.{u1, u3} α γ _inst_1 _inst_3))
Case conversion may be inaccurate. Consider using '#align homeomorph.prod_sum_distrib Homeomorph.prodSumDistribₓ'. -/
/-- `α × (β ⊕ γ)` is homeomorphic to `α × β ⊕ α × γ`. -/
def prodSumDistrib : α × Sum β γ ≃ₜ Sum (α × β) (α × γ) :=
  (prodComm _ _).trans <| sumProdDistrib.trans <| sumCongr (prodComm _ _) (prodComm _ _)
#align homeomorph.prod_sum_distrib Homeomorph.prodSumDistrib

variable {ι : Type _} {σ : ι → Type _} [∀ i, TopologicalSpace (σ i)]

/- warning: homeomorph.sigma_prod_distrib -> Homeomorph.sigmaProdDistrib is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} {σ : ι -> Type.{u3}} [_inst_5 : forall (i : ι), TopologicalSpace.{u3} (σ i)], Homeomorph.{max (max u2 u3) u1, max u2 u3 u1} (Prod.{max u2 u3, u1} (Sigma.{u2, u3} ι (fun (i : ι) => σ i)) β) (Sigma.{u2, max u3 u1} ι (fun (i : ι) => Prod.{u3, u1} (σ i) β)) (Prod.topologicalSpace.{max u2 u3, u1} (Sigma.{u2, u3} ι (fun (i : ι) => σ i)) β (Sigma.topologicalSpace.{u2, u3} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_5 a)) _inst_2) (Sigma.topologicalSpace.{u2, max u3 u1} ι (fun (i : ι) => Prod.{u3, u1} (σ i) β) (fun (a : ι) => Prod.topologicalSpace.{u3, u1} (σ a) β (_inst_5 a) _inst_2))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} {σ : ι -> Type.{u3}} [_inst_5 : forall (i : ι), TopologicalSpace.{u3} (σ i)], Homeomorph.{max u1 u3 u2, max (max u1 u3) u2} (Prod.{max u3 u2, u1} (Sigma.{u2, u3} ι (fun (i : ι) => σ i)) β) (Sigma.{u2, max u1 u3} ι (fun (i : ι) => Prod.{u3, u1} (σ i) β)) (instTopologicalSpaceProd.{max u2 u3, u1} (Sigma.{u2, u3} ι (fun (i : ι) => σ i)) β (instTopologicalSpaceSigma.{u2, u3} ι (fun (i : ι) => σ i) (fun (a : ι) => _inst_5 a)) _inst_2) (instTopologicalSpaceSigma.{u2, max u1 u3} ι (fun (i : ι) => Prod.{u3, u1} (σ i) β) (fun (a : ι) => instTopologicalSpaceProd.{u3, u1} (σ a) β (_inst_5 a) _inst_2))
Case conversion may be inaccurate. Consider using '#align homeomorph.sigma_prod_distrib Homeomorph.sigmaProdDistribₓ'. -/
/-- `(Σ i, σ i) × β` is homeomorphic to `Σ i, (σ i × β)`. -/
def sigmaProdDistrib : (Σi, σ i) × β ≃ₜ Σi, σ i × β :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equiv.sigmaProdDistrib σ β).symm
      (continuous_sigma fun i => continuous_sigmaMk.fst'.prod_mk continuous_snd)
      (isOpenMap_sigma.2 fun i => isOpenMap_sigmaMk.Prod IsOpenMap.id)
#align homeomorph.sigma_prod_distrib Homeomorph.sigmaProdDistrib

end Distrib

#print Homeomorph.funUnique /-
/-- If `ι` has a unique element, then `ι → α` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (ι α : Type _) [Unique ι] [TopologicalSpace α] : (ι → α) ≃ₜ α
    where
  toEquiv := Equiv.funUnique ι α
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_id
#align homeomorph.fun_unique Homeomorph.funUnique
-/

/- warning: homeomorph.pi_fin_two -> Homeomorph.piFinTwo is a dubious translation:
lean 3 declaration is
  forall (α : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}) [_inst_5 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), TopologicalSpace.{u1} (α i)], Homeomorph.{u1, u1} (forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), α i) (Prod.{u1, u1} (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Homeomorph.piFinTwo._proof_1))))) (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Homeomorph.piFinTwo._proof_2)))))) (Pi.topologicalSpace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_5 a)) (Prod.topologicalSpace.{u1, u1} (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Homeomorph.piFinTwo._proof_1))))) (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Homeomorph.piFinTwo._proof_2))))) (_inst_5 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Homeomorph.piFinTwo._proof_1))))) (_inst_5 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) Homeomorph.piFinTwo._proof_2))))))
but is expected to have type
  forall (α : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> Type.{u1}) [_inst_5 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), TopologicalSpace.{u1} (α i)], Homeomorph.{u1, u1} (forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), α i) (Prod.{u1, u1} (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (Pi.topologicalSpace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => α i) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_5 a)) (instTopologicalSpaceProd.{u1, u1} (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_5 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_5 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align homeomorph.pi_fin_two Homeomorph.piFinTwoₓ'. -/
/-- Homeomorphism between dependent functions `Π i : fin 2, α i` and `α 0 × α 1`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwo.{u} (α : Fin 2 → Type u) [∀ i, TopologicalSpace (α i)] : (∀ i, α i) ≃ₜ α 0 × α 1
    where
  toEquiv := piFinTwoEquiv α
  continuous_toFun := (continuous_apply 0).prod_mk (continuous_apply 1)
  continuous_invFun := continuous_pi <| Fin.forall_fin_two.2 ⟨continuous_fst, continuous_snd⟩
#align homeomorph.pi_fin_two Homeomorph.piFinTwo

/- warning: homeomorph.fin_two_arrow -> Homeomorph.finTwoArrow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Homeomorph.{u1, u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (Prod.{u1, u1} α α) (Pi.topologicalSpace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => α) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_1)) (Prod.topologicalSpace.{u1, u1} α α _inst_1 _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α], Homeomorph.{u1, u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) (Prod.{u1, u1} α α) (Pi.topologicalSpace.{0, u1} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => α) (fun (a : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_1)) (instTopologicalSpaceProd.{u1, u1} α α _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align homeomorph.fin_two_arrow Homeomorph.finTwoArrowₓ'. -/
/-- Homeomorphism between `α² = fin 2 → α` and `α × α`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrow : (Fin 2 → α) ≃ₜ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }
#align homeomorph.fin_two_arrow Homeomorph.finTwoArrow

/- warning: homeomorph.image -> Homeomorph.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Homeomorph.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) (fun (_x : Homeomorph.{u1, u2} α β _inst_1 _inst_2) => α -> β) (Homeomorph.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)) _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (e : Homeomorph.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Homeomorph.{u1, u2} (Set.Elem.{u1} α s) (Set.Elem.{u2} β (Set.image.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u1, u2} α β _inst_1 _inst_2))) e) s)) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) (instTopologicalSpaceSubtype.{u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.image.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (Homeomorph.{u1, u2} α β _inst_1 _inst_2) α β (Homeomorph.instEquivLikeHomeomorph.{u1, u2} α β _inst_1 _inst_2))) e) s)) _inst_2)
Case conversion may be inaccurate. Consider using '#align homeomorph.image Homeomorph.imageₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Misc2.lean:304:22: continuitity! not supported at the moment -/
/- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Misc2.lean:304:22: continuitity! not supported at the moment -/
/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps]
def image (e : α ≃ₜ β) (s : Set α) : s ≃ₜ e '' s
    where
  continuous_toFun := by continuity
  continuous_invFun := by continuity
  toEquiv := e.toEquiv.image s
#align homeomorph.image Homeomorph.image

#print Homeomorph.Set.univ /-
/-- `set.univ α` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false })]
def Set.univ (α : Type _) [TopologicalSpace α] : (univ : Set α) ≃ₜ α
    where
  toEquiv := Equiv.Set.univ α
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _
#align homeomorph.set.univ Homeomorph.Set.univ
-/

/- warning: homeomorph.set.prod -> Homeomorph.Set.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (t : Set.{u2} β), Homeomorph.{max u1 u2, max u1 u2} (coeSort.{succ (max u1 u2), succ (succ (max u1 u2))} (Set.{max u1 u2} (Prod.{u1, u2} α β)) Type.{max u1 u2} (Set.hasCoeToSort.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t)) (Prod.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t)) (Subtype.topologicalSpace.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) x (Set.prod.{u1, u2} α β s t)) (Prod.topologicalSpace.{u1, u2} α β _inst_1 _inst_2)) (Prod.topologicalSpace.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) t) (Subtype.topologicalSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) (Subtype.topologicalSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x t) _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] (s : Set.{u1} α) (t : Set.{u2} β), Homeomorph.{max u1 u2, max u2 u1} (Set.Elem.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) (Prod.{u1, u2} (Set.Elem.{u1} α s) (Set.Elem.{u2} β t)) (instTopologicalSpaceSubtype.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => Membership.mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.instMembershipSet.{max u1 u2} (Prod.{u1, u2} α β)) x (Set.prod.{u1, u2} α β s t)) (instTopologicalSpaceProd.{u1, u2} α β _inst_1 _inst_2)) (instTopologicalSpaceProd.{u1, u2} (Set.Elem.{u1} α s) (Set.Elem.{u2} β t) (instTopologicalSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) (instTopologicalSpaceSubtype.{u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x t) _inst_2))
Case conversion may be inaccurate. Consider using '#align homeomorph.set.prod Homeomorph.Set.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- `s ×ˢ t` is homeomorphic to `s × t`. -/
@[simps]
def Set.prod (s : Set α) (t : Set β) : ↥(s ×ˢ t) ≃ₜ s × t
    where
  toEquiv := Equiv.Set.prod s t
  continuous_toFun :=
    (continuous_subtype_val.fst.subtype_mk _).prod_mk (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun :=
    (continuous_subtype_val.fst'.prod_mk continuous_subtype_val.snd').subtype_mk _
#align homeomorph.set.prod Homeomorph.Set.prod

section

variable {ι : Type _}

/- warning: homeomorph.pi_equiv_pi_subtype_prod -> Homeomorph.piEquivPiSubtypeProd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (p : ι -> Prop) (β : ι -> Type.{u2}) [_inst_5 : forall (i : ι), TopologicalSpace.{u2} (β i)] [_inst_6 : DecidablePred.{succ u1} ι p], Homeomorph.{max u1 u2, max u1 u2} (forall (i : ι), β i) (Prod.{max u1 u2, max u1 u2} (forall (i : Subtype.{succ u1} ι (fun (x : ι) => p x)), β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (coeSubtype.{succ u1} ι (fun (x : ι) => p x))))) i)) (forall (i : Subtype.{succ u1} ι (fun (x : ι) => Not (p x))), β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (coeSubtype.{succ u1} ι (fun (x : ι) => Not (p x)))))) i))) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => β i) (fun (a : ι) => _inst_5 a)) (Prod.topologicalSpace.{max u1 u2, max u1 u2} (forall (i : Subtype.{succ u1} ι (fun (x : ι) => p x)), β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (coeSubtype.{succ u1} ι (fun (x : ι) => p x))))) i)) (forall (i : Subtype.{succ u1} ι (fun (x : ι) => Not (p x))), β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (coeSubtype.{succ u1} ι (fun (x : ι) => Not (p x)))))) i)) (Pi.topologicalSpace.{u1, u2} (Subtype.{succ u1} ι (fun (x : ι) => p x)) (fun (i : Subtype.{succ u1} ι (fun (x : ι) => p x)) => β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (coeSubtype.{succ u1} ι (fun (x : ι) => p x))))) i)) (fun (a : Subtype.{succ u1} ι (fun (x : ι) => p x)) => _inst_5 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => p x)) ι (coeSubtype.{succ u1} ι (fun (x : ι) => p x))))) a))) (Pi.topologicalSpace.{u1, u2} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) (fun (i : Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) => β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (coeSubtype.{succ u1} ι (fun (x : ι) => Not (p x)))))) i)) (fun (a : Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) => _inst_5 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) ι (coeSubtype.{succ u1} ι (fun (x : ι) => Not (p x)))))) a))))
but is expected to have type
  forall {ι : Type.{u1}} (p : ι -> Prop) (β : ι -> Type.{u2}) [_inst_5 : forall (i : ι), TopologicalSpace.{u2} (β i)] [_inst_6 : DecidablePred.{succ u1} ι p], Homeomorph.{max u1 u2, max u1 u2} (forall (i : ι), β i) (Prod.{max u1 u2, max u1 u2} (forall (i : Subtype.{succ u1} ι (fun (x : ι) => p x)), β (Subtype.val.{succ u1} ι (fun (x : ι) => p x) i)) (forall (i : Subtype.{succ u1} ι (fun (x : ι) => Not (p x))), β (Subtype.val.{succ u1} ι (fun (x : ι) => Not (p x)) i))) (Pi.topologicalSpace.{u1, u2} ι (fun (i : ι) => β i) (fun (a : ι) => _inst_5 a)) (instTopologicalSpaceProd.{max u1 u2, max u1 u2} (forall (i : Subtype.{succ u1} ι (fun (x : ι) => p x)), β (Subtype.val.{succ u1} ι (fun (x : ι) => p x) i)) (forall (i : Subtype.{succ u1} ι (fun (x : ι) => Not (p x))), β (Subtype.val.{succ u1} ι (fun (x : ι) => Not (p x)) i)) (Pi.topologicalSpace.{u1, u2} (Subtype.{succ u1} ι (fun (x : ι) => p x)) (fun (i : Subtype.{succ u1} ι (fun (x : ι) => p x)) => β (Subtype.val.{succ u1} ι (fun (x : ι) => p x) i)) (fun (a : Subtype.{succ u1} ι (fun (x : ι) => p x)) => _inst_5 (Subtype.val.{succ u1} ι (fun (x : ι) => p x) a))) (Pi.topologicalSpace.{u1, u2} (Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) (fun (i : Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) => β (Subtype.val.{succ u1} ι (fun (x : ι) => Not (p x)) i)) (fun (a : Subtype.{succ u1} ι (fun (x : ι) => Not (p x))) => _inst_5 (Subtype.val.{succ u1} ι (fun (x : ι) => Not (p x)) a))))
Case conversion may be inaccurate. Consider using '#align homeomorph.pi_equiv_pi_subtype_prod Homeomorph.piEquivPiSubtypeProdₓ'. -/
/-- The topological space `Π i, β i` can be split as a product by separating the indices in ι
  depending on whether they satisfy a predicate p or not.-/
@[simps]
def piEquivPiSubtypeProd (p : ι → Prop) (β : ι → Type _) [∀ i, TopologicalSpace (β i)]
    [DecidablePred p] : (∀ i, β i) ≃ₜ (∀ i : { x // p x }, β i) × ∀ i : { x // ¬p x }, β i
    where
  toEquiv := Equiv.piEquivPiSubtypeProd p β
  continuous_toFun := by
    apply Continuous.prod_mk <;> exact continuous_pi fun j => continuous_apply j
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piEquivPiSubtypeProd]; split_ifs
      exacts[(continuous_apply _).comp continuous_fst, (continuous_apply _).comp continuous_snd]
#align homeomorph.pi_equiv_pi_subtype_prod Homeomorph.piEquivPiSubtypeProd

variable [DecidableEq ι] (i : ι)

/- warning: homeomorph.pi_split_at -> Homeomorph.piSplitAt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_5 : DecidableEq.{succ u1} ι] (i : ι) (β : ι -> Type.{u2}) [_inst_6 : forall (j : ι), TopologicalSpace.{u2} (β j)], Homeomorph.{max u1 u2, max u1 u2} (forall (j : ι), β j) (Prod.{u2, max u1 u2} (β i) (forall (j : Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)), β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (coeSubtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i))))) j))) (Pi.topologicalSpace.{u1, u2} ι (fun (j : ι) => β j) (fun (a : ι) => _inst_6 a)) (Prod.topologicalSpace.{u2, max u1 u2} (β i) (forall (j : Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)), β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (coeSubtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i))))) j)) (_inst_6 i) (Pi.topologicalSpace.{u1, u2} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) (fun (j : Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) => β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (coeSubtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i))))) j)) (fun (a : Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) => _inst_6 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (HasLiftT.mk.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (CoeTCₓ.coe.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (coeBase.{succ u1, succ u1} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) ι (coeSubtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i))))) a))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_5 : DecidableEq.{succ u1} ι] (i : ι) (β : ι -> Type.{u2}) [_inst_6 : forall (j : ι), TopologicalSpace.{u2} (β j)], Homeomorph.{max u1 u2, max u1 u2} (forall (j : ι), β j) (Prod.{u2, max u1 u2} (β i) (forall (j : Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)), β (Subtype.val.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i) j))) (Pi.topologicalSpace.{u1, u2} ι (fun (j : ι) => β j) (fun (a : ι) => _inst_6 a)) (instTopologicalSpaceProd.{u2, max u1 u2} (β i) (forall (j : Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)), β (Subtype.val.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i) j)) (_inst_6 i) (Pi.topologicalSpace.{u1, u2} (Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) (fun (j : Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) => β (Subtype.val.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i) j)) (fun (a : Subtype.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i)) => _inst_6 (Subtype.val.{succ u1} ι (fun (j : ι) => Ne.{succ u1} ι j i) a))))
Case conversion may be inaccurate. Consider using '#align homeomorph.pi_split_at Homeomorph.piSplitAtₓ'. -/
/-- A product of topological spaces can be split as the binary product of one of the spaces and
  the product of all the remaining spaces. -/
@[simps]
def piSplitAt (β : ι → Type _) [∀ j, TopologicalSpace (β j)] :
    (∀ j, β j) ≃ₜ β i × ∀ j : { j // j ≠ i }, β j
    where
  toEquiv := Equiv.piSplitAt i β
  continuous_toFun := (continuous_apply i).prod_mk (continuous_pi fun j => continuous_apply j)
  continuous_invFun :=
    continuous_pi fun j => by
      dsimp only [Equiv.piSplitAt]
      split_ifs
      subst h
      exacts[continuous_fst, (continuous_apply _).comp continuous_snd]
#align homeomorph.pi_split_at Homeomorph.piSplitAt

/- warning: homeomorph.fun_split_at -> Homeomorph.funSplitAt is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} [_inst_5 : DecidableEq.{succ u2} ι] (i : ι), Homeomorph.{max u2 u1, max u2 u1} (ι -> β) (Prod.{u1, max u2 u1} β ((Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) -> β)) (Pi.topologicalSpace.{u2, u1} ι (fun (ᾰ : ι) => β) (fun (a : ι) => _inst_2)) (Prod.topologicalSpace.{u1, max u2 u1} β ((Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) -> β) _inst_2 (Pi.topologicalSpace.{u2, u1} (Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) (fun (ᾰ : Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) => β) (fun (a : Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) => _inst_2)))
but is expected to have type
  forall {β : Type.{u1}} [_inst_2 : TopologicalSpace.{u1} β] {ι : Type.{u2}} [_inst_5 : DecidableEq.{succ u2} ι] (i : ι), Homeomorph.{max u1 u2, max u1 u2} (ι -> β) (Prod.{u1, max u1 u2} β ((Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) -> β)) (Pi.topologicalSpace.{u2, u1} ι (fun (ᾰ : ι) => β) (fun (a : ι) => _inst_2)) (instTopologicalSpaceProd.{u1, max u1 u2} β ((Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) -> β) _inst_2 (Pi.topologicalSpace.{u2, u1} (Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) (fun (ᾰ : Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) => β) (fun (a : Subtype.{succ u2} ι (fun (j : ι) => Ne.{succ u2} ι j i)) => _inst_2)))
Case conversion may be inaccurate. Consider using '#align homeomorph.fun_split_at Homeomorph.funSplitAtₓ'. -/
/-- A product of copies of a topological space can be split as the binary product of one copy and
  the product of all the remaining copies. -/
@[simps]
def funSplitAt : (ι → β) ≃ₜ β × ({ j // j ≠ i } → β) :=
  piSplitAt i _
#align homeomorph.fun_split_at Homeomorph.funSplitAt

end

end Homeomorph

#print Equiv.toHomeomorphOfInducing /-
/-- An inducing equiv between topological spaces is a homeomorphism. -/
@[simps]
def Equiv.toHomeomorphOfInducing [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ β)
    (hf : Inducing f) : α ≃ₜ β :=
  { f with
    continuous_toFun := hf.Continuous
    continuous_invFun := hf.continuous_iff.2 <| by simpa using continuous_id }
#align equiv.to_homeomorph_of_inducing Equiv.toHomeomorphOfInducing
-/

namespace Continuous

variable [TopologicalSpace α] [TopologicalSpace β]

/- warning: continuous.continuous_symm_of_equiv_compact_to_t2 -> Continuous.continuous_symm_of_equiv_compact_to_t2 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : TopologicalSpace.{u2} β] [_inst_3 : CompactSpace.{u1} α _inst_1] [_inst_4 : T2Space.{u2} β _inst_2] {f : Equiv.{succ u1, succ u2} α β}, (Continuous.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) f)) -> (Continuous.{u2, u1} β α _inst_2 _inst_1 (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β f)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : TopologicalSpace.{u2} α] [_inst_2 : TopologicalSpace.{u1} β] [_inst_3 : CompactSpace.{u2} α _inst_1] [_inst_4 : T2Space.{u1} β _inst_2] {f : Equiv.{succ u2, succ u1} α β}, (Continuous.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) f)) -> (Continuous.{u1, u2} β α _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β f)))
Case conversion may be inaccurate. Consider using '#align continuous.continuous_symm_of_equiv_compact_to_t2 Continuous.continuous_symm_of_equiv_compact_to_t2ₓ'. -/
theorem continuous_symm_of_equiv_compact_to_t2 [CompactSpace α] [T2Space β] {f : α ≃ β}
    (hf : Continuous f) : Continuous f.symm :=
  by
  rw [continuous_iff_isClosed]
  intro C hC
  have hC' : IsClosed (f '' C) := (hC.is_compact.image hf).IsClosed
  rwa [Equiv.image_eq_preimage] at hC'
#align continuous.continuous_symm_of_equiv_compact_to_t2 Continuous.continuous_symm_of_equiv_compact_to_t2

#print Continuous.homeoOfEquivCompactToT2 /-
/-- Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `continuous.homeo_of_equiv_compact_to_t2.t1_counterexample`). -/
@[simps]
def homeoOfEquivCompactToT2 [CompactSpace α] [T2Space β] {f : α ≃ β} (hf : Continuous f) : α ≃ₜ β :=
  { f with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 }
#align continuous.homeo_of_equiv_compact_to_t2 Continuous.homeoOfEquivCompactToT2
-/

end Continuous

