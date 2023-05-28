/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module ring_theory.adjoin.tower
! leanprover-community/mathlib commit 94eaaaa6064d32e98cf838789144cf5318c37cf0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Adjoin.Fg

/-!
# Adjoining elements and being finitely generated in an algebra tower

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main results

 * `algebra.fg_trans'`: if `S` is finitely generated as `R`-algebra and `A` as `S`-algebra,
   then `A` is finitely generated as `R`-algebra
 * `fg_of_fg_of_fg`: **Artin--Tate lemma**: if C/B/A is a tower of rings, and A is noetherian, and
   C is algebra-finite over A, and C is module-finite over B, then B is algebra-finite over A.
-/


open Pointwise

universe u v w u₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace Algebra

#print Algebra.adjoin_algebraMap /-
theorem adjoin_algebraMap (R : Type u) (S : Type v) (A : Type w) [CommSemiring R] [CommSemiring S]
    [Semiring A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (s : Set S) :
    adjoin R (algebraMap S A '' s) = (adjoin R s).map (IsScalarTower.toAlgHom R S A) :=
  le_antisymm (adjoin_le <| Set.image_subset_iff.2 fun y hy => ⟨y, subset_adjoin hy, rfl⟩)
    (Subalgebra.map_le.2 <| adjoin_le fun y hy => subset_adjoin ⟨y, hy, rfl⟩)
#align algebra.adjoin_algebra_map Algebra.adjoin_algebraMap
-/

/- warning: algebra.adjoin_restrict_scalars -> Algebra.adjoin_restrictScalars is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_restrict_scalars Algebra.adjoin_restrictScalarsₓ'. -/
theorem adjoin_restrictScalars (C D E : Type _) [CommSemiring C] [CommSemiring D] [CommSemiring E]
    [Algebra C D] [Algebra C E] [Algebra D E] [IsScalarTower C D E] (S : Set E) :
    (Algebra.adjoin D S).restrictScalars C =
      (Algebra.adjoin ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) S).restrictScalars
        C :=
  by
  suffices
    Set.range (algebraMap D E) =
      Set.range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E)
    by
    ext x
    change x ∈ Subsemiring.closure (_ ∪ S) ↔ x ∈ Subsemiring.closure (_ ∪ S)
    rw [this]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨⟨algebraMap D E y, ⟨y, ⟨Algebra.mem_top, rfl⟩⟩⟩, hy⟩
  · rintro ⟨⟨y, ⟨z, ⟨h0, h1⟩⟩⟩, h2⟩
    exact ⟨z, Eq.trans h1 h2⟩
#align algebra.adjoin_restrict_scalars Algebra.adjoin_restrictScalars

/- warning: algebra.adjoin_res_eq_adjoin_res -> Algebra.adjoin_res_eq_adjoin_res is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align algebra.adjoin_res_eq_adjoin_res Algebra.adjoin_res_eq_adjoin_resₓ'. -/
theorem adjoin_res_eq_adjoin_res (C D E F : Type _) [CommSemiring C] [CommSemiring D]
    [CommSemiring E] [CommSemiring F] [Algebra C D] [Algebra C E] [Algebra C F] [Algebra D F]
    [Algebra E F] [IsScalarTower C D F] [IsScalarTower C E F] {S : Set D} {T : Set E}
    (hS : Algebra.adjoin C S = ⊤) (hT : Algebra.adjoin C T = ⊤) :
    (Algebra.adjoin E (algebraMap D F '' S)).restrictScalars C =
      (Algebra.adjoin D (algebraMap E F '' T)).restrictScalars C :=
  by
  rw [adjoin_restrict_scalars C E, adjoin_restrict_scalars C D, ← hS, ← hT, ← Algebra.adjoin_image,
    ← Algebra.adjoin_image, ← AlgHom.coe_toRingHom, ← AlgHom.coe_toRingHom,
    IsScalarTower.coe_toAlgHom, IsScalarTower.coe_toAlgHom, ← adjoin_union_eq_adjoin_adjoin, ←
    adjoin_union_eq_adjoin_adjoin, Set.union_comm]
#align algebra.adjoin_res_eq_adjoin_res Algebra.adjoin_res_eq_adjoin_res

end Algebra

section

open Classical

/- warning: algebra.fg_trans' -> Algebra.fg_trans' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} {A : Type.{u3}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : CommSemiring.{u2} S] [_inst_3 : CommSemiring.{u3} A] [_inst_4 : Algebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : Algebra.{u2, u3} S A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3)] [_inst_6 : Algebra.{u1, u3} R A _inst_1 (CommSemiring.toSemiring.{u3} A _inst_3)] [_inst_7 : IsScalarTower.{u1, u2, u3} R S A (SMulZeroClass.toHasSmul.{u1, u2} R S (AddZeroClass.toHasZero.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} R S (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} R S (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u2} S (AddMonoid.toAddZeroClass.{u2} S (AddCommMonoid.toAddMonoid.{u2} S (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))))) (Module.toMulActionWithZero.{u1, u2} R S (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (Algebra.toModule.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4))))) (SMulZeroClass.toHasSmul.{u2, u3} S A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3))))))) (SMulWithZero.toSmulZeroClass.{u2, u3} S A (MulZeroClass.toHasZero.{u2} S (MulZeroOneClass.toMulZeroClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3))))))) (MulActionWithZero.toSMulWithZero.{u2, u3} S A (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3))))))) (Module.toMulActionWithZero.{u2, u3} S A (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3)))) (Algebra.toModule.{u2, u3} S A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_5))))) (SMulZeroClass.toHasSmul.{u1, u3} R A (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3))))))) (SMulWithZero.toSmulZeroClass.{u1, u3} R A (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3))))))) (MulActionWithZero.toSMulWithZero.{u1, u3} R A (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u3} A (AddMonoid.toAddZeroClass.{u3} A (AddCommMonoid.toAddMonoid.{u3} A (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3))))))) (Module.toMulActionWithZero.{u1, u3} R A (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} A (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} A (Semiring.toNonAssocSemiring.{u3} A (CommSemiring.toSemiring.{u3} A _inst_3)))) (Algebra.toModule.{u1, u3} R A _inst_1 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_6)))))], (Subalgebra.FG.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4 (Top.top.{u2} (Subalgebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4) (CompleteLattice.toHasTop.{u2} (Subalgebra.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4) (Algebra.Subalgebra.completeLattice.{u1, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4)))) -> (Subalgebra.FG.{u2, u3} S A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_5 (Top.top.{u3} (Subalgebra.{u2, u3} S A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_5) (CompleteLattice.toHasTop.{u3} (Subalgebra.{u2, u3} S A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_5) (Algebra.Subalgebra.completeLattice.{u2, u3} S A _inst_2 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_5)))) -> (Subalgebra.FG.{u1, u3} R A _inst_1 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_6 (Top.top.{u3} (Subalgebra.{u1, u3} R A _inst_1 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_6) (CompleteLattice.toHasTop.{u3} (Subalgebra.{u1, u3} R A _inst_1 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_6) (Algebra.Subalgebra.completeLattice.{u1, u3} R A _inst_1 (CommSemiring.toSemiring.{u3} A _inst_3) _inst_6))))
but is expected to have type
  forall {R : Type.{u3}} {S : Type.{u2}} {A : Type.{u1}} [_inst_1 : CommSemiring.{u3} R] [_inst_2 : CommSemiring.{u2} S] [_inst_3 : CommSemiring.{u1} A] [_inst_4 : Algebra.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2)] [_inst_5 : Algebra.{u2, u1} S A _inst_2 (CommSemiring.toSemiring.{u1} A _inst_3)] [_inst_6 : Algebra.{u3, u1} R A _inst_1 (CommSemiring.toSemiring.{u1} A _inst_3)] [_inst_7 : IsScalarTower.{u3, u2, u1} R S A (Algebra.toSMul.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4) (Algebra.toSMul.{u2, u1} S A _inst_2 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_5) (Algebra.toSMul.{u3, u1} R A _inst_1 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_6)], (Subalgebra.FG.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4 (Top.top.{u2} (Subalgebra.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4) (CompleteLattice.toTop.{u2} (Subalgebra.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4) (Algebra.instCompleteLatticeSubalgebra.{u3, u2} R S _inst_1 (CommSemiring.toSemiring.{u2} S _inst_2) _inst_4)))) -> (Subalgebra.FG.{u2, u1} S A _inst_2 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_5 (Top.top.{u1} (Subalgebra.{u2, u1} S A _inst_2 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_5) (CompleteLattice.toTop.{u1} (Subalgebra.{u2, u1} S A _inst_2 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_5) (Algebra.instCompleteLatticeSubalgebra.{u2, u1} S A _inst_2 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_5)))) -> (Subalgebra.FG.{u3, u1} R A _inst_1 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_6 (Top.top.{u1} (Subalgebra.{u3, u1} R A _inst_1 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_6) (CompleteLattice.toTop.{u1} (Subalgebra.{u3, u1} R A _inst_1 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_6) (Algebra.instCompleteLatticeSubalgebra.{u3, u1} R A _inst_1 (CommSemiring.toSemiring.{u1} A _inst_3) _inst_6))))
Case conversion may be inaccurate. Consider using '#align algebra.fg_trans' Algebra.fg_trans'ₓ'. -/
theorem Algebra.fg_trans' {R S A : Type _} [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (hRS : (⊤ : Subalgebra R S).FG)
    (hSA : (⊤ : Subalgebra S A).FG) : (⊤ : Subalgebra R A).FG :=
  let ⟨s, hs⟩ := hRS
  let ⟨t, ht⟩ := hSA
  ⟨s.image (algebraMap S A) ∪ t, by
    rw [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union_eq_adjoin_adjoin,
      Algebra.adjoin_algebraMap, hs, Algebra.map_top, IsScalarTower.adjoin_range_toAlgHom, ht,
      Subalgebra.restrictScalars_top]⟩
#align algebra.fg_trans' Algebra.fg_trans'

end

section ArtinTate

variable (C : Type _)

section Semiring

variable [CommSemiring A] [CommSemiring B] [Semiring C]

variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

open Finset Submodule

open Classical

/- warning: exists_subalgebra_of_fg -> exists_subalgebra_of_fg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align exists_subalgebra_of_fg exists_subalgebra_of_fgₓ'. -/
theorem exists_subalgebra_of_fg (hAC : (⊤ : Subalgebra A C).FG) (hBC : (⊤ : Submodule B C).FG) :
    ∃ B₀ : Subalgebra A B, B₀.FG ∧ (⊤ : Submodule B₀ C).FG :=
  by
  cases' hAC with x hx
  cases' hBC with y hy
  have := hy
  simp_rw [eq_top_iff', mem_span_finset] at this
  choose f hf
  let s : Finset B := Finset.image₂ f (x ∪ y * y) y
  have hxy :
    ∀ xi ∈ x, xi ∈ span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) :=
    fun xi hxi =>
    hf xi ▸
      sum_mem fun yj hyj =>
        smul_mem (span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C))
          ⟨f xi yj, Algebra.subset_adjoin <| mem_image₂_of_mem (mem_union_left _ hxi) hyj⟩
          (subset_span <| mem_insert_of_mem hyj)
  have hyy :
    span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) *
        span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) ≤
      span (Algebra.adjoin A (↑s : Set B)) (↑(insert 1 y : Finset C) : Set C) :=
    by
    rw [span_mul_span, span_le, coe_insert]
    rintro _ ⟨yi, yj, rfl | hyi, rfl | hyj, rfl⟩
    · rw [mul_one]
      exact subset_span (Set.mem_insert _ _)
    · rw [one_mul]
      exact subset_span (Set.mem_insert_of_mem _ hyj)
    · rw [mul_one]
      exact subset_span (Set.mem_insert_of_mem _ hyi)
    · rw [← hf (yi * yj)]
      exact
        SetLike.mem_coe.2
          (sum_mem fun yk hyk =>
            smul_mem (span (Algebra.adjoin A (↑s : Set B)) (insert 1 ↑y : Set C))
              ⟨f (yi * yj) yk,
                Algebra.subset_adjoin <|
                  mem_image₂_of_mem (mem_union_right _ <| mul_mem_mul hyi hyj) hyk⟩
              (subset_span <| Set.mem_insert_of_mem _ hyk : yk ∈ _))
  refine' ⟨Algebra.adjoin A (↑s : Set B), Subalgebra.fg_adjoin_finset _, insert 1 y, _⟩
  refine' restrict_scalars_injective A _ _ _
  rw [restrict_scalars_top, eq_top_iff, ← Algebra.top_toSubmodule, ← hx, Algebra.adjoin_eq_span,
    span_le]
  refine' fun r hr =>
    Submonoid.closure_induction hr (fun c hc => hxy c hc) (subset_span <| mem_insert_self _ _)
      fun p q hp hq => hyy <| Submodule.mul_mem_mul hp hq
#align exists_subalgebra_of_fg exists_subalgebra_of_fg

end Semiring

section Ring

variable [CommRing A] [CommRing B] [CommRing C]

variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- warning: fg_of_fg_of_fg -> fg_of_fg_of_fg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align fg_of_fg_of_fg fg_of_fg_of_fgₓ'. -/
/-- **Artin--Tate lemma**: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Stacks 00IS; Altman--Kleiman 16.17. -/
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).FG)
    (hBC : (⊤ : Submodule B C).FG) (hBCi : Function.Injective (algebraMap B C)) :
    (⊤ : Subalgebra A B).FG :=
  let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC
  Algebra.fg_trans' (B₀.fg_top.2 hAB₀) <|
    Subalgebra.fg_of_submodule_fg <|
      have : IsNoetherianRing B₀ := isNoetherianRing_of_fg hAB₀
      have : IsNoetherian B₀ C := isNoetherian_of_fg_of_noetherian' hB₀C
      fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap hBCi
#align fg_of_fg_of_fg fg_of_fg_of_fg

end Ring

end ArtinTate

