/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin

! This file was ported from Lean 3 source module ring_theory.coprime.ideal
! leanprover-community/mathlib commit 932872382355f00112641d305ba0619305dc8642
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Dfinsupp
import Mathbin.RingTheory.Ideal.Operations

/-!
# An additional lemma about coprime ideals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This lemma generalises `exists_sum_eq_one_iff_pairwise_coprime` to the case of non-principal ideals.
It is on a separate file due to import requirements.
-/


namespace Ideal

variable {ι R : Type _} [CommSemiring R]

/- warning: ideal.supr_infi_eq_top_iff_pairwise -> Ideal.iSup_iInf_eq_top_iff_pairwise is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : CommSemiring.{u2} R] {t : Finset.{u1} ι}, (Finset.Nonempty.{u1} ι t) -> (forall (I : ι -> (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))), Iff (Eq.{succ u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (iSup.{u2, succ u1} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Submodule.completeLattice.{u2, u2} R R (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) ι (fun (i : ι) => iSup.{u2, 0} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (ConditionallyCompleteLattice.toHasSup.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (CompleteLattice.toConditionallyCompleteLattice.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Submodule.completeLattice.{u2, u2} R R (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i t) (fun (H : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i t) => iInf.{u2, succ u1} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Submodule.hasInf.{u2, u2} R R (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) ι (fun (j : ι) => iInf.{u2, 0} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Submodule.hasInf.{u2, u2} R R (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j t) (fun (hj : Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) j t) => iInf.{u2, 0} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Submodule.hasInf.{u2, u2} R R (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))) (Ne.{succ u1} ι j i) (fun (ij : Ne.{succ u1} ι j i) => I j)))))) (Top.top.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Submodule.hasTop.{u2, u2} R R (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1))))) (Set.Pairwise.{u1} ι ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) t) (fun (i : ι) (j : ι) => Eq.{succ u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Sup.sup.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (SemilatticeSup.toHasSup.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (IdemSemiring.toSemilatticeSup.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Submodule.idemSemiring.{u2, u2} R _inst_1 R (CommSemiring.toSemiring.{u2} R _inst_1) (Algebra.id.{u2} R _inst_1)))) (I i) (I j)) (Top.top.{u2} (Ideal.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)) (Submodule.hasTop.{u2, u2} R R (CommSemiring.toSemiring.{u2} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))) (Semiring.toModule.{u2} R (CommSemiring.toSemiring.{u2} R _inst_1)))))))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] {t : Finset.{u2} ι}, (Finset.Nonempty.{u2} ι t) -> (forall (I : ι -> (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))), Iff (Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (iSup.{u1, succ u2} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) ι (fun (i : ι) => iSup.{u1, 0} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ConditionallyCompleteLattice.toSupSet.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.completeLattice.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i t) (fun (H : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i t) => iInf.{u1, succ u2} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instInfSetSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) ι (fun (j : ι) => iInf.{u1, 0} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instInfSetSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j t) (fun (hj : Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j t) => iInf.{u1, 0} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instInfSetSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))) (Ne.{succ u2} ι j i) (fun (ij : Ne.{succ u2} ι j i) => I j)))))) (Top.top.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instTopSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (Set.Pairwise.{u2} ι (Finset.toSet.{u2} ι t) (fun (i : ι) (j : ι) => Eq.{succ u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Sup.sup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (SemilatticeSup.toSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (IdemCommSemiring.toSemilatticeSup.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Ideal.instIdemCommSemiringIdealToSemiring.{u1} R _inst_1))) (I i) (I j)) (Top.top.{u1} (Ideal.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (Submodule.instTopSubmodule.{u1, u1} R R (CommSemiring.toSemiring.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Semiring.toModule.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align ideal.supr_infi_eq_top_iff_pairwise Ideal.iSup_iInf_eq_top_iff_pairwiseₓ'. -/
/-- A finite family of ideals is pairwise coprime (that is, any two of them generate the whole ring)
iff when taking all the possible intersections of all but one of these ideals, the resulting family
of ideals still generate the whole ring.

For example with three ideals : `I ⊔ J = I ⊔ K = J ⊔ K = ⊤ ↔ (I ⊓ J) ⊔ (I ⊓ K) ⊔ (J ⊓ K) = ⊤`.

When ideals are all of the form `I i = R ∙ s i`, this is equivalent to the
`exists_sum_eq_one_iff_pairwise_coprime` lemma.-/
theorem iSup_iInf_eq_top_iff_pairwise {t : Finset ι} (h : t.Nonempty) (I : ι → Ideal R) :
    (⨆ i ∈ t, ⨅ (j) (hj : j ∈ t) (ij : j ≠ i), I j) = ⊤ ↔
      (t : Set ι).Pairwise fun i j => I i ⊔ I j = ⊤ :=
  by
  haveI : DecidableEq ι := Classical.decEq ι
  rw [eq_top_iff_one, Submodule.mem_iSup_finset_iff_exists_sum]
  refine' h.cons_induction _ _ <;> clear t h
  · simp only [Finset.sum_singleton, Finset.coe_singleton, Set.pairwise_singleton, iff_true_iff]
    refine' fun a => ⟨fun i => if h : i = a then ⟨1, _⟩ else 0, _⟩
    · rw [h];
      simp only [Finset.mem_singleton, Ne.def, iInf_iInf_eq_left, eq_self_iff_true, not_true,
        iInf_false]
    · simp only [dif_pos, dif_ctx_congr, Submodule.coe_mk, eq_self_iff_true]
  intro a t hat h ih
  rw [Finset.coe_cons,
    Set.pairwise_insert_of_symmetric fun i j (h : I i ⊔ I j = ⊤) => sup_comm.trans h]
  constructor
  · rintro ⟨μ, hμ⟩; rw [Finset.sum_cons] at hμ
    refine' ⟨ih.mp ⟨Pi.single h.some ⟨μ a, _⟩ + fun i => ⟨μ i, _⟩, _⟩, fun b hb ab => _⟩
    · have := Submodule.coe_mem (μ a); rw [mem_infi] at this⊢
      --for some reason `simp only [mem_infi]` times out
      intro i;
      specialize this i; rw [mem_infi, mem_infi] at this⊢
      intro hi _; apply this (Finset.subset_cons _ hi)
      rintro rfl; exact hat hi
    · have := Submodule.coe_mem (μ i); simp only [mem_infi] at this⊢
      intro j hj ij; exact this _ (Finset.subset_cons _ hj) ij
    · rw [← @if_pos _ _ h.some_spec R (μ a) 0, ← Finset.sum_pi_single', ← Finset.sum_add_distrib] at
        hμ
      convert hμ; ext i; rw [Pi.add_apply, Submodule.coe_add, Submodule.coe_mk]
      by_cases hi : i = h.some
      · rw [hi, Pi.single_eq_same, Pi.single_eq_same, Submodule.coe_mk]
      · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, Submodule.coe_zero]
    · rw [eq_top_iff_one, Submodule.mem_sup]
      rw [add_comm] at hμ; refine' ⟨_, _, _, _, hμ⟩
      · refine' sum_mem _ fun x hx => _
        have := Submodule.coe_mem (μ x); simp only [mem_infi] at this
        apply this _ (Finset.mem_cons_self _ _); rintro rfl; exact hat hx
      · have := Submodule.coe_mem (μ a); simp only [mem_infi] at this
        exact this _ (Finset.subset_cons _ hb) ab.symm
  · rintro ⟨hs, Hb⟩
    obtain ⟨μ, hμ⟩ := ih.mpr hs
    have := sup_infi_eq_top fun b hb => Hb b hb (ne_of_mem_of_not_mem hb hat).symm
    rw [eq_top_iff_one, Submodule.mem_sup] at this
    obtain ⟨u, hu, v, hv, huv⟩ := this
    refine' ⟨fun i => if hi : i = a then ⟨v, _⟩ else ⟨u * μ i, _⟩, _⟩
    · simp only [mem_infi] at hv⊢
      intro j hj ij; rw [Finset.mem_cons, ← hi] at hj
      exact hv _ (hj.resolve_left ij)
    · have := Submodule.coe_mem (μ i); simp only [mem_infi] at this⊢
      intro j hj ij
      rcases finset.mem_cons.mp hj with (rfl | hj)
      · exact mul_mem_right _ _ hu
      · exact mul_mem_left _ _ (this _ hj ij)
    · rw [Finset.sum_cons, dif_pos rfl, add_comm]
      rw [← mul_one u] at huv; rw [← huv, ← hμ, Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro j hj
      rw [dif_neg]; rfl
      rintro rfl; exact hat hj
#align ideal.supr_infi_eq_top_iff_pairwise Ideal.iSup_iInf_eq_top_iff_pairwise

end Ideal

