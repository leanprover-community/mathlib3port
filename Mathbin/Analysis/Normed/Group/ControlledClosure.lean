/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module analysis.normed.group.controlled_closure
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.Analysis.SpecificLimits.Normed

/-! # Extending a backward bound on a normed group homomorphism from a dense set

Possible TODO (from the PR's review, https://github.com/leanprover-community/mathlib/pull/8498 ):
"This feels a lot like the second step in the proof of the Banach open mapping theorem
(`exists_preimage_norm_le`) ... wonder if it would be possible to refactor it using one of [the
lemmas in this file]."
-/


open Filter Finset

open Topology BigOperators

variable {G : Type _} [NormedAddCommGroup G] [CompleteSpace G]

variable {H : Type _} [NormedAddCommGroup H]

/- warning: controlled_closure_of_complete -> controlled_closure_of_complete is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} G] [_inst_2 : CompleteSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1)))] {H : Type.{u2}} [_inst_3 : NormedAddCommGroup.{u2} H] {f : NormedAddGroupHom.{u1, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)} {K : AddSubgroup.{u2} H (NormedAddGroup.toAddGroup.{u2} H (NormedAddCommGroup.toNormedAddGroup.{u2} H _inst_3))} {C : Real} {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) C) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (NormedAddGroupHom.SurjectiveOnWith.{u1, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3) f K C) -> (NormedAddGroupHom.SurjectiveOnWith.{u1, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3) f (AddSubgroup.topologicalClosure.{u2} H (UniformSpace.toTopologicalSpace.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))) (NormedAddGroup.toAddGroup.{u2} H (NormedAddCommGroup.toNormedAddGroup.{u2} H _inst_3)) (SeminormedAddCommGroup.to_topologicalAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) K) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) C ε))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u2} G] [_inst_2 : CompleteSpace.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} G _inst_1)))] {H : Type.{u1}} [_inst_3 : NormedAddCommGroup.{u1} H] {f : NormedAddGroupHom.{u2, u1} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} H _inst_3)} {K : AddSubgroup.{u1} H (NormedAddGroup.toAddGroup.{u1} H (NormedAddCommGroup.toNormedAddGroup.{u1} H _inst_3))} {C : Real} {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) C) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (NormedAddGroupHom.SurjectiveOnWith.{u2, u1} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} H _inst_3) f K C) -> (NormedAddGroupHom.SurjectiveOnWith.{u2, u1} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} H _inst_3) f (AddSubgroup.topologicalClosure.{u1} H (UniformSpace.toTopologicalSpace.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} H _inst_3)))) (NormedAddGroup.toAddGroup.{u1} H (NormedAddCommGroup.toNormedAddGroup.{u1} H _inst_3)) (SeminormedAddCommGroup.to_topologicalAddGroup.{u1} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} H _inst_3)) K) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) C ε))
Case conversion may be inaccurate. Consider using '#align controlled_closure_of_complete controlled_closure_of_completeₓ'. -/
/-- Given `f : normed_add_group_hom G H` for some complete `G` and a subgroup `K` of `H`, if every
element `x` of `K` has a preimage under `f` whose norm is at most `C*‖x‖` then the same holds for
elements of the (topological) closure of `K` with constant `C+ε` instead of `C`, for any
positive `ε`.
-/
theorem controlled_closure_of_complete {f : NormedAddGroupHom G H} {K : AddSubgroup H} {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hyp : f.SurjectiveOnWith K C) :
    f.SurjectiveOnWith K.topologicalClosure (C + ε) :=
  by
  rintro (h : H) (h_in : h ∈ K.topological_closure)
  -- We first get rid of the easy case where `h = 0`.
  by_cases hyp_h : h = 0
  · rw [hyp_h]
    use 0
    simp
  /- The desired preimage will be constructed as the sum of a series. Convergence of
    the series will be guaranteed by completeness of `G`. We first write `h` as the sum
    of a sequence `v` of elements of `K` which starts close to `h` and then quickly goes to zero.
    The sequence `b` below quantifies this. -/
  set b : ℕ → ℝ := fun i => (1 / 2) ^ i * (ε * ‖h‖ / 2) / C
  have b_pos : ∀ i, 0 < b i := by
    intro i
    field_simp [b, hC]
    exact
      div_pos (mul_pos hε (norm_pos_iff.mpr hyp_h)) (mul_pos (by norm_num : (0 : ℝ) < 2 ^ i * 2) hC)
  obtain
    ⟨v : ℕ → H, lim_v : tendsto (fun n : ℕ => ∑ k in range (n + 1), v k) at_top (𝓝 h), v_in :
      ∀ n, v n ∈ K, hv₀ : ‖v 0 - h‖ < b 0, hv : ∀ n > 0, ‖v n‖ < b n⟩ :=
    controlled_sum_of_mem_closure h_in b_pos
  /- The controlled surjectivity assumption on `f` allows to build preimages `u n` for all
    elements `v n` of the `v` sequence.-/
  have : ∀ n, ∃ m' : G, f m' = v n ∧ ‖m'‖ ≤ C * ‖v n‖ := fun n : ℕ => hyp (v n) (v_in n)
  choose u hu hnorm_u using this
  /- The desired series `s` is then obtained by summing `u`. We then check our choice of
    `b` ensures `s` is Cauchy. -/
  set s : ℕ → G := fun n => ∑ k in range (n + 1), u k
  have : CauchySeq s :=
    by
    apply NormedAddCommGroup.cauchy_series_of_le_geometric'' (by norm_num) one_half_lt_one
    rintro n (hn : n ≥ 1)
    calc
      ‖u n‖ ≤ C * ‖v n‖ := hnorm_u n
      _ ≤ C * b n := (mul_le_mul_of_nonneg_left (hv _ <| nat.succ_le_iff.mp hn).le hC.le)
      _ = (1 / 2) ^ n * (ε * ‖h‖ / 2) := by simp [b, mul_div_cancel' _ hC.ne.symm]
      _ = ε * ‖h‖ / 2 * (1 / 2) ^ n := mul_comm _ _
      
  -- We now show that the limit `g` of `s` is the desired preimage.
  obtain ⟨g : G, hg⟩ := cauchySeq_tendsto_of_complete this
  refine' ⟨g, _, _⟩
  · -- We indeed get a preimage. First note:
    have : f ∘ s = fun n => ∑ k in range (n + 1), v k :=
      by
      ext n
      simp [map_sum, hu]
    /- In the above equality, the left-hand-side converges to `f g` by continuity of `f` and
           definition of `g` while the right-hand-side converges to `h` by construction of `v` so
           `g` is indeed a preimage of `h`. -/
    rw [← this] at lim_v
    exact tendsto_nhds_unique ((f.continuous.tendsto g).comp hg) lim_v
  · -- Then we need to estimate the norm of `g`, using our careful choice of `b`.
    suffices : ∀ n, ‖s n‖ ≤ (C + ε) * ‖h‖
    exact le_of_tendsto' (continuous_norm.continuous_at.tendsto.comp hg) this
    intro n
    have hnorm₀ : ‖u 0‖ ≤ C * b 0 + C * ‖h‖ :=
      by
      have :=
        calc
          ‖v 0‖ ≤ ‖h‖ + ‖v 0 - h‖ := norm_le_insert' _ _
          _ ≤ ‖h‖ + b 0 := by apply add_le_add_left hv₀.le
          
      calc
        ‖u 0‖ ≤ C * ‖v 0‖ := hnorm_u 0
        _ ≤ C * (‖h‖ + b 0) := (mul_le_mul_of_nonneg_left this hC.le)
        _ = C * b 0 + C * ‖h‖ := by rw [add_comm, mul_add]
        
    have : (∑ k in range (n + 1), C * b k) ≤ ε * ‖h‖ :=
      calc
        (∑ k in range (n + 1), C * b k) = (∑ k in range (n + 1), (1 / 2) ^ k) * (ε * ‖h‖ / 2) := by
          simp only [b, mul_div_cancel' _ hC.ne.symm, ← sum_mul]
        _ ≤ 2 * (ε * ‖h‖ / 2) :=
          (mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by nlinarith [hε, norm_nonneg h]))
        _ = ε * ‖h‖ := mul_div_cancel' _ two_ne_zero
        
    calc
      ‖s n‖ ≤ ∑ k in range (n + 1), ‖u k‖ := norm_sum_le _ _
      _ = (∑ k in range n, ‖u (k + 1)‖) + ‖u 0‖ := (sum_range_succ' _ _)
      _ ≤ (∑ k in range n, C * ‖v (k + 1)‖) + ‖u 0‖ :=
        (add_le_add_right (sum_le_sum fun _ _ => hnorm_u _) _)
      _ ≤ (∑ k in range n, C * b (k + 1)) + (C * b 0 + C * ‖h‖) :=
        (add_le_add (sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hv _ k.succ_pos).le hC.le)
          hnorm₀)
      _ = (∑ k in range (n + 1), C * b k) + C * ‖h‖ := by rw [← add_assoc, sum_range_succ']
      _ ≤ (C + ε) * ‖h‖ := by
        rw [add_comm, add_mul]
        apply add_le_add_left this
      
#align controlled_closure_of_complete controlled_closure_of_complete

/- warning: controlled_closure_range_of_complete -> controlled_closure_range_of_complete is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : NormedAddCommGroup.{u1} G] [_inst_2 : CompleteSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1)))] {H : Type.{u2}} [_inst_3 : NormedAddCommGroup.{u2} H] {f : NormedAddGroupHom.{u1, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)} {K : Type.{u3}} [_inst_4 : SeminormedAddCommGroup.{u3} K] {j : NormedAddGroupHom.{u3, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)}, (forall (x : K), Eq.{1} Real (Norm.norm.{u2} H (NormedAddCommGroup.toHasNorm.{u2} H _inst_3) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (NormedAddGroupHom.{u3, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) (fun (_x : NormedAddGroupHom.{u3, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) => K -> H) (NormedAddGroupHom.hasCoeToFun.{u3, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) j x)) (Norm.norm.{u3} K (SeminormedAddCommGroup.toHasNorm.{u3} K _inst_4) x)) -> (forall {C : Real} {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) C) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (forall (k : K), Exists.{succ u1} G (fun (g : G) => And (Eq.{succ u2} H (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (NormedAddGroupHom.{u1, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) (fun (_x : NormedAddGroupHom.{u1, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) => G -> H) (NormedAddGroupHom.hasCoeToFun.{u1, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) f g) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (NormedAddGroupHom.{u3, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) (fun (_x : NormedAddGroupHom.{u3, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) => K -> H) (NormedAddGroupHom.hasCoeToFun.{u3, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) j k)) (LE.le.{0} Real Real.hasLe (Norm.norm.{u1} G (NormedAddCommGroup.toHasNorm.{u1} G _inst_1) g) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) C (Norm.norm.{u3} K (SeminormedAddCommGroup.toHasNorm.{u3} K _inst_4) k))))) -> (NormedAddGroupHom.SurjectiveOnWith.{u1, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3) f (AddSubgroup.topologicalClosure.{u2} H (UniformSpace.toTopologicalSpace.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))) (SeminormedAddGroup.toAddGroup.{u2} H (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3))) (SeminormedAddCommGroup.to_topologicalAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) (NormedAddGroupHom.range.{u3, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3) j)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) C ε)))
but is expected to have type
  forall {G : Type.{u3}} [_inst_1 : NormedAddCommGroup.{u3} G] [_inst_2 : CompleteSpace.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1)))] {H : Type.{u2}} [_inst_3 : NormedAddCommGroup.{u2} H] {f : NormedAddGroupHom.{u3, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)} {K : Type.{u1}} [_inst_4 : SeminormedAddCommGroup.{u1} K] {j : NormedAddGroupHom.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)}, (forall (x : K), Eq.{1} Real (Norm.norm.{u2} H (NormedAddCommGroup.toNorm.{u2} H _inst_3) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (NormedAddGroupHom.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) K (fun (_x : K) => H) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (NormedAddGroupHom.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) K H (AddZeroClass.toAdd.{u1} K (AddMonoid.toAddZeroClass.{u1} K (SubNegMonoid.toAddMonoid.{u1} K (AddGroup.toSubNegMonoid.{u1} K (SeminormedAddGroup.toAddGroup.{u1} K (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} K _inst_4)))))) (AddZeroClass.toAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (AddGroup.toSubNegMonoid.{u2} H (SeminormedAddGroup.toAddGroup.{u2} H (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3))))))) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (NormedAddGroupHom.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) K H (AddMonoid.toAddZeroClass.{u1} K (SubNegMonoid.toAddMonoid.{u1} K (AddGroup.toSubNegMonoid.{u1} K (SeminormedAddGroup.toAddGroup.{u1} K (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} K _inst_4))))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (AddGroup.toSubNegMonoid.{u2} H (SeminormedAddGroup.toAddGroup.{u2} H (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))))) (NormedAddGroupHom.toAddMonoidHomClass.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))) j x)) (Norm.norm.{u1} K (SeminormedAddCommGroup.toNorm.{u1} K _inst_4) x)) -> (forall {C : Real} {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) C) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (forall (k : K), Exists.{succ u3} G (fun (g : G) => And (Eq.{succ u2} H (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (NormedAddGroupHom.{u3, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) G (fun (_x : G) => H) (AddHomClass.toFunLike.{max u3 u2, u3, u2} (NormedAddGroupHom.{u3, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) G H (AddZeroClass.toAdd.{u3} G (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (SeminormedAddGroup.toAddGroup.{u3} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1))))))) (AddZeroClass.toAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (AddGroup.toSubNegMonoid.{u2} H (SeminormedAddGroup.toAddGroup.{u2} H (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3))))))) (AddMonoidHomClass.toAddHomClass.{max u3 u2, u3, u2} (NormedAddGroupHom.{u3, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) G H (AddMonoid.toAddZeroClass.{u3} G (SubNegMonoid.toAddMonoid.{u3} G (AddGroup.toSubNegMonoid.{u3} G (SeminormedAddGroup.toAddGroup.{u3} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u3} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1)))))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (AddGroup.toSubNegMonoid.{u2} H (SeminormedAddGroup.toAddGroup.{u2} H (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))))) (NormedAddGroupHom.toAddMonoidHomClass.{u3, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))) f g) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (NormedAddGroupHom.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) K (fun (_x : K) => H) (AddHomClass.toFunLike.{max u1 u2, u1, u2} (NormedAddGroupHom.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) K H (AddZeroClass.toAdd.{u1} K (AddMonoid.toAddZeroClass.{u1} K (SubNegMonoid.toAddMonoid.{u1} K (AddGroup.toSubNegMonoid.{u1} K (SeminormedAddGroup.toAddGroup.{u1} K (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} K _inst_4)))))) (AddZeroClass.toAdd.{u2} H (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (AddGroup.toSubNegMonoid.{u2} H (SeminormedAddGroup.toAddGroup.{u2} H (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3))))))) (AddMonoidHomClass.toAddHomClass.{max u1 u2, u1, u2} (NormedAddGroupHom.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) K H (AddMonoid.toAddZeroClass.{u1} K (SubNegMonoid.toAddMonoid.{u1} K (AddGroup.toSubNegMonoid.{u1} K (SeminormedAddGroup.toAddGroup.{u1} K (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} K _inst_4))))) (AddMonoid.toAddZeroClass.{u2} H (SubNegMonoid.toAddMonoid.{u2} H (AddGroup.toSubNegMonoid.{u2} H (SeminormedAddGroup.toAddGroup.{u2} H (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))))) (NormedAddGroupHom.toAddMonoidHomClass.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))) j k)) (LE.le.{0} Real Real.instLEReal (Norm.norm.{u3} G (NormedAddCommGroup.toNorm.{u3} G _inst_1) g) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) C (Norm.norm.{u1} K (SeminormedAddCommGroup.toNorm.{u1} K _inst_4) k))))) -> (NormedAddGroupHom.SurjectiveOnWith.{u3, u2} G H (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3) f (AddSubgroup.topologicalClosure.{u2} H (UniformSpace.toTopologicalSpace.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)))) (SeminormedAddGroup.toAddGroup.{u2} H (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3))) (SeminormedAddCommGroup.to_topologicalAddGroup.{u2} H (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3)) (NormedAddGroupHom.range.{u1, u2} K H _inst_4 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} H _inst_3) j)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) C ε)))
Case conversion may be inaccurate. Consider using '#align controlled_closure_range_of_complete controlled_closure_range_of_completeₓ'. -/
/-- Given `f : normed_add_group_hom G H` for some complete `G`, if every element `x` of the image of
an isometric immersion `j : normed_add_group_hom K H` has a preimage under `f` whose norm is at most
`C*‖x‖` then the same holds for elements of the (topological) closure of this image with constant
`C+ε` instead of `C`, for any positive `ε`.
This is useful in particular if `j` is the inclusion of a normed group into its completion
(in this case the closure is the full target group).
-/
theorem controlled_closure_range_of_complete {f : NormedAddGroupHom G H} {K : Type _}
    [SeminormedAddCommGroup K] {j : NormedAddGroupHom K H} (hj : ∀ x, ‖j x‖ = ‖x‖) {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hyp : ∀ k, ∃ g, f g = j k ∧ ‖g‖ ≤ C * ‖k‖) :
    f.SurjectiveOnWith j.range.topologicalClosure (C + ε) :=
  by
  replace hyp : ∀ h ∈ j.range, ∃ g, f g = h ∧ ‖g‖ ≤ C * ‖h‖
  · intro h h_in
    rcases(j.mem_range _).mp h_in with ⟨k, rfl⟩
    rw [hj]
    exact hyp k
  exact controlled_closure_of_complete hC hε hyp
#align controlled_closure_range_of_complete controlled_closure_range_of_complete

