/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module ring_theory.finiteness
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.RestrictScalars
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.GroupTheory.Finiteness
import Mathbin.RingTheory.Ideal.Operations

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `submodule.fg`, `ideal.fg`
  These express that some object is finitely generated as *submodule* over some base ring.

- `module.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.

## Main results

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

-/


open Function (Surjective)

open BigOperators

namespace Submodule

variable {R : Type _} {M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]

open Set

/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def Fg (N : Submodule R M) : Prop :=
  ∃ S : Finset M, Submodule.span R ↑S = N
#align submodule.fg Submodule.Fg

theorem fg_def {N : Submodule R M} : N.Fg ↔ ∃ S : Set M, S.Finite ∧ span R S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_to_set t, h⟩,
    by
    rintro ⟨t', h, rfl⟩
    rcases finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩
#align submodule.fg_def Submodule.fg_def

theorem fg_iff_add_submonoid_fg (P : Submodule ℕ M) : P.Fg ↔ P.toAddSubmonoid.Fg :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_nat_eq_add_submonoid_closure] using hS⟩, fun ⟨S, hS⟩ =>
    ⟨S, by simpa [← span_nat_eq_add_submonoid_closure] using hS⟩⟩
#align submodule.fg_iff_add_submonoid_fg Submodule.fg_iff_add_submonoid_fg

theorem fg_iff_add_subgroup_fg {G : Type _} [AddCommGroup G] (P : Submodule ℤ G) :
    P.Fg ↔ P.toAddSubgroup.Fg :=
  ⟨fun ⟨S, hS⟩ => ⟨S, by simpa [← span_int_eq_add_subgroup_closure] using hS⟩, fun ⟨S, hS⟩ =>
    ⟨S, by simpa [← span_int_eq_add_subgroup_closure] using hS⟩⟩
#align submodule.fg_iff_add_subgroup_fg Submodule.fg_iff_add_subgroup_fg

theorem fg_iff_exists_fin_generating_family {N : Submodule R M} :
    N.Fg ↔ ∃ (n : ℕ)(s : Fin n → M), span R (range s) = N :=
  by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
  · rintro ⟨n, s, hs⟩
    refine' ⟨range s, finite_range s, hs⟩
#align submodule.fg_iff_exists_fin_generating_family Submodule.fg_iff_exists_fin_generating_family

/-- **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2,
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV) -/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type _} [CommRing R] {M : Type _}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.Fg) (hin : N ≤ I • N) :
    ∃ r : R, r - 1 ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) :=
  by
  rw [fg_def] at hn
  rcases hn with ⟨s, hfs, hs⟩
  have : ∃ r : R, r - 1 ∈ I ∧ N ≤ (I • span R s).comap (LinearMap.lsmul R M r) ∧ s ⊆ N :=
    by
    refine' ⟨1, _, _, _⟩
    · rw [sub_self]
      exact I.zero_mem
    · rw [hs]
      intro n hn
      rw [mem_comap]
      change (1 : R) • n ∈ I • N
      rw [one_smul]
      exact hin hn
    · rw [← span_le, hs]
      exact le_refl N
  clear hin hs
  revert this
  refine' Set.Finite.dinduction_on hfs (fun H => _) fun i s his hfs ih H => _
  · rcases H with ⟨r, hr1, hrn, hs⟩
    refine' ⟨r, hr1, fun n hn => _⟩
    specialize hrn hn
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn
  apply ih
  rcases H with ⟨r, hr1, hrn, hs⟩
  rw [← Set.singleton_union, span_union, smul_sup] at hrn
  rw [Set.insert_subset] at hs
  have : ∃ c : R, c - 1 ∈ I ∧ c • i ∈ I • span R s :=
    by
    specialize hrn hs.1
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    change y + z = r • i at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨c, hci, rfl⟩
    use r - c
    constructor
    · rw [sub_right_comm]
      exact I.sub_mem hr1 hci
    · rw [sub_smul, ← hyz, add_sub_cancel']
      exact hz
  rcases this with ⟨c, hc1, hci⟩
  refine' ⟨c * r, _, _, hs.2⟩
  · rw [← Ideal.Quotient.eq, RingHom.map_one] at hr1 hc1⊢
    rw [RingHom.map_mul, hc1, hr1, mul_one]
  · intro n hn
    specialize hrn hn
    rw [mem_comap, mem_sup] at hrn
    rcases hrn with ⟨y, hy, z, hz, hyz⟩
    change y + z = r • n at hyz
    rw [mem_smul_span_singleton] at hy
    rcases hy with ⟨d, hdi, rfl⟩
    change _ • _ ∈ I • span R s
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_comm, mul_smul]
    exact add_mem (smul_mem _ _ hci) (smul_mem _ _ hz)
#align submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul

theorem exists_mem_and_smul_eq_self_of_fg_of_le_smul {R : Type _} [CommRing R] {M : Type _}
    [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) (hn : N.Fg) (hin : N ≤ I • N) :
    ∃ r ∈ I, ∀ n ∈ N, r • n = n :=
  by
  obtain ⟨r, hr, hr'⟩ := N.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I hn hin
  exact ⟨-(r - 1), I.neg_mem hr, fun n hn => by simpa [sub_smul] using hr' n hn⟩
#align submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul Submodule.exists_mem_and_smul_eq_self_of_fg_of_le_smul

theorem fgBot : (⊥ : Submodule R M).Fg :=
  ⟨∅, by rw [Finset.coe_empty, span_empty]⟩
#align submodule.fg_bot Submodule.fgBot

theorem Subalgebra.fgBotToSubmodule {R A : Type _} [CommSemiring R] [Semiring A] [Algebra R A] :
    (⊥ : Subalgebra R A).toSubmodule.Fg :=
  ⟨{1}, by simp [Algebra.to_submodule_bot]⟩
#align subalgebra.fg_bot_to_submodule Subalgebra.fgBotToSubmodule

theorem fgSpan {s : Set M} (hs : s.Finite) : Fg (span R s) :=
  ⟨hs.toFinset, by rw [hs.coe_to_finset]⟩
#align submodule.fg_span Submodule.fgSpan

theorem fgSpanSingleton (x : M) : Fg (R ∙ x) :=
  fgSpan (finite_singleton x)
#align submodule.fg_span_singleton Submodule.fgSpanSingleton

theorem Fg.sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.Fg) (hN₂ : N₂.Fg) : (N₁ ⊔ N₂).Fg :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [span_union, ht₁.2, ht₂.2]⟩
#align submodule.fg.sup Submodule.Fg.sup

theorem fgFinsetSup {ι : Type _} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).Fg) :
    (s.sup N).Fg :=
  Finset.sup_induction fgBot (fun a ha b hb => ha.sup hb) h
#align submodule.fg_finset_sup Submodule.fgFinsetSup

theorem fgBsupr {ι : Type _} (s : Finset ι) (N : ι → Submodule R M) (h : ∀ i ∈ s, (N i).Fg) :
    (⨆ i ∈ s, N i).Fg := by simpa only [Finset.sup_eq_supᵢ] using fg_finset_sup s N h
#align submodule.fg_bsupr Submodule.fgBsupr

theorem fgSupr {ι : Type _} [Finite ι] (N : ι → Submodule R M) (h : ∀ i, (N i).Fg) : (supᵢ N).Fg :=
  by
  cases nonempty_fintype ι
  simpa using fg_bsupr Finset.univ N fun i hi => h i
#align submodule.fg_supr Submodule.fgSupr

variable {P : Type _} [AddCommMonoid P] [Module R P]

variable (f : M →ₗ[R] P)

theorem Fg.map {N : Submodule R M} (hs : N.Fg) : (N.map f).Fg :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2 ⟨f '' t, ht.1.image _, by rw [span_image, ht.2]⟩
#align submodule.fg.map Submodule.Fg.map

variable {f}

theorem fgOfFgMapInjective (f : M →ₗ[R] P) (hf : Function.Injective f) {N : Submodule R M}
    (hfn : (N.map f).Fg) : N.Fg :=
  let ⟨t, ht⟩ := hfn
  ⟨t.Preimage f fun x _ y _ h => hf h,
    Submodule.map_injective_of_injective hf <|
      by
      rw [f.map_span, Finset.coe_preimage, Set.image_preimage_eq_inter_range,
        Set.inter_eq_self_of_subset_left, ht]
      rw [← LinearMap.range_coe, ← span_le, ht, ← map_top]
      exact map_mono le_top⟩
#align submodule.fg_of_fg_map_injective Submodule.fgOfFgMapInjective

theorem fgOfFgMap {R M P : Type _} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) {N : Submodule R M} (hfn : (N.map f).Fg) : N.Fg :=
  fgOfFgMapInjective f (LinearMap.ker_eq_bot.1 hf) hfn
#align submodule.fg_of_fg_map Submodule.fgOfFgMap

theorem fg_top (N : Submodule R M) : (⊤ : Submodule R N).Fg ↔ N.Fg :=
  ⟨fun h => N.range_subtype ▸ map_top N.Subtype ▸ h.map _, fun h =>
    fgOfFgMapInjective N.Subtype Subtype.val_injective <| by rwa [map_top, range_subtype]⟩
#align submodule.fg_top Submodule.fg_top

theorem fgOfLinearEquiv (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).Fg) : (⊤ : Submodule R M).Fg :=
  e.symm.range ▸ map_top (e.symm : P →ₗ[R] M) ▸ h.map _
#align submodule.fg_of_linear_equiv Submodule.fgOfLinearEquiv

theorem Fg.prod {sb : Submodule R M} {sc : Submodule R P} (hsb : sb.Fg) (hsc : sc.Fg) :
    (sb.Prod sc).Fg :=
  let ⟨tb, htb⟩ := fg_def.1 hsb
  let ⟨tc, htc⟩ := fg_def.1 hsc
  fg_def.2
    ⟨LinearMap.inl R M P '' tb ∪ LinearMap.inr R M P '' tc, (htb.1.image _).union (htc.1.image _),
      by rw [LinearMap.span_inl_union_inr, htb.2, htc.2]⟩
#align submodule.fg.prod Submodule.Fg.prod

theorem fgPi {ι : Type _} {M : ι → Type _} [Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] {p : ∀ i, Submodule R (M i)} (hsb : ∀ i, (p i).Fg) :
    (Submodule.pi Set.univ p).Fg := by
  classical
    simp_rw [fg_def] at hsb⊢
    choose t htf hts using hsb
    refine'
      ⟨⋃ i, (LinearMap.single i : _ →ₗ[R] _) '' t i, Set.finite_Union fun i => (htf i).image _, _⟩
    simp_rw [span_Union, span_image, hts, Submodule.supr_map_single]
#align submodule.fg_pi Submodule.fgPi

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fgOfFgMapOfFgInfKer {R M P : Type _} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup P]
    [Module R P] (f : M →ₗ[R] P) {s : Submodule R M} (hs1 : (s.map f).Fg) (hs2 : (s ⊓ f.ker).Fg) :
    s.Fg := by
  haveI := Classical.decEq R
  haveI := Classical.decEq M
  haveI := Classical.decEq P
  cases' hs1 with t1 ht1
  cases' hs2 with t2 ht2
  have : ∀ y ∈ t1, ∃ x ∈ s, f x = y := by
    intro y hy
    have : y ∈ map f s := by
      rw [← ht1]
      exact subset_span hy
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩
    exact ⟨x, hx1, hx2⟩
  have : ∃ g : P → M, ∀ y ∈ t1, g y ∈ s ∧ f (g y) = y :=
    by
    choose g hg1 hg2
    exists fun y => if H : y ∈ t1 then g y H else 0
    intro y H
    constructor
    · simp only [dif_pos H]
      apply hg1
    · simp only [dif_pos H]
      apply hg2
  cases' this with g hg
  clear this
  exists t1.image g ∪ t2
  rw [Finset.coe_union, span_union, Finset.coe_image]
  apply le_antisymm
  · refine' sup_le (span_le.2 <| image_subset_iff.2 _) (span_le.2 _)
    · intro y hy
      exact (hg y hy).1
    · intro x hx
      have := subset_span hx
      rw [ht2] at this
      exact this.1
  intro x hx
  have : f x ∈ map f s := by
    rw [mem_map]
    exact ⟨x, hx, rfl⟩
  rw [← ht1, ← Set.image_id ↑t1, Finsupp.mem_span_image_iff_total] at this
  rcases this with ⟨l, hl1, hl2⟩
  refine'
    mem_sup.2
      ⟨(Finsupp.total M M R id).toFun ((Finsupp.lmapDomain R R g : (P →₀ R) → M →₀ R) l), _,
        x - Finsupp.total M M R id ((Finsupp.lmapDomain R R g : (P →₀ R) → M →₀ R) l), _,
        add_sub_cancel'_right _ _⟩
  · rw [← Set.image_id (g '' ↑t1), Finsupp.mem_span_image_iff_total]
    refine' ⟨_, _, rfl⟩
    haveI : Inhabited P := ⟨0⟩
    rw [← Finsupp.lmap_domain_supported _ _ g, mem_map]
    refine' ⟨l, hl1, _⟩
    rfl
  rw [ht2, mem_inf]
  constructor
  · apply s.sub_mem hx
    rw [Finsupp.total_apply, Finsupp.lmap_domain_apply, Finsupp.sum_map_domain_index]
    refine' s.sum_mem _
    · intro y hy
      exact s.smul_mem _ (hg y (hl1 hy)).1
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
  · rw [LinearMap.mem_ker, f.map_sub, ← hl2]
    rw [Finsupp.total_apply, Finsupp.total_apply, Finsupp.lmap_domain_apply]
    rw [Finsupp.sum_map_domain_index, Finsupp.sum, Finsupp.sum, f.map_sum]
    rw [sub_eq_zero]
    refine' Finset.sum_congr rfl fun y hy => _
    unfold id
    rw [f.map_smul, (hg y (hl1 hy)).2]
    · exact zero_smul _
    · exact fun _ _ _ => add_smul _ _ _
#align submodule.fg_of_fg_map_of_fg_inf_ker Submodule.fgOfFgMapOfFgInfKer

theorem fgInduction (R M : Type _) [Semiring R] [AddCommMonoid M] [Module R M]
    (P : Submodule R M → Prop) (h₁ : ∀ x, P (Submodule.span R {x}))
    (h₂ : ∀ M₁ M₂, P M₁ → P M₂ → P (M₁ ⊔ M₂)) (N : Submodule R M) (hN : N.Fg) : P N := by
  classical
    obtain ⟨s, rfl⟩ := hN
    induction s using Finset.induction
    · rw [Finset.coe_empty, Submodule.span_empty, ← Submodule.span_zero_singleton]
      apply h₁
    · rw [Finset.coe_insert, Submodule.span_insert]
      apply h₂ <;> apply_assumption
#align submodule.fg_induction Submodule.fgInduction

/-- The kernel of the composition of two linear maps is finitely generated if both kernels are and
the first morphism is surjective. -/
theorem fgKerComp {R M N P : Type _} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf1 : f.ker.Fg)
    (hf2 : g.ker.Fg) (hsur : Function.Surjective f) : (g.comp f).ker.Fg :=
  by
  rw [LinearMap.ker_comp]
  apply fg_of_fg_map_of_fg_inf_ker f
  · rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
  · rwa [inf_of_le_right (show f.ker ≤ comap f g.ker from comap_mono bot_le)]
#align submodule.fg_ker_comp Submodule.fgKerComp

theorem fgRestrictScalars {R S M : Type _} [CommSemiring R] [Semiring S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (N : Submodule S M)
    (hfin : N.Fg) (h : Function.Surjective (algebraMap R S)) : (Submodule.restrictScalars R N).Fg :=
  by
  obtain ⟨X, rfl⟩ := hfin
  use X
  exact Submodule.span_eq_restrict_scalars R S M X h
#align submodule.fg_restrict_scalars Submodule.fgRestrictScalars

theorem Fg.stablizes_of_supr_eq {M' : Submodule R M} (hM' : M'.Fg) (N : ℕ →o Submodule R M)
    (H : supᵢ N = M') : ∃ n, M' = N n :=
  by
  obtain ⟨S, hS⟩ := hM'
  have : ∀ s : S, ∃ n, (s : M) ∈ N n := fun s =>
    (Submodule.mem_supr_of_chain N s).mp
      (by
        rw [H, ← hS]
        exact Submodule.subset_span s.2)
  choose f hf
  use S.attach.sup f
  apply le_antisymm
  · conv_lhs => rw [← hS]
    rw [Submodule.span_le]
    intro s hs
    exact N.2 (Finset.le_sup <| S.mem_attach ⟨s, hs⟩) (hf _)
  · rw [← H]
    exact le_supᵢ _ _
#align submodule.fg.stablizes_of_supr_eq Submodule.Fg.stablizes_of_supr_eq

/-- Finitely generated submodules are precisely compact elements in the submodule lattice. -/
theorem fg_iff_compact (s : Submodule R M) : s.Fg ↔ CompleteLattice.IsCompactElement s := by
  classical
    -- Introduce shorthand for span of an element
    let sp : M → Submodule R M := fun a => span R {a}
    -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
    have supr_rw : ∀ t : Finset M, (⨆ x ∈ t, sp x) = ⨆ x ∈ (↑t : Set M), sp x := fun t => by rfl
    constructor
    · rintro ⟨t, rfl⟩
      rw [span_eq_supr_of_singleton_spans, ← supr_rw, ← Finset.sup_eq_supᵢ t sp]
      apply CompleteLattice.finset_sup_compact_of_compact
      exact fun n _ => singleton_span_is_compact_element n
    · intro h
      -- s is the Sup of the spans of its elements.
      have sSup : s = Sup (sp '' ↑s) := by
        rw [supₛ_eq_supᵢ, supᵢ_image, ← span_eq_supr_of_singleton_spans, eq_comm, span_eq]
      -- by h, s is then below (and equal to) the sup of the spans of finitely many elements.
      obtain ⟨u, ⟨huspan, husup⟩⟩ := h (sp '' ↑s) (le_of_eq sSup)
      have ssup : s = u.sup id := by
        suffices : u.sup id ≤ s
        exact le_antisymm husup this
        rw [sSup, Finset.sup_id_eq_supₛ]
        exact supₛ_le_supₛ huspan
      obtain ⟨t, ⟨hts, rfl⟩⟩ := finset.subset_image_iff.mp huspan
      rw [Finset.sup_finset_image, Function.comp.left_id, Finset.sup_eq_supᵢ, supr_rw, ←
        span_eq_supr_of_singleton_spans, eq_comm] at ssup
      exact ⟨t, ssup⟩
#align submodule.fg_iff_compact Submodule.fg_iff_compact

end Submodule

namespace Submodule

section Map₂

variable {R M N P : Type _}

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]

variable [Module R M] [Module R N] [Module R P]

theorem Fg.map₂ (f : M →ₗ[R] N →ₗ[R] P) {p : Submodule R M} {q : Submodule R N} (hp : p.Fg)
    (hq : q.Fg) : (map₂ f p q).Fg :=
  let ⟨sm, hfm, hm⟩ := fg_def.1 hp
  let ⟨sn, hfn, hn⟩ := fg_def.1 hq
  fg_def.2
    ⟨Set.image2 (fun m n => f m n) sm sn, hfm.image2 _ hfn,
      map₂_span_span R f sm sn ▸ hm ▸ hn ▸ rfl⟩
#align submodule.fg.map₂ Submodule.Fg.map₂

end Map₂

section Mul

variable {R : Type _} {A : Type _} [CommSemiring R] [Semiring A] [Algebra R A]

variable {M N : Submodule R A}

theorem Fg.mul (hm : M.Fg) (hn : N.Fg) : (M * N).Fg :=
  hm.map₂ _ hn
#align submodule.fg.mul Submodule.Fg.mul

theorem Fg.pow (h : M.Fg) (n : ℕ) : (M ^ n).Fg :=
  Nat.recOn n ⟨{1}, by simp [one_eq_span]⟩ fun n ih => by simpa [pow_succ] using h.mul ih
#align submodule.fg.pow Submodule.Fg.pow

end Mul

end Submodule

namespace Ideal

variable {R : Type _} {M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]

/-- An ideal of `R` is finitely generated if it is the span of a finite subset of `R`.

This is defeq to `submodule.fg`, but unfolds more nicely. -/
def Fg (I : Ideal R) : Prop :=
  ∃ S : Finset R, Ideal.span ↑S = I
#align ideal.fg Ideal.Fg

/-- The image of a finitely generated ideal is finitely generated.

This is the `ideal` version of `submodule.fg.map`. -/
theorem Fg.map {R S : Type _} [Semiring R] [Semiring S] {I : Ideal R} (h : I.Fg) (f : R →+* S) :
    (I.map f).Fg := by
  classical
    obtain ⟨s, hs⟩ := h
    refine' ⟨s.image f, _⟩
    rw [Finset.coe_image, ← Ideal.map_span, hs]
#align ideal.fg.map Ideal.Fg.map

theorem fg_ker_comp {R S A : Type _} [CommRing R] [CommRing S] [CommRing A] (f : R →+* S)
    (g : S →+* A) (hf : f.ker.Fg) (hg : g.ker.Fg) (hsur : Function.Surjective f) :
    (g.comp f).ker.Fg := by
  letI : Algebra R S := RingHom.toAlgebra f
  letI : Algebra R A := RingHom.toAlgebra (g.comp f)
  letI : Algebra S A := RingHom.toAlgebra g
  letI : IsScalarTower R S A := IsScalarTower.of_algebra_map_eq fun _ => rfl
  let f₁ := Algebra.linearMap R S
  let g₁ := (IsScalarTower.toAlgHom R S A).toLinearMap
  exact Submodule.fgKerComp f₁ g₁ hf (Submodule.fgRestrictScalars g.ker hg hsur) hsur
#align ideal.fg_ker_comp Ideal.fg_ker_comp

theorem exists_radical_pow_le_of_fg {R : Type _} [CommSemiring R] (I : Ideal R) (h : I.radical.Fg) :
    ∃ n : ℕ, I.radical ^ n ≤ I := by
  have := le_refl I.radical; revert this
  refine' Submodule.fgInduction _ _ (fun J => J ≤ I.radical → ∃ n : ℕ, J ^ n ≤ I) _ _ _ h
  · intro x hx
    obtain ⟨n, hn⟩ := hx (subset_span (Set.mem_singleton x))
    exact ⟨n, by rwa [← Ideal.span, span_singleton_pow, span_le, Set.singleton_subset_iff]⟩
  · intro J K hJ hK hJK
    obtain ⟨n, hn⟩ := hJ fun x hx => hJK <| Ideal.mem_sup_left hx
    obtain ⟨m, hm⟩ := hK fun x hx => hJK <| Ideal.mem_sup_right hx
    use n + m
    rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup, Finset.sup_le_iff]
    refine' fun i hi => ideal.mul_le_right.trans _
    obtain h | h := le_or_lt n i
    · exact ideal.mul_le_right.trans ((Ideal.pow_le_pow h).trans hn)
    · refine' ideal.mul_le_left.trans ((Ideal.pow_le_pow _).trans hm)
      rw [add_comm, Nat.add_sub_assoc h.le]
      apply Nat.le_add_right
#align ideal.exists_radical_pow_le_of_fg Ideal.exists_radical_pow_le_of_fg

end Ideal

section ModuleAndAlgebra

variable (R A B M N : Type _)

/-- A module over a semiring is `finite` if it is finitely generated as a module. -/
class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  out : (⊤ : Submodule R M).Fg
#align module.finite Module.Finite

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

theorem finite_def {R M} [Semiring R] [AddCommMonoid M] [Module R M] :
    Finite R M ↔ (⊤ : Submodule R M).Fg :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align module.finite_def Module.finite_def

namespace Finite

open _Root_.Submodule Set

theorem iff_add_monoid_fg {M : Type _} [AddCommMonoid M] : Module.Finite ℕ M ↔ AddMonoid.Fg M :=
  ⟨fun h => AddMonoid.fg_def.2 <| (fg_iff_add_submonoid_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (fg_iff_add_submonoid_fg ⊤).2 (AddMonoid.fg_def.1 h)⟩
#align module.finite.iff_add_monoid_fg Module.Finite.iff_add_monoid_fg

theorem iff_add_group_fg {G : Type _} [AddCommGroup G] : Module.Finite ℤ G ↔ AddGroup.Fg G :=
  ⟨fun h => AddGroup.fg_def.2 <| (fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h), fun h =>
    finite_def.2 <| (fg_iff_add_subgroup_fg ⊤).2 (AddGroup.fg_def.1 h)⟩
#align module.finite.iff_add_group_fg Module.Finite.iff_add_group_fg

variable {R M N}

theorem exists_fin [Finite R M] : ∃ (n : ℕ)(s : Fin n → M), span R (range s) = ⊤ :=
  Submodule.fg_iff_exists_fin_generating_family.mp out
#align module.finite.exists_fin Module.Finite.exists_fin

theorem ofSurjective [hM : Finite R M] (f : M →ₗ[R] N) (hf : Surjective f) : Finite R N :=
  ⟨by
    rw [← LinearMap.range_eq_top.2 hf, ← Submodule.map_top]
    exact hM.1.map f⟩
#align module.finite.of_surjective Module.Finite.ofSurjective

variable (R)

instance self : Finite R R :=
  ⟨⟨{1}, by simpa only [Finset.coe_singleton] using Ideal.span_singleton_one⟩⟩
#align module.finite.self Module.Finite.self

variable (M)

theorem ofRestrictScalarsFinite (R A M : Type _) [CommSemiring R] [Semiring A] [AddCommMonoid M]
    [Module R M] [Module A M] [Algebra R A] [IsScalarTower R A M] [hM : Finite R M] : Finite A M :=
  by
  rw [finite_def, fg_def] at hM⊢
  obtain ⟨S, hSfin, hSgen⟩ := hM
  refine' ⟨S, hSfin, eq_top_iff.2 _⟩
  have := Submodule.span_le_restrict_scalars R A S
  rw [hSgen] at this
  exact this
#align module.finite.of_restrict_scalars_finite Module.Finite.ofRestrictScalarsFinite

variable {R M}

instance prod [hM : Finite R M] [hN : Finite R N] : Finite R (M × N) :=
  ⟨by
    rw [← Submodule.prod_top]
    exact hM.1.Prod hN.1⟩
#align module.finite.prod Module.Finite.prod

instance pi {ι : Type _} {M : ι → Type _} [Finite ι] [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] [h : ∀ i, Finite R (M i)] : Finite R (∀ i, M i) :=
  ⟨by
    rw [← Submodule.pi_top]
    exact Submodule.fgPi fun i => (h i).1⟩
#align module.finite.pi Module.Finite.pi

theorem equiv [hM : Finite R M] (e : M ≃ₗ[R] N) : Finite R N :=
  ofSurjective (e : M →ₗ[R] N) e.Surjective
#align module.finite.equiv Module.Finite.equiv

section Algebra

theorem trans {R : Type _} (A B : Type _) [CommSemiring R] [CommSemiring A] [Algebra R A]
    [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    ∀ [Finite R A] [Finite A B], Finite R B
  | ⟨⟨s, hs⟩⟩, ⟨⟨t, ht⟩⟩ =>
    ⟨Submodule.fg_def.2
        ⟨Set.image2 (· • ·) (↑s : Set A) (↑t : Set B),
          Set.Finite.image2 _ s.finite_to_set t.finite_to_set, by
          rw [Set.image2_smul, Submodule.span_smul_of_span_eq_top hs (↑t : Set B), ht,
            Submodule.restrict_scalars_top]⟩⟩
#align module.finite.trans Module.Finite.trans

end Algebra

end Finite

end Module

instance Module.Finite.baseChange [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
    [Module R M] [h : Module.Finite R M] : Module.Finite A (TensorProduct R A M) := by
  classical
    obtain ⟨s, hs⟩ := h.out
    refine' ⟨⟨s.image (TensorProduct.mk R A M 1), eq_top_iff.mpr fun x _ => _⟩⟩
    apply TensorProduct.induction_on x
    · exact zero_mem _
    · intro x y
      rw [Finset.coe_image, ← Submodule.span_span_of_tower R, Submodule.span_image, hs,
        Submodule.map_top, LinearMap.range_coe]
      change _ ∈ Submodule.span A (Set.range <| TensorProduct.mk R A M 1)
      rw [← mul_one x, ← smul_eq_mul, ← TensorProduct.smul_tmul']
      exact Submodule.smul_mem _ x (Submodule.subset_span <| Set.mem_range_self y)
    · exact fun _ _ => Submodule.add_mem _
#align module.finite.base_change Module.Finite.baseChange

instance Module.Finite.tensorProduct [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [hM : Module.Finite R M] [hN : Module.Finite R N] :
    Module.Finite R (TensorProduct R M N)
    where out := (TensorProduct.map₂_mk_top_top_eq_top R M N).subst (hM.out.map₂ _ hN.out)
#align module.finite.tensor_product Module.Finite.tensorProduct

namespace Algebra

variable [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

variable [AddCommGroup M] [Module R M]

variable [AddCommGroup N] [Module R N]

end Algebra

end ModuleAndAlgebra

namespace RingHom

variable {A B C : Type _} [CommRing A] [CommRing B] [CommRing C]

/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def Finite (f : A →+* B) : Prop :=
  letI : Algebra A B := f.to_algebra
  Module.Finite A B
#align ring_hom.finite RingHom.Finite

namespace Finite

variable (A)

theorem id : Finite (RingHom.id A) :=
  Module.Finite.self A
#align ring_hom.finite.id RingHom.Finite.id

variable {A}

theorem of_surjective (f : A →+* B) (hf : Surjective f) : f.Finite :=
  letI := f.to_algebra
  Module.Finite.ofSurjective (Algebra.ofId A B).toLinearMap hf
#align ring_hom.finite.of_surjective RingHom.Finite.of_surjective

theorem comp {g : B →+* C} {f : A →+* B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
  @Module.Finite.trans A B C _ _ f.toAlgebra _ (g.comp f).toAlgebra g.toAlgebra
    (by
      fconstructor
      intro a b c
      simp only [Algebra.smul_def, RingHom.map_mul, mul_assoc]
      rfl)
    hf hg
#align ring_hom.finite.comp RingHom.Finite.comp

theorem of_comp_finite {f : A →+* B} {g : B →+* C} (h : (g.comp f).Finite) : g.Finite :=
  by
  letI := f.to_algebra
  letI := g.to_algebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower A B C := RestrictScalars.is_scalar_tower A B C
  letI : Module.Finite A C := h
  exact Module.Finite.ofRestrictScalarsFinite A B C
#align ring_hom.finite.of_comp_finite RingHom.Finite.of_comp_finite

end Finite

end RingHom

namespace AlgHom

variable {R A B C : Type _} [CommRing R]

variable [CommRing A] [CommRing B] [CommRing C]

variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def Finite (f : A →ₐ[R] B) : Prop :=
  f.toRingHom.Finite
#align alg_hom.finite AlgHom.Finite

namespace Finite

variable (R A)

theorem id : Finite (AlgHom.id R A) :=
  RingHom.Finite.id A
#align alg_hom.finite.id AlgHom.Finite.id

variable {R A}

theorem comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.Finite) (hf : f.Finite) : (g.comp f).Finite :=
  RingHom.Finite.comp hg hf
#align alg_hom.finite.comp AlgHom.Finite.comp

theorem of_surjective (f : A →ₐ[R] B) (hf : Surjective f) : f.Finite :=
  RingHom.Finite.of_surjective f hf
#align alg_hom.finite.of_surjective AlgHom.Finite.of_surjective

theorem of_comp_finite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).Finite) : g.Finite :=
  RingHom.Finite.of_comp_finite h
#align alg_hom.finite.of_comp_finite AlgHom.Finite.of_comp_finite

end Finite

end AlgHom

