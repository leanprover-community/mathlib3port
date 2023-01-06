/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard

! This file was ported from Lean 3 source module ring_theory.noetherian
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.Algebra.Tower
import Mathbin.Algebra.Ring.Idempotents
import Mathbin.GroupTheory.Finiteness
import Mathbin.LinearAlgebra.LinearIndependent
import Mathbin.Order.CompactlyGenerated
import Mathbin.Order.OrderIsoNat
import Mathbin.RingTheory.Finiteness
import Mathbin.RingTheory.Nilpotent

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `is_noetherian_iff_well_founded` is the theorem that an R-module M is Noetherian iff
  `>` is well-founded on `submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `ring_theory.polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/


open Set

open BigOperators Pointwise

/-- `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
class IsNoetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  noetherian : ∀ s : Submodule R M, s.Fg
#align is_noetherian IsNoetherian

section

variable {R : Type _} {M : Type _} {P : Type _}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P]

variable [Module R M] [Module R P]

open IsNoetherian

include R

/-- An R-module is Noetherian iff all its submodules are finitely-generated. -/
theorem is_noetherian_def : IsNoetherian R M ↔ ∀ s : Submodule R M, s.Fg :=
  ⟨fun h => h.noetherian, IsNoetherian.mk⟩
#align is_noetherian_def is_noetherian_def

theorem is_noetherian_submodule {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, s ≤ N → s.Fg :=
  by
  refine'
    ⟨fun ⟨hn⟩ => fun s hs =>
      have : s ≤ N.subtype.range := N.range_subtype.symm ▸ hs
      Submodule.map_comap_eq_self this ▸ (hn _).map _,
      fun h => ⟨fun s => _⟩⟩
  have f := (Submodule.equivMapOfInjective N.subtype Subtype.val_injective s).symm
  have h₁ := h (s.map N.subtype) (Submodule.map_subtype_le N s)
  have h₂ : (⊤ : Submodule R (s.map N.subtype)).map f = ⊤ := by simp
  have h₃ := ((Submodule.fg_top _).2 h₁).map (↑f : _ →ₗ[R] s)
  exact (Submodule.fg_top _).1 (h₂ ▸ h₃)
#align is_noetherian_submodule is_noetherian_submodule

theorem is_noetherian_submodule_left {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, (N ⊓ s).Fg :=
  is_noetherian_submodule.trans ⟨fun H s => H _ inf_le_left, fun H s hs => inf_of_le_right hs ▸ H _⟩
#align is_noetherian_submodule_left is_noetherian_submodule_left

theorem is_noetherian_submodule_right {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, (s ⊓ N).Fg :=
  is_noetherian_submodule.trans ⟨fun H s => H _ inf_le_right, fun H s hs => inf_of_le_left hs ▸ H _⟩
#align is_noetherian_submodule_right is_noetherian_submodule_right

instance isNoetherianSubmodule' [IsNoetherian R M] (N : Submodule R M) : IsNoetherian R N :=
  is_noetherian_submodule.2 fun _ _ => IsNoetherian.noetherian _
#align is_noetherian_submodule' isNoetherianSubmodule'

theorem isNoetherianOfLe {s t : Submodule R M} [ht : IsNoetherian R t] (h : s ≤ t) :
    IsNoetherian R s :=
  is_noetherian_submodule.mpr fun s' hs' => is_noetherian_submodule.mp ht _ (le_trans hs' h)
#align is_noetherian_of_le isNoetherianOfLe

variable (M)

theorem isNoetherianOfSurjective (f : M →ₗ[R] P) (hf : f.range = ⊤) [IsNoetherian R M] :
    IsNoetherian R P :=
  ⟨fun s =>
    have : (s.comap f).map f = s := Submodule.map_comap_eq_self <| hf.symm ▸ le_top
    this ▸ (noetherian _).map _⟩
#align is_noetherian_of_surjective isNoetherianOfSurjective

variable {M}

theorem isNoetherianOfLinearEquiv (f : M ≃ₗ[R] P) [IsNoetherian R M] : IsNoetherian R P :=
  isNoetherianOfSurjective _ f.toLinearMap f.range
#align is_noetherian_of_linear_equiv isNoetherianOfLinearEquiv

theorem is_noetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M :=
  by
  constructor <;> intro h
  · exact isNoetherianOfLinearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
  · exact isNoetherianOfLinearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl).symm
#align is_noetherian_top_iff is_noetherian_top_iff

theorem isNoetherianOfInjective [IsNoetherian R P] (f : M →ₗ[R] P) (hf : Function.Injective f) :
    IsNoetherian R M :=
  isNoetherianOfLinearEquiv (LinearEquiv.ofInjective f hf).symm
#align is_noetherian_of_injective isNoetherianOfInjective

theorem fgOfInjective [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P)
    (hf : Function.Injective f) : N.Fg :=
  @IsNoetherian.noetherian _ _ _ (isNoetherianOfInjective f hf) N
#align fg_of_injective fgOfInjective

end

namespace Module

variable {R M N : Type _}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

variable (R M)

-- see Note [lower instance priority]
instance (priority := 100) IsNoetherian.finite [IsNoetherian R M] : Finite R M :=
  ⟨IsNoetherian.noetherian ⊤⟩
#align module.is_noetherian.finite Module.IsNoetherian.finite

variable {R M}

theorem Finite.ofInjective [IsNoetherian R N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Finite R M :=
  ⟨fgOfInjective f hf⟩
#align module.finite.of_injective Module.Finite.ofInjective

end Module

section

variable {R : Type _} {M : Type _} {P : Type _}

variable [Ring R] [AddCommGroup M] [AddCommGroup P]

variable [Module R M] [Module R P]

open IsNoetherian

include R

theorem isNoetherianOfKerBot [IsNoetherian R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) :
    IsNoetherian R M :=
  isNoetherianOfLinearEquiv (LinearEquiv.ofInjective f <| LinearMap.ker_eq_bot.mp hf).symm
#align is_noetherian_of_ker_bot isNoetherianOfKerBot

theorem fgOfKerBot [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P) (hf : f.ker = ⊥) : N.Fg :=
  @IsNoetherian.noetherian _ _ _ (isNoetherianOfKerBot f hf) N
#align fg_of_ker_bot fgOfKerBot

instance isNoetherianProd [IsNoetherian R M] [IsNoetherian R P] : IsNoetherian R (M × P) :=
  ⟨fun s =>
    Submodule.fgOfFgMapOfFgInfKer (LinearMap.snd R M P) (noetherian _) <|
      have : s ⊓ LinearMap.ker (LinearMap.snd R M P) ≤ LinearMap.range (LinearMap.inl R M P) :=
        fun x ⟨hx1, hx2⟩ => ⟨x.1, Prod.ext rfl <| Eq.symm <| LinearMap.mem_ker.1 hx2⟩
      Submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩
#align is_noetherian_prod isNoetherianProd

instance isNoetherianPi {R ι : Type _} {M : ι → Type _} [Ring R] [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [Finite ι] [∀ i, IsNoetherian R (M i)] : IsNoetherian R (∀ i, M i) :=
  by
  cases nonempty_fintype ι
  haveI := Classical.decEq ι
  suffices on_finset : ∀ s : Finset ι, IsNoetherian R (∀ i : s, M i)
  · let coe_e := Equiv.subtypeUnivEquiv Finset.mem_univ
    letI : IsNoetherian R (∀ i : Finset.univ, M (coe_e i)) := on_finset Finset.univ
    exact isNoetherianOfLinearEquiv (LinearEquiv.piCongrLeft R M coe_e)
  intro s
  induction' s using Finset.induction with a s has ih
  · exact ⟨fun s => by convert Submodule.fgBot⟩
  refine' @isNoetherianOfLinearEquiv _ _ _ _ _ _ _ _ _ (@isNoetherianProd _ (M a) _ _ _ _ _ _ _ ih)
  fconstructor
  ·
    exact fun f i =>
      Or.by_cases (Finset.mem_insert.1 i.2) (fun h : i.1 = a => show M i.1 from Eq.recOn h.symm f.1)
        fun h : i.1 ∈ s => show M i.1 from f.2 ⟨i.1, h⟩
  · intro f g
    ext i
    unfold Or.by_cases
    cases' i with i hi
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · change _ = _ + _
      simp only [dif_pos]
      rfl
    · change _ = _ + _
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      rfl
  · intro c f
    ext i
    unfold Or.by_cases
    cases' i with i hi
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · change _ = c • _
      simp only [dif_pos]
      rfl
    · change _ = c • _
      have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [dif_neg this, dif_pos h]
      rfl
  ·
    exact fun f =>
      (f ⟨a, Finset.mem_insert_self _ _⟩, fun i => f ⟨i.1, Finset.mem_insert_of_mem i.2⟩)
  · intro f
    apply Prod.ext
    · simp only [Or.by_cases, dif_pos]
    · ext ⟨i, his⟩
      have : ¬i = a := by
        rintro rfl
        exact has his
      simp only [Or.by_cases, this, not_false_iff, dif_neg]
  · intro f
    ext ⟨i, hi⟩
    rcases Finset.mem_insert.1 hi with (rfl | h)
    · simp only [Or.by_cases, dif_pos]
    · have : ¬i = a := by
        rintro rfl
        exact has h
      simp only [Or.by_cases, dif_neg this, dif_pos h]
#align is_noetherian_pi isNoetherianPi

/-- A version of `is_noetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance isNoetherianPi' {R ι M : Type _} [Ring R] [AddCommGroup M] [Module R M] [Finite ι]
    [IsNoetherian R M] : IsNoetherian R (ι → M) :=
  isNoetherianPi
#align is_noetherian_pi' isNoetherianPi'

end

open IsNoetherian Submodule Function

section

universe w

variable {R M P : Type _} {N : Type w} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]

theorem is_noetherian_iff_well_founded :
    IsNoetherian R M ↔ WellFounded ((· > ·) : Submodule R M → Submodule R M → Prop) :=
  by
  rw [(CompleteLattice.well_founded_characterisations <| Submodule R M).out 0 3]
  exact
    ⟨fun ⟨h⟩ => fun k => (fg_iff_compact k).mp (h k), fun h =>
      ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩
#align is_noetherian_iff_well_founded is_noetherian_iff_well_founded

theorem is_noetherian_iff_fg_well_founded :
    IsNoetherian R M ↔
      WellFounded
        ((· > ·) : { N : Submodule R M // N.Fg } → { N : Submodule R M // N.Fg } → Prop) :=
  by
  let α := { N : Submodule R M // N.Fg }
  constructor
  · intro H
    let f : α ↪o Submodule R M := OrderEmbedding.subtype _
    exact OrderEmbedding.wellFounded f.dual (is_noetherian_iff_well_founded.mp H)
  · intro H
    constructor
    intro N
    obtain ⟨⟨N₀, h₁⟩, e : N₀ ≤ N, h₂⟩ :=
      well_founded.well_founded_iff_has_max'.mp H { N' : α | N'.1 ≤ N }
        ⟨⟨⊥, Submodule.fgBot⟩, bot_le⟩
    convert h₁
    refine' (e.antisymm _).symm
    by_contra h₃
    obtain ⟨x, hx₁ : x ∈ N, hx₂ : x ∉ N₀⟩ := set.not_subset.mp h₃
    apply hx₂
    have := h₂ ⟨(R ∙ x) ⊔ N₀, _⟩ _ _
    · injection this with eq
      rw [← Eq]
      exact (le_sup_left : (R ∙ x) ≤ (R ∙ x) ⊔ N₀) (Submodule.mem_span_singleton_self _)
    · exact Submodule.Fg.sup ⟨{x}, by rw [Finset.coe_singleton]⟩ h₁
    · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) e
    · show N₀ ≤ (R ∙ x) ⊔ N₀
      exact le_sup_right
#align is_noetherian_iff_fg_well_founded is_noetherian_iff_fg_well_founded

variable (R M)

theorem well_founded_submodule_gt (R M) [Semiring R] [AddCommMonoid M] [Module R M] :
    ∀ [IsNoetherian R M], WellFounded ((· > ·) : Submodule R M → Submodule R M → Prop) :=
  is_noetherian_iff_well_founded.mp
#align well_founded_submodule_gt well_founded_submodule_gt

variable {R M}

/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
theorem set_has_maximal_iff_noetherian :
    (∀ a : Set <| Submodule R M, a.Nonempty → ∃ M' ∈ a, ∀ I ∈ a, M' ≤ I → I = M') ↔
      IsNoetherian R M :=
  by rw [is_noetherian_iff_well_founded, WellFounded.wellFounded_iff_has_max']
#align set_has_maximal_iff_noetherian set_has_maximal_iff_noetherian

/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
    (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
  rw [is_noetherian_iff_well_founded, WellFounded.monotone_chain_condition]
#align monotone_stabilizes_iff_noetherian monotone_stabilizes_iff_noetherian

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop}
    (hgt : ∀ I, (∀ J > I, P J) → P I) (I : Submodule R M) : P I :=
  WellFounded.recursion (well_founded_submodule_gt R M) I hgt
#align is_noetherian.induction IsNoetherian.induction

end

section

universe w

variable {R M P : Type _} {N : Type w} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup P] [Module R P]

theorem finite_of_linear_independent [Nontrivial R] [IsNoetherian R M] {s : Set M}
    (hs : LinearIndependent R (coe : s → M)) : s.Finite :=
  by
  refine'
    by_contradiction fun hf =>
      (RelEmbedding.well_founded_iff_no_descending_seq.1 (well_founded_submodule_gt R M)).elim' _
  have f : ℕ ↪ s := Set.Infinite.natEmbedding s hf
  have : ∀ n, coe ∘ f '' { m | m ≤ n } ⊆ s :=
    by
    rintro n x ⟨y, hy₁, rfl⟩
    exact (f y).2
  have : ∀ a b : ℕ, a ≤ b ↔ span R (coe ∘ f '' { m | m ≤ a }) ≤ span R (coe ∘ f '' { m | m ≤ b }) :=
    by
    intro a b
    rw [span_le_span_iff hs (this a) (this b),
      Set.image_subset_image_iff (subtype.coe_injective.comp f.injective), Set.subset_def]
    exact ⟨fun hab x (hxa : x ≤ a) => le_trans hxa hab, fun hx => hx a (le_refl a)⟩
  exact
    ⟨⟨fun n => span R (coe ∘ f '' { m | m ≤ n }), fun x y => by
        simp (config := { contextual := true }) [le_antisymm_iff, (this _ _).symm]⟩,
      by dsimp [GT.gt] <;> simp only [lt_iff_le_not_le, (this _ _).symm] <;> tauto⟩
#align finite_of_linear_independent finite_of_linear_independent

/-- If the first and final modules in a short exact sequence are noetherian,
  then the middle module is also noetherian. -/
theorem isNoetherianOfRangeEqKer [IsNoetherian R M] [IsNoetherian R P] (f : M →ₗ[R] N)
    (g : N →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g) (h : f.range = g.ker) :
    IsNoetherian R N :=
  is_noetherian_iff_well_founded.2 <|
    wellFounded_gt_exact_sequence (well_founded_submodule_gt R M) (well_founded_submodule_gt R P)
      f.range (Submodule.map f) (Submodule.comap f) (Submodule.comap g) (Submodule.map g)
      (Submodule.gciMapComap hf) (Submodule.giMapComap hg)
      (by simp [Submodule.map_comap_eq, inf_comm]) (by simp [Submodule.comap_map_eq, h])
#align is_noetherian_of_range_eq_ker isNoetherianOfRangeEqKer

/-- For any endomorphism of a Noetherian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot [I : IsNoetherian R M]
    (f : M →ₗ[R] M) : ∃ n : ℕ, n ≠ 0 ∧ (f ^ n).ker ⊓ (f ^ n).range = ⊥ :=
  by
  obtain ⟨n, w⟩ :=
    monotone_stabilizes_iff_noetherian.mpr I
      (f.iterate_ker.comp ⟨fun n => n + 1, fun n m w => by linarith⟩)
  specialize w (2 * n + 1) (by linarith only)
  dsimp at w
  refine' ⟨n + 1, Nat.succ_ne_zero _, _⟩
  rw [eq_bot_iff]
  rintro - ⟨h, ⟨y, rfl⟩⟩
  rw [mem_bot, ← LinearMap.mem_ker, w]
  erw [LinearMap.mem_ker] at h⊢
  change (f ^ (n + 1) * f ^ (n + 1)) y = 0 at h
  rw [← pow_add] at h
  convert h using 3
  ring
#align
  is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot

/-- Any surjective endomorphism of a Noetherian module is injective. -/
theorem IsNoetherian.injective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M)
    (s : Surjective f) : Injective f :=
  by
  obtain ⟨n, ne, w⟩ := IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot f
  rw [linear_map.range_eq_top.mpr (LinearMap.iterate_surjective s n), inf_top_eq,
    LinearMap.ker_eq_bot] at w
  exact LinearMap.injective_of_iterate_injective Ne w
#align
  is_noetherian.injective_of_surjective_endomorphism IsNoetherian.injective_of_surjective_endomorphism

/-- Any surjective endomorphism of a Noetherian module is bijective. -/
theorem IsNoetherian.bijective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M)
    (s : Surjective f) : Bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩
#align
  is_noetherian.bijective_of_surjective_endomorphism IsNoetherian.bijective_of_surjective_endomorphism

/-- A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
theorem IsNoetherian.disjoint_partial_sups_eventually_bot [I : IsNoetherian R M]
    (f : ℕ → Submodule R M) (h : ∀ n, Disjoint (partialSups f n) (f (n + 1))) :
    ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ :=
  by
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m + 1) = ⊥
  · obtain ⟨n, w⟩ := t
    use n + 1
    rintro (_ | m) p
    · cases p
    · apply w
      exact nat.succ_le_succ_iff.mp p
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partialSups f)
  exact
    ⟨n, fun m p =>
      (h m).eq_bot_of_ge <| sup_eq_left.1 <| (w (m + 1) <| le_add_right p).symm.trans <| w m p⟩
#align
  is_noetherian.disjoint_partial_sups_eventually_bot IsNoetherian.disjoint_partial_sups_eventually_bot

/-- If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
noncomputable def IsNoetherian.equivPunitOfProdInjective [IsNoetherian R M] (f : M × N →ₗ[R] M)
    (i : Injective f) : N ≃ₗ[R] PUnit.{w + 1} :=
  by
  apply Nonempty.some
  obtain ⟨n, w⟩ :=
    IsNoetherian.disjoint_partial_sups_eventually_bot (f.tailing i) (f.tailings_disjoint_tailing i)
  specialize w n (le_refl n)
  apply Nonempty.intro
  refine' (f.tailing_linear_equiv i n).symm ≪≫ₗ _
  rw [w]
  exact Submodule.botEquivPunit
#align is_noetherian.equiv_punit_of_prod_injective IsNoetherian.equivPunitOfProdInjective

end

/-- A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
@[reducible]
def IsNoetherianRing (R) [Semiring R] :=
  IsNoetherian R R
#align is_noetherian_ring IsNoetherianRing

theorem is_noetherian_ring_iff {R} [Semiring R] : IsNoetherianRing R ↔ IsNoetherian R R :=
  Iff.rfl
#align is_noetherian_ring_iff is_noetherian_ring_iff

/-- A ring is Noetherian if and only if all its ideals are finitely-generated. -/
theorem is_noetherian_ring_iff_ideal_fg (R : Type _) [Semiring R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.Fg :=
  is_noetherian_ring_iff.trans is_noetherian_def
#align is_noetherian_ring_iff_ideal_fg is_noetherian_ring_iff_ideal_fg

-- see Note [lower instance priority]
instance (priority := 80) isNoetherianOfFinite (R M) [Finite M] [Semiring R] [AddCommMonoid M]
    [Module R M] : IsNoetherian R M :=
  ⟨fun s => ⟨(s : Set M).to_finite.toFinset, by rw [Set.Finite.coe_to_finset, Submodule.span_eq]⟩⟩
#align is_noetherian_of_finite isNoetherianOfFinite

-- see Note [lower instance priority]
/-- Modules over the trivial ring are Noetherian. -/
instance (priority := 100) isNoetherianOfSubsingleton (R M) [Subsingleton R] [Semiring R]
    [AddCommMonoid M] [Module R M] : IsNoetherian R M :=
  haveI := Module.subsingleton R M
  isNoetherianOfFinite R M
#align is_noetherian_of_subsingleton isNoetherianOfSubsingleton

theorem isNoetherianOfSubmoduleOfNoetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (h : IsNoetherian R M) : IsNoetherian R N :=
  by
  rw [is_noetherian_iff_well_founded] at h⊢
  exact OrderEmbedding.wellFounded (Submodule.MapSubtype.orderEmbedding N).dual h
#align is_noetherian_of_submodule_of_noetherian isNoetherianOfSubmoduleOfNoetherian

instance Submodule.Quotient.isNoetherian {R} [Ring R] {M} [AddCommGroup M] [Module R M]
    (N : Submodule R M) [h : IsNoetherian R M] : IsNoetherian R (M ⧸ N) :=
  by
  rw [is_noetherian_iff_well_founded] at h⊢
  exact OrderEmbedding.wellFounded (Submodule.ComapMkq.orderEmbedding N).dual h
#align submodule.quotient.is_noetherian Submodule.Quotient.isNoetherian

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem isNoetherianOfTower (R) {S M} [Semiring R] [Semiring S] [AddCommMonoid M] [HasSmul R S]
    [Module S M] [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M :=
  by
  rw [is_noetherian_iff_well_founded] at h⊢
  refine' (Submodule.restrictScalarsEmbedding R S M).dual.WellFounded h
#align is_noetherian_of_tower isNoetherianOfTower

instance Ideal.Quotient.is_noetherian_ring {R : Type _} [CommRing R] [h : IsNoetherianRing R]
    (I : Ideal R) : IsNoetherianRing (R ⧸ I) :=
  is_noetherian_ring_iff.mpr <| isNoetherianOfTower R <| Submodule.Quotient.isNoetherian _
#align ideal.quotient.is_noetherian_ring Ideal.Quotient.is_noetherian_ring

theorem isNoetherianOfFgOfNoetherian {R M} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [IsNoetherianRing R] (hN : N.Fg) : IsNoetherian R N :=
  by
  let ⟨s, hs⟩ := hN
  haveI := Classical.decEq M
  haveI := Classical.decEq R
  letI : IsNoetherian R R := by infer_instance
  have : ∀ x ∈ s, x ∈ N := fun x hx => hs ▸ Submodule.subset_span hx
  refine' @isNoetherianOfSurjective ((↑s : Set M) → R) _ _ _ (Pi.module _ _ _) _ _ _ isNoetherianPi
  · fapply LinearMap.mk
    · exact fun f => ⟨∑ i in s.attach, f i • i.1, N.sum_mem fun c _ => N.smul_mem _ <| this _ c.2⟩
    · intro f g
      apply Subtype.eq
      change (∑ i in s.attach, (f i + g i) • _) = _
      simp only [add_smul, Finset.sum_add_distrib]
      rfl
    · intro c f
      apply Subtype.eq
      change (∑ i in s.attach, (c • f i) • _) = _
      simp only [smul_eq_mul, mul_smul]
      exact finset.smul_sum.symm
  rw [LinearMap.range_eq_top]
  rintro ⟨n, hn⟩
  change n ∈ N at hn
  rw [← hs, ← Set.image_id ↑s, Finsupp.mem_span_image_iff_total] at hn
  rcases hn with ⟨l, hl1, hl2⟩
  refine' ⟨fun x => l x, Subtype.ext _⟩
  change (∑ i in s.attach, l i • (i : M)) = n
  rw [@Finset.sum_attach M M s _ fun i => l i • i, ← hl2, Finsupp.total_apply, Finsupp.sum, eq_comm]
  refine' Finset.sum_subset hl1 fun x _ hx => _
  rw [Finsupp.not_mem_support_iff.1 hx, zero_smul]
#align is_noetherian_of_fg_of_noetherian isNoetherianOfFgOfNoetherian

theorem isNoetherianOfFgOfNoetherian' {R M} [Ring R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] (h : (⊤ : Submodule R M).Fg) : IsNoetherian R M :=
  have : IsNoetherian R (⊤ : Submodule R M) := isNoetherianOfFgOfNoetherian _ h
  isNoetherianOfLinearEquiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
#align is_noetherian_of_fg_of_noetherian' isNoetherianOfFgOfNoetherian'

/-- In a module over a noetherian ring, the submodule generated by finitely many vectors is
noetherian. -/
theorem isNoetherianSpanOfFinite (R) {M} [Ring R] [AddCommGroup M] [Module R M] [IsNoetherianRing R]
    {A : Set M} (hA : A.Finite) : IsNoetherian R (Submodule.span R A) :=
  isNoetherianOfFgOfNoetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)
#align is_noetherian_span_of_finite isNoetherianSpanOfFinite

theorem is_noetherian_ring_of_surjective (R) [Ring R] (S) [Ring S] (f : R →+* S)
    (hf : Function.Surjective f) [H : IsNoetherianRing R] : IsNoetherianRing S :=
  by
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at H⊢
  exact OrderEmbedding.wellFounded (Ideal.orderEmbeddingOfSurjective f hf).dual H
#align is_noetherian_ring_of_surjective is_noetherian_ring_of_surjective

instance is_noetherian_ring_range {R} [Ring R] {S} [Ring S] (f : R →+* S) [IsNoetherianRing R] :
    IsNoetherianRing f.range :=
  is_noetherian_ring_of_surjective R f.range f.range_restrict f.range_restrict_surjective
#align is_noetherian_ring_range is_noetherian_ring_range

theorem is_noetherian_ring_of_ring_equiv (R) [Ring R] {S} [Ring S] (f : R ≃+* S)
    [IsNoetherianRing R] : IsNoetherianRing S :=
  is_noetherian_ring_of_surjective R S f.toRingHom f.toEquiv.Surjective
#align is_noetherian_ring_of_ring_equiv is_noetherian_ring_of_ring_equiv

theorem IsNoetherianRing.is_nilpotent_nilradical (R : Type _) [CommRing R] [IsNoetherianRing R] :
    IsNilpotent (nilradical R) :=
  by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩
#align is_noetherian_ring.is_nilpotent_nilradical IsNoetherianRing.is_nilpotent_nilradical

