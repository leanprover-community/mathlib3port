import Mathbin.GroupTheory.Finiteness 
import Mathbin.Data.Multiset.FinsetOps 
import Mathbin.Algebra.Algebra.Tower 
import Mathbin.Order.OrderIsoNat 
import Mathbin.RingTheory.Ideal.Operations 
import Mathbin.Order.CompactlyGenerated 
import Mathbin.LinearAlgebra.LinearIndependent

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

* `fg N : Prop` is the assertion that `N` is finitely generated as an `R`-module.

* `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

* `is_noetherian_iff_well_founded` is the theorem that an R-module M is Noetherian iff
  `>` is well-founded on `submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `ring_theory.polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/


open Set

open_locale BigOperators Pointwise

namespace Submodule

variable{R : Type _}{M : Type _}[Semiringₓ R][AddCommMonoidₓ M][Module R M]

/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def fg (N : Submodule R M) : Prop :=
  ∃ S : Finset M, Submodule.span R («expr↑ » S) = N

theorem fg_def {N : Submodule R M} : N.fg ↔ ∃ S : Set M, finite S ∧ span R S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_to_set t, h⟩,
    by 
      rintro ⟨t', h, rfl⟩
      rcases finite.exists_finset_coe h with ⟨t, rfl⟩
      exact ⟨t, rfl⟩⟩

theorem fg_iff_add_submonoid_fg (P : Submodule ℕ M) : P.fg ↔ P.to_add_submonoid.fg :=
  ⟨fun ⟨S, hS⟩ =>
      ⟨S,
        by 
          simpa [←span_nat_eq_add_submonoid_closure] using hS⟩,
    fun ⟨S, hS⟩ =>
      ⟨S,
        by 
          simpa [←span_nat_eq_add_submonoid_closure] using hS⟩⟩

theorem fg_iff_add_subgroup_fg {G : Type _} [AddCommGroupₓ G] (P : Submodule ℤ G) : P.fg ↔ P.to_add_subgroup.fg :=
  ⟨fun ⟨S, hS⟩ =>
      ⟨S,
        by 
          simpa [←span_int_eq_add_subgroup_closure] using hS⟩,
    fun ⟨S, hS⟩ =>
      ⟨S,
        by 
          simpa [←span_int_eq_add_subgroup_closure] using hS⟩⟩

theorem fg_iff_exists_fin_generating_family {N : Submodule R M} :
  N.fg ↔ ∃ (n : ℕ)(s : Finₓ n → M), span R (range s) = N :=
  by 
    rw [fg_def]
    split 
    ·
      rintro ⟨S, Sfin, hS⟩
      obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding 
      exact ⟨n, f, hS⟩
    ·
      rintro ⟨n, s, hs⟩
      refine' ⟨range s, finite_range s, hs⟩

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2,
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV) -/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
{R : Type*}
[comm_ring R]
{M : Type*}
[add_comm_group M]
[module R M]
(I : ideal R)
(N : submodule R M)
(hn : N.fg)
(hin : «expr ≤ »(N, «expr • »(I, N))) : «expr∃ , »((r : R), «expr ∧ »(«expr ∈ »(«expr - »(r, 1), I), ∀
  n «expr ∈ » N, «expr = »(«expr • »(r, n), (0 : M)))) :=
begin
  rw [expr fg_def] ["at", ident hn],
  rcases [expr hn, "with", "⟨", ident s, ",", ident hfs, ",", ident hs, "⟩"],
  have [] [":", expr «expr∃ , »((r : R), «expr ∧ »(«expr ∈ »(«expr - »(r, 1), I), «expr ∧ »(«expr ≤ »(N, «expr • »(I, span R s).comap (linear_map.lsmul R M r)), «expr ⊆ »(s, N))))] [],
  { refine [expr ⟨1, _, _, _⟩],
    { rw [expr sub_self] [],
      exact [expr I.zero_mem] },
    { rw ["[", expr hs, "]"] [],
      intros [ident n, ident hn],
      rw ["[", expr mem_comap, "]"] [],
      change [expr «expr ∈ »(«expr • »((1 : R), n), «expr • »(I, N))] [] [],
      rw [expr one_smul] [],
      exact [expr hin hn] },
    { rw ["[", "<-", expr span_le, ",", expr hs, "]"] [],
      exact [expr le_refl N] } },
  clear [ident hin, ident hs],
  revert [ident this],
  refine [expr set.finite.dinduction_on hfs (λ H, _) (λ i s his hfs ih H, _)],
  { rcases [expr H, "with", "⟨", ident r, ",", ident hr1, ",", ident hrn, ",", ident hs, "⟩"],
    refine [expr ⟨r, hr1, λ n hn, _⟩],
    specialize [expr hrn hn],
    rwa ["[", expr mem_comap, ",", expr span_empty, ",", expr smul_bot, ",", expr mem_bot, "]"] ["at", ident hrn] },
  apply [expr ih],
  rcases [expr H, "with", "⟨", ident r, ",", ident hr1, ",", ident hrn, ",", ident hs, "⟩"],
  rw ["[", "<-", expr set.singleton_union, ",", expr span_union, ",", expr smul_sup, "]"] ["at", ident hrn],
  rw ["[", expr set.insert_subset, "]"] ["at", ident hs],
  have [] [":", expr «expr∃ , »((c : R), «expr ∧ »(«expr ∈ »(«expr - »(c, 1), I), «expr ∈ »(«expr • »(c, i), «expr • »(I, span R s))))] [],
  { specialize [expr hrn hs.1],
    rw ["[", expr mem_comap, ",", expr mem_sup, "]"] ["at", ident hrn],
    rcases [expr hrn, "with", "⟨", ident y, ",", ident hy, ",", ident z, ",", ident hz, ",", ident hyz, "⟩"],
    change [expr «expr = »(«expr + »(y, z), «expr • »(r, i))] [] ["at", ident hyz],
    rw [expr mem_smul_span_singleton] ["at", ident hy],
    rcases [expr hy, "with", "⟨", ident c, ",", ident hci, ",", ident rfl, "⟩"],
    use [expr «expr - »(r, c)],
    split,
    { rw ["[", expr sub_right_comm, "]"] [],
      exact [expr I.sub_mem hr1 hci] },
    { rw ["[", expr sub_smul, ",", "<-", expr hyz, ",", expr add_sub_cancel', "]"] [],
      exact [expr hz] } },
  rcases [expr this, "with", "⟨", ident c, ",", ident hc1, ",", ident hci, "⟩"],
  refine [expr ⟨«expr * »(c, r), _, _, hs.2⟩],
  { rw ["[", "<-", expr ideal.quotient.eq, ",", expr ring_hom.map_one, "]"] ["at", ident hr1, ident hc1, "⊢"],
    rw ["[", expr ring_hom.map_mul, ",", expr hc1, ",", expr hr1, ",", expr mul_one, "]"] [] },
  { intros [ident n, ident hn],
    specialize [expr hrn hn],
    rw ["[", expr mem_comap, ",", expr mem_sup, "]"] ["at", ident hrn],
    rcases [expr hrn, "with", "⟨", ident y, ",", ident hy, ",", ident z, ",", ident hz, ",", ident hyz, "⟩"],
    change [expr «expr = »(«expr + »(y, z), «expr • »(r, n))] [] ["at", ident hyz],
    rw [expr mem_smul_span_singleton] ["at", ident hy],
    rcases [expr hy, "with", "⟨", ident d, ",", ident hdi, ",", ident rfl, "⟩"],
    change [expr «expr ∈ »(«expr • »(_, _), «expr • »(I, span R s))] [] [],
    rw ["[", expr mul_smul, ",", "<-", expr hyz, ",", expr smul_add, ",", expr smul_smul, ",", expr mul_comm, ",", expr mul_smul, "]"] [],
    exact [expr add_mem _ (smul_mem _ _ hci) (smul_mem _ _ hz)] }
end

theorem fg_bot : (⊥ : Submodule R M).Fg :=
  ⟨∅,
    by 
      rw [Finset.coe_empty, span_empty]⟩

theorem fg_span {s : Set M} (hs : finite s) : fg (span R s) :=
  ⟨hs.to_finset,
    by 
      rw [hs.coe_to_finset]⟩

theorem fg_span_singleton (x : M) : fg (R∙x) :=
  fg_span (finite_singleton x)

theorem fg_sup {N₁ N₂ : Submodule R M} (hN₁ : N₁.fg) (hN₂ : N₂.fg) : (N₁⊔N₂).Fg :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁ 
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂ 
  fg_def.2
    ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1,
      by 
        rw [span_union, ht₁.2, ht₂.2]⟩

variable{P : Type _}[AddCommMonoidₓ P][Module R P]

variable{f : M →ₗ[R] P}

theorem fg_map {N : Submodule R M} (hs : N.fg) : (N.map f).Fg :=
  let ⟨t, ht⟩ := fg_def.1 hs 
  fg_def.2
    ⟨f '' t, ht.1.Image _,
      by 
        rw [span_image, ht.2]⟩

theorem fg_of_fg_map_injective (f : M →ₗ[R] P) (hf : Function.Injective f) {N : Submodule R M} (hfn : (N.map f).Fg) :
  N.fg :=
  let ⟨t, ht⟩ := hfn
  ⟨t.preimage f$ fun x _ y _ h => hf h,
    Submodule.map_injective_of_injective hf$
      by 
        rw [f.map_span, Finset.coe_preimage, Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left, ht]
        rw [←LinearMap.range_coe, ←span_le, ht, ←map_top]
        exact map_mono le_top⟩

theorem fg_of_fg_map {R M P : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ P] [Module R P]
  (f : M →ₗ[R] P) (hf : f.ker = ⊥) {N : Submodule R M} (hfn : (N.map f).Fg) : N.fg :=
  fg_of_fg_map_injective f (LinearMap.ker_eq_bot.1 hf) hfn

theorem fg_top (N : Submodule R M) : (⊤ : Submodule R N).Fg ↔ N.fg :=
  ⟨fun h => N.range_subtype ▸ map_top N.subtype ▸ fg_map h,
    fun h =>
      fg_of_fg_map_injective N.subtype Subtype.val_injective$
        by 
          rwa [map_top, range_subtype]⟩

theorem fg_of_linear_equiv (e : M ≃ₗ[R] P) (h : (⊤ : Submodule R P).Fg) : (⊤ : Submodule R M).Fg :=
  e.symm.range ▸ map_top (e.symm : P →ₗ[R] M) ▸ fg_map h

theorem fg_prod {sb : Submodule R M} {sc : Submodule R P} (hsb : sb.fg) (hsc : sc.fg) : (sb.prod sc).Fg :=
  let ⟨tb, htb⟩ := fg_def.1 hsb 
  let ⟨Tc, htc⟩ := fg_def.1 hsc 
  fg_def.2
    ⟨LinearMap.inl R M P '' tb ∪ LinearMap.inr R M P '' Tc, (htb.1.Image _).union (htc.1.Image _),
      by 
        rw [LinearMap.span_inl_union_inr, htb.2, htc.2]⟩

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker
{R M P : Type*}
[ring R]
[add_comm_group M]
[module R M]
[add_comm_group P]
[module R P]
(f : «expr →ₗ[ ] »(M, R, P))
{s : submodule R M}
(hs1 : (s.map f).fg)
(hs2 : «expr ⊓ »(s, f.ker).fg) : s.fg :=
begin
  haveI [] [] [":=", expr classical.dec_eq R],
  haveI [] [] [":=", expr classical.dec_eq M],
  haveI [] [] [":=", expr classical.dec_eq P],
  cases [expr hs1] ["with", ident t1, ident ht1],
  cases [expr hs2] ["with", ident t2, ident ht2],
  have [] [":", expr ∀ y «expr ∈ » t1, «expr∃ , »((x «expr ∈ » s), «expr = »(f x, y))] [],
  { intros [ident y, ident hy],
    have [] [":", expr «expr ∈ »(y, map f s)] [],
    { rw ["<-", expr ht1] [],
      exact [expr subset_span hy] },
    rcases [expr mem_map.1 this, "with", "⟨", ident x, ",", ident hx1, ",", ident hx2, "⟩"],
    exact [expr ⟨x, hx1, hx2⟩] },
  have [] [":", expr «expr∃ , »((g : P → M), ∀ y «expr ∈ » t1, «expr ∧ »(«expr ∈ »(g y, s), «expr = »(f (g y), y)))] [],
  { choose [] [ident g] [ident hg1, ident hg2] [],
    existsi [expr λ y, if H : «expr ∈ »(y, t1) then g y H else 0],
    intros [ident y, ident H],
    split,
    { simp [] [] ["only"] ["[", expr dif_pos H, "]"] [] [],
      apply [expr hg1] },
    { simp [] [] ["only"] ["[", expr dif_pos H, "]"] [] [],
      apply [expr hg2] } },
  cases [expr this] ["with", ident g, ident hg],
  clear [ident this],
  existsi [expr «expr ∪ »(t1.image g, t2)],
  rw ["[", expr finset.coe_union, ",", expr span_union, ",", expr finset.coe_image, "]"] [],
  apply [expr le_antisymm],
  { refine [expr sup_le «expr $ »(span_le.2, image_subset_iff.2 _) (span_le.2 _)],
    { intros [ident y, ident hy],
      exact [expr (hg y hy).1] },
    { intros [ident x, ident hx],
      have [] [] [":=", expr subset_span hx],
      rw [expr ht2] ["at", ident this],
      exact [expr this.1] } },
  intros [ident x, ident hx],
  have [] [":", expr «expr ∈ »(f x, map f s)] [],
  { rw [expr mem_map] [],
    exact [expr ⟨x, hx, rfl⟩] },
  rw ["[", "<-", expr ht1, ",", "<-", expr set.image_id «expr↑ »(t1), ",", expr finsupp.mem_span_image_iff_total, "]"] ["at", ident this],
  rcases [expr this, "with", "⟨", ident l, ",", ident hl1, ",", ident hl2, "⟩"],
  refine [expr mem_sup.2 ⟨(finsupp.total M M R id).to_fun ((finsupp.lmap_domain R R g : «expr →₀ »(P, R) → «expr →₀ »(M, R)) l), _, «expr - »(x, finsupp.total M M R id ((finsupp.lmap_domain R R g : «expr →₀ »(P, R) → «expr →₀ »(M, R)) l)), _, add_sub_cancel'_right _ _⟩],
  { rw ["[", "<-", expr set.image_id «expr '' »(g, «expr↑ »(t1)), ",", expr finsupp.mem_span_image_iff_total, "]"] [],
    refine [expr ⟨_, _, rfl⟩],
    haveI [] [":", expr inhabited P] [":=", expr ⟨0⟩],
    rw ["[", "<-", expr finsupp.lmap_domain_supported _ _ g, ",", expr mem_map, "]"] [],
    refine [expr ⟨l, hl1, _⟩],
    refl },
  rw ["[", expr ht2, ",", expr mem_inf, "]"] [],
  split,
  { apply [expr s.sub_mem hx],
    rw ["[", expr finsupp.total_apply, ",", expr finsupp.lmap_domain_apply, ",", expr finsupp.sum_map_domain_index, "]"] [],
    refine [expr s.sum_mem _],
    { intros [ident y, ident hy],
      exact [expr s.smul_mem _ (hg y (hl1 hy)).1] },
    { exact [expr zero_smul _] },
    { exact [expr λ _ _ _, add_smul _ _ _] } },
  { rw ["[", expr linear_map.mem_ker, ",", expr f.map_sub, ",", "<-", expr hl2, "]"] [],
    rw ["[", expr finsupp.total_apply, ",", expr finsupp.total_apply, ",", expr finsupp.lmap_domain_apply, "]"] [],
    rw ["[", expr finsupp.sum_map_domain_index, ",", expr finsupp.sum, ",", expr finsupp.sum, ",", expr f.map_sum, "]"] [],
    rw [expr sub_eq_zero] [],
    refine [expr finset.sum_congr rfl (λ y hy, _)],
    unfold [ident id] [],
    rw ["[", expr f.map_smul, ",", expr (hg y (hl1 hy)).2, "]"] [],
    { exact [expr zero_smul _] },
    { exact [expr λ _ _ _, add_smul _ _ _] } }
end

/-- The image of a finitely generated ideal is finitely generated.

This is the `ideal` version of `submodule.fg_map`. -/
theorem map_fg_of_fg {R S : Type _} [Semiringₓ R] [Semiringₓ S] (I : Ideal R) (h : I.fg) (f : R →+* S) : (I.map f).Fg :=
  by 
    classical 
    obtain ⟨s, hs : Ideal.span («expr↑ » s) = _⟩ := h 
    refine' ⟨s.image f, (_ : Ideal.span _ = _)⟩
    rw [Finset.coe_image, ←Ideal.map_span, hs]

/-- The kernel of the composition of two linear maps is finitely generated if both kernels are and
the first morphism is surjective. -/
theorem fg_ker_comp {R M N P : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [AddCommGroupₓ N] [Module R N]
  [AddCommGroupₓ P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf1 : f.ker.fg) (hf2 : g.ker.fg)
  (hsur : Function.Surjective f) : (g.comp f).ker.Fg :=
  by 
    rw [LinearMap.ker_comp]
    apply fg_of_fg_map_of_fg_inf_ker f
    ·
      rwa [Submodule.map_comap_eq, LinearMap.range_eq_top.2 hsur, top_inf_eq]
    ·
      rwa [inf_of_le_right (show f.ker ≤ comap f g.ker from comap_mono bot_le)]

theorem fg_restrict_scalars {R S M : Type _} [CommRingₓ R] [CommRingₓ S] [Algebra R S] [AddCommGroupₓ M] [Module S M]
  [Module R M] [IsScalarTower R S M] (N : Submodule S M) (hfin : N.fg) (h : Function.Surjective (algebraMap R S)) :
  (Submodule.restrictScalars R N).Fg :=
  by 
    obtain ⟨X, rfl⟩ := hfin 
    use X 
    exact Submodule.span_eq_restrict_scalars R S M X h

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fg_ker_ring_hom_comp
{R S A : Type*}
[comm_ring R]
[comm_ring S]
[comm_ring A]
(f : «expr →+* »(R, S))
(g : «expr →+* »(S, A))
(hf : f.ker.fg)
(hg : g.ker.fg)
(hsur : function.surjective f) : (g.comp f).ker.fg :=
begin
  letI [] [":", expr algebra R S] [":=", expr ring_hom.to_algebra f],
  letI [] [":", expr algebra R A] [":=", expr ring_hom.to_algebra (g.comp f)],
  letI [] [":", expr algebra S A] [":=", expr ring_hom.to_algebra g],
  letI [] [":", expr is_scalar_tower R S A] [":=", expr is_scalar_tower.of_algebra_map_eq (λ _, rfl)],
  let [ident f₁] [] [":=", expr algebra.linear_map R S],
  let [ident g₁] [] [":=", expr (is_scalar_tower.to_alg_hom R S A).to_linear_map],
  exact [expr fg_ker_comp f₁ g₁ hf (fg_restrict_scalars g.ker hg hsur) hsur]
end

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Finitely generated submodules are precisely compact elements in the submodule lattice. -/
theorem fg_iff_compact (s : submodule R M) : «expr ↔ »(s.fg, complete_lattice.is_compact_element s) :=
begin
  classical,
  let [ident sp] [":", expr M → submodule R M] [":=", expr λ a, span R {a}],
  have [ident supr_rw] [":", expr ∀
   t : finset M, «expr = »(«expr⨆ , »((x «expr ∈ » t), sp x), «expr⨆ , »((x «expr ∈ » («expr↑ »(t) : set M)), sp x))] [],
  from [expr λ t, by refl],
  split,
  { rintro ["⟨", ident t, ",", ident rfl, "⟩"],
    rw ["[", expr span_eq_supr_of_singleton_spans, ",", "<-", expr supr_rw, ",", "<-", expr finset.sup_eq_supr t sp, "]"] [],
    apply [expr complete_lattice.finset_sup_compact_of_compact],
    exact [expr λ n _, singleton_span_is_compact_element n] },
  { intro [ident h],
    have [ident sSup] [":", expr «expr = »(s, Sup «expr '' »(sp, «expr↑ »(s)))] [],
    by rw ["[", expr Sup_eq_supr, ",", expr supr_image, ",", "<-", expr span_eq_supr_of_singleton_spans, ",", expr eq_comm, ",", expr span_eq, "]"] [],
    obtain ["⟨", ident u, ",", "⟨", ident huspan, ",", ident husup, "⟩", "⟩", ":=", expr h «expr '' »(sp, «expr↑ »(s)) (le_of_eq sSup)],
    have [ident ssup] [":", expr «expr = »(s, u.sup id)] [],
    { suffices [] [":", expr «expr ≤ »(u.sup id, s)],
      from [expr le_antisymm husup this],
      rw ["[", expr sSup, ",", expr finset.sup_id_eq_Sup, "]"] [],
      exact [expr Sup_le_Sup huspan] },
    obtain ["⟨", ident t, ",", "⟨", ident hts, ",", ident rfl, "⟩", "⟩", ":=", expr finset.subset_image_iff.mp huspan],
    rw ["[", expr finset.sup_finset_image, ",", expr function.comp.left_id, ",", expr finset.sup_eq_supr, ",", expr supr_rw, ",", "<-", expr span_eq_supr_of_singleton_spans, ",", expr eq_comm, "]"] ["at", ident ssup],
    exact [expr ⟨t, ssup⟩] }
end

end Submodule

/--
`is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
class IsNoetherian(R M)[Semiringₓ R][AddCommMonoidₓ M][Module R M] : Prop where 
  noetherian : ∀ (s : Submodule R M), s.fg

section 

variable{R : Type _}{M : Type _}{P : Type _}

variable[Semiringₓ R][AddCommMonoidₓ M][AddCommMonoidₓ P]

variable[Module R M][Module R P]

open IsNoetherian

include R

/-- An R-module is Noetherian iff all its submodules are finitely-generated. -/
theorem is_noetherian_def : IsNoetherian R M ↔ ∀ (s : Submodule R M), s.fg :=
  ⟨fun h => h.noetherian, IsNoetherian.mk⟩

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_noetherian_submodule
{N : submodule R M} : «expr ↔ »(is_noetherian R N, ∀ s : submodule R M, «expr ≤ »(s, N) → s.fg) :=
begin
  refine [expr ⟨λ ⟨hn⟩, λ s hs, have «expr ≤ »(s, N.subtype.range), from «expr ▸ »(N.range_subtype.symm, hs),
    «expr ▸ »(submodule.map_comap_eq_self this, submodule.fg_map (hn _)), λ h, ⟨λ s, _⟩⟩],
  have [ident f] [] [":=", expr (submodule.equiv_map_of_injective N.subtype subtype.val_injective s).symm],
  have [ident h₁] [] [":=", expr h (s.map N.subtype) (submodule.map_subtype_le N s)],
  have [ident h₂] [":", expr «expr = »((«expr⊤»() : submodule R (s.map N.subtype)).map («expr↑ »(f) : «expr →ₗ[ ] »(_, R, s)), «expr⊤»())] [":=", expr by simp [] [] [] [] [] []],
  have [ident h₃] [] [":=", expr @submodule.fg_map _ _ _ _ _ _ _ _ («expr↑ »(f) : «expr →ₗ[ ] »(_, R, s)) _ ((submodule.fg_top _).2 h₁)],
  exact [expr (submodule.fg_top _).1 «expr ▸ »(h₂, h₃)]
end

theorem is_noetherian_submodule_left {N : Submodule R M} : IsNoetherian R N ↔ ∀ (s : Submodule R M), (N⊓s).Fg :=
  is_noetherian_submodule.trans ⟨fun H s => H _ inf_le_left, fun H s hs => inf_of_le_right hs ▸ H _⟩

theorem is_noetherian_submodule_right {N : Submodule R M} : IsNoetherian R N ↔ ∀ (s : Submodule R M), (s⊓N).Fg :=
  is_noetherian_submodule.trans ⟨fun H s => H _ inf_le_right, fun H s hs => inf_of_le_left hs ▸ H _⟩

instance is_noetherian_submodule' [IsNoetherian R M] (N : Submodule R M) : IsNoetherian R N :=
  is_noetherian_submodule.2$ fun _ _ => IsNoetherian.noetherian _

theorem is_noetherian_of_le {s t : Submodule R M} [ht : IsNoetherian R t] (h : s ≤ t) : IsNoetherian R s :=
  is_noetherian_submodule.mpr fun s' hs' => is_noetherian_submodule.mp ht _ (le_transₓ hs' h)

variable(M)

theorem is_noetherian_of_surjective (f : M →ₗ[R] P) (hf : f.range = ⊤) [IsNoetherian R M] : IsNoetherian R P :=
  ⟨fun s =>
      have  : (s.comap f).map f = s := Submodule.map_comap_eq_self$ hf.symm ▸ le_top 
      this ▸ Submodule.fg_map$ noetherian _⟩

variable{M}

theorem is_noetherian_of_linear_equiv (f : M ≃ₗ[R] P) [IsNoetherian R M] : IsNoetherian R P :=
  is_noetherian_of_surjective _ f.to_linear_map f.range

theorem is_noetherian_top_iff : IsNoetherian R (⊤ : Submodule R M) ↔ IsNoetherian R M :=
  by 
    (
      split  <;> intro h)
    ·
      exact is_noetherian_of_linear_equiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)
    ·
      exact is_noetherian_of_linear_equiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl).symm

theorem is_noetherian_of_injective [IsNoetherian R P] (f : M →ₗ[R] P) (hf : Function.Injective f) : IsNoetherian R M :=
  is_noetherian_of_linear_equiv (LinearEquiv.ofInjective f hf).symm

theorem fg_of_injective [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P) (hf : Function.Injective f) : N.fg :=
  @IsNoetherian.noetherian _ _ _ (is_noetherian_of_injective f hf) N

end 

section 

variable{R : Type _}{M : Type _}{P : Type _}

variable[Ringₓ R][AddCommGroupₓ M][AddCommGroupₓ P]

variable[Module R M][Module R P]

open IsNoetherian

include R

theorem is_noetherian_of_ker_bot [IsNoetherian R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) : IsNoetherian R M :=
  is_noetherian_of_linear_equiv (LinearEquiv.ofInjective f$ LinearMap.ker_eq_bot.mp hf).symm

theorem fg_of_ker_bot [IsNoetherian R P] {N : Submodule R M} (f : M →ₗ[R] P) (hf : f.ker = ⊥) : N.fg :=
  @IsNoetherian.noetherian _ _ _ (is_noetherian_of_ker_bot f hf) N

instance is_noetherian_prod [IsNoetherian R M] [IsNoetherian R P] : IsNoetherian R (M × P) :=
  ⟨fun s =>
      Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd R M P) (noetherian _)$
        have  : s⊓LinearMap.ker (LinearMap.snd R M P) ≤ LinearMap.range (LinearMap.inl R M P) :=
          fun x ⟨hx1, hx2⟩ => ⟨x.1, Prod.extₓ rfl$ Eq.symm$ LinearMap.mem_ker.1 hx2⟩
        Submodule.map_comap_eq_self this ▸ Submodule.fg_map (noetherian _)⟩

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance is_noetherian_pi
{R ι : Type*}
{M : ι → Type*}
[ring R]
[∀ i, add_comm_group (M i)]
[∀ i, module R (M i)]
[fintype ι]
[∀ i, is_noetherian R (M i)] : is_noetherian R (∀ i, M i) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  suffices [ident on_finset] [":", expr ∀ s : finset ι, is_noetherian R (∀ i : s, M i)],
  { let [ident coe_e] [] [":=", expr equiv.subtype_univ_equiv finset.mem_univ],
    letI [] [":", expr is_noetherian R (∀ i : finset.univ, M (coe_e i))] [":=", expr on_finset finset.univ],
    exact [expr is_noetherian_of_linear_equiv (linear_equiv.Pi_congr_left R M coe_e)] },
  intro [ident s],
  induction [expr s] ["using", ident finset.induction] ["with", ident a, ident s, ident has, ident ih] [],
  { split,
    intro [ident s],
    convert [] [expr submodule.fg_bot] [],
    apply [expr eq_bot_iff.2],
    intros [ident x, ident hx],
    refine [expr (submodule.mem_bot R).2 _],
    ext [] [ident i] [],
    cases [expr i.2] [] },
  refine [expr @is_noetherian_of_linear_equiv _ _ _ _ _ _ _ _ _ (@is_noetherian_prod _ (M a) _ _ _ _ _ _ _ ih)],
  fconstructor,
  { exact [expr λ
     f
     i, or.by_cases (finset.mem_insert.1 i.2) (λ
      h : «expr = »(i.1, a), show M i.1, from eq.rec_on h.symm f.1) (λ
      h : «expr ∈ »(i.1, s), show M i.1, from f.2 ⟨i.1, h⟩)] },
  { intros [ident f, ident g],
    ext [] [ident i] [],
    unfold [ident or.by_cases] [],
    cases [expr i] ["with", ident i, ident hi],
    rcases [expr finset.mem_insert.1 hi, "with", ident rfl, "|", ident h],
    { change [expr «expr = »(_, «expr + »(_, _))] [] [],
      simp [] [] ["only"] ["[", expr dif_pos, "]"] [] [],
      refl },
    { change [expr «expr = »(_, «expr + »(_, _))] [] [],
      have [] [":", expr «expr¬ »(«expr = »(i, a))] [],
      { rintro [ident rfl],
        exact [expr has h] },
      simp [] [] ["only"] ["[", expr dif_neg this, ",", expr dif_pos h, "]"] [] [],
      refl } },
  { intros [ident c, ident f],
    ext [] [ident i] [],
    unfold [ident or.by_cases] [],
    cases [expr i] ["with", ident i, ident hi],
    rcases [expr finset.mem_insert.1 hi, "with", ident rfl, "|", ident h],
    { change [expr «expr = »(_, «expr • »(c, _))] [] [],
      simp [] [] ["only"] ["[", expr dif_pos, "]"] [] [],
      refl },
    { change [expr «expr = »(_, «expr • »(c, _))] [] [],
      have [] [":", expr «expr¬ »(«expr = »(i, a))] [],
      { rintro [ident rfl],
        exact [expr has h] },
      simp [] [] ["only"] ["[", expr dif_neg this, ",", expr dif_pos h, "]"] [] [],
      refl } },
  { exact [expr λ f, (f ⟨a, finset.mem_insert_self _ _⟩, λ i, f ⟨i.1, finset.mem_insert_of_mem i.2⟩)] },
  { intro [ident f],
    apply [expr prod.ext],
    { simp [] [] ["only"] ["[", expr or.by_cases, ",", expr dif_pos, "]"] [] [] },
    { ext [] ["⟨", ident i, ",", ident his, "⟩"] [],
      have [] [":", expr «expr¬ »(«expr = »(i, a))] [],
      { rintro [ident rfl],
        exact [expr has his] },
      dsimp ["only"] ["[", expr or.by_cases, "]"] [] [],
      change [expr «expr ∈ »(i, s)] [] ["at", ident his],
      rw ["[", expr dif_neg this, ",", expr dif_pos his, "]"] [] } },
  { intro [ident f],
    ext [] ["⟨", ident i, ",", ident hi, "⟩"] [],
    rcases [expr finset.mem_insert.1 hi, "with", ident rfl, "|", ident h],
    { simp [] [] ["only"] ["[", expr or.by_cases, ",", expr dif_pos, "]"] [] [] },
    { have [] [":", expr «expr¬ »(«expr = »(i, a))] [],
      { rintro [ident rfl],
        exact [expr has h] },
      simp [] [] ["only"] ["[", expr or.by_cases, ",", expr dif_neg this, ",", expr dif_pos h, "]"] [] [] } }
end

/-- A version of `is_noetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance is_noetherian_pi' {R ι M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [Fintype ι] [IsNoetherian R M] :
  IsNoetherian R (ι → M) :=
  is_noetherian_pi

end 

open IsNoetherian Submodule Function

section 

universe w

variable{R M P :
    Type
      _}{N :
    Type w}[Semiringₓ R][AddCommMonoidₓ M][Module R M][AddCommMonoidₓ N][Module R N][AddCommMonoidₓ P][Module R P]

theorem is_noetherian_iff_well_founded :
  IsNoetherian R M ↔ WellFounded (· > · : Submodule R M → Submodule R M → Prop) :=
  by 
    rw [(CompleteLattice.well_founded_characterisations$ Submodule R M).out 0 3]
    exact ⟨fun ⟨h⟩ => fun k => (fg_iff_compact k).mp (h k), fun h => ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩

variable(R M)

theorem well_founded_submodule_gt R M [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] :
  ∀ [IsNoetherian R M], WellFounded (· > · : Submodule R M → Submodule R M → Prop) :=
  is_noetherian_iff_well_founded.mp

variable{R M}

/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
theorem set_has_maximal_iff_noetherian :
  (∀ (a : Set$ Submodule R M), a.nonempty → ∃ (M' : _)(_ : M' ∈ a), ∀ I (_ : I ∈ a), M' ≤ I → I = M') ↔
    IsNoetherian R M :=
  by 
    rw [is_noetherian_iff_well_founded, WellFounded.well_founded_iff_has_max']

/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
  (∀ (f : ℕ →ₘ Submodule R M), ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M :=
  by 
    rw [is_noetherian_iff_well_founded, WellFounded.monotone_chain_condition]

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
theorem IsNoetherian.induction [IsNoetherian R M] {P : Submodule R M → Prop} (hgt : ∀ I, (∀ J (_ : J > I), P J) → P I)
  (I : Submodule R M) : P I :=
  WellFounded.recursionₓ (well_founded_submodule_gt R M) I hgt

end 

section 

universe w

variable{R M P :
    Type _}{N : Type w}[Ringₓ R][AddCommGroupₓ M][Module R M][AddCommGroupₓ N][Module R N][AddCommGroupₓ P][Module R P]

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finite_of_linear_independent
[nontrivial R]
[is_noetherian R M]
{s : set M}
(hs : linear_independent R (coe : s → M)) : s.finite :=
begin
  refine [expr classical.by_contradiction (λ
    hf, (rel_embedding.well_founded_iff_no_descending_seq.1 (well_founded_submodule_gt R M)).elim' _)],
  have [ident f] [":", expr «expr ↪ »(exprℕ(), s)] [],
  from [expr @infinite.nat_embedding s ⟨λ f, hf ⟨f⟩⟩],
  have [] [":", expr ∀ n, «expr ⊆ »(«expr '' »(«expr ∘ »(coe, f), {m | «expr ≤ »(m, n)}), s)] [],
  { rintros [ident n, ident x, "⟨", ident y, ",", ident hy₁, ",", ident hy₂, "⟩"],
    subst [expr hy₂],
    exact [expr (f y).2] },
  have [] [":", expr ∀
   a
   b : exprℕ(), «expr ↔ »(«expr ≤ »(a, b), «expr ≤ »(span R «expr '' »(«expr ∘ »(coe, f), {m | «expr ≤ »(m, a)}), span R «expr '' »(«expr ∘ »(coe, f), {m | «expr ≤ »(m, b)})))] [],
  { assume [binders (a b)],
    rw ["[", expr span_le_span_iff hs (this a) (this b), ",", expr set.image_subset_image_iff (subtype.coe_injective.comp f.injective), ",", expr set.subset_def, "]"] [],
    exact [expr ⟨λ (hab x) (hxa : «expr ≤ »(x, a)), le_trans hxa hab, λ hx, hx a (le_refl a)⟩] },
  exact [expr ⟨⟨λ
     n, span R «expr '' »(«expr ∘ »(coe, f), {m | «expr ≤ »(m, n)}), λ
     x
     y, by simp [] [] [] ["[", expr le_antisymm_iff, ",", expr (this _ _).symm, "]"] [] [] { contextual := tt }⟩, by dsimp [] ["[", expr gt, "]"] [] []; simp [] [] ["only"] ["[", expr lt_iff_le_not_le, ",", expr (this _ _).symm, "]"] [] []; tauto []⟩]
end

/-- If the first and final modules in a short exact sequence are noetherian,
  then the middle module is also noetherian. -/
theorem is_noetherian_of_range_eq_ker [IsNoetherian R M] [IsNoetherian R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
  (hf : Function.Injective f) (hg : Function.Surjective g) (h : f.range = g.ker) : IsNoetherian R N :=
  is_noetherian_iff_well_founded.2$
    well_founded_gt_exact_sequence (well_founded_submodule_gt R M) (well_founded_submodule_gt R P) f.range
      (Submodule.map f) (Submodule.comap f) (Submodule.comap g) (Submodule.map g) (Submodule.gciMapComap hf)
      (Submodule.giMapComap hg)
      (by 
        simp [Submodule.map_comap_eq, inf_comm])
      (by 
        simp [Submodule.comap_map_eq, h])

/--
For any endomorphism of a Noetherian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot [I : IsNoetherian R M] (f : M →ₗ[R] M) :
  ∃ n : ℕ, n ≠ 0 ∧ (f^n).ker⊓(f^n).range = ⊥ :=
  by 
    obtain ⟨n, w⟩ :=
      monotone_stabilizes_iff_noetherian.mpr I
        (f.iterate_ker.comp
          ⟨fun n => n+1,
            fun n m w =>
              by 
                linarith⟩)
    specialize
      w ((2*n)+1)
        (by 
          linarith)
    dsimp  at w 
    refine' ⟨n+1, Nat.succ_ne_zero _, _⟩
    rw [eq_bot_iff]
    rintro - ⟨h, ⟨y, rfl⟩⟩
    rw [mem_bot, ←LinearMap.mem_ker, w]
    erw [LinearMap.mem_ker] at h⊢
    change ((f^n+1)*f^n+1) y = 0 at h 
    rw [←pow_addₓ] at h 
    convert h using 3
    linarith

/-- Any surjective endomorphism of a Noetherian module is injective. -/
theorem IsNoetherian.injective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M) (s : surjective f) :
  injective f :=
  by 
    obtain ⟨n, ne, w⟩ := IsNoetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot f 
    rw [linear_map.range_eq_top.mpr (LinearMap.iterate_surjective s n), inf_top_eq, LinearMap.ker_eq_bot] at w 
    exact LinearMap.injective_of_iterate_injective Ne w

/-- Any surjective endomorphism of a Noetherian module is bijective. -/
theorem IsNoetherian.bijective_of_surjective_endomorphism [IsNoetherian R M] (f : M →ₗ[R] M) (s : surjective f) :
  bijective f :=
  ⟨IsNoetherian.injective_of_surjective_endomorphism f s, s⟩

/--
A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
theorem IsNoetherian.disjoint_partial_sups_eventually_bot [I : IsNoetherian R M] (f : ℕ → Submodule R M)
  (h : ∀ n, Disjoint (partialSups f n) (f (n+1))) : ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ :=
  by 
    suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m+1) = ⊥
    ·
      obtain ⟨n, w⟩ := t 
      use n+1
      rintro (_ | m) p
      ·
        cases p
      ·
        apply w 
        exact nat.succ_le_succ_iff.mp p 
    obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partialSups f)
    exact ⟨n, fun m p => eq_bot_of_disjoint_absorbs (h m) ((Eq.symm (w (m+1) (le_add_right p))).trans (w m p))⟩

/--
If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
noncomputable def IsNoetherian.equivPunitOfProdInjective [IsNoetherian R M] (f : M × N →ₗ[R] M) (i : injective f) :
  N ≃ₗ[R] PUnit.{w + 1} :=
  by 
    apply Nonempty.some 
    obtain ⟨n, w⟩ := IsNoetherian.disjoint_partial_sups_eventually_bot (f.tailing i) (f.tailings_disjoint_tailing i)
    specialize w n (le_reflₓ n)
    apply Nonempty.intro 
    refine' (f.tailing_linear_equiv i n).symm ≪≫ₗ _ 
    rw [w]
    exact Submodule.botEquivPunit

end 

/--
A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
class IsNoetherianRing(R)[Semiringₓ R] extends IsNoetherian R R : Prop

theorem is_noetherian_ring_iff {R} [Semiringₓ R] : IsNoetherianRing R ↔ IsNoetherian R R :=
  ⟨fun h => h.1, @IsNoetherianRing.mk _ _⟩

/-- A commutative ring is Noetherian if and only if all its ideals are finitely-generated. -/
theorem is_noetherian_ring_iff_ideal_fg (R : Type _) [CommSemiringₓ R] : IsNoetherianRing R ↔ ∀ (I : Ideal R), I.fg :=
  is_noetherian_ring_iff.trans is_noetherian_def

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 80]
instance ring.is_noetherian_of_fintype
(R M)
[fintype M]
[semiring R]
[add_comm_monoid M]
[module R M] : is_noetherian R M :=
by letI [] [] [":=", expr classical.dec]; exact [expr ⟨assume
  s, ⟨to_finset s, by rw ["[", expr set.coe_to_finset, ",", expr submodule.span_eq, "]"] []⟩⟩]

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ring.is_noetherian_of_zero_eq_one {R} [semiring R] (h01 : «expr = »((0 : R), 1)) : is_noetherian_ring R :=
by haveI [] [] [":=", expr subsingleton_of_zero_eq_one h01]; haveI [] [] [":=", expr fintype.of_subsingleton (0 : R)]; exact [expr is_noetherian_ring_iff.2 (ring.is_noetherian_of_fintype R R)]

theorem is_noetherian_of_submodule_of_noetherian R M [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (N : Submodule R M)
  (h : IsNoetherian R M) : IsNoetherian R N :=
  by 
    rw [is_noetherian_iff_well_founded] at h⊢
    exact OrderEmbedding.well_founded (Submodule.MapSubtype.orderEmbedding N).dual h

instance Submodule.Quotient.is_noetherian {R} [Ringₓ R] {M} [AddCommGroupₓ M] [Module R M] (N : Submodule R M)
  [h : IsNoetherian R M] : IsNoetherian R N.quotient :=
  by 
    rw [is_noetherian_iff_well_founded] at h⊢
    exact OrderEmbedding.well_founded (Submodule.ComapMkq.orderEmbedding N).dual h

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem is_noetherian_of_tower R {S M} [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ M] [HasScalar R S] [Module S M]
  [Module R M] [IsScalarTower R S M] (h : IsNoetherian R M) : IsNoetherian S M :=
  by 
    rw [is_noetherian_iff_well_founded] at h⊢
    refine' (Submodule.restrictScalarsEmbedding R S M).dual.WellFounded h

instance Ideal.Quotient.is_noetherian_ring {R : Type _} [CommRingₓ R] [h : IsNoetherianRing R] (I : Ideal R) :
  IsNoetherianRing I.quotient :=
  is_noetherian_ring_iff.mpr$ is_noetherian_of_tower R$ Submodule.Quotient.is_noetherian _

-- error in RingTheory.Noetherian: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_noetherian_of_fg_of_noetherian
{R M}
[ring R]
[add_comm_group M]
[module R M]
(N : submodule R M)
[is_noetherian_ring R]
(hN : N.fg) : is_noetherian R N :=
let ⟨s, hs⟩ := hN in
begin
  haveI [] [] [":=", expr classical.dec_eq M],
  haveI [] [] [":=", expr classical.dec_eq R],
  letI [] [":", expr is_noetherian R R] [":=", expr by apply_instance],
  have [] [":", expr ∀ x «expr ∈ » s, «expr ∈ »(x, N)] [],
  from [expr λ x hx, «expr ▸ »(hs, submodule.subset_span hx)],
  refine [expr @@is_noetherian_of_surjective ((«expr↑ »(s) : set M) → R) _ _ _ (pi.module _ _ _) _ _ _ is_noetherian_pi],
  { fapply [expr linear_map.mk],
    { exact [expr λ
       f, ⟨«expr∑ in , »((i), s.attach, «expr • »(f i, i.1)), N.sum_mem (λ
         c _, «expr $ »(N.smul_mem _, this _ c.2))⟩] },
    { intros [ident f, ident g],
      apply [expr subtype.eq],
      change [expr «expr = »(«expr∑ in , »((i), s.attach, «expr • »(«expr + »(f i, g i), _)), _)] [] [],
      simp [] [] ["only"] ["[", expr add_smul, ",", expr finset.sum_add_distrib, "]"] [] [],
      refl },
    { intros [ident c, ident f],
      apply [expr subtype.eq],
      change [expr «expr = »(«expr∑ in , »((i), s.attach, «expr • »(«expr • »(c, f i), _)), _)] [] [],
      simp [] [] ["only"] ["[", expr smul_eq_mul, ",", expr mul_smul, "]"] [] [],
      exact [expr finset.smul_sum.symm] } },
  rw [expr linear_map.range_eq_top] [],
  rintro ["⟨", ident n, ",", ident hn, "⟩"],
  change [expr «expr ∈ »(n, N)] [] ["at", ident hn],
  rw ["[", "<-", expr hs, ",", "<-", expr set.image_id «expr↑ »(s), ",", expr finsupp.mem_span_image_iff_total, "]"] ["at", ident hn],
  rcases [expr hn, "with", "⟨", ident l, ",", ident hl1, ",", ident hl2, "⟩"],
  refine [expr ⟨λ x, l x, subtype.ext _⟩],
  change [expr «expr = »(«expr∑ in , »((i), s.attach, «expr • »(l i, (i : M))), n)] [] [],
  rw ["[", expr @finset.sum_attach M M s _ (λ
    i, «expr • »(l i, i)), ",", "<-", expr hl2, ",", expr finsupp.total_apply, ",", expr finsupp.sum, ",", expr eq_comm, "]"] [],
  refine [expr finset.sum_subset hl1 (λ x _ hx, _)],
  rw ["[", expr finsupp.not_mem_support_iff.1 hx, ",", expr zero_smul, "]"] []
end

theorem is_noetherian_of_fg_of_noetherian' {R M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [IsNoetherianRing R]
  (h : (⊤ : Submodule R M).Fg) : IsNoetherian R M :=
  have  : IsNoetherian R (⊤ : Submodule R M) := is_noetherian_of_fg_of_noetherian _ h 
  by 
    exact is_noetherian_of_linear_equiv (LinearEquiv.ofTop (⊤ : Submodule R M) rfl)

/-- In a module over a noetherian ring, the submodule generated by finitely many vectors is
noetherian. -/
theorem is_noetherian_span_of_finite R {M} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [IsNoetherianRing R] {A : Set M}
  (hA : finite A) : IsNoetherian R (Submodule.span R A) :=
  is_noetherian_of_fg_of_noetherian _ (Submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem is_noetherian_ring_of_surjective R [CommRingₓ R] S [CommRingₓ S] (f : R →+* S) (hf : Function.Surjective f)
  [H : IsNoetherianRing R] : IsNoetherianRing S :=
  by 
    rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at H⊢
    exact OrderEmbedding.well_founded (Ideal.orderEmbeddingOfSurjective f hf).dual H

instance is_noetherian_ring_range {R} [CommRingₓ R] {S} [CommRingₓ S] (f : R →+* S) [IsNoetherianRing R] :
  IsNoetherianRing f.range :=
  is_noetherian_ring_of_surjective R f.range f.range_restrict f.range_restrict_surjective

theorem is_noetherian_ring_of_ring_equiv R [CommRingₓ R] {S} [CommRingₓ S] (f : R ≃+* S) [IsNoetherianRing R] :
  IsNoetherianRing S :=
  is_noetherian_ring_of_surjective R S f.to_ring_hom f.to_equiv.surjective

namespace Submodule

variable{R : Type _}{A : Type _}[CommSemiringₓ R][Semiringₓ A][Algebra R A]

variable(M N : Submodule R A)

theorem fg_mul (hm : M.fg) (hn : N.fg) : (M*N).Fg :=
  let ⟨m, hfm, hm⟩ := fg_def.1 hm 
  let ⟨n, hfn, hn⟩ := fg_def.1 hn 
  fg_def.2 ⟨m*n, hfm.mul hfn, span_mul_span R m n ▸ hm ▸ hn ▸ rfl⟩

theorem fg_pow (h : M.fg) (n : ℕ) : (M^n).Fg :=
  Nat.recOn n
    ⟨{1},
      by 
        simp [one_eq_span]⟩
    fun n ih =>
      by 
        simpa [pow_succₓ] using fg_mul _ _ h ih

end Submodule

