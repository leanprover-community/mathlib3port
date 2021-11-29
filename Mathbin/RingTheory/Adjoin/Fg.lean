import Mathbin.RingTheory.Polynomial.Basic 
import Mathbin.RingTheory.PrincipalIdealDomain 
import Mathbin.RingTheory.Adjoin.Polynomial

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of finitely-generated subalgebras.

## Definitions

* `fg (S : subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/


universe u v w

open Subsemiring Ringₓ Submodule

open_locale Pointwise

namespace Algebra

variable{R : Type u}{A : Type v}{B : Type w}[CommSemiringₓ R][CommSemiringₓ A][Algebra R A]{s t : Set A}

-- error in RingTheory.Adjoin.Fg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fg_trans
(h1 : (adjoin R s).to_submodule.fg)
(h2 : (adjoin (adjoin R s) t).to_submodule.fg) : (adjoin R «expr ∪ »(s, t)).to_submodule.fg :=
begin
  rcases [expr fg_def.1 h1, "with", "⟨", ident p, ",", ident hp, ",", ident hp', "⟩"],
  rcases [expr fg_def.1 h2, "with", "⟨", ident q, ",", ident hq, ",", ident hq', "⟩"],
  refine [expr fg_def.2 ⟨«expr * »(p, q), hp.mul hq, le_antisymm _ _⟩],
  { rw ["[", expr span_le, "]"] [],
    rintros ["_", "⟨", ident x, ",", ident y, ",", ident hx, ",", ident hy, ",", ident rfl, "⟩"],
    change [expr «expr ∈ »(«expr * »(x, y), _)] [] [],
    refine [expr subalgebra.mul_mem _ _ _],
    { have [] [":", expr «expr ∈ »(x, (adjoin R s).to_submodule)] [],
      { rw ["<-", expr hp'] [],
        exact [expr subset_span hx] },
      exact [expr adjoin_mono (set.subset_union_left _ _) this] },
    have [] [":", expr «expr ∈ »(y, (adjoin (adjoin R s) t).to_submodule)] [],
    { rw ["<-", expr hq'] [],
      exact [expr subset_span hy] },
    change [expr «expr ∈ »(y, adjoin R «expr ∪ »(s, t))] [] [],
    rwa [expr adjoin_union_eq_adjoin_adjoin] [] },
  { intros [ident r, ident hr],
    change [expr «expr ∈ »(r, adjoin R «expr ∪ »(s, t))] [] ["at", ident hr],
    rw [expr adjoin_union_eq_adjoin_adjoin] ["at", ident hr],
    change [expr «expr ∈ »(r, (adjoin (adjoin R s) t).to_submodule)] [] ["at", ident hr],
    rw ["[", "<-", expr hq', ",", "<-", expr set.image_id q, ",", expr finsupp.mem_span_image_iff_total (adjoin R s), "]"] ["at", ident hr],
    rcases [expr hr, "with", "⟨", ident l, ",", ident hlq, ",", ident rfl, "⟩"],
    have [] [] [":=", expr @finsupp.total_apply A A (adjoin R s)],
    rw ["[", expr this, ",", expr finsupp.sum, "]"] [],
    refine [expr sum_mem _ _],
    intros [ident z, ident hz],
    change [expr «expr ∈ »(«expr * »((l z).1, _), _)] [] [],
    have [] [":", expr «expr ∈ »((l z).1, (adjoin R s).to_submodule)] [":=", expr (l z).2],
    rw ["[", "<-", expr hp', ",", "<-", expr set.image_id p, ",", expr finsupp.mem_span_image_iff_total R, "]"] ["at", ident this],
    rcases [expr this, "with", "⟨", ident l2, ",", ident hlp, ",", ident hl, "⟩"],
    have [] [] [":=", expr @finsupp.total_apply A A R],
    rw [expr this] ["at", ident hl],
    rw ["[", "<-", expr hl, ",", expr finsupp.sum_mul, "]"] [],
    refine [expr sum_mem _ _],
    intros [ident t, ident ht],
    change [expr «expr ∈ »(«expr * »(_, _), _)] [] [],
    rw [expr smul_mul_assoc] [],
    refine [expr smul_mem _ _ _],
    exact [expr subset_span ⟨t, z, hlp ht, hlq hz, rfl⟩] }
end

end Algebra

namespace Subalgebra

variable{R : Type u}{A : Type v}{B : Type w}

variable[CommSemiringₓ R][Semiringₓ A][Algebra R A][Semiringₓ B][Algebra R B]

/-- A subalgebra `S` is finitely generated if there exists `t : finset A` such that
`algebra.adjoin R t = S`. -/
def fg (S : Subalgebra R A) : Prop :=
  ∃ t : Finset A, Algebra.adjoin R («expr↑ » t) = S

theorem fg_adjoin_finset (s : Finset A) : (Algebra.adjoin R («expr↑ » s : Set A)).Fg :=
  ⟨s, rfl⟩

theorem fg_def {S : Subalgebra R A} : S.fg ↔ ∃ t : Set A, Set.Finite t ∧ Algebra.adjoin R t = S :=
  ⟨fun ⟨t, ht⟩ => ⟨«expr↑ » t, Set.finite_mem_finset t, ht⟩,
    fun ⟨t, ht1, ht2⟩ =>
      ⟨ht1.to_finset,
        by 
          rwa [Set.Finite.coe_to_finset]⟩⟩

theorem fg_bot : (⊥ : Subalgebra R A).Fg :=
  ⟨∅, Algebra.adjoin_empty R A⟩

theorem fg_of_fg_to_submodule {S : Subalgebra R A} : S.to_submodule.fg → S.fg :=
  fun ⟨t, ht⟩ =>
    ⟨t,
      le_antisymmₓ (Algebra.adjoin_le fun x hx => show x ∈ S.to_submodule from ht ▸ subset_span hx)$
        show S.to_submodule ≤ (Algebra.adjoin R («expr↑ » t)).toSubmodule from
          fun x hx =>
            span_le.mpr (fun x hx => Algebra.subset_adjoin hx)
              (show x ∈ span R («expr↑ » t)by 
                rw [ht]
                exact hx)⟩

theorem fg_of_noetherian [IsNoetherian R A] (S : Subalgebra R A) : S.fg :=
  fg_of_fg_to_submodule (IsNoetherian.noetherian S.to_submodule)

theorem fg_of_submodule_fg (h : (⊤ : Submodule R A).Fg) : (⊤ : Subalgebra R A).Fg :=
  let ⟨s, hs⟩ := h
  ⟨s,
    to_submodule_injective$
      by 
        rw [Algebra.top_to_submodule, eq_top_iff, ←hs, span_le]
        exact Algebra.subset_adjoin⟩

theorem fg_prod {S : Subalgebra R A} {T : Subalgebra R B} (hS : S.fg) (hT : T.fg) : (S.prod T).Fg :=
  by 
    obtain ⟨s, hs⟩ := fg_def.1 hS 
    obtain ⟨t, ht⟩ := fg_def.1 hT 
    rw [←hs.2, ←ht.2]
    exact
      fg_def.2
        ⟨LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}),
          Set.Finite.union (Set.Finite.image _ (Set.Finite.union hs.1 (Set.finite_singleton _)))
            (Set.Finite.image _ (Set.Finite.union ht.1 (Set.finite_singleton _))),
          Algebra.adjoin_inl_union_inr_eq_prod R s t⟩

section 

open_locale Classical

theorem fg_map (S : Subalgebra R A) (f : A →ₐ[R] B) (hs : S.fg) : (S.map f).Fg :=
  let ⟨s, hs⟩ := hs
  ⟨s.image f,
    by 
      rw [Finset.coe_image, Algebra.adjoin_image, hs]⟩

end 

theorem fg_of_fg_map (S : Subalgebra R A) (f : A →ₐ[R] B) (hf : Function.Injective f) (hs : (S.map f).Fg) : S.fg :=
  let ⟨s, hs⟩ := hs
  ⟨s.preimage f$ fun _ _ _ _ h => hf h,
    map_injective f hf$
      by 
        rw [←Algebra.adjoin_image, Finset.coe_preimage, Set.image_preimage_eq_of_subset, hs]
        rw [←AlgHom.coe_range, ←Algebra.adjoin_le_iff, hs, ←Algebra.map_top]
        exact map_mono le_top⟩

theorem fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).Fg ↔ S.fg :=
  ⟨fun h =>
      by 
        rw [←S.range_val, ←Algebra.map_top]
        exact fg_map _ _ h,
    fun h =>
      fg_of_fg_map _ S.val Subtype.val_injective$
        by 
          rw [Algebra.map_top, range_val]
          exact h⟩

theorem induction_on_adjoin [IsNoetherian R A] (P : Subalgebra R A → Prop) (base : P ⊥)
  (ih : ∀ (S : Subalgebra R A) (x : A), P S → P (Algebra.adjoin R (insert x S))) (S : Subalgebra R A) : P S :=
  by 
    classical 
    obtain ⟨t, rfl⟩ := S.fg_of_noetherian 
    refine' Finset.induction_on t _ _
    ·
      simpa using base 
    intro x t hxt h 
    rw [Finset.coe_insert]
    simpa only [Algebra.adjoin_insert_adjoin] using ih _ x h

end Subalgebra

section Semiringₓ

variable{R : Type u}{A : Type v}{B : Type w}

variable[CommSemiringₓ R][CommRingₓ A][CommRingₓ B][Algebra R A][Algebra R B]

/-- The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring. -/
instance AlgHom.is_noetherian_ring_range (f : A →ₐ[R] B) [IsNoetherianRing A] : IsNoetherianRing f.range :=
  is_noetherian_ring_range f.to_ring_hom

end Semiringₓ

section Ringₓ

variable{R : Type u}{A : Type v}{B : Type w}

variable[CommRingₓ R][CommRingₓ A][CommRingₓ B][Algebra R A][Algebra R B]

-- error in RingTheory.Adjoin.Fg: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_noetherian_ring_of_fg {S : subalgebra R A} (HS : S.fg) [is_noetherian_ring R] : is_noetherian_ring S :=
let ⟨t, ht⟩ := HS in
«expr ▸ »(ht, «expr ▸ »((algebra.adjoin_eq_range R («expr↑ »(t) : set A)).symm, by haveI [] [":", expr is_noetherian_ring (mv_polynomial («expr↑ »(t) : set A) R)] [":=", expr mv_polynomial.is_noetherian_ring]; convert [] [expr alg_hom.is_noetherian_ring_range _] []; apply_instance))

theorem is_noetherian_subring_closure (s : Set R) (hs : s.finite) : IsNoetherianRing (Subring.closure s) :=
  show IsNoetherianRing (subalgebraOfSubring (Subring.closure s)) from
    Algebra.adjoin_int s ▸ is_noetherian_ring_of_fg (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)

end Ringₓ

