import Mathbin.Algebra.Algebra.Tower 
import Mathbin.LinearAlgebra.Prod

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of subalgebras of an R-algebra generated
by a set of elements. A basic interface for `adjoin` is set up, and various
results about finitely-generated subalgebras and submodules are proved.

## Definitions

* `fg (S : subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/


universe u v w

open_locale Pointwise

open Submodule Subsemiring

variable{R : Type u}{A : Type v}{B : Type w}

namespace Algebra

section Semiringₓ

variable[CommSemiringₓ R][Semiringₓ A][Semiringₓ B]

variable[Algebra R A][Algebra R B]{s t : Set A}

theorem subset_adjoin : s ⊆ adjoin R s :=
  Algebra.gc.le_u_l s

theorem adjoin_le {S : Subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
  Algebra.gc.l_le H

theorem adjoin_le_iff {S : Subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S :=
  Algebra.gc _ _

theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  Algebra.gc.monotone_l H

theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ adjoin R s) : adjoin R s = S :=
  le_antisymmₓ (adjoin_le h₁) h₂

theorem adjoin_eq (S : Subalgebra R A) : adjoin R («expr↑ » S) = S :=
  adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin

@[elab_as_eliminator]
theorem adjoin_induction {p : A → Prop} {x : A} (h : x ∈ adjoin R s) (Hs : ∀ x (_ : x ∈ s), p x)
  (Halg : ∀ r, p (algebraMap R A r)) (Hadd : ∀ x y, p x → p y → p (x+y)) (Hmul : ∀ x y, p x → p y → p (x*y)) : p x :=
  let S : Subalgebra R A := { Carrier := p, mul_mem' := Hmul, add_mem' := Hadd, algebra_map_mem' := Halg }
  adjoin_le (show s ≤ S from Hs) h

-- error in RingTheory.Adjoin.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The difference with `algebra.adjoin_induction` is that this acts on the subtype. -/
theorem adjoin_induction'
{p : adjoin R s → exprProp()}
(Hs : ∀ (x) (h : «expr ∈ »(x, s)), p ⟨x, subset_adjoin h⟩)
(Halg : ∀ r, p (algebra_map R _ r))
(Hadd : ∀ x y, p x → p y → p «expr + »(x, y))
(Hmul : ∀ x y, p x → p y → p «expr * »(x, y))
(x : adjoin R s) : p x :=
«expr $ »(subtype.rec_on x, λ x hx, begin
   refine [expr exists.elim _ (λ (hx : «expr ∈ »(x, adjoin R s)) (hc : p ⟨x, hx⟩), hc)],
   exact [expr adjoin_induction hx (λ
     x
     hx, ⟨subset_adjoin hx, Hs x hx⟩) (λ
     r, ⟨subalgebra.algebra_map_mem _ r, Halg r⟩) (λ
     x
     y
     hx
     hy, «expr $ »(exists.elim hx, λ
      hx'
      hx, «expr $ »(exists.elim hy, λ
       hy'
       hy, ⟨subalgebra.add_mem _ hx' hy', Hadd _ _ hx hy⟩))) (λ
     x
     y
     hx
     hy, «expr $ »(exists.elim hx, λ
      hx' hx, «expr $ »(exists.elim hy, λ hy' hy, ⟨subalgebra.mul_mem _ hx' hy', Hmul _ _ hx hy⟩)))]
 end)

@[simp]
theorem adjoin_adjoin_coe_preimage {s : Set A} : adjoin R ((coeₓ : adjoin R s → A) ⁻¹' s) = ⊤ :=
  by 
    refine' eq_top_iff.2 fun x => adjoin_induction' (fun a ha => _) (fun r => _) (fun _ _ => _) (fun _ _ => _) x
    ·
      exact subset_adjoin ha
    ·
      exact Subalgebra.algebra_map_mem _ r
    ·
      exact Subalgebra.add_mem _
    ·
      exact Subalgebra.mul_mem _

theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s⊔adjoin R t :=
  (Algebra.gc : GaloisConnection _ (coeₓ : Subalgebra R A → Set A)).l_sup

variable(R A)

@[simp]
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ :=
  show adjoin R ⊥ = ⊥by 
    apply GaloisConnection.l_bot 
    exact Algebra.gc

@[simp]
theorem adjoin_univ : adjoin R (Set.Univ : Set A) = ⊤ :=
  eq_top_iff.2$ fun x => subset_adjoin$ Set.mem_univ _

variable(R){A}(s)

theorem adjoin_eq_span : (adjoin R s).toSubmodule = span R (Submonoid.closure s) :=
  by 
    apply le_antisymmₓ
    ·
      intro r hr 
      rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
      clear hr 
      induction' L with hd tl ih
      ·
        exact zero_mem _ 
      rw [List.forall_mem_consₓ] at HL 
      rw [List.map_consₓ, List.sum_cons]
      refine' Submodule.add_mem _ _ (ih HL.2)
      replace HL := HL.1
      clear ih tl 
      suffices  : ∃ (z r : _)(hr : r ∈ Submonoid.closure s), HasScalar.smul z r = List.prod hd
      ·
        rcases this with ⟨z, r, hr, hzr⟩
        rw [←hzr]
        exact smul_mem _ _ (subset_span hr)
      induction' hd with hd tl ih
      ·
        exact ⟨1, 1, (Submonoid.closure s).one_mem', one_smul _ _⟩
      rw [List.forall_mem_consₓ] at HL 
      rcases ih HL.2 with ⟨z, r, hr, hzr⟩
      rw [List.prod_cons, ←hzr]
      rcases HL.1 with (⟨hd, rfl⟩ | hs)
      ·
        refine' ⟨hd*z, r, hr, _⟩
        rw [Algebra.smul_def, Algebra.smul_def, (algebraMap _ _).map_mul, _root_.mul_assoc]
      ·
        exact ⟨z, hd*r, Submonoid.mul_mem _ (Submonoid.subset_closure hs) hr, (mul_smul_comm _ _ _).symm⟩
    refine' span_le.2 _ 
    change Submonoid.closure s ≤ (adjoin R s).toSubsemiring.toSubmonoid 
    exact Submonoid.closure_le.2 subset_adjoin

theorem span_le_adjoin (s : Set A) : span R s ≤ (adjoin R s).toSubmodule :=
  span_le.mpr subset_adjoin

theorem adjoin_to_submodule_le {s : Set A} {t : Submodule R A} :
  (adjoin R s).toSubmodule ≤ t ↔ «expr↑ » (Submonoid.closure s) ⊆ (t : Set A) :=
  by 
    rw [adjoin_eq_span, span_le]

theorem adjoin_eq_span_of_subset {s : Set A} (hs : «expr↑ » (Submonoid.closure s) ⊆ (span R s : Set A)) :
  (adjoin R s).toSubmodule = span R s :=
  le_antisymmₓ ((adjoin_to_submodule_le R).mpr hs) (span_le_adjoin R s)

theorem adjoin_image (f : A →ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R s).map f :=
  le_antisymmₓ (adjoin_le$ Set.image_subset _ subset_adjoin)$
    Subalgebra.map_le.2$ adjoin_le$ Set.image_subset_iff.1 subset_adjoin

@[simp]
theorem adjoin_insert_adjoin (x : A) : adjoin R (insert x («expr↑ » (adjoin R s))) = adjoin R (insert x s) :=
  le_antisymmₓ
    (adjoin_le (Set.insert_subset.mpr ⟨subset_adjoin (Set.mem_insert _ _), adjoin_mono (Set.subset_insert _ _)⟩))
    (Algebra.adjoin_mono (Set.insert_subset_insert Algebra.subset_adjoin))

theorem adjoin_prod_le (s : Set A) (t : Set B) : adjoin R (Set.Prod s t) ≤ (adjoin R s).Prod (adjoin R t) :=
  adjoin_le$ Set.prod_mono subset_adjoin subset_adjoin

-- error in RingTheory.Adjoin.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_adjoin_of_map_mul
{s}
{x : A}
{f : «expr →ₗ[ ] »(A, R, B)}
(hf : ∀ a₁ a₂, «expr = »(f «expr * »(a₁, a₂), «expr * »(f a₁, f a₂)))
(h : «expr ∈ »(x, adjoin R s)) : «expr ∈ »(f x, adjoin R «expr '' »(f, «expr ∪ »(s, {1}))) :=
begin
  refine [expr @adjoin_induction R A _ _ _ _ (λ
    a, «expr ∈ »(f a, adjoin R «expr '' »(f, «expr ∪ »(s, {1})))) x h (λ
    a
    ha, subset_adjoin ⟨a, ⟨set.subset_union_left _ _ ha, rfl⟩⟩) (λ
    r, _) (λ
    y
    z
    hy
    hz, by simpa [] [] [] ["[", expr hy, ",", expr hz, "]"] [] ["using", expr subalgebra.add_mem _ hy hz]) (λ
    y
    z
    hy
    hz, by simpa [] [] [] ["[", expr hy, ",", expr hz, ",", expr hf y z, "]"] [] ["using", expr subalgebra.mul_mem _ hy hz])],
  have [] [":", expr «expr ∈ »(f 1, adjoin R «expr '' »(f, «expr ∪ »(s, {1})))] [":=", expr subset_adjoin ⟨1, ⟨«expr $ »(set.subset_union_right _ _, set.mem_singleton 1), rfl⟩⟩],
  replace [ident this] [] [":=", expr subalgebra.smul_mem (adjoin R «expr '' »(f, «expr ∪ »(s, {1}))) this r],
  convert [] [expr this] [],
  rw [expr algebra_map_eq_smul_one] [],
  exact [expr f.map_smul _ _]
end

-- error in RingTheory.Adjoin.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem adjoin_inl_union_inr_eq_prod
(s)
(t) : «expr = »(adjoin R «expr ∪ »(«expr '' »(linear_map.inl R A B, «expr ∪ »(s, {1})), «expr '' »(linear_map.inr R A B, «expr ∪ »(t, {1}))), (adjoin R s).prod (adjoin R t)) :=
begin
  apply [expr le_antisymm],
  { simp [] [] ["only"] ["[", expr adjoin_le_iff, ",", expr set.insert_subset, ",", expr subalgebra.zero_mem, ",", expr subalgebra.one_mem, ",", expr subset_adjoin, ",", expr set.union_subset_iff, ",", expr linear_map.coe_inl, ",", expr set.mk_preimage_prod_right, ",", expr set.image_subset_iff, ",", expr set_like.mem_coe, ",", expr set.mk_preimage_prod_left, ",", expr linear_map.coe_inr, ",", expr and_self, ",", expr set.union_singleton, ",", expr subalgebra.coe_prod, "]"] [] [] },
  { rintro ["⟨", ident a, ",", ident b, "⟩", "⟨", ident ha, ",", ident hb, "⟩"],
    let [ident P] [] [":=", expr adjoin R «expr ∪ »(«expr '' »(linear_map.inl R A B, «expr ∪ »(s, {1})), «expr '' »(linear_map.inr R A B, «expr ∪ »(t, {1})))],
    have [ident Ha] [":", expr «expr ∈ »((a, (0 : B)), adjoin R «expr '' »(linear_map.inl R A B, «expr ∪ »(s, {1})))] [":=", expr mem_adjoin_of_map_mul R linear_map.inl_map_mul ha],
    have [ident Hb] [":", expr «expr ∈ »(((0 : A), b), adjoin R «expr '' »(linear_map.inr R A B, «expr ∪ »(t, {1})))] [":=", expr mem_adjoin_of_map_mul R linear_map.inr_map_mul hb],
    replace [ident Ha] [":", expr «expr ∈ »((a, (0 : B)), P)] [":=", expr adjoin_mono (set.subset_union_left _ _) Ha],
    replace [ident Hb] [":", expr «expr ∈ »(((0 : A), b), P)] [":=", expr adjoin_mono (set.subset_union_right _ _) Hb],
    simpa [] [] [] [] [] ["using", expr subalgebra.add_mem _ Ha Hb] }
end

end Semiringₓ

section CommSemiringₓ

variable[CommSemiringₓ R][CommSemiringₓ A]

variable[Algebra R A]{s t : Set A}

variable(R s t)

theorem adjoin_union_eq_adjoin_adjoin : adjoin R (s ∪ t) = (adjoin (adjoin R s) t).restrictScalars R :=
  le_antisymmₓ
    (closure_mono$
      Set.union_subset (Set.range_subset_iff.2$ fun r => Or.inl ⟨algebraMap R (adjoin R s) r, rfl⟩)
        (Set.union_subset_union_left _$ fun x hxs => ⟨⟨_, subset_adjoin hxs⟩, rfl⟩))
    (closure_le.2$
      Set.union_subset (Set.range_subset_iff.2$ fun x => adjoin_mono (Set.subset_union_left _ _) x.2)
        (Set.Subset.trans (Set.subset_union_right _ _) subset_adjoin))

theorem adjoin_singleton_one : adjoin R ({1} : Set A) = ⊥ :=
  eq_bot_iff.2$ adjoin_le$ Set.singleton_subset_iff.2$ SetLike.mem_coe.2$ one_mem _

theorem adjoin_union_coe_submodule :
  (adjoin R (s ∪ t)).toSubmodule = (adjoin R s).toSubmodule*(adjoin R t).toSubmodule :=
  by 
    rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span]
    congr 1 with z 
    simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]

end CommSemiringₓ

section Ringₓ

variable[CommRingₓ R][Ringₓ A]

variable[Algebra R A]{s t : Set A}

variable{R s t}

theorem adjoin_int (s : Set R) : adjoin ℤ s = subalgebraOfSubring (Subring.closure s) :=
  le_antisymmₓ (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s ≤ (adjoin ℤ s).toSubring)

theorem mem_adjoin_iff {s : Set A} {x : A} : x ∈ adjoin R s ↔ x ∈ Subring.closure (Set.Range (algebraMap R A) ∪ s) :=
  ⟨fun hx =>
      Subsemiring.closure_induction hx Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
        (fun _ _ => Subring.add_mem _) fun _ _ => Subring.mul_mem _,
    suffices Subring.closure (Set.Range («expr⇑ » (algebraMap R A)) ∪ s) ≤ (adjoin R s).toSubring from @this x 
    Subring.closure_le.2 Subsemiring.subset_closure⟩

theorem adjoin_eq_ring_closure (s : Set A) :
  (adjoin R s).toSubring = Subring.closure (Set.Range (algebraMap R A) ∪ s) :=
  Subring.ext$ fun x => mem_adjoin_iff

end Ringₓ

end Algebra

open Algebra Subalgebra

namespace AlgHom

variable[CommSemiringₓ R][Semiringₓ A][Semiringₓ B][Algebra R A][Algebra R B]

theorem map_adjoin (φ : A →ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ '' s) :=
  (adjoin_image _ _ _).symm

end AlgHom

