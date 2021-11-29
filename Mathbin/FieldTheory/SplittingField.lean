import Mathbin.FieldTheory.Minpoly 
import Mathbin.RingTheory.AdjoinRoot 
import Mathbin.LinearAlgebra.FiniteDimensional 
import Mathbin.Algebra.Polynomial.BigOperators 
import Mathbin.RingTheory.Algebraic 
import Mathbin.RingTheory.AlgebraTower 
import Mathbin.Tactic.FieldSimp

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : polynomial K` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : polynomial K` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `polynomial.splits i f`: A predicate on a field homomorphism `i : K → L` and a polynomial `f`
  saying that `f` is zero or all of its irreducible factors over `L` have degree `1`.
* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.
* `polynomial.is_splitting_field`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `polynomial.C_leading_coeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.
* `lift_of_splits`: If `K` and `L` are field extensions of a field `F` and for some finite subset
  `S` of `K`, the minimal polynomial of every `x ∈ K` splits as a polynomial with coefficients in
  `L`, then `algebra.adjoin F S` embeds into `L`.
* `polynomial.is_splitting_field.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.
* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorpic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

-/


noncomputable theory

open_locale Classical BigOperators

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section Splits

variable (i : K →+* L)

/-- A polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1. -/
def splits (f : Polynomial K) : Prop :=
  f = 0 ∨ ∀ {g : Polynomial L}, Irreducible g → g ∣ f.map i → degree g = 1

@[simp]
theorem splits_zero : splits i (0 : Polynomial K) :=
  Or.inl rfl

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem splits_C (a : K) : splits i (C a) :=
if ha : «expr = »(a, 0) then «expr ▸ »(ha.symm, «expr ▸ »((@C_0 K _).symm, splits_zero i)) else have hia : «expr ≠ »(i a, 0), from mt (i.injective_iff.1 i.injective _) ha,
«expr $ »(or.inr, λ
 (g hg)
 ⟨p, hp⟩, absurd hg.1 (not_not.2 «expr $ »(is_unit_iff_degree_eq_zero.2, by have [] [] [":=", expr congr_arg degree hp]; simp [] [] [] ["[", expr degree_C hia, ",", expr @eq_comm (with_bot exprℕ()) 0, ",", expr nat.with_bot.add_eq_zero_iff, "]"] [] ["at", ident this]; clear [ident _fun_match]; tauto [])))

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem splits_of_degree_eq_one {f : polynomial K} (hf : «expr = »(degree f, 1)) : splits i f :=
«expr $ »(or.inr, λ
 (g hg)
 ⟨p, hp⟩, by have [] [] [":=", expr congr_arg degree hp]; simp [] [] [] ["[", expr nat.with_bot.add_eq_one_iff, ",", expr hf, ",", expr @eq_comm (with_bot exprℕ()) 1, ",", expr mt is_unit_iff_degree_eq_zero.2 hg.1, "]"] [] ["at", ident this]; clear [ident _fun_match]; tauto [])

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem splits_of_degree_le_one {f : polynomial K} (hf : «expr ≤ »(degree f, 1)) : splits i f :=
begin
  cases [expr h, ":", expr degree f] ["with", ident n],
  { rw ["[", expr degree_eq_bot.1 h, "]"] []; exact [expr splits_zero i] },
  { cases [expr n] ["with", ident n],
    { rw ["[", expr eq_C_of_degree_le_zero (trans_rel_right ((«expr ≤ »)) h (le_refl _)), "]"] []; exact [expr splits_C _ _] },
    { have [ident hn] [":", expr «expr = »(n, 0)] [],
      { rw [expr h] ["at", ident hf],
        cases [expr n] [],
        { refl },
        { exact [expr absurd hf exprdec_trivial()] } },
      exact [expr splits_of_degree_eq_one _ (by rw ["[", expr h, ",", expr hn, "]"] []; refl)] } }
end

theorem splits_of_nat_degree_le_one {f : Polynomial K} (hf : nat_degree f ≤ 1) : splits i f :=
  splits_of_degree_le_one i (degree_le_of_nat_degree_le hf)

theorem splits_of_nat_degree_eq_one {f : Polynomial K} (hf : nat_degree f = 1) : splits i f :=
  splits_of_nat_degree_le_one i (le_of_eqₓ hf)

theorem splits_mul {f g : Polynomial K} (hf : splits i f) (hg : splits i g) : splits i (f*g) :=
  if h : (f*g) = 0 then
    by 
      simp [h]
  else
    Or.inr$
      fun p hp hpf =>
        ((PrincipalIdealRing.irreducible_iff_prime.1 hp).2.2 _ _
              (show p ∣ map i f*map i g by 
                convert hpf <;> rw [Polynomial.map_mul])).elim
          (hf.resolve_left
            (fun hf =>
              by 
                simpa [hf] using h)
            hp)
          (hg.resolve_left
            (fun hg =>
              by 
                simpa [hg] using h)
            hp)

theorem splits_of_splits_mul {f g : Polynomial K} (hfg : (f*g) ≠ 0) (h : splits i (f*g)) : splits i f ∧ splits i g :=
  ⟨Or.inr$
      fun g hgi hg =>
        Or.resolve_left h hfg hgi
          (by 
            rw [map_mul] <;> exact hg.trans (dvd_mul_right _ _)),
    Or.inr$
      fun g hgi hg =>
        Or.resolve_left h hfg hgi
          (by 
            rw [map_mul] <;> exact hg.trans (dvd_mul_left _ _))⟩

theorem splits_of_splits_of_dvd {f g : Polynomial K} (hf0 : f ≠ 0) (hf : splits i f) (hgf : g ∣ f) : splits i g :=
  by 
    obtain ⟨f, rfl⟩ := hgf 
    exact (splits_of_splits_mul i hf0 hf).1

theorem splits_of_splits_gcd_left {f g : Polynomial K} (hf0 : f ≠ 0) (hf : splits i f) :
  splits i (EuclideanDomain.gcd f g) :=
  Polynomial.splits_of_splits_of_dvd i hf0 hf (EuclideanDomain.gcd_dvd_left f g)

theorem splits_of_splits_gcd_right {f g : Polynomial K} (hg0 : g ≠ 0) (hg : splits i g) :
  splits i (EuclideanDomain.gcd f g) :=
  Polynomial.splits_of_splits_of_dvd i hg0 hg (EuclideanDomain.gcd_dvd_right f g)

theorem splits_map_iff (j : L →+* F) {f : Polynomial K} : splits j (f.map i) ↔ splits (j.comp i) f :=
  by 
    simp [splits, Polynomial.map_map]

theorem splits_one : splits i 1 :=
  splits_C i 1

theorem splits_of_is_unit {u : Polynomial K} (hu : IsUnit u) : u.splits i :=
  splits_of_splits_of_dvd i one_ne_zero (splits_one _)$ is_unit_iff_dvd_one.1 hu

theorem splits_X_sub_C {x : K} : (X - C x).Splits i :=
  splits_of_degree_eq_one _$ degree_X_sub_C x

theorem splits_X : X.Splits i :=
  splits_of_degree_eq_one _$ degree_X

theorem splits_id_iff_splits {f : Polynomial K} : (f.map i).Splits (RingHom.id L) ↔ f.splits i :=
  by 
    rw [splits_map_iff, RingHom.id_comp]

theorem splits_mul_iff {f g : Polynomial K} (hf : f ≠ 0) (hg : g ≠ 0) : (f*g).Splits i ↔ f.splits i ∧ g.splits i :=
  ⟨splits_of_splits_mul i (mul_ne_zero hf hg), fun ⟨hfs, hgs⟩ => splits_mul i hfs hgs⟩

theorem splits_prod {ι : Type u} {s : ι → Polynomial K} {t : Finset ι} :
  (∀ j _ : j ∈ t, (s j).Splits i) → (∏x in t, s x).Splits i :=
  by 
    refine' Finset.induction_on t (fun _ => splits_one i) fun a t hat ih ht => _ 
    rw [Finset.forall_mem_insert] at ht 
    rw [Finset.prod_insert hat]
    exact splits_mul i ht.1 (ih ht.2)

theorem splits_pow {f : Polynomial K} (hf : f.splits i) (n : ℕ) : (f^n).Splits i :=
  by 
    rw [←Finset.card_range n, ←Finset.prod_const]
    exact splits_prod i fun j hj => hf

theorem splits_X_pow (n : ℕ) : (X^n).Splits i :=
  splits_pow i (splits_X i) n

theorem splits_prod_iff {ι : Type u} {s : ι → Polynomial K} {t : Finset ι} :
  (∀ j _ : j ∈ t, s j ≠ 0) → ((∏x in t, s x).Splits i ↔ ∀ j _ : j ∈ t, (s j).Splits i) :=
  by 
    refine' Finset.induction_on t (fun _ => ⟨fun _ _ h => h.elim, fun _ => splits_one i⟩) fun a t hat ih ht => _ 
    rw [Finset.forall_mem_insert] at ht⊢
    rw [Finset.prod_insert hat, splits_mul_iff i ht.1 (Finset.prod_ne_zero_iff.2 ht.2), ih ht.2]

theorem degree_eq_one_of_irreducible_of_splits {p : Polynomial L} (h_nz : p ≠ 0) (hp : Irreducible p)
  (hp_splits : splits (RingHom.id L) p) : p.degree = 1 :=
  by 
    rcases hp_splits with ⟨⟩
    ·
      contradiction
    ·
      apply hp_splits hp 
      simp 

theorem exists_root_of_splits {f : Polynomial K} (hs : splits i f) (hf0 : degree f ≠ 0) : ∃ x, eval₂ i x f = 0 :=
  if hf0 : f = 0 then
    ⟨37,
      by 
        simp [hf0]⟩
  else
    let ⟨g, hg⟩ :=
      WfDvdMonoid.exists_irreducible_factor
        (show ¬IsUnit (f.map i) from
          mt is_unit_iff_degree_eq_zero.1
            (by 
              rwa [degree_map]))
        (map_ne_zero hf0)
    let ⟨x, hx⟩ := exists_root_of_degree_eq_one (hs.resolve_left hf0 hg.1 hg.2)
    let ⟨i, hi⟩ := hg.2
    ⟨x,
      by 
        rw [←eval_map, hi, eval_mul, show _ = _ from hx, zero_mul]⟩

theorem exists_multiset_of_splits {f : Polynomial K} :
  splits i f → ∃ s : Multiset L, f.map i = C (i f.leading_coeff)*(s.map fun a : L => (X : Polynomial L) - C a).Prod :=
  suffices
    splits (RingHom.id _) (f.map i) →
      ∃ s : Multiset L, f.map i = C (f.map i).leadingCoeff*(s.map fun a : L => (X : Polynomial L) - C a).Prod by
    
    rwa [splits_map_iff, leading_coeff_map i] at this 
  WfDvdMonoid.induction_on_irreducible (f.map i)
    (fun _ =>
      ⟨{37},
        by 
          simp [i.map_zero]⟩)
    (fun u hu _ =>
      ⟨0,
        by 
          convLHS => rw [eq_C_of_degree_eq_zero (is_unit_iff_degree_eq_zero.1 hu)] <;>
            simp [leading_coeff, nat_degree_eq_of_degree_eq_some (is_unit_iff_degree_eq_zero.1 hu)]⟩)
    fun f p hf0 hp ih hfs =>
      have hpf0 : (p*f) ≠ 0 := mul_ne_zero hp.ne_zero hf0 
      let ⟨s, hs⟩ := ih (splits_of_splits_mul _ hpf0 hfs).2
      ⟨-(p*norm_unit p).coeff 0 ::ₘ s,
        have hp1 : degree p = 1 :=
          hfs.resolve_left hpf0 hp
            (by 
              simp )
        by 
          rw [Multiset.map_cons, Multiset.prod_cons, leading_coeff_mul, C_mul, mul_assocₓ,
            mul_left_commₓ (C f.leading_coeff), ←hs, ←mul_assocₓ, mul_left_inj' hf0]
          convLHS => rw [eq_X_add_C_of_degree_eq_one hp1]
          simp only [mul_addₓ, coe_norm_unit_of_ne_zero hp.ne_zero, mul_commₓ p, coeff_neg, C_neg, sub_eq_add_neg,
            neg_negₓ, coeff_C_mul, (mul_assocₓ _ _ _).symm, C_mul.symm,
            mul_inv_cancel (show p.leading_coeff ≠ 0 from mt leading_coeff_eq_zero.1 hp.ne_zero), one_mulₓ]⟩

/-- Pick a root of a polynomial that splits. -/
def root_of_splits {f : Polynomial K} (hf : f.splits i) (hfd : f.degree ≠ 0) : L :=
  Classical.some$ exists_root_of_splits i hf hfd

theorem map_root_of_splits {f : Polynomial K} (hf : f.splits i) hfd : f.eval₂ i (root_of_splits i hf hfd) = 0 :=
  Classical.some_spec$ exists_root_of_splits i hf hfd

theorem roots_map {f : Polynomial K} (hf : f.splits$ RingHom.id K) : (f.map i).roots = f.roots.map i :=
  if hf0 : f = 0 then
    by 
      rw [hf0, map_zero, roots_zero, roots_zero, Multiset.map_zero]
  else
    have hmf0 : f.map i ≠ 0 := map_ne_zero hf0 
    let ⟨m, hm⟩ := exists_multiset_of_splits _ hf 
    have h1 : (0 : Polynomial K) ∉ m.map fun r => X - C r := zero_nmem_multiset_map_X_sub_C _ _ 
    have h2 : (0 : Polynomial L) ∉ m.map fun r => X - C (i r) := zero_nmem_multiset_map_X_sub_C _ _ 
    by 
      rw [map_id] at hm 
      rw [hm] at hf0 hmf0⊢
      rw [map_mul] at hmf0⊢
      rw [roots_mul hf0, roots_mul hmf0, map_C, roots_C, zero_addₓ, roots_C, zero_addₓ, map_multiset_prod,
        Multiset.map_map]
      simpRw [· ∘ ·, map_sub, map_X, map_C]
      rw [roots_multiset_prod _ h2, Multiset.bind_map, roots_multiset_prod _ h1, Multiset.bind_map]
      simpRw [roots_X_sub_C]
      rw [Multiset.bind_singleton, Multiset.bind_singleton, Multiset.map_id']

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eq_prod_roots_of_splits
{p : polynomial K}
{i : «expr →+* »(K, L)}
(hsplit : splits i p) : «expr = »(p.map i, «expr * »(C (i p.leading_coeff), ((p.map i).roots.map (λ
    a, «expr - »(X, C a))).prod)) :=
begin
  by_cases [expr p_eq_zero, ":", expr «expr = »(p, 0)],
  { rw ["[", expr p_eq_zero, ",", expr map_zero, ",", expr leading_coeff_zero, ",", expr i.map_zero, ",", expr C.map_zero, ",", expr zero_mul, "]"] [] },
  obtain ["⟨", ident s, ",", ident hs, "⟩", ":=", expr exists_multiset_of_splits i hsplit],
  have [ident map_ne_zero] [":", expr «expr ≠ »(p.map i, 0)] [":=", expr map_ne_zero p_eq_zero],
  have [ident prod_ne_zero] [":", expr «expr ≠ »(«expr * »(C (i p.leading_coeff), (multiset.map (λ
       a, «expr - »(X, C a)) s).prod), 0)] [":=", expr by rwa [expr hs] ["at", ident map_ne_zero]],
  have [ident zero_nmem] [":", expr «expr ∉ »((0 : polynomial L), s.map (λ a, «expr - »(X, C a)))] [],
  from [expr zero_nmem_multiset_map_X_sub_C _ _],
  have [ident map_bind_roots_eq] [":", expr «expr = »((s.map (λ a, «expr - »(X, C a))).bind (λ a, a.roots), s)] [],
  { refine [expr multiset.induction_on s (by rw ["[", expr multiset.map_zero, ",", expr multiset.zero_bind, "]"] []) _],
    intros [ident a, ident s, ident ih],
    rw ["[", expr multiset.map_cons, ",", expr multiset.cons_bind, ",", expr ih, ",", expr roots_X_sub_C, ",", expr multiset.singleton_add, "]"] [] },
  rw ["[", expr hs, ",", expr roots_mul prod_ne_zero, ",", expr roots_C, ",", expr zero_add, ",", expr roots_multiset_prod _ zero_nmem, ",", expr map_bind_roots_eq, "]"] []
end

theorem eq_prod_roots_of_splits_id {p : Polynomial K} (hsplit : splits (RingHom.id K) p) :
  p = C p.leading_coeff*(p.roots.map fun a => X - C a).Prod :=
  by 
    simpa using eq_prod_roots_of_splits hsplit

theorem eq_prod_roots_of_monic_of_splits_id {p : Polynomial K} (m : monic p) (hsplit : splits (RingHom.id K) p) :
  p = (p.roots.map fun a => X - C a).Prod :=
  by 
    convert eq_prod_roots_of_splits_id hsplit 
    simp [m]

theorem eq_X_sub_C_of_splits_of_single_root {x : K} {h : Polynomial K} (h_splits : splits i h)
  (h_roots : (h.map i).roots = {i x}) : h = C (leading_coeff h)*X - C x :=
  by 
    apply Polynomial.map_injective _ i.injective 
    rw [eq_prod_roots_of_splits h_splits, h_roots]
    simp 

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem nat_degree_eq_card_roots
{p : polynomial K}
{i : «expr →+* »(K, L)}
(hsplit : splits i p) : «expr = »(p.nat_degree, (p.map i).roots.card) :=
begin
  by_cases [expr p_eq_zero, ":", expr «expr = »(p, 0)],
  { rw ["[", expr p_eq_zero, ",", expr nat_degree_zero, ",", expr map_zero, ",", expr roots_zero, ",", expr multiset.card_zero, "]"] [] },
  have [ident map_ne_zero] [":", expr «expr ≠ »(p.map i, 0)] [":=", expr map_ne_zero p_eq_zero],
  rw [expr eq_prod_roots_of_splits hsplit] ["at", ident map_ne_zero],
  conv_lhs [] [] { rw ["[", "<-", expr nat_degree_map i, ",", expr eq_prod_roots_of_splits hsplit, "]"] },
  have [] [":", expr «expr ∉ »((0 : polynomial L), (map i p).roots.map (λ a, «expr - »(X, C a)))] [],
  from [expr zero_nmem_multiset_map_X_sub_C _ _],
  simp [] [] [] ["[", expr nat_degree_mul (left_ne_zero_of_mul map_ne_zero) (right_ne_zero_of_mul map_ne_zero), ",", expr nat_degree_multiset_prod _ this, "]"] [] []
end

theorem degree_eq_card_roots {p : Polynomial K} {i : K →+* L} (p_ne_zero : p ≠ 0) (hsplit : splits i p) :
  p.degree = (p.map i).roots.card :=
  by 
    rw [degree_eq_nat_degree p_ne_zero, nat_degree_eq_card_roots hsplit]

section UFD

attribute [local instance] PrincipalIdealRing.to_unique_factorization_monoid

local infixl:50 " ~ᵤ " => Associated

open UniqueFactorizationMonoid Associates

theorem splits_of_exists_multiset {f : Polynomial K} {s : Multiset L}
  (hs : f.map i = C (i f.leading_coeff)*(s.map fun a : L => (X : Polynomial L) - C a).Prod) : splits i f :=
  if hf0 : f = 0 then Or.inl hf0 else
    Or.inr$
      fun p hp hdp =>
        have ht :
          Multiset.Rel Associated (normalized_factors (f.map i)) (s.map fun a : L => (X : Polynomial L) - C a) :=
          factors_unique (fun p hp => irreducible_of_normalized_factor _ hp)
            (fun p' m =>
              by 
                obtain ⟨a, m, rfl⟩ := Multiset.mem_map.1 m 
                exact irreducible_of_degree_eq_one (degree_X_sub_C _))
            (Associated.symm$
              calc _ ~ᵤ f.map i :=
                ⟨(Units.map C.toMonoidHom : Units L →* Units (Polynomial L))
                    (Units.mk0 (f.map i).leadingCoeff (mt leading_coeff_eq_zero.1 (map_ne_zero hf0))),
                  by 
                    convRHS => rw [hs, ←leading_coeff_map i, mul_commₓ] <;> rfl⟩
                _ ~ᵤ _ :=
                (UniqueFactorizationMonoid.normalized_factors_prod
                    (by 
                      simpa using hf0)).symm
                )
        let ⟨q, hq, hpq⟩ :=
          exists_mem_normalized_factors_of_dvd
            (by 
              simpa)
            hp hdp 
        let ⟨q', hq', hqq'⟩ := Multiset.exists_mem_of_rel_of_mem ht hq 
        let ⟨a, ha⟩ := Multiset.mem_map.1 hq' 
        by 
          rw [←degree_X_sub_C a, ha.2] <;> exact degree_eq_degree_of_associated (hpq.trans hqq')

theorem splits_of_splits_id {f : Polynomial K} : splits (RingHom.id _) f → splits i f :=
  UniqueFactorizationMonoid.induction_on_prime f (fun _ => splits_zero _)
    (fun _ hu _ =>
      splits_of_degree_le_one _
        ((is_unit_iff_degree_eq_zero.1 hu).symm ▸
          by 
            decide))
    fun a p ha0 hp ih hfi =>
      splits_mul _
        (splits_of_degree_eq_one _
          ((splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).1.resolve_left hp.1 hp.irreducible
            (by 
              rw [map_id])))
        (ih (splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).2)

end UFD

theorem splits_iff_exists_multiset {f : Polynomial K} :
  splits i f ↔ ∃ s : Multiset L, f.map i = C (i f.leading_coeff)*(s.map fun a : L => (X : Polynomial L) - C a).Prod :=
  ⟨exists_multiset_of_splits i, fun ⟨s, hs⟩ => splits_of_exists_multiset i hs⟩

theorem splits_comp_of_splits (j : L →+* F) {f : Polynomial K} (h : splits i f) : splits (j.comp i) f :=
  by 
    change i with (RingHom.id _).comp i at h 
    rw [←splits_map_iff]
    rw [←splits_map_iff i] at h 
    exact splits_of_splits_id _ h

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq
{p : polynomial K}
(hmonic : p.monic)
(hroots : «expr = »(p.roots.card, p.nat_degree)) : «expr = »((multiset.map (λ
   a : K, «expr - »(X, C a)) p.roots).prod, p) :=
begin
  have [ident hprodmonic] [":", expr (multiset.map (λ a : K, «expr - »(X, C a)) p.roots).prod.monic] [],
  { simp [] [] ["only"] ["[", expr prod_multiset_root_eq_finset_root (ne_zero_of_monic hmonic), ",", expr monic_prod_of_monic, ",", expr monic_X_sub_C, ",", expr monic_pow, ",", expr forall_true_iff, "]"] [] [] },
  have [ident hdegree] [":", expr «expr = »((multiset.map (λ
      a : K, «expr - »(X, C a)) p.roots).prod.nat_degree, p.nat_degree)] [],
  { rw ["[", "<-", expr hroots, ",", expr nat_degree_multiset_prod _ (zero_nmem_multiset_map_X_sub_C _ (λ
       a : K, a)), "]"] [],
    simp [] [] ["only"] ["[", expr eq_self_iff_true, ",", expr mul_one, ",", expr nat.cast_id, ",", expr nsmul_eq_mul, ",", expr multiset.sum_repeat, ",", expr multiset.map_const, ",", expr nat_degree_X_sub_C, ",", expr function.comp, ",", expr multiset.map_map, "]"] [] [] },
  obtain ["⟨", ident q, ",", ident hq, "⟩", ":=", expr prod_multiset_X_sub_C_dvd p],
  have [ident qzero] [":", expr «expr ≠ »(q, 0)] [],
  { rintro [ident rfl],
    apply [expr hmonic.ne_zero],
    simpa [] [] ["only"] ["[", expr mul_zero, "]"] [] ["using", expr hq] },
  have [ident degp] [":", expr «expr = »(p.nat_degree, «expr + »((multiset.map (λ
       a : K, «expr - »(X, C a)) p.roots).prod.nat_degree, q.nat_degree))] [],
  { nth_rewrite [0] ["[", expr hq, "]"] [],
    simp [] [] ["only"] ["[", expr nat_degree_mul (ne_zero_of_monic hprodmonic) qzero, "]"] [] [] },
  have [ident degq] [":", expr «expr = »(q.nat_degree, 0)] [],
  { rw [expr hdegree] ["at", ident degp],
    exact [expr (add_right_inj p.nat_degree).mp (tactic.ring_exp.add_pf_sum_z degp rfl).symm] },
  obtain ["⟨", ident u, ",", ident hu, "⟩", ":=", expr is_unit_iff_degree_eq_zero.2 ((degree_eq_iff_nat_degree_eq qzero).2 degq)],
  have [ident hassoc] [":", expr associated (multiset.map (λ a : K, «expr - »(X, C a)) p.roots).prod p] [],
  { rw [expr associated] [],
    use [expr u],
    rw ["[", expr hu, ",", "<-", expr hq, "]"] [] },
  exact [expr eq_of_monic_of_associated hprodmonic hmonic hassoc]
end

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leading_coeff * ∏(X - a)`, for `a` in `p.roots`. -/
theorem C_leading_coeff_mul_prod_multiset_X_sub_C
{p : polynomial K}
(hroots : «expr = »(p.roots.card, p.nat_degree)) : «expr = »(«expr * »(C p.leading_coeff, (multiset.map (λ
    a : K, «expr - »(X, C a)) p.roots).prod), p) :=
begin
  by_cases [expr hzero, ":", expr «expr = »(p, 0)],
  { rw ["[", expr hzero, ",", expr leading_coeff_zero, ",", expr ring_hom.map_zero, ",", expr zero_mul, "]"] [] },
  { have [ident hcoeff] [":", expr «expr ≠ »(p.leading_coeff, 0)] [],
    { intro [ident h],
      exact [expr hzero (leading_coeff_eq_zero.1 h)] },
    have [ident hrootsnorm] [":", expr «expr = »((normalize p).roots.card, (normalize p).nat_degree)] [],
    { rw ["[", expr roots_normalize, ",", expr normalize_apply, ",", expr nat_degree_mul hzero (units.ne_zero _), ",", expr hroots, ",", expr coe_norm_unit, ",", expr nat_degree_C, ",", expr add_zero, "]"] [] },
    have [ident hprod] [] [":=", expr prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_normalize hzero) hrootsnorm],
    rw ["[", expr roots_normalize, ",", expr normalize_apply, ",", expr coe_norm_unit_of_ne_zero hzero, "]"] ["at", ident hprod],
    calc
      «expr = »(«expr * »(C p.leading_coeff, (multiset.map (λ
          a : K, «expr - »(X, C a)) p.roots).prod), «expr * »(p, C «expr * »(«expr ⁻¹»(p.leading_coeff), p.leading_coeff))) : by rw ["[", expr hprod, ",", expr mul_comm, ",", expr mul_assoc, ",", "<-", expr C_mul, "]"] []
      «expr = »(..., «expr * »(p, C 1)) : by field_simp [] [] [] []
      «expr = »(..., p) : by simp [] [] ["only"] ["[", expr mul_one, ",", expr ring_hom.map_one, "]"] [] [] }
end

/-- A polynomial splits if and only if it has as many roots as its degree. -/
theorem splits_iff_card_roots {p : Polynomial K} : splits (RingHom.id K) p ↔ p.roots.card = p.nat_degree :=
  by 
    split 
    ·
      intro H 
      rw [nat_degree_eq_card_roots H, map_id]
    ·
      intro hroots 
      apply (splits_iff_exists_multiset (RingHom.id K)).2
      use p.roots 
      simp only [RingHom.id_apply, map_id]
      exact (C_leading_coeff_mul_prod_multiset_X_sub_C hroots).symm

theorem aeval_root_derivative_of_splits [Algebra K L] {P : Polynomial K} (hmo : P.monic)
  (hP : P.splits (algebraMap K L)) {r : L} (hr : r ∈ (P.map (algebraMap K L)).roots) :
  aeval r P.derivative = (Multiset.map (fun a => r - a) ((P.map (algebraMap K L)).roots.erase r)).Prod :=
  by 
    replace hmo := monic_map (algebraMap K L) hmo 
    replace hP := (splits_id_iff_splits (algebraMap K L)).2 hP 
    rw [aeval_def, ←eval_map, ←derivative_map]
    nthRw 0[eq_prod_roots_of_monic_of_splits_id hmo hP]
    rw [eval_multiset_prod_X_sub_C_derivative hr]

end Splits

end Polynomial

section Embeddings

variable (F) [Field F]

/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
def AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly {R : Type _} [CommRingₓ R] [Algebra F R] (x : R) :
  Algebra.adjoin F ({x} : Set R) ≃ₐ[F] AdjoinRoot (minpoly F x) :=
  AlgEquiv.symm$
    AlgEquiv.ofBijective
      (AlgHom.codRestrict (AdjoinRoot.liftHom _ x$ minpoly.aeval F x) _
        fun p =>
          AdjoinRoot.induction_on _ p$
            fun p => (Algebra.adjoin_singleton_eq_range_aeval F x).symm ▸ (Polynomial.aeval _).mem_range.mpr ⟨p, rfl⟩)
      ⟨(AlgHom.injective_cod_restrict _ _ _).2$
          (AlgHom.injective_iff _).2$
            fun p =>
              AdjoinRoot.induction_on _ p$
                fun p hp => Ideal.Quotient.eq_zero_iff_mem.2$ Ideal.mem_span_singleton.2$ minpoly.dvd F x hp,
        fun y =>
          let ⟨p, hp⟩ := (SetLike.ext_iff.1 (Algebra.adjoin_singleton_eq_range_aeval F x) (y : R)).1 y.2
          ⟨AdjoinRoot.mk _ p, Subtype.eq hp⟩⟩

open Finset

/-- If a `subalgebra` is finite_dimensional as a submodule then it is `finite_dimensional`. -/
theorem FiniteDimensional.of_subalgebra_to_submodule {K V : Type _} [Field K] [Ringₓ V] [Algebra K V]
  {s : Subalgebra K V} (h : FiniteDimensional K s.to_submodule) : FiniteDimensional K s :=
  h

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`. -/
theorem lift_of_splits
{F K L : Type*}
[field F]
[field K]
[field L]
[algebra F K]
[algebra F L]
(s : finset K) : ∀
x «expr ∈ » s, «expr ∧ »(is_integral F x, polynomial.splits (algebra_map F L) (minpoly F x)) → nonempty «expr →ₐ[ ] »(algebra.adjoin F («expr↑ »(s) : set K), F, L) :=
begin
  refine [expr finset.induction_on s (λ H, _) (λ a s has ih H, _)],
  { rw ["[", expr coe_empty, ",", expr algebra.adjoin_empty, "]"] [],
    exact [expr ⟨(algebra.of_id F L).comp (algebra.bot_equiv F K)⟩] },
  rw [expr forall_mem_insert] ["at", ident H],
  rcases [expr H, "with", "⟨", "⟨", ident H1, ",", ident H2, "⟩", ",", ident H3, "⟩"],
  cases [expr ih H3] ["with", ident f],
  choose [] [ident H3] [ident H4] ["using", expr H3],
  rw ["[", expr coe_insert, ",", expr set.insert_eq, ",", expr set.union_comm, ",", expr algebra.adjoin_union_eq_adjoin_adjoin, "]"] [],
  letI [] [] [":=", expr (f : «expr →+* »(algebra.adjoin F («expr↑ »(s) : set K), L)).to_algebra],
  haveI [] [":", expr finite_dimensional F (algebra.adjoin F («expr↑ »(s) : set K))] [":=", expr ((submodule.fg_iff_finite_dimensional _).1 (fg_adjoin_of_finite (set.finite_mem_finset s) H3)).of_subalgebra_to_submodule],
  letI [] [] [":=", expr field_of_finite_dimensional F (algebra.adjoin F («expr↑ »(s) : set K))],
  have [ident H5] [":", expr is_integral (algebra.adjoin F («expr↑ »(s) : set K)) a] [":=", expr is_integral_of_is_scalar_tower a H1],
  have [ident H6] [":", expr (minpoly (algebra.adjoin F («expr↑ »(s) : set K)) a).splits (algebra_map (algebra.adjoin F («expr↑ »(s) : set K)) L)] [],
  { refine [expr polynomial.splits_of_splits_of_dvd _ («expr $ »(polynomial.map_ne_zero, minpoly.ne_zero H1) : «expr ≠ »(polynomial.map (algebra_map _ _) _, 0)) ((polynomial.splits_map_iff _ _).2 _) (minpoly.dvd _ _ _)],
    { rw ["<-", expr is_scalar_tower.algebra_map_eq] [],
      exact [expr H2] },
    { rw ["[", "<-", expr is_scalar_tower.aeval_apply, ",", expr minpoly.aeval, "]"] [] } },
  obtain ["⟨", ident y, ",", ident hy, "⟩", ":=", expr polynomial.exists_root_of_splits _ H6 (ne_of_lt (minpoly.degree_pos H5)).symm],
  refine [expr ⟨subalgebra.of_restrict_scalars _ _ _⟩],
  refine [expr (adjoin_root.lift_hom (minpoly (algebra.adjoin F («expr↑ »(s) : set K)) a) y hy).comp _],
  exact [expr alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly (algebra.adjoin F («expr↑ »(s) : set K)) a]
end

end Embeddings

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : Polynomial K) : Polynomial K :=
  if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.some H else X

instance irreducible_factor (f : Polynomial K) : Irreducible (factor f) :=
  by 
    rw [factor]
    splitIfs with H
    ·
      exact (Classical.some_spec H).1
    ·
      exact irreducible_X

theorem factor_dvd_of_not_is_unit {f : Polynomial K} (hf1 : ¬IsUnit f) : factor f ∣ f :=
  by 
    byCases' hf2 : f = 0
    ·
      rw [hf2]
      exact dvd_zero _ 
    rw [factor, dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
    exact (Classical.some_spec$ WfDvdMonoid.exists_irreducible_factor hf1 hf2).2

theorem factor_dvd_of_degree_ne_zero {f : Polynomial K} (hf : f.degree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {f : Polynomial K} (hf : f.nat_degree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def remove_factor (f : Polynomial K) : Polynomial (AdjoinRoot$ factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))

theorem X_sub_C_mul_remove_factor (f : Polynomial K) (hf : f.nat_degree ≠ 0) :
  ((X - C (AdjoinRoot.root f.factor))*f.remove_factor) = map (AdjoinRoot.of f.factor) f :=
  let ⟨g, hg⟩ := factor_dvd_of_nat_degree_ne_zero hf 
  mul_div_by_monic_eq_iff_is_root.2$
    by 
      rw [is_root.def, eval_map, hg, eval₂_mul, ←hg, AdjoinRoot.eval₂_root, zero_mul]

theorem nat_degree_remove_factor (f : Polynomial K) : f.remove_factor.nat_degree = f.nat_degree - 1 :=
  by 
    rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map, nat_degree_X_sub_C]

theorem nat_degree_remove_factor' {f : Polynomial K} {n : ℕ} (hfn : f.nat_degree = n+1) :
  f.remove_factor.nat_degree = n :=
  by 
    rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial. Uses induction on the degree. -/
def splitting_field_aux (n : ℕ) :
  ∀ {K : Type u} [Field K],
    by 
      exact ∀ f : Polynomial K, f.nat_degree = n → Type u :=
  (Nat.recOn n fun K _ _ _ => K)$
    fun n ih K _ f hf =>
      by 
        exact ih f.remove_factor (nat_degree_remove_factor' hf)

namespace SplittingFieldAux

theorem succ (n : ℕ) (f : Polynomial K) (hfn : f.nat_degree = n+1) :
  splitting_field_aux (n+1) f hfn = splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn) :=
  rfl

instance Field (n : ℕ) :
  ∀ {K : Type u} [Field K],
    by 
      exact ∀ {f : Polynomial K} hfn : f.nat_degree = n, Field (splitting_field_aux n f hfn) :=
  (Nat.recOn n fun K _ _ _ => ‹Field K›)$ fun n ih K _ f hf => ih _

instance Inhabited {n : ℕ} {f : Polynomial K} (hfn : f.nat_degree = n) : Inhabited (splitting_field_aux n f hfn) :=
  ⟨37⟩

instance Algebra (n : ℕ) :
  ∀ R : Type _ {K : Type u} [CommSemiringₓ R] [Field K],
    by 
      exact ∀ [Algebra R K] {f : Polynomial K} hfn : f.nat_degree = n, Algebra R (splitting_field_aux n f hfn) :=
  (Nat.recOn n
      fun R K _ _ _ _ _ =>
        by 
          exact ‹Algebra R K›)$
    fun n ih R K _ _ _ f hfn =>
      by 
        exact ih R (nat_degree_remove_factor' hfn)

instance IsScalarTower (n : ℕ) :
  ∀ R₁ R₂ : Type _ {K : Type u} [CommSemiringₓ R₁] [CommSemiringₓ R₂] [HasScalar R₁ R₂] [Field K],
    by 
      exact
        ∀ [Algebra R₁ K] [Algebra R₂ K],
          by 
            exact
              ∀ [IsScalarTower R₁ R₂ K] {f : Polynomial K} hfn : f.nat_degree = n,
                IsScalarTower R₁ R₂ (splitting_field_aux n f hfn) :=
  (Nat.recOn n
      fun R₁ R₂ K _ _ _ _ _ _ _ _ _ =>
        by 
          exact ‹IsScalarTower R₁ R₂ K›)$
    fun n ih R₁ R₂ K _ _ _ _ _ _ _ f hfn =>
      by 
        exact ih R₁ R₂ (nat_degree_remove_factor' hfn)

instance algebra''' {n : ℕ} {f : Polynomial K} (hfn : f.nat_degree = n+1) :
  Algebra (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
  splitting_field_aux.algebra n _ _

instance algebra' {n : ℕ} {f : Polynomial K} (hfn : f.nat_degree = n+1) :
  Algebra (AdjoinRoot f.factor) (splitting_field_aux n.succ f hfn) :=
  splitting_field_aux.algebra''' _

instance algebra'' {n : ℕ} {f : Polynomial K} (hfn : f.nat_degree = n+1) :
  Algebra K (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
  splitting_field_aux.algebra n K _

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance scalar_tower'
{n : exprℕ()}
{f : polynomial K}
(hfn : «expr = »(f.nat_degree, «expr + »(n, 1))) : is_scalar_tower K (adjoin_root f.factor) (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
begin
  haveI [] [":", expr is_scalar_tower K (adjoin_root f.factor) (adjoin_root f.factor)] [":=", expr is_scalar_tower.right],
  exact [expr splitting_field_aux.is_scalar_tower n K (adjoin_root f.factor) (nat_degree_remove_factor' hfn)]
end

instance scalar_tower {n : ℕ} {f : Polynomial K} (hfn : f.nat_degree = n+1) :
  IsScalarTower K (AdjoinRoot f.factor) (splitting_field_aux _ f hfn) :=
  splitting_field_aux.scalar_tower' _

theorem algebra_map_succ (n : ℕ) (f : Polynomial K) (hfn : f.nat_degree = n+1) :
  by 
    exact
      algebraMap K (splitting_field_aux _ _ hfn) =
        (algebraMap (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn))).comp
          (AdjoinRoot.of f.factor) :=
  IsScalarTower.algebra_map_eq _ _ _

protected theorem splits (n : ℕ) :
  ∀ {K : Type u} [Field K],
    by 
      exact ∀ f : Polynomial K hfn : f.nat_degree = n, splits (algebraMap K$ splitting_field_aux n f hfn) f :=
  (Nat.recOn n
      fun K _ _ hf =>
        by 
          exact splits_of_degree_le_one _ (le_transₓ degree_le_nat_degree$ hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))$
    fun n ih K _ f hf =>
      by 
        skip 
        rw [←splits_id_iff_splits, algebra_map_succ, ←map_map, splits_id_iff_splits,
          ←X_sub_C_mul_remove_factor f
            fun h =>
              by 
                rw [h] at hf 
                cases hf]
        exact splits_mul _ (splits_X_sub_C _) (ih _ _)

theorem exists_lift (n : ℕ) :
  ∀ {K : Type u} [Field K],
    by 
      exact
        ∀ f : Polynomial K hfn : f.nat_degree = n {L : Type _} [Field L],
          by 
            exact ∀ j : K →+* L hf : splits j f, ∃ k : splitting_field_aux n f hfn →+* L, k.comp (algebraMap _ _) = j :=
  (Nat.recOn n
      fun K _ _ _ L _ j _ =>
        by 
          exact ⟨j, j.comp_id⟩)$
    fun n ih K _ f hf L _ j hj =>
      by 
        exact
          have hndf : f.nat_degree ≠ 0 :=
            by 
              intro h 
              rw [h] at hf 
              cases hf 
          have hfn0 : f ≠ 0 :=
            by 
              intro h 
              rw [h] at hndf 
              exact hndf rfl 
          let ⟨r, hr⟩ :=
            exists_root_of_splits _ (splits_of_splits_of_dvd j hfn0 hj (factor_dvd_of_nat_degree_ne_zero hndf))
              (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1)
          have hmf0 : map (AdjoinRoot.of f.factor) f ≠ 0 := map_ne_zero hfn0 
          have hsf : splits (AdjoinRoot.lift j r hr) f.remove_factor :=
            by 
              rw [←X_sub_C_mul_remove_factor _ hndf] at hmf0 
              refine' (splits_of_splits_mul _ hmf0 _).2
              rwa [X_sub_C_mul_remove_factor _ hndf, ←splits_id_iff_splits, map_map, AdjoinRoot.lift_comp_of,
                splits_id_iff_splits]
          let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (AdjoinRoot.lift j r hr) hsf
          ⟨k,
            by 
              rw [algebra_map_succ, ←RingHom.comp_assoc, hk, AdjoinRoot.lift_comp_of]⟩

theorem adjoin_roots (n : ℕ) :
  ∀ {K : Type u} [Field K],
    by 
      exact
        ∀ f : Polynomial K hfn : f.nat_degree = n,
          Algebra.adjoin K
              («expr↑ » (f.map$ algebraMap K$ splitting_field_aux n f hfn).roots.toFinset :
              Set (splitting_field_aux n f hfn)) =
            ⊤ :=
  (Nat.recOn n
      fun K _ f hf =>
        by 
          exact Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)$
    fun n ih K _ f hfn =>
      by 
        exact
          have hndf : f.nat_degree ≠ 0 :=
            by 
              intro h 
              rw [h] at hfn 
              cases hfn 
          have hfn0 : f ≠ 0 :=
            by 
              intro h 
              rw [h] at hndf 
              exact hndf rfl 
          have hmf0 : map (algebraMap K (splitting_field_aux n.succ f hfn)) f ≠ 0 := map_ne_zero hfn0 
          by 
            rw [algebra_map_succ, ←map_map, ←X_sub_C_mul_remove_factor _ hndf, map_mul] at hmf0⊢
            rw [roots_mul hmf0, map_sub, map_X, map_C, roots_X_sub_C, Multiset.to_finset_add, Finset.coe_union,
              Multiset.to_finset_singleton, Finset.coe_singleton, Algebra.adjoin_union_eq_adjoin_adjoin,
              ←Set.image_singleton,
              Algebra.adjoin_algebra_map K (AdjoinRoot f.factor)
                (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)),
              AdjoinRoot.adjoin_root_eq_top, Algebra.map_top,
              IsScalarTower.adjoin_range_to_alg_hom K (AdjoinRoot f.factor)
                (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)),
              ih, Subalgebra.restrict_scalars_top]

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
def splitting_field (f : Polynomial K) :=
  splitting_field_aux _ f rfl

namespace SplittingField

variable (f : Polynomial K)

instance : Field (splitting_field f) :=
  splitting_field_aux.field _ _

instance Inhabited : Inhabited (splitting_field f) :=
  ⟨37⟩

/-- This should be an instance globally, but it creates diamonds with the `ℕ` and `ℤ` actions:

```lean
example :
  (add_comm_monoid.nat_module : module ℕ (splitting_field f)) =
    @algebra.to_module _ _ _ _ (splitting_field.algebra' f) :=
rfl  -- fails

example :
  (add_comm_group.int_module _ : module ℤ (splitting_field f)) =
    @algebra.to_module _ _ _ _ (splitting_field.algebra' f) :=
rfl  -- fails
```

Until we resolve these diamonds, it's more convenient to only turn this instance on with
`local attribute [instance]` in places where the benefit of having the instance outweighs the cost.

In the meantime, the `splitting_field.algebra` instance below is immune to these particular diamonds
since `K = ℕ` and `K = ℤ` are not possible due to the `field K` assumption. Diamonds in
`algebra ℚ (splitting_field f)` instances are still possible, but this is a problem throughout the
library and not unique to this `algebra` instance.
-/
instance algebra' {R} [CommSemiringₓ R] [Algebra R K] : Algebra R (splitting_field f) :=
  splitting_field_aux.algebra _ _ _

instance : Algebra K (splitting_field f) :=
  splitting_field_aux.algebra _ _ _

protected theorem splits : splits (algebraMap K (splitting_field f)) f :=
  splitting_field_aux.splits _ _ _

variable [Algebra K L] (hb : splits (algebraMap K L) f)

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : «expr →ₐ[ ] »(splitting_field f, K, L) :=
{ commutes' := λ r, by { have [] [] [":=", expr classical.some_spec (splitting_field_aux.exists_lift _ _ _ _ hb)],
    exact [expr ring_hom.ext_iff.1 this r] },
  ..classical.some (splitting_field_aux.exists_lift _ _ _ _ hb) }

theorem adjoin_roots :
  Algebra.adjoin K («expr↑ » (f.map (algebraMap K$ splitting_field f)).roots.toFinset : Set (splitting_field f)) = ⊤ :=
  splitting_field_aux.adjoin_roots _ _ _

theorem adjoin_root_set : Algebra.adjoin K (f.root_set f.splitting_field) = ⊤ :=
  adjoin_roots f

end SplittingField

variable (K L) [Algebra K L]

/-- Typeclass characterising splitting fields. -/
class is_splitting_field (f : Polynomial K) : Prop where 
  Splits{} : splits (algebraMap K L) f 
  adjoin_roots{} : Algebra.adjoin K («expr↑ » (f.map (algebraMap K L)).roots.toFinset : Set L) = ⊤

namespace IsSplittingField

variable {K}

instance splitting_field (f : Polynomial K) : is_splitting_field K (splitting_field f) f :=
  ⟨splitting_field.splits f, splitting_field.adjoin_roots f⟩

section ScalarTower

variable {K L F} [Algebra F K] [Algebra F L] [IsScalarTower F K L]

variable {K}

instance map (f : Polynomial F) [is_splitting_field F L f] : is_splitting_field K L (f.map$ algebraMap F K) :=
  ⟨by 
      rw [splits_map_iff, ←IsScalarTower.algebra_map_eq]
      exact splits L f,
    Subalgebra.restrict_scalars_injective F$
      by 
        rw [map_map, ←IsScalarTower.algebra_map_eq, Subalgebra.restrict_scalars_top, eq_top_iff, ←adjoin_roots L f,
          Algebra.adjoin_le_iff]
        exact fun x hx => @Algebra.subset_adjoin K _ _ _ _ _ _ hx⟩

variable {K} (L)

theorem splits_iff (f : Polynomial K) [is_splitting_field K L f] :
  Polynomial.Splits (RingHom.id K) f ↔ (⊤ : Subalgebra K L) = ⊥ :=
  ⟨fun h =>
      eq_bot_iff.2$
        adjoin_roots L f ▸
          (roots_map (algebraMap K L) h).symm ▸
            Algebra.adjoin_le_iff.2
              fun y hy =>
                let ⟨x, hxs, hxy⟩ :=
                  Finset.mem_image.1
                    (by 
                      rwa [Multiset.to_finset_map] at hy)
                hxy ▸ SetLike.mem_coe.2$ Subalgebra.algebra_map_mem _ _,
    fun h =>
      @RingEquiv.to_ring_hom_refl K _ ▸
        RingEquiv.self_trans_symm (RingEquiv.ofBijective _$ Algebra.bijective_algebra_map_iff.2 h) ▸
          by 
            rw [RingEquiv.to_ring_hom_trans]
            exact splits_comp_of_splits _ _ (splits L f)⟩

theorem mul (f g : Polynomial F) (hf : f ≠ 0) (hg : g ≠ 0) [is_splitting_field F K f]
  [is_splitting_field K L (g.map$ algebraMap F K)] : is_splitting_field F L (f*g) :=
  ⟨(IsScalarTower.algebra_map_eq F K L).symm ▸
      splits_mul _ (splits_comp_of_splits _ _ (splits K f)) ((splits_map_iff _ _).1 (splits L$ g.map$ algebraMap F K)),
    by 
      rw [map_mul, roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebraMap F L) ≠ 0) (map_ne_zero hg)),
        Multiset.to_finset_add, Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin,
        IsScalarTower.algebra_map_eq F K L, ←map_map,
        roots_map (algebraMap K L) ((splits_id_iff_splits$ algebraMap F K).2$ splits K f), Multiset.to_finset_map,
        Finset.coe_image, Algebra.adjoin_algebra_map, adjoin_roots, Algebra.map_top,
        IsScalarTower.adjoin_range_to_alg_hom, ←map_map, adjoin_roots, Subalgebra.restrict_scalars_top]⟩

end ScalarTower

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [Algebra K F] (f : Polynomial K) [is_splitting_field K L f] (hf : Polynomial.Splits (algebraMap K F) f) :
  L →ₐ[K] F :=
  if hf0 : f = 0 then
    (Algebra.ofId K F).comp$
      (Algebra.botEquiv K L : (⊥ : Subalgebra K L) →ₐ[K] K).comp$
        by 
          rw [←(splits_iff L f).1 (show f.splits (RingHom.id K) from hf0.symm ▸ splits_zero _)]
          exact Algebra.toTop
  else
    AlgHom.comp
      (by 
        rw [←adjoin_roots L f]
        exact
          Classical.choice
            (lift_of_splits _$
              fun y hy =>
                have  : aeval y f = 0 :=
                  (eval₂_eq_eval_map _).trans$
                    (mem_roots$
                          by 
                            exact map_ne_zero hf0).1
                      (multiset.mem_to_finset.mp hy)
                ⟨(is_algebraic_iff_is_integral _).1 ⟨f, hf0, this⟩,
                  splits_of_splits_of_dvd _ hf0 hf$ minpoly.dvd _ _ this⟩))
      Algebra.toTop

theorem FiniteDimensional (f : Polynomial K) [is_splitting_field K L f] : FiniteDimensional K L :=
  ⟨@Algebra.top_to_submodule K L _ _ _ ▸
      adjoin_roots L f ▸
        fg_adjoin_of_finite (Set.finite_mem_finset _)
          fun y hy =>
            if hf : f = 0 then
              by 
                rw [hf, map_zero, roots_zero] at hy 
                cases hy
            else
              (is_algebraic_iff_is_integral _).1
                ⟨f, hf,
                  (eval₂_eq_eval_map _).trans$
                    (mem_roots$
                          by 
                            exact map_ne_zero hf).1
                      (Multiset.mem_to_finset.mp hy)⟩⟩

instance (f : Polynomial K) : _root_.finite_dimensional K f.splitting_field :=
  FiniteDimensional f.splitting_field f

-- error in FieldTheory.SplittingField: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Any splitting field is isomorphic to `splitting_field f`. -/
def alg_equiv (f : polynomial K) [is_splitting_field K L f] : «expr ≃ₐ[ ] »(L, K, splitting_field f) :=
begin
  refine [expr alg_equiv.of_bijective «expr $ »(lift L f, splits (splitting_field f) f) ⟨ring_hom.injective «expr $ »(lift L f, splits (splitting_field f) f).to_ring_hom, _⟩],
  haveI [] [] [":=", expr finite_dimensional (splitting_field f) f],
  haveI [] [] [":=", expr finite_dimensional L f],
  have [] [":", expr «expr = »(finite_dimensional.finrank K L, finite_dimensional.finrank K (splitting_field f))] [":=", expr le_antisymm (linear_map.finrank_le_finrank_of_injective (show function.injective «expr $ »(lift L f, splits (splitting_field f) f).to_linear_map, from ring_hom.injective («expr $ »(lift L f, splits (splitting_field f) f) : «expr →+* »(L, f.splitting_field)))) (linear_map.finrank_le_finrank_of_injective (show function.injective «expr $ »(lift (splitting_field f) f, splits L f).to_linear_map, from ring_hom.injective («expr $ »(lift (splitting_field f) f, splits L f) : «expr →+* »(f.splitting_field, L))))],
  change [expr function.surjective «expr $ »(lift L f, splits (splitting_field f) f).to_linear_map] [] [],
  refine [expr (linear_map.injective_iff_surjective_of_finrank_eq_finrank this).1 _],
  exact [expr ring_hom.injective («expr $ »(lift L f, splits (splitting_field f) f) : «expr →+* »(L, f.splitting_field))]
end

end IsSplittingField

end SplittingField

end Polynomial

