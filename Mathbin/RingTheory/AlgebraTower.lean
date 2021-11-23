import Mathbin.Algebra.Invertible 
import Mathbin.RingTheory.Adjoin.Fg 
import Mathbin.LinearAlgebra.Basis 
import Mathbin.Algebra.Algebra.Tower 
import Mathbin.Algebra.Algebra.RestrictScalars

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

In `field_theory/tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is a `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/


open_locale Pointwise

universe u v w u₁

variable(R : Type u)(S : Type v)(A : Type w)(B : Type u₁)

namespace IsScalarTower

section Semiringₓ

variable[CommSemiringₓ R][CommSemiringₓ S][Semiringₓ A][Semiringₓ B]

variable[Algebra R S][Algebra S A][Algebra S B][Algebra R A][Algebra R B]

variable[IsScalarTower R S A][IsScalarTower R S B]

variable(R S A B)

/-- Suppose that `R -> S -> A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`. -/
def invertible.algebra_tower (r : R) [Invertible (algebraMap R S r)] : Invertible (algebraMap R A r) :=
  Invertible.copy (Invertible.map (algebraMap S A : S →* A) (algebraMap R S r)) (algebraMap R A r)
    (by 
      rw [RingHom.coe_monoid_hom, IsScalarTower.algebra_map_apply R S A])

-- error in RingTheory.AlgebraTower: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
def invertible_algebra_coe_nat (n : exprℕ()) [inv : invertible (n : R)] : invertible (n : A) :=
by { haveI [] [":", expr invertible (algebra_map exprℕ() R n)] [":=", expr inv],
  exact [expr invertible.algebra_tower exprℕ() R A n] }

end Semiringₓ

section CommSemiringₓ

variable[CommSemiringₓ R][CommSemiringₓ A][CommSemiringₓ B]

variable[Algebra R A][Algebra A B][Algebra R B][IsScalarTower R A B]

end CommSemiringₓ

end IsScalarTower

namespace Algebra

theorem adjoin_algebra_map' {R : Type u} {S : Type v} {A : Type w} [CommSemiringₓ R] [CommSemiringₓ S] [Semiringₓ A]
  [Algebra R S] [Algebra S A] (s : Set S) :
  adjoin R (algebraMap S (RestrictScalars R S A) '' s) =
    (adjoin R s).map ((Algebra.ofId S (RestrictScalars R S A)).restrictScalars R) :=
  le_antisymmₓ (adjoin_le$ Set.image_subset_iff.2$ fun y hy => ⟨y, subset_adjoin hy, rfl⟩)
    (Subalgebra.map_le.2$ adjoin_le$ fun y hy => subset_adjoin ⟨y, hy, rfl⟩)

theorem adjoin_algebra_map (R : Type u) (S : Type v) (A : Type w) [CommSemiringₓ R] [CommSemiringₓ S] [Semiringₓ A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] (s : Set S) :
  adjoin R (algebraMap S A '' s) = Subalgebra.map (adjoin R s) (IsScalarTower.toAlgHom R S A) :=
  le_antisymmₓ (adjoin_le$ Set.image_subset_iff.2$ fun y hy => ⟨y, subset_adjoin hy, rfl⟩)
    (Subalgebra.map_le.2$ adjoin_le$ fun y hy => subset_adjoin ⟨y, hy, rfl⟩)

theorem adjoin_restrict_scalars (C D E : Type _) [CommSemiringₓ C] [CommSemiringₓ D] [CommSemiringₓ E] [Algebra C D]
  [Algebra C E] [Algebra D E] [IsScalarTower C D E] (S : Set E) :
  (Algebra.adjoin D S).restrictScalars C =
    (Algebra.adjoin ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) S).restrictScalars C :=
  by 
    suffices  :
      Set.Range (algebraMap D E) = Set.Range (algebraMap ((⊤ : Subalgebra C D).map (IsScalarTower.toAlgHom C D E)) E)
    ·
      ext x 
      change x ∈ Subsemiring.closure (_ ∪ S) ↔ x ∈ Subsemiring.closure (_ ∪ S)
      rw [this]
    ext x 
    split 
    ·
      rintro ⟨y, hy⟩
      exact ⟨⟨algebraMap D E y, ⟨y, ⟨Algebra.mem_top, rfl⟩⟩⟩, hy⟩
    ·
      rintro ⟨⟨y, ⟨z, ⟨h0, h1⟩⟩⟩, h2⟩
      exact ⟨z, Eq.trans h1 h2⟩

theorem adjoin_res_eq_adjoin_res (C D E F : Type _) [CommSemiringₓ C] [CommSemiringₓ D] [CommSemiringₓ E]
  [CommSemiringₓ F] [Algebra C D] [Algebra C E] [Algebra C F] [Algebra D F] [Algebra E F] [IsScalarTower C D F]
  [IsScalarTower C E F] {S : Set D} {T : Set E} (hS : Algebra.adjoin C S = ⊤) (hT : Algebra.adjoin C T = ⊤) :
  (Algebra.adjoin E (algebraMap D F '' S)).restrictScalars C =
    (Algebra.adjoin D (algebraMap E F '' T)).restrictScalars C :=
  by 
    rw [adjoin_restrict_scalars C E, adjoin_restrict_scalars C D, ←hS, ←hT, ←Algebra.adjoin_image,
      ←Algebra.adjoin_image, ←AlgHom.coe_to_ring_hom, ←AlgHom.coe_to_ring_hom, IsScalarTower.coe_to_alg_hom,
      IsScalarTower.coe_to_alg_hom, ←adjoin_union_eq_adjoin_adjoin, ←adjoin_union_eq_adjoin_adjoin, Set.union_comm]

end Algebra

section 

open_locale Classical

theorem Algebra.fg_trans' {R S A : Type _} [CommSemiringₓ R] [CommSemiringₓ S] [CommSemiringₓ A] [Algebra R S]
  [Algebra S A] [Algebra R A] [IsScalarTower R S A] (hRS : (⊤ : Subalgebra R S).Fg) (hSA : (⊤ : Subalgebra S A).Fg) :
  (⊤ : Subalgebra R A).Fg :=
  let ⟨s, hs⟩ := hRS 
  let ⟨t, ht⟩ := hSA
  ⟨s.image (algebraMap S A) ∪ t,
    by 
      rw [Finset.coe_union, Finset.coe_image, Algebra.adjoin_union_eq_adjoin_adjoin, Algebra.adjoin_algebra_map, hs,
        Algebra.map_top, IsScalarTower.adjoin_range_to_alg_hom, ht, Subalgebra.restrict_scalars_top]⟩

end 

section AlgebraMapCoeffs

variable{R}(A){ι M : Type _}[CommSemiringₓ R][Semiringₓ A][AddCommMonoidₓ M]

variable[Algebra R A][Module A M][Module R M][IsScalarTower R A M]

variable(b : Basis ι R M)(h : Function.Bijective (algebraMap R A))

/-- If `R` and `A` have a bijective `algebra_map R A` and act identically on `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module. -/
@[simps]
noncomputable def Basis.algebraMapCoeffs : Basis ι A M :=
  b.map_coeffs (RingEquiv.ofBijective _ h)
    fun c x =>
      by 
        simp 

theorem Basis.algebra_map_coeffs_apply (i : ι) : b.algebra_map_coeffs A h i = b i :=
  b.map_coeffs_apply _ _ _

@[simp]
theorem Basis.coe_algebra_map_coeffs : (b.algebra_map_coeffs A h : ι → M) = b :=
  b.coe_map_coeffs _ _

end AlgebraMapCoeffs

section Semiringₓ

open Finsupp

open_locale BigOperators Classical

universe v₁ w₁

variable{R S A}

variable[CommSemiringₓ R][Semiringₓ S][AddCommMonoidₓ A]

variable[Algebra R S][Module S A][Module R A][IsScalarTower R S A]

-- error in RingTheory.AlgebraTower: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem linear_independent_smul
{ι : Type v₁}
{b : ι → S}
{ι' : Type w₁}
{c : ι' → A}
(hb : linear_independent R b)
(hc : linear_independent S c) : linear_independent R (λ p : «expr × »(ι, ι'), «expr • »(b p.1, c p.2)) :=
begin
  rw [expr linear_independent_iff'] ["at", ident hb, ident hc],
  rw [expr linear_independent_iff''] [],
  rintros [ident s, ident g, ident hg, ident hsg, "⟨", ident i, ",", ident k, "⟩"],
  by_cases [expr hik, ":", expr «expr ∈ »((i, k), s)],
  { have [ident h1] [":", expr «expr = »(«expr∑ in , »((i), (s.image prod.fst).product (s.image prod.snd), «expr • »(g i, «expr • »(b i.1, c i.2))), 0)] [],
    { rw ["<-", expr hsg] [],
      exact [expr «expr $ »(finset.sum_subset finset.subset_product, λ
        p
        _
        hp, show «expr = »(«expr • »(g p, «expr • »(b p.1, c p.2)), 0), by rw ["[", expr hg p hp, ",", expr zero_smul, "]"] []).symm] },
    rw [expr finset.sum_product_right] ["at", ident h1],
    simp_rw ["[", "<-", expr smul_assoc, ",", "<-", expr finset.sum_smul, "]"] ["at", ident h1],
    exact [expr hb _ _ (hc _ _ h1 k (finset.mem_image_of_mem _ hik)) i (finset.mem_image_of_mem _ hik)] },
  exact [expr hg _ hik]
end

/-- `basis.smul (b : basis ι R S) (c : basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b i • c j`. -/
noncomputable def Basis.smul {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) : Basis (ι × ι') R A :=
  Basis.of_repr
    (c.repr.restrict_scalars R ≪≫ₗ
      (Finsupp.lcongr (Equiv.refl _) b.repr ≪≫ₗ
        ((finsupp_prod_lequiv R).symm ≪≫ₗ Finsupp.lcongr (Equiv.prodComm ι' ι) (LinearEquiv.refl _ _))))

@[simp]
theorem Basis.smul_repr {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) x ij :
  (b.smul c).repr x ij = b.repr (c.repr x ij.2) ij.1 :=
  by 
    simp [Basis.smul]

theorem Basis.smul_repr_mk {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) x i j :
  (b.smul c).repr x (i, j) = b.repr (c.repr x j) i :=
  b.smul_repr c x (i, j)

@[simp]
theorem Basis.smul_apply {ι : Type v₁} {ι' : Type w₁} (b : Basis ι R S) (c : Basis ι' S A) ij :
  (b.smul c) ij = b ij.1 • c ij.2 :=
  by 
    obtain ⟨i, j⟩ := ij 
    rw [Basis.apply_eq_iff]
    ext ⟨i', j'⟩
    rw [Basis.smul_repr, LinearEquiv.map_smul, Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    dsimp only 
    splitIfs with hi
    ·
      simp [hi, Finsupp.single_apply]
    ·
      simp [hi]

end Semiringₓ

section Ringₓ

variable{R S}

variable[CommRingₓ R][Ringₓ S][Algebra R S]

theorem Basis.algebra_map_injective {ι : Type _} [NoZeroDivisors R] [Nontrivial S] (b : Basis ι R S) :
  Function.Injective (algebraMap R S) :=
  have  : NoZeroSmulDivisors R S := b.no_zero_smul_divisors 
  by 
    exact NoZeroSmulDivisors.algebra_map_injective R S

end Ringₓ

section ArtinTate

variable(C : Type _)

section Semiringₓ

variable[CommSemiringₓ A][CommSemiringₓ B][Semiringₓ C]

variable[Algebra A B][Algebra B C][Algebra A C][IsScalarTower A B C]

open Finset Submodule

open_locale Classical

-- error in RingTheory.AlgebraTower: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_subalgebra_of_fg
(hAC : («expr⊤»() : subalgebra A C).fg)
(hBC : («expr⊤»() : submodule B C).fg) : «expr∃ , »((B₀ : subalgebra A B), «expr ∧ »(B₀.fg, («expr⊤»() : submodule B₀ C).fg)) :=
begin
  cases [expr hAC] ["with", ident x, ident hx],
  cases [expr hBC] ["with", ident y, ident hy],
  have [] [] [":=", expr hy],
  simp_rw ["[", expr eq_top_iff', ",", expr mem_span_finset, "]"] ["at", ident this],
  choose [] [ident f] [ident hf] [],
  let [ident s] [":", expr finset B] [":=", expr (finset.product «expr ∪ »(x, «expr * »(y, y)) y).image (function.uncurry f)],
  have [ident hsx] [":", expr ∀
   (xi «expr ∈ » x)
   (yj «expr ∈ » y), «expr ∈ »(f xi yj, s)] [":=", expr λ
   xi
   hxi
   yj
   hyj, show «expr ∈ »(function.uncurry f (xi, yj), s), from «expr $ »(mem_image_of_mem _, mem_product.2 ⟨mem_union_left _ hxi, hyj⟩)],
  have [ident hsy] [":", expr ∀
   yi
   yj
   yk «expr ∈ » y, «expr ∈ »(f «expr * »(yi, yj) yk, s)] [":=", expr λ
   yi
   yj
   yk
   hyi
   hyj
   hyk, show «expr ∈ »(function.uncurry f («expr * »(yi, yj), yk), s), from «expr $ »(mem_image_of_mem _, mem_product.2 ⟨«expr $ »(mem_union_right _, finset.mul_mem_mul hyi hyj), hyk⟩)],
  have [ident hxy] [":", expr ∀
   xi «expr ∈ » x, «expr ∈ »(xi, span (algebra.adjoin A («expr↑ »(s) : set B)) («expr↑ »((insert 1 y : finset C)) : set C))] [":=", expr λ
   xi
   hxi, «expr ▸ »(hf xi, sum_mem _ (λ
     yj
     hyj, smul_mem (span (algebra.adjoin A («expr↑ »(s) : set B)) («expr↑ »((insert 1 y : finset C)) : set C)) ⟨f xi yj, «expr $ »(algebra.subset_adjoin, hsx xi hxi yj hyj)⟩ «expr $ »(subset_span, mem_insert_of_mem hyj)))],
  have [ident hyy] [":", expr «expr ≤ »(«expr * »(span (algebra.adjoin A («expr↑ »(s) : set B)) («expr↑ »((insert 1 y : finset C)) : set C), span (algebra.adjoin A («expr↑ »(s) : set B)) («expr↑ »((insert 1 y : finset C)) : set C)), span (algebra.adjoin A («expr↑ »(s) : set B)) («expr↑ »((insert 1 y : finset C)) : set C))] [],
  { rw ["[", expr span_mul_span, ",", expr span_le, ",", expr coe_insert, "]"] [],
    rintros ["_", "⟨", ident yi, ",", ident yj, ",", ident rfl, "|", ident hyi, ",", ident rfl, "|", ident hyj, ",", ident rfl, "⟩"],
    { rw [expr mul_one] [],
      exact [expr subset_span (set.mem_insert _ _)] },
    { rw [expr one_mul] [],
      exact [expr subset_span (set.mem_insert_of_mem _ hyj)] },
    { rw [expr mul_one] [],
      exact [expr subset_span (set.mem_insert_of_mem _ hyi)] },
    { rw ["<-", expr hf «expr * »(yi, yj)] [],
      exact [expr set_like.mem_coe.2 «expr $ »(sum_mem _, λ
        yk
        hyk, smul_mem (span (algebra.adjoin A («expr↑ »(s) : set B)) (insert 1 «expr↑ »(y) : set C)) ⟨f «expr * »(yi, yj) yk, «expr $ »(algebra.subset_adjoin, hsy yi yj yk hyi hyj hyk)⟩ («expr $ »(subset_span, set.mem_insert_of_mem _ hyk) : «expr ∈ »(yk, _)))] } },
  refine [expr ⟨algebra.adjoin A («expr↑ »(s) : set B), subalgebra.fg_adjoin_finset _, insert 1 y, _⟩],
  refine [expr restrict_scalars_injective A _ _ _],
  rw ["[", expr restrict_scalars_top, ",", expr eq_top_iff, ",", "<-", expr algebra.top_to_submodule, ",", "<-", expr hx, ",", expr algebra.adjoin_eq_span, ",", expr span_le, "]"] [],
  refine [expr λ
   r
   hr, submonoid.closure_induction hr (λ
    c
    hc, hxy c hc) «expr $ »(subset_span, mem_insert_self _ _) (λ
    p q hp hq, «expr $ »(hyy, submodule.mul_mem_mul hp hq))]
end

end Semiringₓ

section Ringₓ

variable[CommRingₓ A][CommRingₓ B][CommRingₓ C]

variable[Algebra A B][Algebra B C][Algebra A C][IsScalarTower A B C]

/-- Artin--Tate lemma: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Stacks 00IS; Altman--Kleiman 16.17. -/
theorem fg_of_fg_of_fg [IsNoetherianRing A] (hAC : (⊤ : Subalgebra A C).Fg) (hBC : (⊤ : Submodule B C).Fg)
  (hBCi : Function.Injective (algebraMap B C)) : (⊤ : Subalgebra A B).Fg :=
  let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC 
  Algebra.fg_trans' (B₀.fg_top.2 hAB₀)$
    Subalgebra.fg_of_submodule_fg$
      have  : IsNoetherianRing B₀ := is_noetherian_ring_of_fg hAB₀ 
      have  : IsNoetherian B₀ C :=
        by 
          exact is_noetherian_of_fg_of_noetherian' hB₀C 
      by 
        exact fg_of_injective (IsScalarTower.toAlgHom B₀ B C).toLinearMap hBCi

end Ringₓ

end ArtinTate

section AlgHomTower

variable{A}{C D : Type _}[CommSemiringₓ A][CommSemiringₓ C][CommSemiringₓ D][Algebra A C][Algebra A D]

variable(f : C →ₐ[A] D)(B)[CommSemiringₓ B][Algebra A B][Algebra B C][IsScalarTower A B C]

/-- Restrict the domain of an `alg_hom`. -/
def AlgHom.restrictDomain : B →ₐ[A] D :=
  f.comp (IsScalarTower.toAlgHom A B C)

/-- Extend the scalars of an `alg_hom`. -/
def AlgHom.extendScalars : @AlgHom B C D _ _ _ _ (f.restrict_domain B).toRingHom.toAlgebra :=
  { f with commutes' := fun _ => rfl }

variable{B}

-- error in RingTheory.AlgebraTower: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `alg_hom`s from the top of a tower are equivalent to a pair of `alg_hom`s. -/
def alg_hom_equiv_sigma : «expr ≃ »(«expr →ₐ[ ] »(C, A, D), «exprΣ , »((f : «expr →ₐ[ ] »(B, A, D)), @alg_hom B C D _ _ _ _ f.to_ring_hom.to_algebra)) :=
{ to_fun := λ f, ⟨f.restrict_domain B, f.extend_scalars B⟩,
  inv_fun := λ fg, let alg := fg.1.to_ring_hom.to_algebra in
  by exactI [expr fg.2.restrict_scalars A],
  left_inv := λ f, by { dsimp ["only"] [] [] [],
    ext [] [] [],
    refl },
  right_inv := begin
    rintros ["⟨", "⟨", ident f, ",", "_", ",", "_", ",", "_", ",", "_", ",", "_", "⟩", ",", ident g, ",", "_", ",", "_", ",", "_", ",", "_", ",", ident hg, "⟩"],
    have [] [":", expr «expr = »(f, λ
      x, g (algebra_map B C x))] [":=", expr by { ext [] [] [], exact [expr (hg x).symm] }],
    subst [expr this],
    refl
  end }

end AlgHomTower

