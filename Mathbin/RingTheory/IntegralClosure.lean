import Mathbin.RingTheory.Adjoin.Fg 
import Mathbin.RingTheory.Polynomial.ScaleRoots 
import Mathbin.RingTheory.Polynomial.Tower

/-!
# Integral closure of a subring.

If A is an R-algebra then `a : A` is integral over R if it is a root of a monic polynomial
with coefficients in R. Enough theory is developed to prove that integral elements
form a sub-R-algebra of A.

## Main definitions

Let `R` be a `comm_ring` and let `A` be an R-algebra.

* `ring_hom.is_integral_elem (f : R →+* A) (x : A)` : `x` is integral with respect to the map `f`,

* `is_integral (x : A)`  : `x` is integral over `R`, i.e., is a root of a monic polynomial with
                           coefficients in `R`.
* `integral_closure R A` : the integral closure of `R` in `A`, regarded as a sub-`R`-algebra of `A`.
-/


open_locale Classical

open_locale BigOperators

open Polynomial Submodule

section Ringₓ

variable {R S A : Type _}

variable [CommRingₓ R] [Ringₓ A] [Ringₓ S] (f : R →+* S)

/-- An element `x` of `A` is said to be integral over `R` with respect to `f`
if it is a root of a monic polynomial `p : polynomial R` evaluated under `f` -/
def RingHom.IsIntegralElem (f : R →+* A) (x : A) :=
  ∃ p : Polynomial R, monic p ∧ eval₂ f x p = 0

/-- A ring homomorphism `f : R →+* A` is said to be integral
if every element `A` is integral with respect to the map `f` -/
def RingHom.IsIntegral (f : R →+* A) :=
  ∀ x : A, f.is_integral_elem x

variable [Algebra R A] (R)

/-- An element `x` of an algebra `A` over a commutative ring `R` is said to be *integral*,
if it is a root of some monic polynomial `p : polynomial R`.
Equivalently, the element is integral over `R` with respect to the induced `algebra_map` -/
def IsIntegral (x : A) : Prop :=
  (algebraMap R A).IsIntegralElem x

variable (A)

/-- An algebra is integral if every element of the extension is integral over the base ring -/
def Algebra.IsIntegral : Prop :=
  (algebraMap R A).IsIntegral

variable {R A}

theorem RingHom.is_integral_map {x : R} : f.is_integral_elem (f x) :=
  ⟨X - C x, monic_X_sub_C _,
    by 
      simp ⟩

theorem is_integral_algebra_map {x : R} : IsIntegral R (algebraMap R A x) :=
  (algebraMap R A).is_integral_map

-- error in RingTheory.IntegralClosure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_integral_of_noetherian (H : is_noetherian R A) (x : A) : is_integral R x :=
begin
  let [ident leval] [":", expr «expr →ₗ[ ] »(polynomial R, R, A)] [":=", expr (aeval x).to_linear_map],
  let [ident D] [":", expr exprℕ() → submodule R A] [":=", expr λ n, (degree_le R n).map leval],
  let [ident M] [] [":=", expr well_founded.min (is_noetherian_iff_well_founded.1 H) (set.range D) ⟨_, ⟨0, rfl⟩⟩],
  have [ident HM] [":", expr «expr ∈ »(M, set.range D)] [":=", expr well_founded.min_mem _ _ _],
  cases [expr HM] ["with", ident N, ident HN],
  have [ident HM] [":", expr «expr¬ »(«expr < »(M, D «expr + »(N, 1)))] [":=", expr well_founded.not_lt_min (is_noetherian_iff_well_founded.1 H) (set.range D) _ ⟨«expr + »(N, 1), rfl⟩],
  rw ["<-", expr HN] ["at", ident HM],
  have [ident HN2] [":", expr «expr ≤ »(D «expr + »(N, 1), D N)] [":=", expr classical.by_contradiction (λ
    H, HM (lt_of_le_not_le (map_mono (degree_le_mono (with_bot.coe_le_coe.2 (nat.le_succ N)))) H))],
  have [ident HN3] [":", expr «expr ∈ »(leval «expr ^ »(X, «expr + »(N, 1)), D N)] [],
  { exact [expr HN2 (mem_map_of_mem (mem_degree_le.2 (degree_X_pow_le _)))] },
  rcases [expr HN3, "with", "⟨", ident p, ",", ident hdp, ",", ident hpe, "⟩"],
  refine [expr ⟨«expr - »(«expr ^ »(X, «expr + »(N, 1)), p), monic_X_pow_sub (mem_degree_le.1 hdp), _⟩],
  show [expr «expr = »(leval «expr - »(«expr ^ »(X, «expr + »(N, 1)), p), 0)],
  rw ["[", expr linear_map.map_sub, ",", expr hpe, ",", expr sub_self, "]"] []
end

theorem is_integral_of_submodule_noetherian (S : Subalgebra R A) (H : IsNoetherian R S.to_submodule) (x : A)
  (hx : x ∈ S) : IsIntegral R x :=
  by 
    suffices  : IsIntegral R (show S from ⟨x, hx⟩)
    ·
      rcases this with ⟨p, hpm, hpx⟩
      replace hpx := congr_argₓ S.val hpx 
      refine' ⟨p, hpm, Eq.trans _ hpx⟩
      simp only [aeval_def, eval₂, sum_def]
      rw [S.val.map_sum]
      refine' Finset.sum_congr rfl fun n hn => _ 
      rw [S.val.map_mul, S.val.map_pow, S.val.commutes, S.val_apply, Subtype.coe_mk]
    refine' is_integral_of_noetherian H ⟨x, hx⟩

end Ringₓ

section 

variable {R A B S : Type _}

variable [CommRingₓ R] [CommRingₓ A] [CommRingₓ B] [CommRingₓ S]

variable [Algebra R A] [Algebra R B] (f : R →+* S)

theorem is_integral_alg_hom (f : A →ₐ[R] B) {x : A} (hx : IsIntegral R x) : IsIntegral R (f x) :=
  let ⟨p, hp, hpx⟩ := hx
  ⟨p, hp,
    by 
      rw [←aeval_def, aeval_alg_hom_apply, aeval_def, hpx, f.map_zero]⟩

@[simp]
theorem is_integral_alg_equiv (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x :=
  ⟨fun h =>
      by 
        simpa using is_integral_alg_hom f.symm.to_alg_hom h,
    is_integral_alg_hom f.to_alg_hom⟩

theorem is_integral_of_is_scalar_tower [Algebra A B] [IsScalarTower R A B] (x : B) (hx : IsIntegral R x) :
  IsIntegral A x :=
  let ⟨p, hp, hpx⟩ := hx
  ⟨p.map$ algebraMap R A, monic_map _ hp,
    by 
      rw [←aeval_def, ←IsScalarTower.aeval_apply, aeval_def, hpx]⟩

theorem is_integral_of_subring {x : A} (T : Subring R) (hx : IsIntegral T x) : IsIntegral R x :=
  is_integral_of_is_scalar_tower x hx

theorem IsIntegral.algebra_map [Algebra A B] [IsScalarTower R A B] {x : A} (h : IsIntegral R x) :
  IsIntegral R (algebraMap A B x) :=
  by 
    rcases h with ⟨f, hf, hx⟩
    use f, hf 
    rw [IsScalarTower.algebra_map_eq R A B, ←hom_eval₂, hx, RingHom.map_zero]

theorem is_integral_algebra_map_iff [Algebra A B] [IsScalarTower R A B] {x : A}
  (hAB : Function.Injective (algebraMap A B)) : IsIntegral R (algebraMap A B x) ↔ IsIntegral R x :=
  by 
    refine' ⟨_, fun h => h.algebra_map⟩
    rintro ⟨f, hf, hx⟩
    use f, hf 
    exact IsScalarTower.aeval_eq_zero_of_aeval_algebra_map_eq_zero R A B hAB hx

theorem is_integral_iff_is_integral_closure_finite {r : A} :
  IsIntegral R r ↔ ∃ s : Set R, s.finite ∧ IsIntegral (Subring.closure s) r :=
  by 
    split  <;> intro hr
    ·
      rcases hr with ⟨p, hmp, hpr⟩
      refine' ⟨_, Set.finite_mem_finset _, p.restriction, monic_restriction.2 hmp, _⟩
      erw [←aeval_def, IsScalarTower.aeval_apply _ R, map_restriction, aeval_def, hpr]
    rcases hr with ⟨s, hs, hsr⟩
    exact is_integral_of_subring _ hsr

-- error in RingTheory.IntegralClosure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fg_adjoin_singleton_of_integral
(x : A)
(hx : is_integral R x) : (algebra.adjoin R ({x} : set A)).to_submodule.fg :=
begin
  rcases [expr hx, "with", "⟨", ident f, ",", ident hfm, ",", ident hfx, "⟩"],
  existsi [expr finset.image (((«expr ^ »)) x) (finset.range «expr + »(nat_degree f, 1))],
  apply [expr le_antisymm],
  { rw [expr span_le] [],
    intros [ident s, ident hs],
    rw [expr finset.mem_coe] ["at", ident hs],
    rcases [expr finset.mem_image.1 hs, "with", "⟨", ident k, ",", ident hk, ",", ident rfl, "⟩"],
    clear [ident hk],
    exact [expr (algebra.adjoin R {x}).pow_mem (algebra.subset_adjoin (set.mem_singleton _)) k] },
  intros [ident r, ident hr],
  change [expr «expr ∈ »(r, algebra.adjoin R ({x} : set A))] [] ["at", ident hr],
  rw [expr algebra.adjoin_singleton_eq_range_aeval] ["at", ident hr],
  rcases [expr (aeval x).mem_range.mp hr, "with", "⟨", ident p, ",", ident rfl, "⟩"],
  rw ["<-", expr mod_by_monic_add_div p hfm] [],
  rw ["<-", expr aeval_def] ["at", ident hfx],
  rw ["[", expr alg_hom.map_add, ",", expr alg_hom.map_mul, ",", expr hfx, ",", expr zero_mul, ",", expr add_zero, "]"] [],
  have [] [":", expr «expr ≤ »(degree «expr %ₘ »(p, f), degree f)] [":=", expr degree_mod_by_monic_le p hfm],
  generalize_hyp [] [":"] [expr «expr = »(«expr %ₘ »(p, f), q)] ["at", ident this, "⊢"],
  rw ["[", "<-", expr sum_C_mul_X_eq q, ",", expr aeval_def, ",", expr eval₂_sum, ",", expr sum_def, "]"] [],
  refine [expr sum_mem _ (λ k hkq, _)],
  rw ["[", expr eval₂_mul, ",", expr eval₂_C, ",", expr eval₂_pow, ",", expr eval₂_X, ",", "<-", expr algebra.smul_def, "]"] [],
  refine [expr smul_mem _ _ (subset_span _)],
  rw [expr finset.mem_coe] [],
  refine [expr finset.mem_image.2 ⟨_, _, rfl⟩],
  rw ["[", expr finset.mem_range, ",", expr nat.lt_succ_iff, "]"] [],
  refine [expr le_of_not_lt (λ hk, _)],
  rw ["[", expr degree_le_iff_coeff_zero, "]"] ["at", ident this],
  rw ["[", expr mem_support_iff, "]"] ["at", ident hkq],
  apply [expr hkq],
  apply [expr this],
  exact [expr lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 hk)]
end

theorem fg_adjoin_of_finite {s : Set A} (hfs : s.finite) (his : ∀ x _ : x ∈ s, IsIntegral R x) :
  (Algebra.adjoin R s).toSubmodule.Fg :=
  Set.Finite.induction_on hfs
    (fun _ =>
      ⟨{1},
        Submodule.ext$
          fun x =>
            by 
              erw [Algebra.adjoin_empty, Finset.coe_singleton, ←one_eq_span, one_eq_range, LinearMap.mem_range,
                Algebra.mem_bot]
              rfl⟩)
    (fun a s has hs ih his =>
      by 
        rw [←Set.union_singleton, Algebra.adjoin_union_coe_submodule] <;>
          exact
            fg_mul _ _ (ih$ fun i hi => his i$ Set.mem_insert_of_mem a hi)
              (fg_adjoin_singleton_of_integral _$ his a$ Set.mem_insert a s))
    his

theorem is_noetherian_adjoin_finset [IsNoetherianRing R] (s : Finset A) (hs : ∀ x _ : x ∈ s, IsIntegral R x) :
  IsNoetherian R (Algebra.adjoin R («expr↑ » s : Set A)) :=
  is_noetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_to_set hs)

-- error in RingTheory.IntegralClosure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `S` is a sub-`R`-algebra of `A` and `S` is finitely-generated as an `R`-module,
  then all elements of `S` are integral over `R`. -/
theorem is_integral_of_mem_of_fg
(S : subalgebra R A)
(HS : S.to_submodule.fg)
(x : A)
(hx : «expr ∈ »(x, S)) : is_integral R x :=
begin
  cases [expr HS] ["with", ident y, ident hy],
  obtain ["⟨", ident lx, ",", ident hlx1, ",", ident hlx2, "⟩", ":", expr «expr∃ , »((l : «expr →₀ »(A, R))
    (H : «expr ∈ »(l, finsupp.supported R R «expr↑ »(y))), «expr = »(finsupp.total A A R id l, x))],
  { rwa ["[", "<-", expr @finsupp.mem_span_image_iff_total A A R _ _ _ id «expr↑ »(y) x, ",", expr set.image_id «expr↑ »(y), ",", expr hy, "]"] [] },
  have [ident hyS] [":", expr ∀
   {p}, «expr ∈ »(p, y) → «expr ∈ »(p, S)] [":=", expr λ
   p hp, show «expr ∈ »(p, S.to_submodule), by { rw ["<-", expr hy] [],
     exact [expr subset_span hp] }],
  have [] [":", expr ∀
   jk : («expr↑ »(y.product y) : set «expr × »(A, A)), «expr ∈ »(«expr * »(jk.1.1, jk.1.2), S.to_submodule)] [":=", expr λ
   jk, S.mul_mem (hyS (finset.mem_product.1 jk.2).1) (hyS (finset.mem_product.1 jk.2).2)],
  rw ["[", "<-", expr hy, ",", "<-", expr set.image_id «expr↑ »(y), "]"] ["at", ident this],
  simp [] [] ["only"] ["[", expr finsupp.mem_span_image_iff_total, "]"] [] ["at", ident this],
  choose [] [ident ly] [ident hly1, ident hly2] [],
  let [ident S₀] [":", expr subring R] [":=", expr subring.closure «expr↑ »(«expr ∪ »(lx.frange, finset.bUnion finset.univ «expr ∘ »(finsupp.frange, ly)))],
  refine [expr is_integral_of_subring S₀ _],
  letI [] [":", expr comm_ring S₀] [":=", expr subring.to_comm_ring S₀],
  letI [] [":", expr algebra S₀ A] [":=", expr algebra.of_subring S₀],
  have [] [":", expr «expr ≤ »(«expr * »(span S₀ (insert 1 «expr↑ »(y) : set A), span S₀ (insert 1 «expr↑ »(y) : set A)), span S₀ (insert 1 «expr↑ »(y) : set A))] [],
  { rw [expr span_mul_span] [],
    refine [expr span_le.2 (λ z hz, _)],
    rcases [expr set.mem_mul.1 hz, "with", "⟨", ident p, ",", ident q, ",", ident rfl, "|", ident hp, ",", ident hq, ",", ident rfl, "⟩"],
    { rw [expr one_mul] [],
      exact [expr subset_span hq] },
    rcases [expr hq, "with", ident rfl, "|", ident hq],
    { rw [expr mul_one] [],
      exact [expr subset_span (or.inr hp)] },
    erw ["<-", expr hly2 ⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩] [],
    rw ["[", expr finsupp.total_apply, ",", expr finsupp.sum, "]"] [],
    refine [expr (span S₀ (insert 1 «expr↑ »(y) : set A)).sum_mem (λ t ht, _)],
    have [] [":", expr «expr ∈ »(ly ⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩ t, S₀)] [":=", expr subring.subset_closure «expr $ »(finset.mem_union_right _, finset.mem_bUnion.2 ⟨⟨(p, q), finset.mem_product.2 ⟨hp, hq⟩⟩, finset.mem_univ _, finsupp.mem_frange.2 ⟨finsupp.mem_support_iff.1 ht, _, rfl⟩⟩)],
    change [expr «expr ∈ »(«expr • »((⟨_, this⟩ : S₀), t), _)] [] [],
    exact [expr smul_mem _ _ «expr $ »(subset_span, «expr $ »(or.inr, hly1 _ ht))] },
  let [ident S₁] [":", expr subring A] [":=", expr { carrier := span S₀ (insert 1 «expr↑ »(y) : set A),
     one_mem' := «expr $ »(subset_span, or.inl rfl),
     mul_mem' := λ p q hp hq, «expr $ »(this, mul_mem_mul hp hq),
     zero_mem' := (span S₀ (insert 1 «expr↑ »(y) : set A)).zero_mem,
     add_mem' := λ _ _, (span S₀ (insert 1 «expr↑ »(y) : set A)).add_mem,
     neg_mem' := λ _, (span S₀ (insert 1 «expr↑ »(y) : set A)).neg_mem }],
  have [] [":", expr «expr = »(S₁, (algebra.adjoin S₀ («expr↑ »(y) : set A)).to_subring)] [],
  { ext [] [ident z] [],
    suffices [] [":", expr «expr ↔ »(«expr ∈ »(z, span «expr↥ »(S₀) (insert 1 «expr↑ »(y) : set A)), «expr ∈ »(z, (algebra.adjoin «expr↥ »(S₀) (y : set A)).to_submodule))],
    { simpa [] [] [] [] [] [] },
    split; intro [ident hz],
    { exact [expr span_le.2 (set.insert_subset.2 ⟨(algebra.adjoin S₀ «expr↑ »(y)).one_mem, algebra.subset_adjoin⟩) hz] },
    { rw ["[", expr subalgebra.mem_to_submodule, ",", expr algebra.mem_adjoin_iff, "]"] ["at", ident hz],
      suffices [] [":", expr «expr ≤ »(subring.closure «expr ∪ »(set.range «expr⇑ »(algebra_map «expr↥ »(S₀) A), «expr↑ »(y)), S₁)],
      { exact [expr this hz] },
      refine [expr subring.closure_le.2 (set.union_subset _ (λ t ht, «expr $ »(subset_span, or.inr ht)))],
      rw [expr set.range_subset_iff] [],
      intro [ident y],
      rw [expr algebra.algebra_map_eq_smul_one] [],
      exact [expr smul_mem _ y (subset_span (or.inl rfl))] } },
  have [ident foo] [":", expr ∀
   z, «expr ↔ »(«expr ∈ »(z, S₁), «expr ∈ »(z, algebra.adjoin «expr↥ »(S₀) (y : set A)))] [],
  simp [] [] [] ["[", expr this, "]"] [] [],
  haveI [] [":", expr is_noetherian_ring «expr↥ »(S₀)] [":=", expr is_noetherian_subring_closure _ (finset.finite_to_set _)],
  refine [expr is_integral_of_submodule_noetherian (algebra.adjoin S₀ «expr↑ »(y)) (is_noetherian_of_fg_of_noetherian _ ⟨insert 1 y, by { rw ["[", expr finset.coe_insert, "]"] [],
       ext [] [ident z] [],
       simp [] [] [] ["[", expr S₁, "]"] [] [],
       convert [] [expr foo z] [] }⟩) _ _],
  rw ["[", "<-", expr hlx2, ",", expr finsupp.total_apply, ",", expr finsupp.sum, "]"] [],
  refine [expr subalgebra.sum_mem _ (λ r hr, _)],
  have [] [":", expr «expr ∈ »(lx r, S₀)] [":=", expr subring.subset_closure (finset.mem_union_left _ (finset.mem_image_of_mem _ hr))],
  change [expr «expr ∈ »(«expr • »((⟨_, this⟩ : S₀), r), _)] [] [],
  rw [expr finsupp.mem_supported] ["at", ident hlx1],
  exact [expr subalgebra.smul_mem _ «expr $ »(algebra.subset_adjoin, hlx1 hr) _]
end

-- error in RingTheory.IntegralClosure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem ring_hom.is_integral_of_mem_closure
{x y z : S}
(hx : f.is_integral_elem x)
(hy : f.is_integral_elem y)
(hz : «expr ∈ »(z, subring.closure ({x, y} : set S))) : f.is_integral_elem z :=
begin
  letI [] [":", expr algebra R S] [":=", expr f.to_algebra],
  have [] [] [":=", expr fg_mul _ _ (fg_adjoin_singleton_of_integral x hx) (fg_adjoin_singleton_of_integral y hy)],
  rw ["[", "<-", expr algebra.adjoin_union_coe_submodule, ",", expr set.singleton_union, "]"] ["at", ident this],
  exact [expr is_integral_of_mem_of_fg (algebra.adjoin R {x, y}) this z «expr $ »(algebra.mem_adjoin_iff.2, subring.closure_mono (set.subset_union_right _ _) hz)]
end

theorem is_integral_of_mem_closure {x y z : A} (hx : IsIntegral R x) (hy : IsIntegral R y)
  (hz : z ∈ Subring.closure ({x, y} : Set A)) : IsIntegral R z :=
  (algebraMap R A).is_integral_of_mem_closure hx hy hz

theorem RingHom.is_integral_zero : f.is_integral_elem 0 :=
  f.map_zero ▸ f.is_integral_map

theorem is_integral_zero : IsIntegral R (0 : A) :=
  (algebraMap R A).is_integral_zero

theorem RingHom.is_integral_one : f.is_integral_elem 1 :=
  f.map_one ▸ f.is_integral_map

theorem is_integral_one : IsIntegral R (1 : A) :=
  (algebraMap R A).is_integral_one

theorem RingHom.is_integral_add {x y : S} (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) :
  f.is_integral_elem (x+y) :=
  f.is_integral_of_mem_closure hx hy$
    Subring.add_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl))

theorem is_integral_add {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x+y) :=
  (algebraMap R A).is_integral_add hx hy

theorem RingHom.is_integral_neg {x : S} (hx : f.is_integral_elem x) : f.is_integral_elem (-x) :=
  f.is_integral_of_mem_closure hx hx (Subring.neg_mem _ (Subring.subset_closure (Or.inl rfl)))

theorem is_integral_neg {x : A} (hx : IsIntegral R x) : IsIntegral R (-x) :=
  (algebraMap R A).is_integral_neg hx

theorem RingHom.is_integral_sub {x y : S} (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) :
  f.is_integral_elem (x - y) :=
  by 
    simpa only [sub_eq_add_neg] using f.is_integral_add hx (f.is_integral_neg hy)

theorem is_integral_sub {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x - y) :=
  (algebraMap R A).is_integral_sub hx hy

theorem RingHom.is_integral_mul {x y : S} (hx : f.is_integral_elem x) (hy : f.is_integral_elem y) :
  f.is_integral_elem (x*y) :=
  f.is_integral_of_mem_closure hx hy
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl rfl)) (Subring.subset_closure (Or.inr rfl)))

theorem is_integral_mul {x y : A} (hx : IsIntegral R x) (hy : IsIntegral R y) : IsIntegral R (x*y) :=
  (algebraMap R A).is_integral_mul hx hy

variable (R A)

/-- The integral closure of R in an R-algebra A. -/
def integralClosure : Subalgebra R A :=
  { Carrier := { r | IsIntegral R r }, zero_mem' := is_integral_zero, one_mem' := is_integral_one,
    add_mem' := fun _ _ => is_integral_add, mul_mem' := fun _ _ => is_integral_mul,
    algebra_map_mem' := fun x => is_integral_algebra_map }

theorem mem_integral_closure_iff_mem_fg {r : A} :
  r ∈ integralClosure R A ↔ ∃ M : Subalgebra R A, M.to_submodule.fg ∧ r ∈ M :=
  ⟨fun hr => ⟨Algebra.adjoin R {r}, fg_adjoin_singleton_of_integral _ hr, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => is_integral_of_mem_of_fg M Hf _ hrM⟩

variable {R} {A}

/-- Mapping an integral closure along an `alg_equiv` gives the integral closure. -/
theorem integral_closure_map_alg_equiv (f : A ≃ₐ[R] B) :
  (integralClosure R A).map (f : A →ₐ[R] B) = integralClosure R B :=
  by 
    ext y 
    rw [Subalgebra.mem_map]
    split 
    ·
      rintro ⟨x, hx, rfl⟩
      exact is_integral_alg_hom f hx
    ·
      intro hy 
      use f.symm y, is_integral_alg_hom (f.symm : B →ₐ[R] A) hy 
      simp 

theorem integralClosure.is_integral (x : integralClosure R A) : IsIntegral R x :=
  let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
    Subtype.eq$
      by 
        rwa [←aeval_def, Subtype.val_eq_coe, ←Subalgebra.val_apply, aeval_alg_hom_apply] at hpx⟩

theorem RingHom.is_integral_of_is_integral_mul_unit (x y : S) (r : R) (hr : (f r*y) = 1)
  (hx : f.is_integral_elem (x*y)) : f.is_integral_elem x :=
  by 
    obtain ⟨p, ⟨p_monic, hp⟩⟩ := hx 
    refine' ⟨scaleRoots p r, ⟨(monic_scale_roots_iff r).2 p_monic, _⟩⟩
    convert scale_roots_eval₂_eq_zero f hp 
    rw [mul_commₓ x y, ←mul_assocₓ, hr, one_mulₓ]

theorem is_integral_of_is_integral_mul_unit {x y : A} {r : R} (hr : (algebraMap R A r*y) = 1)
  (hx : IsIntegral R (x*y)) : IsIntegral R x :=
  (algebraMap R A).is_integral_of_is_integral_mul_unit x y r hr hx

/-- Generalization of `is_integral_of_mem_closure` bootstrapped up from that lemma -/
theorem is_integral_of_mem_closure' (G : Set A) (hG : ∀ x _ : x ∈ G, IsIntegral R x) :
  ∀ x _ : x ∈ Subring.closure G, IsIntegral R x :=
  fun x hx =>
    Subring.closure_induction hx hG is_integral_zero is_integral_one (fun _ _ => is_integral_add)
      (fun _ => is_integral_neg) fun _ _ => is_integral_mul

theorem is_integral_of_mem_closure'' {S : Type _} [CommRingₓ S] {f : R →+* S} (G : Set S)
  (hG : ∀ x _ : x ∈ G, f.is_integral_elem x) : ∀ x _ : x ∈ Subring.closure G, f.is_integral_elem x :=
  fun x hx => @is_integral_of_mem_closure' R S _ _ f.to_algebra G hG x hx

theorem IsIntegral.pow {x : A} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (x^n) :=
  (integralClosure R A).pow_mem h n

theorem IsIntegral.nsmul {x : A} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (n • x) :=
  (integralClosure R A).nsmul_mem h n

theorem IsIntegral.zsmul {x : A} (h : IsIntegral R x) (n : ℤ) : IsIntegral R (n • x) :=
  (integralClosure R A).zsmul_mem h n

theorem IsIntegral.multiset_prod {s : Multiset A} (h : ∀ x _ : x ∈ s, IsIntegral R x) : IsIntegral R s.prod :=
  (integralClosure R A).multiset_prod_mem h

theorem IsIntegral.multiset_sum {s : Multiset A} (h : ∀ x _ : x ∈ s, IsIntegral R x) : IsIntegral R s.sum :=
  (integralClosure R A).multiset_sum_mem h

theorem IsIntegral.prod {α : Type _} {s : Finset α} (f : α → A) (h : ∀ x _ : x ∈ s, IsIntegral R (f x)) :
  IsIntegral R (∏x in s, f x) :=
  (integralClosure R A).prod_mem h

theorem IsIntegral.sum {α : Type _} {s : Finset α} (f : α → A) (h : ∀ x _ : x ∈ s, IsIntegral R (f x)) :
  IsIntegral R (∑x in s, f x) :=
  (integralClosure R A).sum_mem h

end 

section IsIntegralClosure

/-- `is_integral_closure A R B` is the characteristic predicate stating `A` is
the integral closure of `R` in `B`,
i.e. that an element of `B` is integral over `R` iff it is an element of (the image of) `A`.
-/
class IsIntegralClosure (A R B : Type _) [CommRingₓ R] [CommSemiringₓ A] [CommRingₓ B] [Algebra R B] [Algebra A B] :
  Prop where 
  algebra_map_injective{} : Function.Injective (algebraMap A B)
  is_integral_iff : ∀ {x : B}, IsIntegral R x ↔ ∃ y, algebraMap A B y = x

instance integralClosure.is_integral_closure (R A : Type _) [CommRingₓ R] [CommRingₓ A] [Algebra R A] :
  IsIntegralClosure (integralClosure R A) R A :=
  ⟨Subtype.coe_injective,
    fun x =>
      ⟨fun h => ⟨⟨x, h⟩, rfl⟩,
        by 
          rintro ⟨⟨_, h⟩, rfl⟩
          exact h⟩⟩

namespace IsIntegralClosure

variable {R A B : Type _} [CommRingₓ R] [CommRingₓ A] [CommRingₓ B]

variable [Algebra R B] [Algebra A B] [IsIntegralClosure A R B]

variable (R) {A} (B)

protected theorem IsIntegral [Algebra R A] [IsScalarTower R A B] (x : A) : IsIntegral R x :=
  (is_integral_algebra_map_iff (algebra_map_injective A R B)).mp$
    show IsIntegral R (algebraMap A B x) from is_integral_iff.mpr ⟨x, rfl⟩

theorem is_integral_algebra [Algebra R A] [IsScalarTower R A B] : Algebra.IsIntegral R A :=
  fun x => IsIntegralClosure.is_integral R B x

variable {R} (A) {B}

/-- If `x : B` is integral over `R`, then it is an element of the integral closure of `R` in `B`. -/
noncomputable def mk' (x : B) (hx : IsIntegral R x) : A :=
  Classical.some (is_integral_iff.mp hx)

@[simp]
theorem algebra_map_mk' (x : B) (hx : IsIntegral R x) : algebraMap A B (mk' A x hx) = x :=
  Classical.some_spec (is_integral_iff.mp hx)

@[simp]
theorem mk'_one (h : IsIntegral R (1 : B) := is_integral_one) : mk' A 1 h = 1 :=
  algebra_map_injective A R B$
    by 
      rw [algebra_map_mk', RingHom.map_one]

@[simp]
theorem mk'_zero (h : IsIntegral R (0 : B) := is_integral_zero) : mk' A 0 h = 0 :=
  algebra_map_injective A R B$
    by 
      rw [algebra_map_mk', RingHom.map_zero]

@[simp]
theorem mk'_add (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
  mk' A (x+y) (is_integral_add hx hy) = mk' A x hx+mk' A y hy :=
  algebra_map_injective A R B$
    by 
      simp only [algebra_map_mk', RingHom.map_add]

@[simp]
theorem mk'_mul (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
  mk' A (x*y) (is_integral_mul hx hy) = mk' A x hx*mk' A y hy :=
  algebra_map_injective A R B$
    by 
      simp only [algebra_map_mk', RingHom.map_mul]

@[simp]
theorem mk'_algebra_map [Algebra R A] [IsScalarTower R A B] (x : R)
  (h : IsIntegral R (algebraMap R B x) := is_integral_algebra_map) :
  IsIntegralClosure.mk' A (algebraMap R B x) h = algebraMap R A x :=
  algebra_map_injective A R B$
    by 
      rw [algebra_map_mk', ←IsScalarTower.algebra_map_apply]

section lift

variable {R} (A B) {S : Type _} [CommRingₓ S] [Algebra R S] [Algebra S B] [IsScalarTower R S B]

variable [Algebra R A] [IsScalarTower R A B] (h : Algebra.IsIntegral R S)

/-- If `B / S / R` is a tower of ring extensions where `S` is integral over `R`,
then `S` maps (uniquely) into an integral closure `B / A / R`. -/
noncomputable def lift : S →ₐ[R] A :=
  { toFun := fun x => mk' A (algebraMap S B x) (IsIntegral.algebra_map (h x)),
    map_one' :=
      by 
        simp only [RingHom.map_one, mk'_one],
    map_zero' :=
      by 
        simp only [RingHom.map_zero, mk'_zero],
    map_add' :=
      fun x y =>
        by 
          simpRw [←mk'_add, RingHom.map_add],
    map_mul' :=
      fun x y =>
        by 
          simpRw [←mk'_mul, RingHom.map_mul],
    commutes' :=
      fun x =>
        by 
          simpRw [←IsScalarTower.algebra_map_apply, mk'_algebra_map] }

@[simp]
theorem algebra_map_lift (x : S) : algebraMap A B (lift A B h x) = algebraMap S B x :=
  algebra_map_mk' _ _ _

end lift

section Equiv

variable (R A B) (A' : Type _) [CommRingₓ A'] [Algebra A' B] [IsIntegralClosure A' R B]

variable [Algebra R A] [Algebra R A'] [IsScalarTower R A B] [IsScalarTower R A' B]

/-- Integral closures are all isomorphic to each other. -/
noncomputable def Equiv : A ≃ₐ[R] A' :=
  AlgEquiv.ofAlgHom (lift _ B (is_integral_algebra R B)) (lift _ B (is_integral_algebra R B))
    (by 
      ext x 
      apply algebra_map_injective A' R B 
      simp )
    (by 
      ext x 
      apply algebra_map_injective A R B 
      simp )

@[simp]
theorem algebra_map_equiv (x : A) : algebraMap A' B (Equiv R A B A' x) = algebraMap A B x :=
  algebra_map_lift _ _ _ _

end Equiv

end IsIntegralClosure

end IsIntegralClosure

section Algebra

open Algebra

variable {R A B S T : Type _}

variable [CommRingₓ R] [CommRingₓ A] [CommRingₓ B] [CommRingₓ S] [CommRingₓ T]

variable [Algebra A B] [Algebra R B] (f : R →+* S) (g : S →+* T)

-- error in RingTheory.IntegralClosure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_integral_trans_aux
(x : B)
{p : polynomial A}
(pmonic : monic p)
(hp : «expr = »(aeval x p, 0)) : is_integral (adjoin R («expr↑ »(«expr $ »(p.map, algebra_map A B).frange) : set B)) x :=
begin
  generalize [ident hS] [":"] [expr «expr = »((«expr↑ »(«expr $ »(p.map, algebra_map A B).frange) : set B), S)],
  have [ident coeffs_mem] [":", expr ∀ i, «expr ∈ »(«expr $ »(p.map, algebra_map A B).coeff i, adjoin R S)] [],
  { intro [ident i],
    by_cases [expr hi, ":", expr «expr = »(«expr $ »(p.map, algebra_map A B).coeff i, 0)],
    { rw [expr hi] [],
      exact [expr subalgebra.zero_mem _] },
    rw ["<-", expr hS] [],
    exact [expr subset_adjoin (coeff_mem_frange _ _ hi)] },
  obtain ["⟨", ident q, ",", ident hq, "⟩", ":", expr «expr∃ , »((q : polynomial (adjoin R S)), «expr = »(q.map (algebra_map (adjoin R S) B), «expr $ »(p.map, algebra_map A B)))],
  { rw ["<-", expr set.mem_range] [],
    exact [expr (polynomial.mem_map_range _).2 (λ i, ⟨⟨_, coeffs_mem i⟩, rfl⟩)] },
  use [expr q],
  split,
  { suffices [ident h] [":", expr (q.map (algebra_map (adjoin R S) B)).monic],
    { refine [expr monic_of_injective _ h],
      exact [expr subtype.val_injective] },
    { rw [expr hq] [],
      exact [expr monic_map _ pmonic] } },
  { convert [] [expr hp] ["using", 1],
    replace [ident hq] [] [":=", expr congr_arg (eval x) hq],
    convert [] [expr hq] ["using", 1]; symmetry; apply [expr eval_map] }
end

variable [Algebra R A] [IsScalarTower R A B]

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R.-/
theorem is_integral_trans (A_int : IsIntegral R A) (x : B) (hx : IsIntegral A x) : IsIntegral R x :=
  by 
    rcases hx with ⟨p, pmonic, hp⟩
    let S : Set B := «expr↑ » (p.map$ algebraMap A B).frange 
    refine' is_integral_of_mem_of_fg (adjoin R (S ∪ {x})) _ _ (subset_adjoin$ Or.inr rfl)
    refine' fg_trans (fg_adjoin_of_finite (Finset.finite_to_set _) fun x hx => _) _
    ·
      rw [Finset.mem_coe, frange, Finset.mem_image] at hx 
      rcases hx with ⟨i, _, rfl⟩
      rw [coeff_map]
      exact is_integral_alg_hom (IsScalarTower.toAlgHom R A B) (A_int _)
    ·
      apply fg_adjoin_singleton_of_integral 
      exact is_integral_trans_aux _ pmonic hp

/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R.-/
theorem Algebra.is_integral_trans (hA : IsIntegral R A) (hB : IsIntegral A B) : IsIntegral R B :=
  fun x => is_integral_trans hA x (hB x)

theorem RingHom.is_integral_trans (hf : f.is_integral) (hg : g.is_integral) : (g.comp f).IsIntegral :=
  @Algebra.is_integral_trans R S T _ _ _ g.to_algebra (g.comp f).toAlgebra f.to_algebra
    (@IsScalarTower.of_algebra_map_eq R S T _ _ _ f.to_algebra g.to_algebra (g.comp f).toAlgebra
      (RingHom.comp_apply g f))
    hf hg

theorem RingHom.is_integral_of_surjective (hf : Function.Surjective f) : f.is_integral :=
  fun x => (hf x).recOn fun y hy => (hy ▸ f.is_integral_map : f.is_integral_elem x)

theorem is_integral_of_surjective (h : Function.Surjective (algebraMap R A)) : IsIntegral R A :=
  (algebraMap R A).is_integral_of_surjective h

/-- If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A` -/
theorem is_integral_tower_bot_of_is_integral (H : Function.Injective (algebraMap A B)) {x : A}
  (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  by 
    rcases h with ⟨p, ⟨hp, hp'⟩⟩
    refine' ⟨p, ⟨hp, _⟩⟩
    rw [IsScalarTower.algebra_map_eq R A B, ←eval₂_map, eval₂_hom, ←RingHom.map_zero (algebraMap A B)] at hp' 
    rw [eval₂_eq_eval_map]
    exact H hp'

theorem RingHom.is_integral_tower_bot_of_is_integral (hg : Function.Injective g) (hfg : (g.comp f).IsIntegral) :
  f.is_integral :=
  fun x =>
    @is_integral_tower_bot_of_is_integral R S T _ _ _ g.to_algebra (g.comp f).toAlgebra f.to_algebra
      (@IsScalarTower.of_algebra_map_eq R S T _ _ _ f.to_algebra g.to_algebra (g.comp f).toAlgebra
        (RingHom.comp_apply g f))
      hg x (hfg (g x))

theorem is_integral_tower_bot_of_is_integral_field {R A B : Type _} [CommRingₓ R] [Field A] [CommRingₓ B] [Nontrivial B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] {x : A} (h : IsIntegral R (algebraMap A B x)) :
  IsIntegral R x :=
  is_integral_tower_bot_of_is_integral (algebraMap A B).Injective h

theorem RingHom.is_integral_elem_of_is_integral_elem_comp {x : T} (h : (g.comp f).IsIntegralElem x) :
  g.is_integral_elem x :=
  let ⟨p, ⟨hp, hp'⟩⟩ := h
  ⟨p.map f, monic_map f hp,
    by 
      rwa [←eval₂_map] at hp'⟩

theorem RingHom.is_integral_tower_top_of_is_integral (h : (g.comp f).IsIntegral) : g.is_integral :=
  fun x => RingHom.is_integral_elem_of_is_integral_elem_comp f g (h x)

/-- If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`. -/
theorem is_integral_tower_top_of_is_integral {x : B} (h : IsIntegral R x) : IsIntegral A x :=
  by 
    rcases h with ⟨p, ⟨hp, hp'⟩⟩
    refine' ⟨p.map (algebraMap R A), ⟨monic_map (algebraMap R A) hp, _⟩⟩
    rw [IsScalarTower.algebra_map_eq R A B, ←eval₂_map] at hp' 
    exact hp'

theorem RingHom.is_integral_quotient_of_is_integral {I : Ideal S} (hf : f.is_integral) :
  (Ideal.quotientMap I f le_rfl).IsIntegral :=
  by 
    rintro ⟨x⟩
    obtain ⟨p, ⟨p_monic, hpx⟩⟩ := hf x 
    refine' ⟨p.map (Ideal.Quotient.mk _), ⟨monic_map _ p_monic, _⟩⟩
    simpa only [hom_eval₂, eval₂_map] using congr_argₓ (Ideal.Quotient.mk I) hpx

theorem is_integral_quotient_of_is_integral {I : Ideal A} (hRA : IsIntegral R A) :
  IsIntegral (I.comap (algebraMap R A)).Quotient I.quotient :=
  (algebraMap R A).is_integral_quotient_of_is_integral hRA

-- error in RingTheory.IntegralClosure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_integral_quotient_map_iff
{I : ideal S} : «expr ↔ »((ideal.quotient_map I f le_rfl).is_integral, ((ideal.quotient.mk I).comp f : «expr →+* »(R, I.quotient)).is_integral) :=
begin
  let [ident g] [] [":=", expr ideal.quotient.mk (I.comap f)],
  have [] [] [":=", expr ideal.quotient_map_comp_mk le_rfl],
  refine [expr ⟨λ h, _, λ h, ring_hom.is_integral_tower_top_of_is_integral g _ «expr ▸ »(this, h)⟩],
  refine [expr «expr ▸ »(this, ring_hom.is_integral_trans g (ideal.quotient_map I f le_rfl) _ h)],
  exact [expr ring_hom.is_integral_of_surjective g ideal.quotient.mk_surjective]
end

-- error in RingTheory.IntegralClosure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the integral extension `R → S` is injective, and `S` is a field, then `R` is also a field. -/
theorem is_field_of_is_integral_of_is_field
{R S : Type*}
[comm_ring R]
[is_domain R]
[comm_ring S]
[is_domain S]
[algebra R S]
(H : is_integral R S)
(hRS : function.injective (algebra_map R S))
(hS : is_field S) : is_field R :=
begin
  refine [expr ⟨⟨0, 1, zero_ne_one⟩, mul_comm, λ a ha, _⟩],
  obtain ["⟨", ident a_inv, ",", ident ha_inv, "⟩", ":=", expr hS.mul_inv_cancel (λ
    h, ha (hRS (trans h (ring_hom.map_zero _).symm)))],
  obtain ["⟨", ident p, ",", ident p_monic, ",", ident hp, "⟩", ":=", expr H a_inv],
  use [expr «expr- »(«expr∑ in , »((i : exprℕ()), finset.range p.nat_degree, «expr * »(p.coeff i, «expr ^ »(a, «expr - »(«expr - »(p.nat_degree, i), 1)))))],
  have [ident hq] [":", expr «expr = »(«expr∑ in , »((i : exprℕ()), finset.range «expr + »(p.nat_degree, 1), «expr * »(p.coeff i, «expr ^ »(a, «expr - »(p.nat_degree, i)))), 0)] [],
  { apply [expr (algebra_map R S).injective_iff.mp hRS],
    have [ident a_inv_ne_zero] [":", expr «expr ≠ »(a_inv, 0)] [":=", expr right_ne_zero_of_mul (mt ha_inv.symm.trans one_ne_zero)],
    refine [expr (mul_eq_zero.mp _).resolve_right (pow_ne_zero p.nat_degree a_inv_ne_zero)],
    rw ["[", expr eval₂_eq_sum_range, "]"] ["at", ident hp],
    rw ["[", expr ring_hom.map_sum, ",", expr finset.sum_mul, "]"] [],
    refine [expr (finset.sum_congr rfl (λ i hi, _)).trans hp],
    rw ["[", expr ring_hom.map_mul, ",", expr mul_assoc, "]"] [],
    congr,
    have [] [":", expr «expr = »(«expr ^ »(a_inv, p.nat_degree), «expr * »(«expr ^ »(a_inv, «expr - »(p.nat_degree, i)), «expr ^ »(a_inv, i)))] [],
    { rw ["[", "<-", expr pow_add a_inv, ",", expr tsub_add_cancel_of_le (nat.le_of_lt_succ (finset.mem_range.mp hi)), "]"] [] },
    rw ["[", expr ring_hom.map_pow, ",", expr this, ",", "<-", expr mul_assoc, ",", "<-", expr mul_pow, ",", expr ha_inv, ",", expr one_pow, ",", expr one_mul, "]"] [] },
  rw ["[", expr finset.sum_range_succ_comm, ",", expr p_monic.coeff_nat_degree, ",", expr one_mul, ",", expr tsub_self, ",", expr pow_zero, ",", expr add_eq_zero_iff_eq_neg, ",", expr eq_comm, "]"] ["at", ident hq],
  rw ["[", expr mul_comm, ",", "<-", expr neg_mul_eq_neg_mul, ",", expr finset.sum_mul, "]"] [],
  convert [] [expr hq] ["using", 2],
  refine [expr finset.sum_congr rfl (λ i hi, _)],
  have [] [":", expr «expr ≤ »(1, «expr - »(p.nat_degree, i))] [":=", expr le_tsub_of_add_le_left (finset.mem_range.mp hi)],
  rw ["[", expr mul_assoc, ",", "<-", expr pow_succ', ",", expr tsub_add_cancel_of_le this, "]"] []
end

end Algebra

theorem integral_closure_idem {R : Type _} {A : Type _} [CommRingₓ R] [CommRingₓ A] [Algebra R A] :
  integralClosure (integralClosure R A : Set A) A = ⊥ :=
  eq_bot_iff.2$
    fun x hx =>
      Algebra.mem_bot.2
        ⟨⟨x, @is_integral_trans _ _ _ _ _ _ _ _ (integralClosure R A).Algebra _ integralClosure.is_integral x hx⟩, rfl⟩

section IsDomain

variable {R S : Type _} [CommRingₓ R] [CommRingₓ S] [IsDomain S] [Algebra R S]

instance : IsDomain (integralClosure R S) :=
  inferInstance

end IsDomain

