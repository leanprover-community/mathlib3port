import Mathbin.RingTheory.Localization 
import Mathbin.RingTheory.Ideal.Over 
import Mathbin.RingTheory.JacobsonIdeal

/-!
# Jacobson Rings
The following conditions are equivalent for a ring `R`:
1. Every radical ideal `I` is equal to its Jacobson radical
2. Every radical ideal `I` can be written as an intersection of maximal ideals
3. Every prime ideal `I` is equal to its Jacobson radical
Any ring satisfying any of these equivalent conditions is said to be Jacobson.
Some particular examples of Jacobson rings are also proven.
`is_jacobson_quotient` says that the quotient of a Jacobson ring is Jacobson.
`is_jacobson_localization` says the localization of a Jacobson ring to a single element is Jacobson.
`is_jacobson_polynomial_iff_is_jacobson` says polynomials over a Jacobson ring form a Jacobson ring.
## Main definitions
Let `R` be a commutative ring. Jacobson Rings are defined using the first of the above conditions
* `is_jacobson R` is the proposition that `R` is a Jacobson ring. It is a class,
  implemented as the predicate that for any ideal, `I.radical = I` implies `I.jacobson = I`.

## Main statements
* `is_jacobson_iff_prime_eq` is the equivalence between conditions 1 and 3 above.
* `is_jacobson_iff_Inf_maximal` is the equivalence between conditions 1 and 2 above.
* `is_jacobson_of_surjective` says that if `R` is a Jacobson ring and `f : R →+* S` is surjective,
  then `S` is also a Jacobson ring
* `is_jacobson_mv_polynomial` says that multi-variate polynomials over a Jacobson ring are Jacobson.
## Tags
Jacobson, Jacobson Ring
-/


namespace Ideal

open Polynomial

section IsJacobson

variable{R S : Type _}[CommRingₓ R][CommRingₓ S]{I : Ideal R}

/-- A ring is a Jacobson ring if for every radical ideal `I`,
 the Jacobson radical of `I` is equal to `I`.
 See `is_jacobson_iff_prime_eq` and `is_jacobson_iff_Inf_maximal` for equivalent definitions. -/
class is_jacobson(R : Type _)[CommRingₓ R] : Prop where 
  out' : ∀ (I : Ideal R), I.radical = I → I.jacobson = I

theorem is_jacobson_iff {R} [CommRingₓ R] : is_jacobson R ↔ ∀ (I : Ideal R), I.radical = I → I.jacobson = I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem is_jacobson.out {R} [CommRingₓ R] : is_jacobson R → ∀ {I : Ideal R}, I.radical = I → I.jacobson = I :=
  is_jacobson_iff.1

/--  A ring is a Jacobson ring if and only if for all prime ideals `P`,
 the Jacobson radical of `P` is equal to `P`. -/
theorem is_jacobson_iff_prime_eq : is_jacobson R ↔ ∀ (P : Ideal R), is_prime P → P.jacobson = P :=
  by 
    refine' is_jacobson_iff.trans ⟨fun h I hI => h I (is_prime.radical hI), _⟩
    refine' fun h I hI => le_antisymmₓ (fun x hx => _) fun x hx => mem_Inf.mpr fun _ hJ => hJ.left hx 
    rw [←hI, radical_eq_Inf I, mem_Inf]
    intro P hP 
    rw [Set.mem_set_of_eq] at hP 
    erw [mem_Inf] at hx 
    erw [←h P hP.right, mem_Inf]
    exact fun J hJ => hx ⟨le_transₓ hP.left hJ.left, hJ.right⟩

/-- A ring `R` is Jacobson if and only if for every prime ideal `I`,
 `I` can be written as the infimum of some collection of maximal ideals.
 Allowing ⊤ in the set `M` of maximal ideals is equivalent, but makes some proofs cleaner. -/
theorem is_jacobson_iff_Inf_maximal :
  is_jacobson R ↔
    ∀ {I : Ideal R}, I.is_prime → ∃ M : Set (Ideal R), (∀ J (_ : J ∈ M), is_maximal J ∨ J = ⊤) ∧ I = Inf M :=
  ⟨fun H I h => eq_jacobson_iff_Inf_maximal.1 (H.out (is_prime.radical h)),
    fun H => is_jacobson_iff_prime_eq.2 fun P hP => eq_jacobson_iff_Inf_maximal.2 (H hP)⟩

theorem is_jacobson_iff_Inf_maximal' :
  is_jacobson R ↔
    ∀ {I : Ideal R}, I.is_prime → ∃ M : Set (Ideal R), (∀ J (_ : J ∈ M) (K : Ideal R), J < K → K = ⊤) ∧ I = Inf M :=
  ⟨fun H I h => eq_jacobson_iff_Inf_maximal'.1 (H.out (is_prime.radical h)),
    fun H => is_jacobson_iff_prime_eq.2 fun P hP => eq_jacobson_iff_Inf_maximal'.2 (H hP)⟩

theorem radical_eq_jacobson [H : is_jacobson R] (I : Ideal R) : I.radical = I.jacobson :=
  le_antisymmₓ (le_Inf fun J ⟨hJ, hJ_max⟩ => (is_prime.radical_le_iff hJ_max.is_prime).mpr hJ)
    (H.out (radical_idem I) ▸ jacobson_mono le_radical)

/-- Fields have only two ideals, and the condition holds for both of them.  -/
instance (priority := 100)is_jacobson_field {K : Type _} [Field K] : is_jacobson K :=
  ⟨fun I hI =>
      Or.rec_on (eq_bot_or_top I)
        (fun h => le_antisymmₓ (Inf_le ⟨le_of_eqₓ rfl, Eq.symm h ▸ bot_is_maximal⟩) (Eq.symm h ▸ bot_le))
        fun h =>
          by 
            rw [h, jacobson_eq_top_iff]⟩

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_jacobson_of_surjective
[H : is_jacobson R] : «expr∃ , »((f : «expr →+* »(R, S)), function.surjective f) → is_jacobson S :=
begin
  rintros ["⟨", ident f, ",", ident hf, "⟩"],
  rw [expr is_jacobson_iff_Inf_maximal] [],
  intros [ident p, ident hp],
  use [expr «expr '' »(map f, {J : ideal R | «expr ∧ »(«expr ≤ »(comap f p, J), J.is_maximal)})],
  use [expr λ (j) ⟨J, hJ, hmap⟩, «expr ▸ »(hmap, or.symm (map_eq_top_or_is_maximal_of_surjective f hf hJ.right))],
  have [] [":", expr «expr = »(p, map f (comap f p).jacobson)] [],
  from [expr «expr ▸ »((is_jacobson.out' (comap f p) (by rw ["[", "<-", expr comap_radical, ",", expr is_prime.radical hp, "]"] [])).symm, (map_comap_of_surjective f hf p).symm)],
  exact [expr eq.trans this (map_Inf hf (λ (J) ⟨hJ, _⟩, le_trans (ideal.ker_le_comap f) hJ))]
end

instance (priority := 100)is_jacobson_quotient [is_jacobson R] : is_jacobson (Quotientₓ I) :=
  is_jacobson_of_surjective
    ⟨Quotientₓ.mk I,
      by 
        rintro ⟨x⟩ <;> use x <;> rfl⟩

theorem is_jacobson_iso (e : R ≃+* S) : is_jacobson R ↔ is_jacobson S :=
  ⟨fun h => @is_jacobson_of_surjective _ _ _ _ h ⟨(e : R →+* S), e.surjective⟩,
    fun h => @is_jacobson_of_surjective _ _ _ _ h ⟨(e.symm : S →+* R), e.symm.surjective⟩⟩

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_jacobson_of_is_integral [algebra R S] (hRS : algebra.is_integral R S) (hR : is_jacobson R) : is_jacobson S :=
begin
  rw [expr is_jacobson_iff_prime_eq] [],
  introsI [ident P, ident hP],
  by_cases [expr hP_top, ":", expr «expr = »(comap (algebra_map R S) P, «expr⊤»())],
  { simp [] [] [] ["[", expr comap_eq_top_iff.1 hP_top, "]"] [] [] },
  { haveI [] [":", expr nontrivial (comap (algebra_map R S) P).quotient] [":=", expr quotient.nontrivial hP_top],
    rw [expr jacobson_eq_iff_jacobson_quotient_eq_bot] [],
    refine [expr eq_bot_of_comap_eq_bot (is_integral_quotient_of_is_integral hRS) _],
    rw ["[", expr eq_bot_iff, ",", "<-", expr jacobson_eq_iff_jacobson_quotient_eq_bot.1 (is_jacobson_iff_prime_eq.1 hR (comap (algebra_map R S) P) (comap_is_prime _ _)), ",", expr comap_jacobson, "]"] [],
    refine [expr Inf_le_Inf (λ J hJ, _)],
    simp [] [] ["only"] ["[", expr true_and, ",", expr set.mem_image, ",", expr bot_le, ",", expr set.mem_set_of_eq, "]"] [] [],
    haveI [] [":", expr J.is_maximal] [],
    { simpa [] [] [] [] [] ["using", expr hJ] },
    exact [expr exists_ideal_over_maximal_of_is_integral (is_integral_quotient_of_is_integral hRS) J (comap_bot_le_of_injective _ algebra_map_quotient_injective)] }
end

theorem is_jacobson_of_is_integral' (f : R →+* S) (hf : f.is_integral) (hR : is_jacobson R) : is_jacobson S :=
  @is_jacobson_of_is_integral _ _ _ _ f.to_algebra hf hR

end IsJacobson

section Localization

open IsLocalization Submonoid

variable{R S : Type _}[CommRingₓ R][CommRingₓ S]{I : Ideal R}

variable(y : R)[Algebra R S][IsLocalization.Away y S]

theorem disjoint_powers_iff_not_mem (hI : I.radical = I) :
  Disjoint (Submonoid.powers y : Set R) («expr↑ » I) ↔ y ∉ I.1 :=
  by 
    refine' ⟨fun h => Set.disjoint_left.1 h (mem_powers _), fun h => disjoint_iff.mpr (eq_bot_iff.mpr _)⟩
    rintro x ⟨⟨n, rfl⟩, hx'⟩
    rw [←hI] at hx' 
    exact absurd (hI ▸ mem_radical_of_pow_mem hx' : y ∈ I.carrier) h

variable(S)

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its comap.
See `le_rel_iso_of_maximal` for the more general relation isomorphism -/
theorem is_maximal_iff_is_maximal_disjoint
[H : is_jacobson R]
(J : ideal S) : «expr ↔ »(J.is_maximal, «expr ∧ »((comap (algebra_map R S) J).is_maximal, «expr ∉ »(y, ideal.comap (algebra_map R S) J))) :=
begin
  split,
  { refine [expr λ h, ⟨_, λ hy, h.ne_top (ideal.eq_top_of_is_unit_mem _ hy (map_units _ ⟨y, submonoid.mem_powers _⟩))⟩],
    have [ident hJ] [":", expr J.is_prime] [":=", expr is_maximal.is_prime h],
    rw [expr is_prime_iff_is_prime_disjoint (submonoid.powers y)] ["at", ident hJ],
    have [] [":", expr «expr ∉ »(y, (comap (algebra_map R S) J).1)] [":=", expr set.disjoint_left.1 hJ.right (submonoid.mem_powers _)],
    erw ["[", "<-", expr H.out (is_prime.radical hJ.left), ",", expr mem_Inf, "]"] ["at", ident this],
    push_neg ["at", ident this],
    rcases [expr this, "with", "⟨", ident I, ",", ident hI, ",", ident hI', "⟩"],
    convert [] [expr hI.right] [],
    by_cases [expr hJ, ":", expr «expr = »(J, map (algebra_map R S) I)],
    { rw ["[", expr hJ, ",", expr comap_map_of_is_prime_disjoint (powers y) S I (is_maximal.is_prime hI.right), "]"] [],
      rwa [expr disjoint_powers_iff_not_mem y (is_maximal.is_prime hI.right).radical] [] },
    { have [ident hI_p] [":", expr (map (algebra_map R S) I).is_prime] [],
      { refine [expr is_prime_of_is_prime_disjoint (powers y) _ I hI.right.is_prime _],
        rwa [expr disjoint_powers_iff_not_mem y (is_maximal.is_prime hI.right).radical] [] },
      have [] [":", expr «expr ≤ »(J, map (algebra_map R S) I)] [":=", expr «expr ▸ »(map_comap (submonoid.powers y) S J, map_mono hI.left)],
      exact [expr absurd (h.1.2 _ (lt_of_le_of_ne this hJ)) hI_p.1] } },
  { refine [expr λ h, ⟨⟨λ hJ, h.1.ne_top (eq_top_iff.2 _), λ I hI, _⟩⟩],
    { rwa ["[", expr eq_top_iff, ",", "<-", expr (is_localization.order_embedding (powers y) S).le_iff_le, "]"] ["at", ident hJ] },
    { have [] [] [":=", expr congr_arg (map (algebra_map R S)) (h.1.1.2 _ ⟨comap_mono (le_of_lt hI), _⟩)],
      rwa ["[", expr map_comap (powers y) S I, ",", expr map_top, "]"] ["at", ident this],
      refine [expr λ hI', hI.right _],
      rw ["[", "<-", expr map_comap (powers y) S I, ",", "<-", expr map_comap (powers y) S J, "]"] [],
      exact [expr map_mono hI'] } }
end

variable{S}

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y`.
This lemma gives the correspondence in the particular case of an ideal and its map.
See `le_rel_iso_of_maximal` for the more general statement, and the reverse of this implication -/
theorem is_maximal_of_is_maximal_disjoint [is_jacobson R] (I : Ideal R) (hI : I.is_maximal) (hy : y ∉ I) :
  (map (algebraMap R S) I).IsMaximal :=
  by 
    rw [is_maximal_iff_is_maximal_disjoint S y,
      comap_map_of_is_prime_disjoint (powers y) S I (is_maximal.is_prime hI)
        ((disjoint_powers_iff_not_mem y (is_maximal.is_prime hI).radical).2 hy)]
    exact ⟨hI, hy⟩

/-- If `R` is a Jacobson ring, then maximal ideals in the localization at `y`
correspond to maximal ideals in the original ring `R` that don't contain `y` -/
def order_iso_of_maximal [is_jacobson R] : { p : Ideal S // p.is_maximal } ≃o { p : Ideal R // p.is_maximal ∧ y ∉ p } :=
  { toFun := fun p => ⟨Ideal.comap (algebraMap R S) p.1, (is_maximal_iff_is_maximal_disjoint S y p.1).1 p.2⟩,
    invFun := fun p => ⟨Ideal.map (algebraMap R S) p.1, is_maximal_of_is_maximal_disjoint y p.1 p.2.1 p.2.2⟩,
    left_inv := fun J => Subtype.eq (map_comap (powers y) S J),
    right_inv :=
      fun I =>
        Subtype.eq
          (comap_map_of_is_prime_disjoint _ _ I.1 (is_maximal.is_prime I.2.1)
            ((disjoint_powers_iff_not_mem y I.2.1.IsPrime.radical).2 I.2.2)),
    map_rel_iff' :=
      fun I I' =>
        ⟨fun h =>
            show I.val ≤ I'.val from map_comap (powers y) S I.val ▸ map_comap (powers y) S I'.val ▸ Ideal.map_mono h,
          fun h x hx => h hx⟩ }

include y

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `S` is the localization of the Jacobson ring `R` at the submonoid generated by `y : R`, then
`S` is Jacobson. -/ theorem is_jacobson_localization [H : is_jacobson R] : is_jacobson S :=
begin
  rw [expr is_jacobson_iff_prime_eq] [],
  refine [expr λ P' hP', le_antisymm _ le_jacobson],
  obtain ["⟨", ident hP', ",", ident hPM, "⟩", ":=", expr (is_localization.is_prime_iff_is_prime_disjoint (powers y) S P').mp hP'],
  have [ident hP] [] [":=", expr H.out (is_prime.radical hP')],
  refine [expr (le_of_eq (is_localization.map_comap (powers y) S P'.jacobson).symm).trans ((map_mono _).trans (le_of_eq (is_localization.map_comap (powers y) S P')))],
  have [] [":", expr «expr ≤ »(Inf {I : ideal R | «expr ∧ »(«expr ≤ »(comap (algebra_map R S) P', I), «expr ∧ »(I.is_maximal, «expr ∉ »(y, I)))}, comap (algebra_map R S) P')] [],
  { intros [ident x, ident hx],
    have [ident hxy] [":", expr «expr ∈ »(«expr * »(x, y), (comap (algebra_map R S) P').jacobson)] [],
    { rw ["[", expr ideal.jacobson, ",", expr mem_Inf, "]"] [],
      intros [ident J, ident hJ],
      by_cases [expr «expr ∈ »(y, J)],
      { exact [expr J.smul_mem x h] },
      { exact [expr «expr ▸ »(mul_comm y x, J.smul_mem y (mem_Inf.1 hx ⟨hJ.left, ⟨hJ.right, h⟩⟩))] } },
    rw [expr hP] ["at", ident hxy],
    cases [expr hP'.mem_or_mem hxy] ["with", ident hxy, ident hxy],
    { exact [expr hxy] },
    { exact [expr (hPM ⟨submonoid.mem_powers _, hxy⟩).elim] } },
  refine [expr le_trans _ this],
  rw ["[", expr ideal.jacobson, ",", expr comap_Inf', ",", expr Inf_eq_infi, "]"] [],
  refine [expr infi_le_infi_of_subset (λ I hI, ⟨map (algebra_map R S) I, ⟨_, _⟩⟩)],
  { exact [expr ⟨le_trans (le_of_eq (is_localization.map_comap (powers y) S P').symm) (map_mono hI.1), is_maximal_of_is_maximal_disjoint y _ hI.2.1 hI.2.2⟩] },
  { exact [expr is_localization.comap_map_of_is_prime_disjoint _ S I (is_maximal.is_prime hI.2.1) ((disjoint_powers_iff_not_mem y hI.2.1.is_prime.radical).2 hI.2.2)] }
end

end Localization

namespace Polynomial

open Polynomial

section CommRingₓ

variable{R S : Type _}[CommRingₓ R][CommRingₓ S][IsDomain S]

variable{Rₘ Sₘ : Type _}[CommRingₓ Rₘ][CommRingₓ Sₘ]

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `I` is a prime ideal of `polynomial R` and `pX ∈ I` is a non-constant polynomial,
  then the map `R →+* R[x]/I` descends to an integral map when localizing at `pX.leading_coeff`.
  In particular `X` is integral because it satisfies `pX`, and constants are trivially integral,
  so integrality of the entire extension follows by closure under addition and multiplication. -/
theorem is_integral_is_localization_polynomial_quotient
(P : ideal (polynomial R))
(pX : polynomial R)
(hpX : «expr ∈ »(pX, P))
[algebra (P.comap (C : «expr →+* »(R, _))).quotient Rₘ]
[is_localization.away (pX.map (quotient.mk (P.comap C))).leading_coeff Rₘ]
[algebra P.quotient Sₘ]
[is_localization ((submonoid.powers (pX.map (quotient.mk (P.comap C))).leading_coeff).map (quotient_map P C le_rfl) : submonoid P.quotient) Sₘ] : (is_localization.map Sₘ (quotient_map P C le_rfl) (submonoid.powers (pX.map (quotient.mk (P.comap C))).leading_coeff).le_comap_map : «expr →+* »(Rₘ, _)).is_integral :=
begin
  let [ident P'] [":", expr ideal R] [":=", expr P.comap C],
  let [ident M] [":", expr submonoid P'.quotient] [":=", expr submonoid.powers (pX.map (quotient.mk (P.comap C))).leading_coeff],
  let [ident M'] [":", expr submonoid P.quotient] [":=", expr (submonoid.powers (pX.map (quotient.mk (P.comap C))).leading_coeff).map (quotient_map P C le_rfl)],
  let [ident φ] [":", expr «expr →+* »(P'.quotient, P.quotient)] [":=", expr quotient_map P C le_rfl],
  let [ident φ'] [] [":=", expr is_localization.map Sₘ φ M.le_comap_map],
  have [ident hφ'] [":", expr «expr = »(φ.comp (quotient.mk P'), (quotient.mk P).comp C)] [":=", expr rfl],
  intro [ident p],
  obtain ["⟨", "⟨", ident p', ",", "⟨", ident q, ",", ident hq, "⟩", "⟩", ",", ident hp, "⟩", ":=", expr is_localization.surj M' p],
  suffices [] [":", expr φ'.is_integral_elem (algebra_map _ _ p')],
  { obtain ["⟨", ident q', ",", ident hq', ",", ident rfl, "⟩", ":=", expr hq],
    obtain ["⟨", ident q'', ",", ident hq'', "⟩", ":=", expr is_unit_iff_exists_inv'.1 (is_localization.map_units Rₘ (⟨q', hq'⟩ : M))],
    refine [expr φ'.is_integral_of_is_integral_mul_unit p (algebra_map _ _ (φ q')) q'' _ «expr ▸ »(hp.symm, this)],
    convert [] [expr trans (trans (φ'.map_mul _ _).symm (congr_arg φ' hq'')) φ'.map_one] ["using", 2],
    rw ["[", "<-", expr φ'.comp_apply, ",", expr is_localization.map_comp, ",", expr ring_hom.comp_apply, ",", expr subtype.coe_mk, "]"] [] },
  refine [expr is_integral_of_mem_closure'' «expr '' »((algebra_map _ Sₘ).comp (quotient.mk P), insert X {p | «expr ≤ »(p.degree, 0)}) _ _ _],
  { rintros [ident x, "⟨", ident p, ",", ident hp, ",", ident rfl, "⟩"],
    refine [expr hp.rec_on (λ hy, _) (λ hy, _)],
    { refine [expr «expr ▸ »(hy.symm, φ.is_integral_elem_localization_at_leading_coeff (quotient.mk P X) (pX.map (quotient.mk P')) _ M ⟨1, pow_one _⟩)],
      rwa ["[", expr eval₂_map, ",", expr hφ', ",", "<-", expr hom_eval₂, ",", expr quotient.eq_zero_iff_mem, ",", expr eval₂_C_X, "]"] [] },
    { rw ["[", expr set.mem_set_of_eq, ",", expr degree_le_zero_iff, "]"] ["at", ident hy],
      refine [expr «expr ▸ »(hy.symm, ⟨«expr - »(X, C (algebra_map _ _ (quotient.mk P' (p.coeff 0)))), monic_X_sub_C _, _⟩)],
      simp [] [] ["only"] ["[", expr eval₂_sub, ",", expr eval₂_C, ",", expr eval₂_X, "]"] [] [],
      rw ["[", expr sub_eq_zero, ",", "<-", expr φ'.comp_apply, ",", expr is_localization.map_comp, "]"] [],
      refl } },
  { obtain ["⟨", ident p, ",", ident rfl, "⟩", ":=", expr quotient.mk_surjective p'],
    refine [expr polynomial.induction_on p (λ
      r, «expr $ »(subring.subset_closure, set.mem_image_of_mem _ (or.inr degree_C_le))) (λ
      _ _ h1 h2, _) (λ n _ hr, _)],
    { convert [] [expr subring.add_mem _ h1 h2] [],
      rw ["[", expr ring_hom.map_add, ",", expr ring_hom.map_add, "]"] [] },
    { rw ["[", expr pow_succ X n, ",", expr mul_comm X, ",", "<-", expr mul_assoc, ",", expr ring_hom.map_mul, ",", expr ring_hom.map_mul, "]"] [],
      exact [expr subring.mul_mem _ hr (subring.subset_closure (set.mem_image_of_mem _ (or.inl rfl)))] } }
end

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `f : R → S` descends to an integral map in the localization at `x`,
  and `R` is a Jacobson ring, then the intersection of all maximal ideals in `S` is trivial -/
theorem jacobson_bot_of_integral_localization
{R : Type*}
[comm_ring R]
[is_domain R]
[is_jacobson R]
(Rₘ Sₘ : Type*)
[comm_ring Rₘ]
[comm_ring Sₘ]
(φ : «expr →+* »(R, S))
(hφ : function.injective φ)
(x : R)
(hx : «expr ≠ »(x, 0))
[algebra R Rₘ]
[is_localization.away x Rₘ]
[algebra S Sₘ]
[is_localization ((submonoid.powers x).map φ : submonoid S) Sₘ]
(hφ' : ring_hom.is_integral (is_localization.map Sₘ φ (submonoid.powers x).le_comap_map : «expr →+* »(Rₘ, Sₘ))) : «expr = »((«expr⊥»() : ideal S).jacobson, («expr⊥»() : ideal S)) :=
begin
  have [ident hM] [":", expr «expr ≤ »(((submonoid.powers x).map φ : submonoid S), non_zero_divisors S)] [":=", expr φ.map_le_non_zero_divisors_of_injective hφ (powers_le_non_zero_divisors_of_no_zero_divisors hx)],
  letI [] [":", expr is_domain Sₘ] [":=", expr is_localization.is_domain_of_le_non_zero_divisors _ hM],
  let [ident φ'] [":", expr «expr →+* »(Rₘ, Sₘ)] [":=", expr is_localization.map _ φ (submonoid.powers x).le_comap_map],
  suffices [] [":", expr ∀ I : ideal Sₘ, I.is_maximal → (I.comap (algebra_map S Sₘ)).is_maximal],
  { have [ident hϕ'] [":", expr «expr = »(comap (algebra_map S Sₘ) («expr⊥»() : ideal Sₘ), («expr⊥»() : ideal S))] [],
    { rw ["[", "<-", expr ring_hom.ker_eq_comap_bot, ",", "<-", expr ring_hom.injective_iff_ker_eq_bot, "]"] [],
      exact [expr is_localization.injective Sₘ hM] },
    have [ident hSₘ] [":", expr is_jacobson Sₘ] [":=", expr is_jacobson_of_is_integral' φ' hφ' (is_jacobson_localization x)],
    refine [expr eq_bot_iff.mpr (le_trans _ (le_of_eq hϕ'))],
    rw ["[", "<-", expr hSₘ.out radical_bot_of_is_domain, ",", expr comap_jacobson, "]"] [],
    exact [expr Inf_le_Inf (λ j hj, ⟨bot_le, let ⟨J, hJ⟩ := hj in «expr ▸ »(hJ.2, this J hJ.1.2)⟩)] },
  introsI [ident I, ident hI],
  haveI [] [":", expr (I.comap (algebra_map S Sₘ)).is_prime] [":=", expr comap_is_prime _ I],
  haveI [] [":", expr (I.comap φ').is_prime] [":=", expr comap_is_prime φ' I],
  haveI [] [":", expr («expr⊥»() : ideal (I.comap (algebra_map S Sₘ)).quotient).is_prime] [":=", expr bot_prime],
  have [ident hcomm] [":", expr «expr = »(φ'.comp (algebra_map R Rₘ), (algebra_map S Sₘ).comp φ)] [":=", expr is_localization.map_comp _],
  let [ident f] [] [":=", expr quotient_map (I.comap (algebra_map S Sₘ)) φ le_rfl],
  let [ident g] [] [":=", expr quotient_map I (algebra_map S Sₘ) le_rfl],
  have [] [] [":=", expr is_maximal_comap_of_is_integral_of_is_maximal' φ' hφ' I (by convert [] [expr hI] []; casesI [expr _inst_4] []; refl)],
  have [] [] [":=", expr ((is_maximal_iff_is_maximal_disjoint Rₘ x _).1 this).left],
  have [] [":", expr ((I.comap (algebra_map S Sₘ)).comap φ).is_maximal] [],
  { rwa ["[", expr comap_comap, ",", expr hcomm, ",", "<-", expr comap_comap, "]"] ["at", ident this] },
  rw ["<-", expr bot_quotient_is_maximal_iff] ["at", ident this, "⊢"],
  refine [expr is_maximal_of_is_integral_of_is_maximal_comap' f _ «expr⊥»() «expr ▸ »((eq_bot_iff.2 (comap_bot_le_of_injective f quotient_map_injective)).symm, this)],
  exact [expr f.is_integral_tower_bot_of_is_integral g quotient_map_injective «expr ▸ »((comp_quotient_map_eq_of_comp_eq hcomm I).symm, ring_hom.is_integral_trans _ _ (ring_hom.is_integral_of_surjective _ (is_localization.surjective_quotient_map_of_maximal_of_localization (submonoid.powers x) Rₘ (by rwa ["[", expr comap_comap, ",", expr hcomm, ",", "<-", expr bot_quotient_is_maximal_iff, "]"] []))) (ring_hom.is_integral_quotient_of_is_integral _ hφ'))]
end

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Used to bootstrap the proof of `is_jacobson_polynomial_iff_is_jacobson`.
  That theorem is more general and should be used instead of this one. -/
private
theorem is_jacobson_polynomial_of_domain
(R : Type*)
[comm_ring R]
[is_domain R]
[hR : is_jacobson R]
(P : ideal (polynomial R))
[is_prime P]
(hP : ∀ x : R, «expr ∈ »(C x, P) → «expr = »(x, 0)) : «expr = »(P.jacobson, P) :=
begin
  by_cases [expr Pb, ":", expr «expr = »(P, «expr⊥»())],
  { exact [expr «expr ▸ »(Pb.symm, jacobson_bot_polynomial_of_jacobson_bot (hR.out radical_bot_of_is_domain))] },
  { rw [expr jacobson_eq_iff_jacobson_quotient_eq_bot] [],
    haveI [] [":", expr (P.comap (C : «expr →+* »(R, polynomial R))).is_prime] [":=", expr comap_is_prime C P],
    obtain ["⟨", ident p, ",", ident pP, ",", ident p0, "⟩", ":=", expr exists_nonzero_mem_of_ne_bot Pb hP],
    let [ident x] [] [":=", expr (polynomial.map (quotient.mk (comap (C : «expr →+* »(R, _)) P)) p).leading_coeff],
    have [ident hx] [":", expr «expr ≠ »(x, 0)] [":=", expr by rwa ["[", expr ne.def, ",", expr leading_coeff_eq_zero, "]"] []],
    refine [expr jacobson_bot_of_integral_localization (localization.away x) (localization ((submonoid.powers x).map (P.quotient_map C le_rfl) : submonoid P.quotient)) (quotient_map P C le_rfl) quotient_map_injective x hx _],
    convert [] [expr is_integral_is_localization_polynomial_quotient P p pP] [] }
end

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_jacobson_polynomial_of_is_jacobson (hR : is_jacobson R) : is_jacobson (polynomial R) :=
begin
  refine [expr is_jacobson_iff_prime_eq.mpr (λ I, _)],
  introI [ident hI],
  let [ident R'] [":", expr subring I.quotient] [":=", expr ((quotient.mk I).comp C).range],
  let [ident i] [":", expr «expr →+* »(R, R')] [":=", expr ((quotient.mk I).comp C).range_restrict],
  have [ident hi] [":", expr function.surjective (i : R → R')] [":=", expr ((quotient.mk I).comp C).range_restrict_surjective],
  have [ident hi'] [":", expr «expr ≤ »((polynomial.map_ring_hom i : «expr →+* »(polynomial R, polynomial R')).ker, I)] [],
  { refine [expr λ f hf, polynomial_mem_ideal_of_coeff_mem_ideal I f (λ n, _)],
    replace [ident hf] [] [":=", expr congr_arg (λ g : polynomial ((quotient.mk I).comp C).range, g.coeff n) hf],
    change [expr «expr = »((polynomial.map ((quotient.mk I).comp C).range_restrict f).coeff n, 0)] [] ["at", ident hf],
    rw ["[", expr coeff_map, ",", expr subtype.ext_iff, "]"] ["at", ident hf],
    rwa ["[", expr mem_comap, ",", "<-", expr quotient.eq_zero_iff_mem, ",", "<-", expr ring_hom.comp_apply, "]"] [] },
  haveI [] [":", expr (ideal.map (map_ring_hom i) I).is_prime] [":=", expr map_is_prime_of_surjective (map_surjective i hi) hi'],
  suffices [] [":", expr «expr = »((I.map (polynomial.map_ring_hom i)).jacobson, I.map (polynomial.map_ring_hom i))],
  { replace [ident this] [] [":=", expr congr_arg (comap (polynomial.map_ring_hom i)) this],
    rw ["[", "<-", expr map_jacobson_of_surjective _ hi', ",", expr comap_map_of_surjective _ _, ",", expr comap_map_of_surjective _ _, "]"] ["at", ident this],
    refine [expr le_antisymm (le_trans (le_sup_of_le_left le_rfl) (le_trans (le_of_eq this) (sup_le le_rfl hi'))) le_jacobson],
    all_goals { exact [expr polynomial.map_surjective i hi] } },
  exact [expr @is_jacobson_polynomial_of_domain R' _ _ (is_jacobson_of_surjective ⟨i, hi⟩) (map (map_ring_hom i) I) _ (eq_zero_of_polynomial_mem_map_range I)]
end

theorem is_jacobson_polynomial_iff_is_jacobson : is_jacobson (Polynomial R) ↔ is_jacobson R :=
  by 
    refine' ⟨_, is_jacobson_polynomial_of_is_jacobson⟩
    intro H 
    exact
      is_jacobson_of_surjective
        ⟨eval₂_ring_hom (RingHom.id _) 1,
          fun x =>
            ⟨C x,
              by 
                simp only [coe_eval₂_ring_hom, RingHom.id_apply, eval₂_C]⟩⟩

instance  [is_jacobson R] : is_jacobson (Polynomial R) :=
  is_jacobson_polynomial_iff_is_jacobson.mpr ‹is_jacobson R›

end CommRingₓ

section 

variable{R : Type _}[CommRingₓ R][is_jacobson R]

variable(P : Ideal (Polynomial R))[hP : P.is_maximal]

include P hP

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_maximal_comap_C_of_is_maximal
[nontrivial R]
(hP' : ∀ x : R, «expr ∈ »(C x, P) → «expr = »(x, 0)) : is_maximal (comap C P : ideal R) :=
begin
  haveI [ident hp'_prime] [":", expr (P.comap C : ideal R).is_prime] [":=", expr comap_is_prime C P],
  obtain ["⟨", ident m, ",", ident hm, "⟩", ":=", expr submodule.nonzero_mem_of_bot_lt (bot_lt_of_maximal P polynomial_not_is_field)],
  have [] [":", expr «expr ≠ »((m : polynomial R), 0)] [],
  rwa ["[", expr ne.def, ",", expr submodule.coe_eq_zero, "]"] [],
  let [ident φ] [":", expr «expr →+* »((P.comap C : ideal R).quotient, P.quotient)] [":=", expr quotient_map P C le_rfl],
  let [ident M] [":", expr submonoid (P.comap C : ideal R).quotient] [":=", expr submonoid.powers ((m : polynomial R).map (quotient.mk (P.comap C : ideal R))).leading_coeff],
  rw ["<-", expr bot_quotient_is_maximal_iff] [],
  have [ident hp0] [":", expr «expr ≠ »(((m : polynomial R).map (quotient.mk (P.comap C : ideal R))).leading_coeff, 0)] [":=", expr λ
   hp0', «expr $ »(this, map_injective (quotient.mk (P.comap C : ideal R)) ((quotient.mk (P.comap C : ideal R)).injective_iff.2 (λ
      x
      hx, by rwa ["[", expr quotient.eq_zero_iff_mem, ",", expr (by rwa [expr eq_bot_iff] [] : «expr = »((P.comap C : ideal R), «expr⊥»())), "]"] ["at", ident hx])) (by simpa [] [] ["only"] ["[", expr leading_coeff_eq_zero, ",", expr map_zero, "]"] [] ["using", expr hp0']))],
  have [ident hM] [":", expr «expr ∉ »((0 : (P.comap C : ideal R).quotient), M)] [":=", expr λ
   ⟨n, hn⟩, hp0 (pow_eq_zero hn)],
  suffices [] [":", expr («expr⊥»() : ideal (localization M)).is_maximal],
  { rw ["<-", expr is_localization.comap_map_of_is_prime_disjoint M (localization M) «expr⊥»() bot_prime (λ
      x hx, hM «expr ▸ »(hx.2, hx.1))] [],
    refine [expr ((is_maximal_iff_is_maximal_disjoint (localization M) _ _).mp (by rwa [expr map_bot] [])).1],
    swap,
    exact [expr localization.is_localization] },
  let [ident M'] [":", expr submonoid P.quotient] [":=", expr M.map φ],
  have [ident hM'] [":", expr «expr ∉ »((0 : P.quotient), M')] [":=", expr λ
   ⟨z, hz⟩, hM «expr ▸ »(quotient_map_injective (trans hz.2 φ.map_zero.symm), hz.1)],
  haveI [] [":", expr is_domain (localization M')] [":=", expr is_localization.is_domain_localization (le_non_zero_divisors_of_no_zero_divisors hM')],
  suffices [] [":", expr («expr⊥»() : ideal (localization M')).is_maximal],
  { rw [expr le_antisymm bot_le (comap_bot_le_of_injective _ (is_localization.map_injective_of_injective M (localization M) (localization M') quotient_map_injective (le_non_zero_divisors_of_no_zero_divisors hM')))] [],
    refine [expr is_maximal_comap_of_is_integral_of_is_maximal' _ _ «expr⊥»() this],
    apply [expr is_integral_is_localization_polynomial_quotient P _ (submodule.coe_mem m)] },
  rw [expr (map_bot.symm : «expr = »((«expr⊥»() : ideal (localization M')), map (algebra_map P.quotient (localization M')) «expr⊥»()))] [],
  let [ident bot_maximal] [] [":=", expr (bot_quotient_is_maximal_iff _).mpr hP],
  refine [expr map.is_maximal (algebra_map _ _) (localization_map_bijective_of_field hM' _) bot_maximal],
  rwa ["[", "<-", expr quotient.maximal_ideal_iff_is_field_quotient, ",", "<-", expr bot_quotient_is_maximal_iff, "]"] []
end

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Used to bootstrap the more general `quotient_mk_comp_C_is_integral_of_jacobson` -/
private
theorem quotient_mk_comp_C_is_integral_of_jacobson'
[nontrivial R]
(hR : is_jacobson R)
(hP' : ∀
 x : R, «expr ∈ »(C x, P) → «expr = »(x, 0)) : ((quotient.mk P).comp C : «expr →+* »(R, P.quotient)).is_integral :=
begin
  refine [expr (is_integral_quotient_map_iff _).mp _],
  let [ident P'] [":", expr ideal R] [":=", expr P.comap C],
  obtain ["⟨", ident pX, ",", ident hpX, ",", ident hp0, "⟩", ":=", expr exists_nonzero_mem_of_ne_bot (ne_of_lt (bot_lt_of_maximal P polynomial_not_is_field)).symm hP'],
  let [ident M] [":", expr submonoid P'.quotient] [":=", expr submonoid.powers (pX.map (quotient.mk P')).leading_coeff],
  let [ident φ] [":", expr «expr →+* »(P'.quotient, P.quotient)] [":=", expr quotient_map P C le_rfl],
  haveI [ident hp'_prime] [":", expr P'.is_prime] [":=", expr comap_is_prime C P],
  have [ident hM] [":", expr «expr ∉ »((0 : P'.quotient), M)] [":=", expr λ
   ⟨n, hn⟩, «expr $ »(hp0, leading_coeff_eq_zero.mp (pow_eq_zero hn))],
  let [ident M'] [":", expr submonoid P.quotient] [":=", expr M.map (quotient_map P C le_rfl)],
  refine [expr (quotient_map P C le_rfl).is_integral_tower_bot_of_is_integral (algebra_map _ (localization M')) _ _],
  { refine [expr is_localization.injective (localization M') (show «expr ≤ »(M', _), from le_non_zero_divisors_of_no_zero_divisors (λ
       hM', hM _))],
    exact [expr let ⟨z, zM, z0⟩ := hM' in «expr ▸ »(quotient_map_injective (trans z0 φ.map_zero.symm), zM)] },
  { rw ["<-", expr is_localization.map_comp M.le_comap_map] [],
    refine [expr ring_hom.is_integral_trans (algebra_map P'.quotient (localization M)) (is_localization.map _ _ M.le_comap_map) _ _],
    { exact [expr (algebra_map P'.quotient (localization M)).is_integral_of_surjective (localization_map_bijective_of_field hM ((quotient.maximal_ideal_iff_is_field_quotient _).mp (is_maximal_comap_C_of_is_maximal P hP'))).2] },
    { convert [] [expr is_integral_is_localization_polynomial_quotient P pX hpX] [] } }
end

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `R` is a Jacobson ring, and `P` is a maximal ideal of `polynomial R`,
  then `R → (polynomial R)/P` is an integral map. -/
theorem quotient_mk_comp_C_is_integral_of_jacobson : ((quotient.mk P).comp C : «expr →+* »(R, P.quotient)).is_integral :=
begin
  let [ident P'] [":", expr ideal R] [":=", expr P.comap C],
  haveI [] [":", expr P'.is_prime] [":=", expr comap_is_prime C P],
  let [ident f] [":", expr «expr →+* »(polynomial R, polynomial P'.quotient)] [":=", expr polynomial.map_ring_hom (quotient.mk P')],
  have [ident hf] [":", expr function.surjective f] [":=", expr map_surjective (quotient.mk P') quotient.mk_surjective],
  have [ident hPJ] [":", expr «expr = »(P, (P.map f).comap f)] [],
  { rw [expr comap_map_of_surjective _ hf] [],
    refine [expr le_antisymm (le_sup_of_le_left le_rfl) (sup_le le_rfl _)],
    refine [expr λ p hp, polynomial_mem_ideal_of_coeff_mem_ideal P p (λ n, quotient.eq_zero_iff_mem.mp _)],
    simpa [] [] ["only"] ["[", expr coeff_map, ",", expr coe_map_ring_hom, "]"] [] ["using", expr polynomial.ext_iff.mp hp n] },
  refine [expr ring_hom.is_integral_tower_bot_of_is_integral _ _ (injective_quotient_le_comap_map P) _],
  rw ["<-", expr quotient_mk_maps_eq] [],
  refine [expr ring_hom.is_integral_trans _ _ ((quotient.mk P').is_integral_of_surjective quotient.mk_surjective) _],
  apply [expr quotient_mk_comp_C_is_integral_of_jacobson' _ _ (λ x hx, _)],
  any_goals { exact [expr ideal.is_jacobson_quotient] },
  { exact [expr or.rec_on (map_eq_top_or_is_maximal_of_surjective f hf hP) (λ
      h, absurd (trans («expr ▸ »(h, hPJ) : «expr = »(P, comap f «expr⊤»())) comap_top : «expr = »(P, «expr⊤»())) hP.ne_top) id] },
  { apply_instance },
  { obtain ["⟨", ident z, ",", ident rfl, "⟩", ":=", expr quotient.mk_surjective x],
    rwa ["[", expr quotient.eq_zero_iff_mem, ",", expr mem_comap, ",", expr hPJ, ",", expr mem_comap, ",", expr coe_map_ring_hom, ",", expr map_C, "]"] [] }
end

theorem is_maximal_comap_C_of_is_jacobson : (P.comap (C : R →+* Polynomial R)).IsMaximal :=
  by 
    rw [←@mk_ker _ _ P, RingHom.ker_eq_comap_bot, comap_comap]
    exact
      is_maximal_comap_of_is_integral_of_is_maximal' _ (quotient_mk_comp_C_is_integral_of_jacobson P) ⊥
        ((bot_quotient_is_maximal_iff _).mpr hP)

omit P hP

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_C_integral_of_surjective_of_jacobson
{S : Type*}
[field S]
(f : «expr →+* »(polynomial R, S))
(hf : function.surjective f) : (f.comp C).is_integral :=
begin
  haveI [] [":", expr f.ker.is_maximal] [":=", expr f.ker_is_maximal_of_surjective hf],
  let [ident g] [":", expr «expr →+* »(f.ker.quotient, S)] [":=", expr ideal.quotient.lift f.ker f (λ _ h, h)],
  have [ident hfg] [":", expr «expr = »(g.comp (quotient.mk f.ker), f)] [":=", expr ring_hom_ext' rfl rfl],
  rw ["[", "<-", expr hfg, ",", expr ring_hom.comp_assoc, "]"] [],
  refine [expr ring_hom.is_integral_trans _ g (quotient_mk_comp_C_is_integral_of_jacobson f.ker) (g.is_integral_of_surjective _)],
  rw ["[", "<-", expr hfg, "]"] ["at", ident hf],
  exact [expr function.surjective.of_comp hf]
end

end 

end Polynomial

open MvPolynomial RingHom

namespace MvPolynomial

theorem is_jacobson_mv_polynomial_fin {R : Type _} [CommRingₓ R] [H : is_jacobson R] :
  ∀ (n : ℕ), is_jacobson (MvPolynomial (Finₓ n) R)
| 0 =>
  (is_jacobson_iso ((rename_equiv R (Equiv.equivPempty (Finₓ 0))).toRingEquiv.trans (is_empty_ring_equiv R Pempty))).mpr
    H
| n+1 =>
  (is_jacobson_iso (finSuccEquiv R n).toRingEquiv).2
    (polynomial.is_jacobson_polynomial_iff_is_jacobson.2 (is_jacobson_mv_polynomial_fin n))

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- General form of the nullstellensatz for Jacobson rings, since in a Jacobson ring we have
  `Inf {P maximal | P ≥ I} = Inf {P prime | P ≥ I} = I.radical`. Fields are always Jacobson,
  and in that special case this is (most of) the classical Nullstellensatz,
  since `I(V(I))` is the intersection of maximal ideals containing `I`, which is then `I.radical` -/
instance {R : Type*} [comm_ring R] {ι : Type*} [fintype ι] [is_jacobson R] : is_jacobson (mv_polynomial ι R) :=
begin
  haveI [] [] [":=", expr classical.dec_eq ι],
  let [ident e] [] [":=", expr fintype.equiv_fin ι],
  rw [expr is_jacobson_iso (rename_equiv R e).to_ring_equiv] [],
  exact [expr is_jacobson_mv_polynomial_fin _]
end

variable{n : ℕ}

theorem quotient_mk_comp_C_is_integral_of_jacobson {R : Type _} [CommRingₓ R] [is_jacobson R]
  (P : Ideal (MvPolynomial (Finₓ n) R)) [P.is_maximal] :
  ((Quotientₓ.mk P).comp MvPolynomial.c : R →+* P.quotient).IsIntegral :=
  by 
    (
      induction' n with n IH)
    ·
      refine' RingHom.is_integral_of_surjective _ (Function.Surjective.comp quotient.mk_surjective _)
      exact C_surjective (Finₓ 0)
    ·
      rw [←fin_succ_equiv_comp_C_eq_C, ←RingHom.comp_assoc, ←RingHom.comp_assoc, ←quotient_map_comp_mk le_rfl,
        RingHom.comp_assoc Polynomial.c, ←quotient_map_comp_mk le_rfl, RingHom.comp_assoc, RingHom.comp_assoc,
        ←quotient_map_comp_mk le_rfl, ←RingHom.comp_assoc (Quotientₓ.mk _)]
      refine' RingHom.is_integral_trans _ _ _ _
      ·
        refine' RingHom.is_integral_trans _ _ (is_integral_of_surjective _ quotient.mk_surjective) _ 
        refine' RingHom.is_integral_trans _ _ _ _
        ·
          apply (is_integral_quotient_map_iff _).mpr (IH _)
          apply polynomial.is_maximal_comap_C_of_is_jacobson _
          ·
            exact mv_polynomial.is_jacobson_mv_polynomial_fin n
          ·
            apply comap_is_maximal_of_surjective 
            exact (finSuccEquiv R n).symm.Surjective
        ·
          refine' (is_integral_quotient_map_iff _).mpr _ 
          rw [←quotient_map_comp_mk le_rfl]
          refine' RingHom.is_integral_trans _ _ _ ((is_integral_quotient_map_iff _).mpr _)
          ·
            exact RingHom.is_integral_of_surjective _ quotient.mk_surjective
          ·
            apply polynomial.quotient_mk_comp_C_is_integral_of_jacobson _
            ·
              exact mv_polynomial.is_jacobson_mv_polynomial_fin n
            ·
              exact comap_is_maximal_of_surjective _ (finSuccEquiv R n).symm.Surjective
      ·
        refine' (is_integral_quotient_map_iff _).mpr _ 
        refine' RingHom.is_integral_trans _ _ _ (is_integral_of_surjective _ quotient.mk_surjective)
        exact RingHom.is_integral_of_surjective _ (finSuccEquiv R n).symm.Surjective

-- error in RingTheory.Jacobson: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comp_C_integral_of_surjective_of_jacobson
{R : Type*}
[comm_ring R]
[is_jacobson R]
{σ : Type*}
[fintype σ]
{S : Type*}
[field S]
(f : «expr →+* »(mv_polynomial σ R, S))
(hf : function.surjective f) : (f.comp C).is_integral :=
begin
  haveI [] [] [":=", expr classical.dec_eq σ],
  obtain ["⟨", ident e, "⟩", ":=", expr fintype.trunc_equiv_fin σ],
  let [ident f'] [":", expr «expr →+* »(mv_polynomial (fin _) R, S)] [":=", expr f.comp (rename_equiv R e.symm).to_ring_equiv.to_ring_hom],
  have [ident hf'] [":", expr function.surjective f'] [":=", expr function.surjective.comp hf (rename_equiv R e.symm).surjective],
  have [] [":", expr (f'.comp C).is_integral] [],
  { haveI [] [":", expr f'.ker.is_maximal] [":=", expr f'.ker_is_maximal_of_surjective hf'],
    let [ident g] [":", expr «expr →+* »(f'.ker.quotient, S)] [":=", expr ideal.quotient.lift f'.ker f' (λ _ h, h)],
    have [ident hfg] [":", expr «expr = »(g.comp (quotient.mk f'.ker), f')] [":=", expr ring_hom_ext (λ
      r, rfl) (λ i, rfl)],
    rw ["[", "<-", expr hfg, ",", expr ring_hom.comp_assoc, "]"] [],
    refine [expr ring_hom.is_integral_trans _ g (quotient_mk_comp_C_is_integral_of_jacobson f'.ker) (g.is_integral_of_surjective _)],
    rw ["<-", expr hfg] ["at", ident hf'],
    exact [expr function.surjective.of_comp hf'] },
  rw [expr ring_hom.comp_assoc] ["at", ident this],
  convert [] [expr this] [],
  refine [expr ring_hom.ext (λ x, _)],
  exact [expr ((rename_equiv R e.symm).commutes' x).symm]
end

end MvPolynomial

end Ideal

