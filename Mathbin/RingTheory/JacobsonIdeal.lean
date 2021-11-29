import Mathbin.RingTheory.Ideal.Quotient 
import Mathbin.RingTheory.Polynomial.Basic

/-!
# Jacobson radical

The Jacobson radical of a ring `R` is defined to be the intersection of all maximal ideals of `R`.
This is similar to how the nilradical is equal to the intersection of all prime ideals of `R`.

We can extend the idea of the nilradical to ideals of `R`,
by letting the radical of an ideal `I` be the intersection of prime ideals containing `I`.
Under this extension, the original nilradical is the radical of the zero ideal `⊥`.
Here we define the Jacobson radical of an ideal `I` in a similar way,
as the intersection of maximal ideals containing `I`.

## Main definitions

Let `R` be a commutative ring, and `I` be an ideal of `R`

* `jacobson I` is the jacobson radical, i.e. the infimum of all maximal ideals containing I.

* `is_local I` is the proposition that the jacobson radical of `I` is itself a maximal ideal

## Main statements

* `mem_jacobson_iff` gives a characterization of members of the jacobson of I

* `is_local_of_is_maximal_radical`: if the radical of I is maximal then so is the jacobson radical

## Tags

Jacobson, Jacobson radical, Local Ideal

-/


universe u v

namespace Ideal

variable {R : Type u} [CommRingₓ R] {I : Ideal R}

variable {S : Type v} [CommRingₓ S]

section Jacobson

/-- The Jacobson radical of `I` is the infimum of all maximal ideals containing `I`. -/
def jacobson (I : Ideal R) : Ideal R :=
  Inf { J:Ideal R | I ≤ J ∧ is_maximal J }

theorem le_jacobson : I ≤ jacobson I :=
  fun x hx => mem_Inf.mpr fun J hJ => hJ.left hx

@[simp]
theorem jacobson_idem : jacobson (jacobson I) = jacobson I :=
  le_antisymmₓ (Inf_le_Inf fun J hJ => ⟨Inf_le hJ, hJ.2⟩) le_jacobson

theorem radical_le_jacobson : radical I ≤ jacobson I :=
  le_Inf fun J hJ => (radical_eq_Inf I).symm ▸ Inf_le ⟨hJ.left, is_maximal.is_prime hJ.right⟩

theorem eq_radical_of_eq_jacobson : jacobson I = I → radical I = I :=
  fun h => le_antisymmₓ (le_transₓ radical_le_jacobson (le_of_eqₓ h)) le_radical

@[simp]
theorem jacobson_top : jacobson (⊤ : Ideal R) = ⊤ :=
  eq_top_iff.2 le_jacobson

@[simp]
theorem jacobson_eq_top_iff : jacobson I = ⊤ ↔ I = ⊤ :=
  ⟨fun H =>
      Classical.by_contradiction$
        fun hi =>
          let ⟨M, hm, him⟩ := exists_le_maximal I hi 
          lt_top_iff_ne_top.1
            (lt_of_le_of_ltₓ (show jacobson I ≤ M from Inf_le ⟨him, hm⟩)$ lt_top_iff_ne_top.2 hm.ne_top) H,
    fun H => eq_top_iff.2$ le_Inf$ fun J ⟨hij, hj⟩ => H ▸ hij⟩

theorem jacobson_eq_bot : jacobson I = ⊥ → I = ⊥ :=
  fun h => eq_bot_iff.mpr (h ▸ le_jacobson)

theorem jacobson_eq_self_of_is_maximal [H : is_maximal I] : I.jacobson = I :=
  le_antisymmₓ (Inf_le ⟨le_of_eqₓ rfl, H⟩) le_jacobson

instance (priority := 100) jacobson.is_maximal [H : is_maximal I] : is_maximal (jacobson I) :=
  ⟨⟨fun htop => H.1.1 (jacobson_eq_top_iff.1 htop), fun J hJ => H.1.2 _ (lt_of_le_of_ltₓ le_jacobson hJ)⟩⟩

theorem mem_jacobson_iff {x : R} : x ∈ jacobson I ↔ ∀ y, ∃ z, (((x*y)*z)+z) - 1 ∈ I :=
  ⟨fun hx y =>
      Classical.by_cases
        (fun hxy : I⊔span {(x*y)+1} = ⊤ =>
          let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy)
          let ⟨r, hr⟩ := mem_span_singleton.1 hq
          ⟨r,
            by 
              rw [←one_mulₓ r, ←mul_assocₓ, ←add_mulₓ, mul_oneₓ, ←hr, ←hpq, ←neg_sub, add_sub_cancel] <;>
                exact I.neg_mem hpi⟩)
        fun hxy : I⊔span {(x*y)+1} ≠ ⊤ =>
          let ⟨M, hm1, hm2⟩ := exists_le_maximal _ hxy 
          suffices x ∉ M from (this$ mem_Inf.1 hx ⟨le_transₓ le_sup_left hm2, hm1⟩).elim 
          fun hxm =>
            hm1.1.1$
              (eq_top_iff_one _).2$
                add_sub_cancel' (x*y) 1 ▸
                  M.sub_mem (le_sup_right.trans hm2$ mem_span_singleton.2 dvd_rfl) (M.mul_mem_right _ hxm),
    fun hx =>
      mem_Inf.2$
        fun M ⟨him, hm⟩ =>
          Classical.by_contradiction$
            fun hxm =>
              let ⟨y, hy⟩ := hm.exists_inv hxm 
              let ⟨z, hz⟩ := hx (-y)
              hm.1.1$
                (eq_top_iff_one _).2$
                  sub_sub_cancel (((x*-y)*z)+z) 1 ▸
                    M.sub_mem
                      (by 
                        rw [←one_mulₓ z, ←mul_assocₓ, ←add_mulₓ, mul_oneₓ, mul_neg_eq_neg_mul_symm, neg_add_eq_sub,
                          ←neg_sub, neg_mul_eq_neg_mul_symm, neg_mul_eq_mul_neg, mul_commₓ x y, mul_commₓ _ (-z)]
                        rcases hy with ⟨i, hi, df⟩
                        rw [←sub_eq_iff_eq_add.mpr df.symm, sub_sub, add_commₓ, ←sub_sub, sub_self, zero_sub]
                        refine' M.mul_mem_left (-z) ((neg_mem_iff _).mpr hi))
                      (him hz)⟩

theorem exists_mul_sub_mem_of_sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 1 ∈ jacobson I) :
  ∃ s, (r*s) - 1 ∈ I :=
  by 
    cases' mem_jacobson_iff.1 h 1 with s hs 
    use s 
    simpa [sub_mul] using hs

theorem is_unit_of_sub_one_mem_jacobson_bot (r : R) (h : r - 1 ∈ jacobson (⊥ : Ideal R)) : IsUnit r :=
  by 
    cases' exists_mul_sub_mem_of_sub_one_mem_jacobson r h with s hs 
    rw [mem_bot, sub_eq_zero] at hs 
    exact is_unit_of_mul_eq_one _ _ hs

/-- An ideal equals its Jacobson radical iff it is the intersection of a set of maximal ideals.
Allowing the set to include ⊤ is equivalent, and is included only to simplify some proofs. -/
theorem eq_jacobson_iff_Inf_maximal :
  I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀ J _ : J ∈ M, is_maximal J ∨ J = ⊤) ∧ I = Inf M :=
  by 
    use fun hI => ⟨{ J:Ideal R | I ≤ J ∧ J.is_maximal }, ⟨fun _ hJ => Or.inl hJ.right, hI.symm⟩⟩
    rintro ⟨M, hM, hInf⟩
    refine' le_antisymmₓ (fun x hx => _) le_jacobson 
    rw [hInf, mem_Inf]
    intro I hI 
    cases' hM I hI with is_max is_top
    ·
      exact (mem_Inf.1 hx) ⟨le_Inf_iff.1 (le_of_eqₓ hInf) I hI, is_max⟩
    ·
      exact is_top.symm ▸ Submodule.mem_top

theorem eq_jacobson_iff_Inf_maximal' :
  I.jacobson = I ↔ ∃ M : Set (Ideal R), (∀ J _ : J ∈ M K : Ideal R, J < K → K = ⊤) ∧ I = Inf M :=
  eq_jacobson_iff_Inf_maximal.trans
    ⟨fun h =>
        let ⟨M, hM⟩ := h
        ⟨M,
          ⟨fun J hJ K hK => Or.rec_on (hM.1 J hJ) (fun h => h.1.2 K hK) fun h => eq_top_iff.2 (le_of_ltₓ (h ▸ hK)),
            hM.2⟩⟩,
      fun h =>
        let ⟨M, hM⟩ := h
        ⟨M, ⟨fun J hJ => Or.rec_on (Classical.em (J = ⊤)) (fun h => Or.inr h) fun h => Or.inl ⟨⟨h, hM.1 J hJ⟩⟩, hM.2⟩⟩⟩

/-- An ideal `I` equals its Jacobson radical if and only if every element outside `I`
also lies outside of a maximal ideal containing `I`. -/
theorem eq_jacobson_iff_not_mem : I.jacobson = I ↔ ∀ x _ : x ∉ I, ∃ M : Ideal R, (I ≤ M ∧ M.is_maximal) ∧ x ∉ M :=
  by 
    split 
    ·
      intro h x hx 
      erw [←h, mem_Inf] at hx 
      pushNeg  at hx 
      exact hx
    ·
      refine' fun h => le_antisymmₓ (fun x hx => _) le_jacobson 
      contrapose hx 
      erw [mem_Inf]
      pushNeg 
      exact h x hx

-- error in RingTheory.JacobsonIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_jacobson_of_surjective
{f : «expr →+* »(R, S)}
(hf : function.surjective f) : «expr ≤ »(ring_hom.ker f, I) → «expr = »(map f I.jacobson, (map f I).jacobson) :=
begin
  intro [ident h],
  unfold [ident ideal.jacobson] [],
  have [] [":", expr ∀
   J «expr ∈ » {J : ideal R | «expr ∧ »(«expr ≤ »(I, J), J.is_maximal)}, «expr ≤ »(f.ker, J)] [":=", expr λ
   J hJ, le_trans h hJ.left],
  refine [expr trans (map_Inf hf this) (le_antisymm _ _)],
  { refine [expr Inf_le_Inf (λ J hJ, ⟨comap f J, ⟨⟨le_comap_of_map_le hJ.1, _⟩, map_comap_of_surjective f hf J⟩⟩)],
    haveI [] [":", expr J.is_maximal] [":=", expr hJ.right],
    exact [expr comap_is_maximal_of_surjective f hf] },
  { refine [expr Inf_le_Inf_of_subset_insert_top (λ j hj, hj.rec_on (λ J hJ, _))],
    rw ["<-", expr hJ.2] [],
    cases [expr map_eq_top_or_is_maximal_of_surjective f hf hJ.left.right] ["with", ident htop, ident hmax],
    { exact [expr «expr ▸ »(htop.symm, set.mem_insert «expr⊤»() _)] },
    { exact [expr set.mem_insert_of_mem «expr⊤»() ⟨map_mono hJ.1.1, hmax⟩] } }
end

theorem map_jacobson_of_bijective {f : R →+* S} (hf : Function.Bijective f) : map f I.jacobson = (map f I).jacobson :=
  map_jacobson_of_surjective hf.right (le_transₓ (le_of_eqₓ (f.injective_iff_ker_eq_bot.1 hf.left)) bot_le)

theorem comap_jacobson {f : R →+* S} {K : Ideal S} :
  comap f K.jacobson = Inf (comap f '' { J:Ideal S | K ≤ J ∧ J.is_maximal }) :=
  trans (comap_Inf' f _) Inf_eq_infi.symm

-- error in RingTheory.JacobsonIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comap_jacobson_of_surjective
{f : «expr →+* »(R, S)}
(hf : function.surjective f)
{K : ideal S} : «expr = »(comap f K.jacobson, (comap f K).jacobson) :=
begin
  unfold [ident ideal.jacobson] [],
  refine [expr le_antisymm _ _],
  { refine [expr le_trans (comap_mono (le_of_eq (trans top_inf_eq.symm Inf_insert.symm))) _],
    rw ["[", expr comap_Inf', ",", expr Inf_eq_infi, "]"] [],
    refine [expr infi_le_infi_of_subset (λ J hJ, _)],
    have [] [":", expr «expr = »(comap f (map f J), J)] [":=", expr trans (comap_map_of_surjective f hf J) (le_antisymm (sup_le_iff.2 ⟨le_of_eq rfl, le_trans (comap_mono bot_le) hJ.left⟩) le_sup_left)],
    cases [expr map_eq_top_or_is_maximal_of_surjective _ hf hJ.right] ["with", ident htop, ident hmax],
    { refine [expr ⟨«expr⊤»(), ⟨set.mem_insert «expr⊤»() _, «expr ▸ »(htop, this)⟩⟩] },
    { refine [expr ⟨map f J, ⟨set.mem_insert_of_mem _ ⟨le_map_of_comap_le_of_surjective f hf hJ.1, hmax⟩, this⟩⟩] } },
  { rw [expr comap_Inf] [],
    refine [expr le_infi_iff.2 (λ J, le_infi_iff.2 (λ hJ, _))],
    haveI [] [":", expr J.is_maximal] [":=", expr hJ.right],
    refine [expr Inf_le ⟨comap_mono hJ.left, comap_is_maximal_of_surjective _ hf⟩] }
end

theorem mem_jacobson_bot {x : R} : x ∈ jacobson (⊥ : Ideal R) ↔ ∀ y, IsUnit ((x*y)+1) :=
  ⟨fun hx y =>
      let ⟨z, hz⟩ := (mem_jacobson_iff.1 hx) y 
      is_unit_iff_exists_inv.2
        ⟨z,
          by 
            rwa [add_mulₓ, one_mulₓ, ←sub_eq_zero]⟩,
    fun h =>
      mem_jacobson_iff.mpr
        fun y =>
          let ⟨b, hb⟩ := is_unit_iff_exists_inv.1 (h y)
          ⟨b,
            (Submodule.mem_bot R).2
              (hb ▸
                by 
                  ring)⟩⟩

-- error in RingTheory.JacobsonIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An ideal `I` of `R` is equal to its Jacobson radical if and only if
the Jacobson radical of the quotient ring `R/I` is the zero ideal -/
theorem jacobson_eq_iff_jacobson_quotient_eq_bot : «expr ↔ »(«expr = »(I.jacobson, I), «expr = »(jacobson («expr⊥»() : ideal I.quotient), «expr⊥»())) :=
begin
  have [ident hf] [":", expr function.surjective (quotient.mk I)] [":=", expr submodule.quotient.mk_surjective I],
  split,
  { intro [ident h],
    replace [ident h] [] [":=", expr congr_arg (map (quotient.mk I)) h],
    rw [expr map_jacobson_of_surjective hf (le_of_eq mk_ker)] ["at", ident h],
    simpa [] [] [] [] [] ["using", expr h] },
  { intro [ident h],
    replace [ident h] [] [":=", expr congr_arg (comap (quotient.mk I)) h],
    rw ["[", expr comap_jacobson_of_surjective hf, ",", "<-", expr (quotient.mk I).ker_eq_comap_bot, "]"] ["at", ident h],
    simpa [] [] [] [] [] ["using", expr h] }
end

-- error in RingTheory.JacobsonIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The standard radical and Jacobson radical of an ideal `I` of `R` are equal if and only if
the nilradical and Jacobson radical of the quotient ring `R/I` coincide -/
theorem radical_eq_jacobson_iff_radical_quotient_eq_jacobson_bot : «expr ↔ »(«expr = »(I.radical, I.jacobson), «expr = »(radical («expr⊥»() : ideal I.quotient), jacobson «expr⊥»())) :=
begin
  have [ident hf] [":", expr function.surjective (quotient.mk I)] [":=", expr submodule.quotient.mk_surjective I],
  split,
  { intro [ident h],
    have [] [] [":=", expr congr_arg (map (quotient.mk I)) h],
    rw ["[", expr map_radical_of_surjective hf (le_of_eq mk_ker), ",", expr map_jacobson_of_surjective hf (le_of_eq mk_ker), "]"] ["at", ident this],
    simpa [] [] [] [] [] ["using", expr this] },
  { intro [ident h],
    have [] [] [":=", expr congr_arg (comap (quotient.mk I)) h],
    rw ["[", expr comap_radical, ",", expr comap_jacobson_of_surjective hf, ",", "<-", expr (quotient.mk I).ker_eq_comap_bot, "]"] ["at", ident this],
    simpa [] [] [] [] [] ["using", expr this] }
end

@[mono]
theorem jacobson_mono {I J : Ideal R} : I ≤ J → I.jacobson ≤ J.jacobson :=
  by 
    intro h x hx 
    erw [mem_Inf] at hx⊢
    exact fun K ⟨hK, hK_max⟩ => hx ⟨trans h hK, hK_max⟩

theorem jacobson_radical_eq_jacobson : I.radical.jacobson = I.jacobson :=
  le_antisymmₓ
    (le_transₓ (le_of_eqₓ (congr_argₓ jacobson (radical_eq_Inf I)))
      (Inf_le_Inf fun J hJ => ⟨Inf_le ⟨hJ.1, hJ.2.IsPrime⟩, hJ.2⟩))
    (jacobson_mono le_radical)

end Jacobson

section Polynomial

open Polynomial

-- error in RingTheory.JacobsonIdeal: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem jacobson_bot_polynomial_le_Inf_map_maximal : «expr ≤ »(jacobson («expr⊥»() : ideal (polynomial R)), Inf «expr '' »(map C, {J : ideal R | J.is_maximal})) :=
begin
  refine [expr le_Inf (λ J, exists_imp_distrib.2 (λ j hj, _))],
  haveI [] [":", expr j.is_maximal] [":=", expr hj.1],
  refine [expr trans (jacobson_mono bot_le) (le_of_eq _ : «expr ≤ »(J.jacobson, J))],
  suffices [] [":", expr «expr = »((«expr⊥»() : ideal (polynomial j.quotient)).jacobson, «expr⊥»())],
  { rw ["[", "<-", expr hj.2, ",", expr jacobson_eq_iff_jacobson_quotient_eq_bot, "]"] [],
    replace [ident this] [] [":=", expr congr_arg (map (polynomial_quotient_equiv_quotient_polynomial j).to_ring_hom) this],
    rwa ["[", expr map_jacobson_of_bijective _, ",", expr map_bot, "]"] ["at", ident this],
    exact [expr ring_equiv.bijective (polynomial_quotient_equiv_quotient_polynomial j)] },
  refine [expr eq_bot_iff.2 (λ f hf, _)],
  simpa [] [] [] ["[", expr (λ
   hX, by simpa [] [] [] [] [] ["using", expr congr_arg (λ
     f, coeff f 1) hX] : «expr ≠ »((X : polynomial j.quotient), 0)), "]"] [] ["using", expr eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit (mem_jacobson_bot.1 hf X))]
end

theorem jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : Ideal R) = ⊥) :
  jacobson (⊥ : Ideal (Polynomial R)) = ⊥ :=
  by 
    refine' eq_bot_iff.2 (le_transₓ jacobson_bot_polynomial_le_Inf_map_maximal _)
    refine' fun f hf => (Submodule.mem_bot _).2 (Polynomial.ext fun n => trans _ (coeff_zero n).symm)
    suffices  : f.coeff n ∈ Ideal.jacobson ⊥
    ·
      rwa [h, Submodule.mem_bot] at this 
    exact mem_Inf.2 fun j hj => (mem_map_C_iff.1 ((mem_Inf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n

end Polynomial

section IsLocal

/-- An ideal `I` is local iff its Jacobson radical is maximal. -/
class is_local (I : Ideal R) : Prop where 
  out : is_maximal (jacobson I)

theorem is_local_iff {I : Ideal R} : is_local I ↔ is_maximal (jacobson I) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem is_local_of_is_maximal_radical {I : Ideal R} (hi : is_maximal (radical I)) : is_local I :=
  ⟨have  : radical I = jacobson I :=
      le_antisymmₓ (le_Inf$ fun M ⟨him, hm⟩ => hm.is_prime.radical_le_iff.2 him) (Inf_le ⟨le_radical, hi⟩)
    show is_maximal (jacobson I) from this ▸ hi⟩

theorem is_local.le_jacobson {I J : Ideal R} (hi : is_local I) (hij : I ≤ J) (hj : J ≠ ⊤) : J ≤ jacobson I :=
  let ⟨M, hm, hjm⟩ := exists_le_maximal J hj 
  le_transₓ hjm$ le_of_eqₓ$ Eq.symm$ hi.1.eq_of_le hm.1.1$ Inf_le ⟨le_transₓ hij hjm, hm⟩

theorem is_local.mem_jacobson_or_exists_inv {I : Ideal R} (hi : is_local I) (x : R) :
  x ∈ jacobson I ∨ ∃ y, (y*x) - 1 ∈ I :=
  Classical.by_cases
    (fun h : I⊔span {x} = ⊤ =>
      let ⟨p, hpi, q, hq, hpq⟩ := Submodule.mem_sup.1 ((eq_top_iff_one _).1 h)
      let ⟨r, hr⟩ := mem_span_singleton.1 hq 
      Or.inr
        ⟨r,
          by 
            rw [←hpq, mul_commₓ, ←hr, ←neg_sub, add_sub_cancel] <;> exact I.neg_mem hpi⟩)
    fun h : I⊔span {x} ≠ ⊤ =>
      Or.inl$ le_transₓ le_sup_right (hi.le_jacobson le_sup_left h)$ mem_span_singleton.2$ dvd_refl x

end IsLocal

theorem is_primary_of_is_maximal_radical {I : Ideal R} (hi : is_maximal (radical I)) : is_primary I :=
  have  : radical I = jacobson I :=
    le_antisymmₓ (le_Inf$ fun M ⟨him, hm⟩ => hm.is_prime.radical_le_iff.2 him) (Inf_le ⟨le_radical, hi⟩)
  ⟨ne_top_of_lt$ lt_of_le_of_ltₓ le_radical (lt_top_iff_ne_top.2 hi.1.1),
    fun x y hxy =>
      ((is_local_of_is_maximal_radical hi).mem_jacobson_or_exists_inv y).symm.imp
        (fun ⟨z, hz⟩ =>
          by 
            rw [←mul_oneₓ x, ←sub_sub_cancel (z*y) 1, mul_sub, mul_left_commₓ] <;>
              exact I.sub_mem (I.mul_mem_left _ hxy) (I.mul_mem_left _ hz))
        (this ▸ id)⟩

end Ideal

