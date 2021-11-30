import Mathbin.FieldTheory.SplittingField

/-!
# Algebraically Closed Field

In this file we define the typeclass for algebraically closed fields and algebraic closures,
and prove some of their properties.

## Main Definitions

- `is_alg_closed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
polynomial in `k` splits.

- `is_alg_closure k K` is the typeclass saying `K` is an algebraic closure of `k`.

- `is_alg_closed.lift` is a map from an algebraic extension `L` of `K`, into any algebraically
  closed extension of `K`.

- `is_alg_closure.equiv` is a proof that any two algebraic closures of the
  same field are isomorphic.

## TODO

Show that any two algebraic closures are isomorphic

## Tags

algebraic closure, algebraically closed

-/


universe u v w

open_locale Classical BigOperators

open Polynomial

variable (k : Type u) [Field k]

/-- Typeclass for algebraically closed fields.

To show `polynomial.splits p f` for an arbitrary ring homomorphism `f`,
see `is_alg_closed.splits_codomain` and `is_alg_closed.splits_domain`.
-/
class IsAlgClosed : Prop where 
  Splits : ∀ p : Polynomial k, p.splits$ RingHom.id k

/-- Every polynomial splits in the field extension `f : K →+* k` if `k` is algebraically closed.

See also `is_alg_closed.splits_domain` for the case where `K` is algebraically closed.
-/
theorem IsAlgClosed.splits_codomain {k K : Type _} [Field k] [IsAlgClosed k] [Field K] {f : K →+* k}
  (p : Polynomial K) : p.splits f :=
  by 
    convert IsAlgClosed.splits (p.map f)
    simp [splits_map_iff]

/-- Every polynomial splits in the field extension `f : K →+* k` if `K` is algebraically closed.

See also `is_alg_closed.splits_codomain` for the case where `k` is algebraically closed.
-/
theorem IsAlgClosed.splits_domain {k K : Type _} [Field k] [IsAlgClosed k] [Field K] {f : k →+* K} (p : Polynomial k) :
  p.splits f :=
  Polynomial.splits_of_splits_id _$ IsAlgClosed.splits _

namespace IsAlgClosed

variable {k}

theorem exists_root [IsAlgClosed k] (p : Polynomial k) (hp : p.degree ≠ 0) : ∃ x, is_root p x :=
  exists_root_of_splits _ (IsAlgClosed.splits p) hp

theorem exists_pow_nat_eq [IsAlgClosed k] (x : k) {n : ℕ} (hn : 0 < n) : ∃ z, (z^n) = x :=
  by 
    rcases exists_root ((X^n) - C x) _ with ⟨z, hz⟩
    swap
    ·
      rw [degree_X_pow_sub_C hn x]
      exact ne_of_gtₓ (WithBot.coe_lt_coe.2 hn)
    use z 
    simp only [eval_C, eval_X, eval_pow, eval_sub, is_root.def] at hz 
    exact sub_eq_zero.1 hz

theorem exists_eq_mul_self [IsAlgClosed k] (x : k) : ∃ z, x = z*z :=
  by 
    rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
    exact ⟨z, sq z⟩

theorem exists_eval₂_eq_zero_of_injective {R : Type _} [Ringₓ R] [IsAlgClosed k] (f : R →+* k)
  (hf : Function.Injective f) (p : Polynomial R) (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ :=
    exists_root (p.map f)
      (by 
        rwa [degree_map_eq_of_injective hf])
  ⟨x,
    by 
      rwa [eval₂_eq_eval_map, ←is_root]⟩

theorem exists_eval₂_eq_zero {R : Type _} [Field R] [IsAlgClosed k] (f : R →+* k) (p : Polynomial R)
  (hp : p.degree ≠ 0) : ∃ x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective f f.injective p hp

variable (k)

theorem exists_aeval_eq_zero_of_injective {R : Type _} [CommRingₓ R] [IsAlgClosed k] [Algebra R k]
  (hinj : Function.Injective (algebraMap R k)) (p : Polynomial R) (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp

theorem exists_aeval_eq_zero {R : Type _} [Field R] [IsAlgClosed k] [Algebra R k] (p : Polynomial R)
  (hp : p.degree ≠ 0) : ∃ x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero (algebraMap R k) p hp

theorem of_exists_root (H : ∀ p : Polynomial k, p.monic → Irreducible p → ∃ x, p.eval x = 0) : IsAlgClosed k :=
  ⟨fun p =>
      Or.inr$
        fun q hq hqp =>
          have  : Irreducible (q*C (leading_coeff q⁻¹)) :=
            by 
              rw [←coe_norm_unit_of_ne_zero hq.ne_zero]
              exact (associated_normalize _).Irreducible hq 
          let ⟨x, hx⟩ := H (q*C (leading_coeff q⁻¹)) (monic_mul_leading_coeff_inv hq.ne_zero) this 
          degree_mul_leading_coeff_inv q hq.ne_zero ▸ degree_eq_one_of_irreducible_of_root this hx⟩

theorem degree_eq_one_of_irreducible [IsAlgClosed k] {p : Polynomial k} (h_nz : p ≠ 0) (hp : Irreducible p) :
  p.degree = 1 :=
  degree_eq_one_of_irreducible_of_splits h_nz hp (IsAlgClosed.splits_codomain _)

-- error in FieldTheory.IsAlgClosed.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem algebra_map_surjective_of_is_integral
{k K : Type*}
[field k]
[ring K]
[is_domain K]
[hk : is_alg_closed k]
[algebra k K]
(hf : algebra.is_integral k K) : function.surjective (algebra_map k K) :=
begin
  refine [expr λ x, ⟨«expr- »((minpoly k x).coeff 0), _⟩],
  have [ident hq] [":", expr «expr = »((minpoly k x).leading_coeff, 1)] [":=", expr minpoly.monic (hf x)],
  have [ident h] [":", expr «expr = »((minpoly k x).degree, 1)] [":=", expr degree_eq_one_of_irreducible k (minpoly.ne_zero (hf x)) (minpoly.irreducible (hf x))],
  have [] [":", expr «expr = »(aeval x (minpoly k x), 0)] [":=", expr minpoly.aeval k x],
  rw ["[", expr eq_X_add_C_of_degree_eq_one h, ",", expr hq, ",", expr C_1, ",", expr one_mul, ",", expr aeval_add, ",", expr aeval_X, ",", expr aeval_C, ",", expr add_eq_zero_iff_eq_neg, "]"] ["at", ident this],
  exact [expr «expr ▸ »((ring_hom.map_neg (algebra_map k K) ((minpoly k x).coeff 0)).symm, this.symm)]
end

theorem algebra_map_surjective_of_is_integral' {k K : Type _} [Field k] [CommRingₓ K] [IsDomain K] [hk : IsAlgClosed k]
  (f : k →+* K) (hf : f.is_integral) : Function.Surjective f :=
  @algebra_map_surjective_of_is_integral k K _ _ _ _ f.to_algebra hf

theorem algebra_map_surjective_of_is_algebraic {k K : Type _} [Field k] [Ringₓ K] [IsDomain K] [hk : IsAlgClosed k]
  [Algebra k K] (hf : Algebra.IsAlgebraic k K) : Function.Surjective (algebraMap k K) :=
  algebra_map_surjective_of_is_integral ((is_algebraic_iff_is_integral' k).mp hf)

end IsAlgClosed

/-- Typeclass for an extension being an algebraic closure. -/
class IsAlgClosure (K : Type v) [Field K] [Algebra k K] : Prop where 
  alg_closed : IsAlgClosed K 
  algebraic : Algebra.IsAlgebraic k K

theorem is_alg_closure_iff (K : Type v) [Field K] [Algebra k K] :
  IsAlgClosure k K ↔ IsAlgClosed K ∧ Algebra.IsAlgebraic k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

-- error in FieldTheory.IsAlgClosed.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Every element `f` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `K`
has non-empty spectrum:
that is, there is some `c : K` so `f - c • 1` is not invertible.
-/
theorem exists_spectrum_of_is_alg_closed_of_finite_dimensional
(𝕜 : Type*)
[field 𝕜]
[is_alg_closed 𝕜]
{A : Type*}
[nontrivial A]
[ring A]
[algebra 𝕜 A]
[I : finite_dimensional 𝕜 A]
(f : A) : «expr∃ , »((c : 𝕜), «expr¬ »(is_unit «expr - »(f, algebra_map 𝕜 A c))) :=
begin
  obtain ["⟨", ident p, ",", "⟨", ident h_mon, ",", ident h_eval_p, "⟩", "⟩", ":=", expr is_integral_of_noetherian (is_noetherian.iff_fg.2 I) f],
  have [ident nu] [":", expr «expr¬ »(is_unit (aeval f p))] [],
  { rw ["[", "<-", expr aeval_def, "]"] ["at", ident h_eval_p],
    rw [expr h_eval_p] [],
    simp [] [] [] [] [] [] },
  rw ["[", expr eq_prod_roots_of_monic_of_splits_id h_mon (is_alg_closed.splits p), ",", "<-", expr multiset.prod_to_list, ",", expr alg_hom.map_list_prod, "]"] ["at", ident nu],
  replace [ident nu] [] [":=", expr mt list.prod_is_unit nu],
  simp [] [] ["only"] ["[", expr not_forall, ",", expr exists_prop, ",", expr aeval_C, ",", expr multiset.mem_to_list, ",", expr list.mem_map, ",", expr aeval_X, ",", expr exists_exists_and_eq_and, ",", expr multiset.mem_map, ",", expr alg_hom.map_sub, "]"] [] ["at", ident nu],
  exact [expr ⟨nu.some, nu.some_spec.2⟩]
end

namespace lift

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Algebra K L] [Field M] [Algebra K M]
  [IsAlgClosed M] (hL : Algebra.IsAlgebraic K L)

variable (K L M)

include hL

open Zorn Subalgebra AlgHom Function

/-- This structure is used to prove the existence of a homomorphism from any algebraic extension
into an algebraic closure -/
structure subfield_with_hom where 
  Carrier : Subalgebra K L 
  emb : carrier →ₐ[K] M

variable {K L M hL}

namespace SubfieldWithHom

variable {E₁ E₂ E₃ : subfield_with_hom K L M hL}

instance : LE (subfield_with_hom K L M hL) :=
  { le := fun E₁ E₂ => ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x }

noncomputable instance : Inhabited (subfield_with_hom K L M hL) :=
  ⟨{ Carrier := ⊥, emb := (Algebra.ofId K M).comp (Algebra.botEquiv K L).toAlgHom }⟩

theorem le_def : E₁ ≤ E₂ ↔ ∃ h : E₁.carrier ≤ E₂.carrier, ∀ x, E₂.emb (inclusion h x) = E₁.emb x :=
  Iff.rfl

theorem compat (h : E₁ ≤ E₂) : ∀ x, E₂.emb (inclusion h.fst x) = E₁.emb x :=
  by 
    rw [le_def] at h 
    cases h 
    assumption

instance : Preorderₓ (subfield_with_hom K L M hL) :=
  { le := · ≤ ·,
    le_refl :=
      fun E =>
        ⟨le_reflₓ _,
          by 
            simp ⟩,
    le_trans :=
      fun E₁ E₂ E₃ h₁₂ h₂₃ =>
        ⟨le_transₓ h₁₂.fst h₂₃.fst,
          fun _ =>
            by 
              erw [←inclusion_inclusion h₁₂.fst h₂₃.fst, compat, compat]⟩ }

open Lattice

-- error in FieldTheory.IsAlgClosed.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem maximal_subfield_with_hom_chain_bounded
(c : set (subfield_with_hom K L M hL))
(hc : chain ((«expr ≤ »)) c)
(hcn : c.nonempty) : «expr∃ , »((ub : subfield_with_hom K L M hL), ∀ N, «expr ∈ »(N, c) → «expr ≤ »(N, ub)) :=
let ub : subfield_with_hom K L M hL := by haveI [] [":", expr nonempty c] [":=", expr set.nonempty.to_subtype hcn]; exact [expr { carrier := «expr⨆ , »((i : c), (i : subfield_with_hom K L M hL).carrier),
       emb := subalgebra.supr_lift (λ
        i : c, (i : subfield_with_hom K L M hL).carrier) (λ
        i j, let ⟨k, hik, hjk⟩ := directed_on_iff_directed.1 hc.directed_on i j in
        ⟨k, hik.fst, hjk.fst⟩) (λ
        i, (i : subfield_with_hom K L M hL).emb) (begin
          assume [binders (i j h)],
          ext [] [ident x] [],
          cases [expr hc.total i.prop j.prop] ["with", ident hij, ident hji],
          { simp [] [] [] ["[", "<-", expr hij.snd x, "]"] [] [] },
          { erw ["[", expr alg_hom.comp_apply, ",", "<-", expr hji.snd (inclusion h x), ",", expr inclusion_inclusion, ",", expr inclusion_self, ",", expr alg_hom.id_apply x, "]"] [] }
        end) _ rfl }] in
⟨ub, λ
 N
 hN, ⟨(le_supr (λ i : c, (i : subfield_with_hom K L M hL).carrier) ⟨N, hN⟩ : _), begin
    intro [ident x],
    simp [] [] [] ["[", expr ub, "]"] [] [],
    refl
  end⟩⟩

variable (hL M)

theorem exists_maximal_subfield_with_hom : ∃ E : subfield_with_hom K L M hL, ∀ N, E ≤ N → N ≤ E :=
  Zorn.exists_maximal_of_nonempty_chains_bounded maximal_subfield_with_hom_chain_bounded fun _ _ _ => le_transₓ

/-- The maximal `subfield_with_hom`. We later prove that this is equal to `⊤`. -/
noncomputable def maximal_subfield_with_hom : subfield_with_hom K L M hL :=
  Classical.some (exists_maximal_subfield_with_hom M hL)

theorem maximal_subfield_with_hom_is_maximal :
  ∀ N : subfield_with_hom K L M hL, maximal_subfield_with_hom M hL ≤ N → N ≤ maximal_subfield_with_hom M hL :=
  Classical.some_spec (exists_maximal_subfield_with_hom M hL)

-- error in FieldTheory.IsAlgClosed.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem maximal_subfield_with_hom_eq_top : «expr = »((maximal_subfield_with_hom M hL).carrier, «expr⊤»()) :=
begin
  rw ["[", expr eq_top_iff, "]"] [],
  intros [ident x, "_"],
  let [ident p] [] [":=", expr minpoly K x],
  let [ident N] [":", expr subalgebra K L] [":=", expr (maximal_subfield_with_hom M hL).carrier],
  letI [] [":", expr field N] [":=", expr is_field.to_field _ (subalgebra.is_field_of_algebraic N hL)],
  letI [] [":", expr algebra N M] [":=", expr (maximal_subfield_with_hom M hL).emb.to_ring_hom.to_algebra],
  cases [expr is_alg_closed.exists_aeval_eq_zero M (minpoly N x) (ne_of_gt (minpoly.degree_pos ((is_algebraic_iff_is_integral _).1 (algebra.is_algebraic_of_larger_base _ _ hL x))))] ["with", ident y, ident hy],
  let [ident O] [":", expr subalgebra N L] [":=", expr algebra.adjoin N {(x : L)}],
  let [ident larger_emb] [] [":=", expr (adjoin_root.lift_hom (minpoly N x) y hy).comp (alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly N x).to_alg_hom],
  have [ident hNO] [":", expr «expr ≤ »(N, O.restrict_scalars K)] [],
  { intros [ident z, ident hz],
    show [expr «expr ∈ »(algebra_map N L ⟨z, hz⟩, O)],
    exact [expr O.algebra_map_mem _] },
  let [ident O'] [":", expr subfield_with_hom K L M hL] [":=", expr { carrier := O.restrict_scalars K,
     emb := larger_emb.restrict_scalars K }],
  have [ident hO'] [":", expr «expr ≤ »(maximal_subfield_with_hom M hL, O')] [],
  { refine [expr ⟨hNO, _⟩],
    intros [ident z],
    show [expr «expr = »(O'.emb (algebra_map N O z), algebra_map N M z)],
    simp [] [] ["only"] ["[", expr O', ",", expr restrict_scalars_apply, ",", expr alg_hom.commutes, "]"] [] [] },
  refine [expr (maximal_subfield_with_hom_is_maximal M hL O' hO').fst _],
  exact [expr algebra.subset_adjoin (set.mem_singleton x)]
end

end SubfieldWithHom

end lift

namespace IsAlgClosed

variable {K : Type u} [Field K] {L : Type v} {M : Type w} [Field L] [Algebra K L] [Field M] [Algebra K M]
  [IsAlgClosed M] (hL : Algebra.IsAlgebraic K L)

variable (K L M)

include hL

/-- A (random) hom from an algebraic extension of K into an algebraically closed extension of K -/
noncomputable irreducible_def lift : L →ₐ[K] M :=
  (lift.SubfieldWithHom.maximalSubfieldWithHom M hL).emb.comp$
    Eq.recOnₓ (lift.SubfieldWithHom.maximal_subfield_with_hom_eq_top M hL).symm Algebra.toTop

end IsAlgClosed

namespace IsAlgClosure

variable (J : Type _) (K : Type u) [Field J] [Field K] (L : Type v) (M : Type w) [Field L] [Field M] [Algebra K M]
  [IsAlgClosure K M]

attribute [local instance] IsAlgClosure.alg_closed

section 

variable [Algebra K L] [IsAlgClosure K L]

-- error in FieldTheory.IsAlgClosed.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A (random) isomorphism between two algebraic closures of `K`. -/ noncomputable def equiv : «expr ≃ₐ[ ] »(L, K, M) :=
let f : «expr →ₐ[ ] »(L, K, M) := is_alg_closed.lift K L M is_alg_closure.algebraic in
alg_equiv.of_bijective f ⟨ring_hom.injective f.to_ring_hom, begin
   letI [] [":", expr algebra L M] [":=", expr ring_hom.to_algebra f],
   letI [] [":", expr is_scalar_tower K L M] [":=", expr is_scalar_tower.of_algebra_map_eq (by simp [] [] [] ["[", expr ring_hom.algebra_map_to_algebra, "]"] [] [])],
   show [expr function.surjective (algebra_map L M)],
   exact [expr is_alg_closed.algebra_map_surjective_of_is_algebraic (algebra.is_algebraic_of_larger_base K L is_alg_closure.algebraic)]
 end⟩

end 

section EquivOfAlgebraic

variable [Algebra K J] [Algebra J L] [IsAlgClosure J L] [Algebra K L] [IsScalarTower K J L]

-- error in FieldTheory.IsAlgClosed.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An equiv between an algebraic closure of `K` and an algebraic closure of an algebraic
  extension of `K` -/ noncomputable def equiv_of_algebraic (hKJ : algebra.is_algebraic K J) : «expr ≃ₐ[ ] »(L, K, M) :=
begin
  letI [] [":", expr is_alg_closure K L] [":=", expr { alg_closed := by apply_instance,
     algebraic := algebra.is_algebraic_trans hKJ is_alg_closure.algebraic }],
  exact [expr is_alg_closure.equiv _ _ _]
end

end EquivOfAlgebraic

section EquivOfEquiv

variable [Algebra J L] [IsAlgClosure J L]

variable {J K}

-- error in FieldTheory.IsAlgClosed.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Used in the definition of `equiv_of_equiv` -/
noncomputable
def equiv_of_equiv_aux
(hJK : «expr ≃+* »(J, K)) : {e : «expr ≃+* »(L, M) // «expr = »(e.to_ring_hom.comp (algebra_map J L), (algebra_map K M).comp hJK.to_ring_hom)} :=
begin
  letI [] [":", expr algebra K J] [":=", expr ring_hom.to_algebra hJK.symm.to_ring_hom],
  have [] [":", expr algebra.is_algebraic K J] [],
  from [expr λ x, begin
     rw ["[", "<-", expr ring_equiv.symm_apply_apply hJK x, "]"] [],
     exact [expr is_algebraic_algebra_map _]
   end],
  letI [] [":", expr algebra K L] [":=", expr ring_hom.to_algebra ((algebra_map J L).comp (algebra_map K J))],
  letI [] [":", expr is_scalar_tower K J L] [":=", expr is_scalar_tower.of_algebra_map_eq (λ _, rfl)],
  refine [expr ⟨equiv_of_algebraic J K L M this, _⟩],
  ext [] [] [],
  simp [] [] ["only"] ["[", expr ring_equiv.to_ring_hom_eq_coe, ",", expr function.comp_app, ",", expr ring_hom.coe_comp, ",", expr alg_equiv.coe_ring_equiv, ",", expr ring_equiv.coe_to_ring_hom, "]"] [] [],
  conv_lhs [] [] { rw ["[", "<-", expr hJK.symm_apply_apply x, "]"] },
  show [expr «expr = »(equiv_of_algebraic J K L M this (algebra_map K L (hJK x)), _)],
  rw ["[", expr alg_equiv.commutes, "]"] []
end

/-- Algebraic closure of isomorphic fields are isomorphic -/
noncomputable def equiv_of_equiv (hJK : J ≃+* K) : L ≃+* M :=
  equiv_of_equiv_aux L M hJK

@[simp]
theorem equiv_of_equiv_comp_algebra_map (hJK : J ≃+* K) :
  («expr↑ » (equiv_of_equiv L M hJK) : L →+* M).comp (algebraMap J L) = (algebraMap K M).comp hJK :=
  (equiv_of_equiv_aux L M hJK).2

@[simp]
theorem equiv_of_equiv_algebra_map (hJK : J ≃+* K) (j : J) :
  equiv_of_equiv L M hJK (algebraMap J L j) = algebraMap K M (hJK j) :=
  RingHom.ext_iff.1 (equiv_of_equiv_comp_algebra_map L M hJK) j

@[simp]
theorem equiv_of_equiv_symm_algebra_map (hJK : J ≃+* K) (k : K) :
  (equiv_of_equiv L M hJK).symm (algebraMap K M k) = algebraMap J L (hJK.symm k) :=
  (equiv_of_equiv L M hJK).Injective
    (by 
      simp )

@[simp]
theorem equiv_of_equiv_symm_comp_algebra_map (hJK : J ≃+* K) :
  ((equiv_of_equiv L M hJK).symm : M →+* L).comp (algebraMap K M) = (algebraMap J L).comp hJK.symm :=
  RingHom.ext_iff.2 (equiv_of_equiv_symm_algebra_map L M hJK)

end EquivOfEquiv

end IsAlgClosure

