import Mathbin.FieldTheory.Adjoin 
import Mathbin.FieldTheory.IsAlgClosed.Basic 
import Mathbin.FieldTheory.Separable 
import Mathbin.RingTheory.IntegralDomain

/-!
# Primitive Element Theorem

In this file we prove the primitive element theorem.

## Main results

- `exists_primitive_element`: a finite separable extension `E / F` has a primitive element, i.e.
  there is an `α : E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.

## Implementation notes

In declaration names, `primitive_element` abbreviates `adjoin_simple_eq_top`:
it stands for the statement `F⟮α⟯ = (⊤ : subalgebra F E)`. We did not add an extra
declaration `is_primitive_element F α := F⟮α⟯ = (⊤ : subalgebra F E)` because this
requires more unfolding without much obvious benefit.

## Tags

primitive element, separable field extension, separable extension, intermediate field, adjoin,
exists_adjoin_simple_eq_top

-/


noncomputable theory

open_locale Classical

open FiniteDimensional Polynomial IntermediateField

namespace Field

section PrimitiveElementFinite

variable(F : Type _)[Field F](E : Type _)[Field E][Algebra F E]

/-! ### Primitive element theorem for finite fields -/


-- error in FieldTheory.PrimitiveElement: ././Mathport/Syntax/Translate/Basic.lean:341:40: in exact: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- **Primitive element theorem** assuming E is finite. -/
theorem exists_primitive_element_of_fintype_top
[fintype E] : «expr∃ , »((α : E), «expr = »(«expr ⟮ , ⟯»(F, [α]), «expr⊤»())) :=
begin
  obtain ["⟨", ident α, ",", ident hα, "⟩", ":=", expr is_cyclic.exists_generator (units E)],
  use [expr α],
  apply [expr eq_top_iff.mpr],
  rintros [ident x, "-"],
  by_cases [expr hx, ":", expr «expr = »(x, 0)],
  { rw [expr hx] [],
    exact [expr «expr ⟮ , ⟯»(F, [α.val]).zero_mem] },
  { obtain ["⟨", ident n, ",", ident hn, "⟩", ":=", expr set.mem_range.mp (hα (units.mk0 x hx))],
    rw [expr show «expr = »(x, «expr ^ »(α, n)), by { norm_cast [],
       rw ["[", expr hn, ",", expr units.coe_mk0, "]"] [] }] [],
    exact [expr pow_mem «expr ⟮ , ⟯»(F, [«expr↑ »(α)]) (mem_adjoin_simple_self F «expr↑ »(α)) n] }
end

-- error in FieldTheory.PrimitiveElement: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- Primitive element theorem for finite dimensional extension of a finite field. -/
theorem exists_primitive_element_of_fintype_bot
[fintype F]
[finite_dimensional F E] : «expr∃ , »((α : E), «expr = »(«expr ⟮ , ⟯»(F, [α]), «expr⊤»())) :=
begin
  haveI [] [":", expr fintype E] [":=", expr fintype_of_fintype F E],
  exact [expr exists_primitive_element_of_fintype_top F E]
end

end PrimitiveElementFinite

/-! ### Primitive element theorem for infinite fields -/


section PrimitiveElementInf

variable{F : Type _}[Field F][Infinite F]{E : Type _}[Field E](ϕ : F →+* E)(α β : E)

theorem primitive_element_inf_aux_exists_c (f g : Polynomial F) :
  ∃ c : F, ∀ α' (_ : α' ∈ (f.map ϕ).roots) β' (_ : β' ∈ (g.map ϕ).roots), -(α' - α) / (β' - β) ≠ ϕ c :=
  by 
    let sf := (f.map ϕ).roots 
    let sg := (g.map ϕ).roots 
    let s := (sf.bind fun α' => sg.map fun β' => -(α' - α) / (β' - β)).toFinset 
    let s' := s.preimage ϕ fun x hx y hy h => ϕ.injective h 
    obtain ⟨c, hc⟩ := Infinite.exists_not_mem_finset s' 
    simpRw [Finset.mem_preimage, Multiset.mem_to_finset, Multiset.mem_bind, Multiset.mem_map]  at hc 
    pushNeg  at hc 
    exact ⟨c, hc⟩

variable(F)[Algebra F E]

-- error in FieldTheory.PrimitiveElement: ././Mathport/Syntax/Translate/Basic.lean:341:40: in suffices: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem primitive_element_inf_aux
[is_separable F E] : «expr∃ , »((γ : E), «expr = »(«expr ⟮ , ⟯»(F, [α, β]), «expr ⟮ , ⟯»(F, [γ]))) :=
begin
  have [ident hα] [] [":=", expr is_separable.is_integral F α],
  have [ident hβ] [] [":=", expr is_separable.is_integral F β],
  let [ident f] [] [":=", expr minpoly F α],
  let [ident g] [] [":=", expr minpoly F β],
  let [ident ιFE] [] [":=", expr algebra_map F E],
  let [ident ιEE'] [] [":=", expr algebra_map E (splitting_field (g.map ιFE))],
  obtain ["⟨", ident c, ",", ident hc, "⟩", ":=", expr primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g],
  let [ident γ] [] [":=", expr «expr + »(α, «expr • »(c, β))],
  suffices [ident β_in_Fγ] [":", expr «expr ∈ »(β, «expr ⟮ , ⟯»(F, [γ]))],
  { use [expr γ],
    apply [expr le_antisymm],
    { rw [expr adjoin_le_iff] [],
      have [ident α_in_Fγ] [":", expr «expr ∈ »(α, «expr ⟮ , ⟯»(F, [γ]))] [],
      { rw ["<-", expr add_sub_cancel α «expr • »(c, β)] [],
        exact [expr «expr ⟮ , ⟯»(F, [γ]).sub_mem (mem_adjoin_simple_self F γ) («expr ⟮ , ⟯»(F, [γ]).to_subalgebra.smul_mem β_in_Fγ c)] },
      exact [expr λ x hx, by cases [expr hx] []; cases [expr hx] []; cases [expr hx] []; assumption] },
    { rw [expr adjoin_le_iff] [],
      change [expr «expr ⊆ »({γ}, _)] [] [],
      rw [expr set.singleton_subset_iff] [],
      have [ident α_in_Fαβ] [":", expr «expr ∈ »(α, «expr ⟮ , ⟯»(F, [α, β]))] [":=", expr subset_adjoin F {α, β} (set.mem_insert α {β})],
      have [ident β_in_Fαβ] [":", expr «expr ∈ »(β, «expr ⟮ , ⟯»(F, [α, β]))] [":=", expr subset_adjoin F {α, β} (set.mem_insert_of_mem α rfl)],
      exact [expr «expr ⟮ , ⟯»(F, [α, β]).add_mem α_in_Fαβ («expr ⟮ , ⟯»(F, [α, β]).smul_mem β_in_Fαβ)] } },
  let [ident p] [] [":=", expr euclidean_domain.gcd ((f.map (algebra_map F «expr ⟮ , ⟯»(F, [γ]))).comp «expr - »(C (adjoin_simple.gen F γ), «expr * »(C «expr↑ »(c), X))) (g.map (algebra_map F «expr ⟮ , ⟯»(F, [γ])))],
  let [ident h] [] [":=", expr euclidean_domain.gcd ((f.map ιFE).comp «expr - »(C γ, «expr * »(C (ιFE c), X))) (g.map ιFE)],
  have [ident map_g_ne_zero] [":", expr «expr ≠ »(g.map ιFE, 0)] [":=", expr map_ne_zero (minpoly.ne_zero hβ)],
  have [ident h_ne_zero] [":", expr «expr ≠ »(h, 0)] [":=", expr mt euclidean_domain.gcd_eq_zero_iff.mp (not_and.mpr (λ
     _, map_g_ne_zero))],
  suffices [ident p_linear] [":", expr «expr = »(p.map (algebra_map «expr ⟮ , ⟯»(F, [γ]) E), «expr * »(C h.leading_coeff, «expr - »(X, C β)))],
  { have [ident finale] [":", expr «expr = »(β, algebra_map «expr ⟮ , ⟯»(F, [γ]) E «expr / »(«expr- »(p.coeff 0), p.coeff 1))] [],
    { rw ["[", expr ring_hom.map_div, ",", expr ring_hom.map_neg, ",", "<-", expr coeff_map, ",", "<-", expr coeff_map, ",", expr p_linear, "]"] [],
      simp [] [] [] ["[", expr mul_sub, ",", expr coeff_C, ",", expr mul_div_cancel_left β (mt leading_coeff_eq_zero.mp h_ne_zero), "]"] [] [] },
    rw [expr finale] [],
    exact [expr subtype.mem «expr / »(«expr- »(p.coeff 0), p.coeff 1)] },
  have [ident h_sep] [":", expr h.separable] [":=", expr separable_gcd_right _ (is_separable.separable F β).map],
  have [ident h_root] [":", expr «expr = »(h.eval β, 0)] [],
  { apply [expr eval_gcd_eq_zero],
    { rw ["[", expr eval_comp, ",", expr eval_sub, ",", expr eval_mul, ",", expr eval_C, ",", expr eval_C, ",", expr eval_X, ",", expr eval_map, ",", "<-", expr aeval_def, ",", "<-", expr algebra.smul_def, ",", expr add_sub_cancel, ",", expr minpoly.aeval, "]"] [] },
    { rw ["[", expr eval_map, ",", "<-", expr aeval_def, ",", expr minpoly.aeval, "]"] [] } },
  have [ident h_splits] [":", expr splits ιEE' h] [":=", expr splits_of_splits_gcd_right ιEE' map_g_ne_zero (splitting_field.splits _)],
  have [ident h_roots] [":", expr ∀ x «expr ∈ » (h.map ιEE').roots, «expr = »(x, ιEE' β)] [],
  { intros [ident x, ident hx],
    rw [expr mem_roots_map h_ne_zero] ["at", ident hx],
    specialize [expr hc «expr - »(ιEE' γ, «expr * »(ιEE' (ιFE c), x)) (begin
        have [ident f_root] [] [":=", expr root_left_of_root_gcd hx],
        rw ["[", expr eval₂_comp, ",", expr eval₂_sub, ",", expr eval₂_mul, ",", expr eval₂_C, ",", expr eval₂_C, ",", expr eval₂_X, ",", expr eval₂_map, "]"] ["at", ident f_root],
        exact [expr (mem_roots_map (minpoly.ne_zero hα)).mpr f_root]
      end)],
    specialize [expr hc x (begin
        rw ["[", expr mem_roots_map (minpoly.ne_zero hβ), ",", "<-", expr eval₂_map, "]"] [],
        exact [expr root_right_of_root_gcd hx]
      end)],
    by_contradiction [ident a],
    apply [expr hc],
    apply [expr (div_eq_iff (sub_ne_zero.mpr a)).mpr],
    simp [] [] ["only"] ["[", expr algebra.smul_def, ",", expr ring_hom.map_add, ",", expr ring_hom.map_mul, ",", expr ring_hom.comp_apply, "]"] [] [],
    ring [] },
  rw ["<-", expr eq_X_sub_C_of_separable_of_root_eq h_sep h_root h_splits h_roots] [],
  transitivity [expr euclidean_domain.gcd (_ : polynomial E) (_ : polynomial E)],
  { dsimp ["only"] ["[", expr p, "]"] [] [],
    convert [] [expr (gcd_map (algebra_map «expr ⟮ , ⟯»(F, [γ]) E)).symm] [] },
  { simpa [] [] [] ["[", expr map_comp, ",", expr map_map, ",", "<-", expr is_scalar_tower.algebra_map_eq, ",", expr h, "]"] [] [] }
end

end PrimitiveElementInf

variable(F E : Type _)[Field F][Field E]

variable[Algebra F E][FiniteDimensional F E][IsSeparable F E]

-- error in FieldTheory.PrimitiveElement: ././Mathport/Syntax/Translate/Basic.lean:341:40: in let: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- Primitive element theorem: a finite separable field extension `E` of `F` has a
  primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.-/
theorem exists_primitive_element : «expr∃ , »((α : E), «expr = »(«expr ⟮ , ⟯»(F, [α]), «expr⊤»())) :=
begin
  rcases [expr is_empty_or_nonempty (fintype F), "with", ident F_inf, "|", "⟨", "⟨", ident F_finite, "⟩", "⟩"],
  { let [ident P] [":", expr intermediate_field F E → exprProp()] [":=", expr λ
     K, «expr∃ , »((α : E), «expr = »(«expr ⟮ , ⟯»(F, [α]), K))],
    have [ident base] [":", expr P «expr⊥»()] [":=", expr ⟨0, adjoin_zero⟩],
    have [ident ih] [":", expr ∀ (K : intermediate_field F E) (x : E), P K → P «expr↑ »(«expr ⟮ , ⟯»(K, [x]))] [],
    { intros [ident K, ident β, ident hK],
      cases [expr hK] ["with", ident α, ident hK],
      rw ["[", "<-", expr hK, ",", expr adjoin_simple_adjoin_simple, "]"] [],
      haveI [] [":", expr infinite F] [":=", expr is_empty_fintype.mp F_inf],
      cases [expr primitive_element_inf_aux F α β] ["with", ident γ, ident hγ],
      exact [expr ⟨γ, hγ.symm⟩] },
    exact [expr induction_on_adjoin P base ih «expr⊤»()] },
  { exactI [expr exists_primitive_element_of_fintype_bot F E] }
end

-- error in FieldTheory.PrimitiveElement: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- Alternative phrasing of primitive element theorem:
a finite separable field extension has a basis `1, α, α^2, ..., α^n`.

See also `exists_primitive_element`. -/ noncomputable def power_basis_of_finite_of_separable : power_basis F E :=
let α := (exists_primitive_element F E).some, pb := adjoin.power_basis (is_separable.is_integral F α) in
have e : «expr = »(«expr ⟮ , ⟯»(F, [α]), «expr⊤»()) := (exists_primitive_element F E).some_spec,
pb.map ((intermediate_field.equiv_of_eq e).trans intermediate_field.top_equiv)

/-- If `E / F` is a finite separable extension, then there are finitely many
embeddings from `E` into `K` that fix `F`, corresponding to the number of
conjugate roots of the primitive element generating `F`. -/
instance  {K : Type _} [Field K] [Algebra F K] : Fintype (E →ₐ[F] K) :=
  PowerBasis.AlgHom.fintype (power_basis_of_finite_of_separable F E)

end Field

@[simp]
theorem AlgHom.card (F E K : Type _) [Field F] [Field E] [Field K] [IsAlgClosed K] [Algebra F E] [FiniteDimensional F E]
  [IsSeparable F E] [Algebra F K] : Fintype.card (E →ₐ[F] K) = finrank F E :=
  (AlgHom.card_of_power_basis (Field.powerBasisOfFiniteOfSeparable F E) (IsSeparable.separable _ _)
        (IsAlgClosed.splits_codomain _)).trans
    (PowerBasis.finrank _).symm

