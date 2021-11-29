import Mathbin.FieldTheory.Normal 
import Mathbin.FieldTheory.PrimitiveElement 
import Mathbin.FieldTheory.Fixed 
import Mathbin.RingTheory.PowerBasis

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `is_galois F E` where `E` is an extension of `F`
- `fixed_field H` where `H : subgroup (E ≃ₐ[F] E)`
- `fixing_subgroup K` where `K : intermediate_field F E`
- `galois_correspondence` where `E/F` is finite dimensional and Galois

## Main results

- `fixing_subgroup_of_fixed_field` : If `E/F` is finite dimensional (but not necessarily Galois)
  then `fixing_subgroup (fixed_field H) = H`
- `fixed_field_of_fixing_subgroup`: If `E/F` is finite dimensional and Galois
  then `fixed_field (fixing_subgroup K) = K`
Together, these two result prove the Galois correspondence

- `is_galois.tfae` : Equivalent characterizations of a Galois extension of finite degree
-/


noncomputable theory

open_locale Classical

open FiniteDimensional AlgEquiv

section 

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

/-- A field extension E/F is galois if it is both separable and normal -/
class IsGalois : Prop where 
  [to_is_separable : IsSeparable F E]
  [to_normal : Normal F E]

variable {F E}

theorem is_galois_iff : IsGalois F E ↔ IsSeparable F E ∧ Normal F E :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => { to_is_separable := h.1, to_normal := h.2 }⟩

attribute [instance] IsGalois.to_is_separable IsGalois.to_normal

variable (F E)

namespace IsGalois

instance self : IsGalois F F :=
  ⟨⟩

variable (F) {E}

theorem integral [IsGalois F E] (x : E) : IsIntegral F x :=
  Normal.is_integral' x

theorem separable [IsGalois F E] (x : E) : (minpoly F x).Separable :=
  IsSeparable.separable F x

theorem splits [IsGalois F E] (x : E) : (minpoly F x).Splits (algebraMap F E) :=
  Normal.splits' x

variable (F E)

instance of_fixed_field (G : Type _) [Groupₓ G] [Fintype G] [MulSemiringAction G E] :
  IsGalois (FixedPoints.subfield G E) E :=
  ⟨⟩

-- error in FieldTheory.Galois: ././Mathport/Syntax/Translate/Basic.lean:341:40: in letI: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem intermediate_field.adjoin_simple.card_aut_eq_finrank
[finite_dimensional F E]
{α : E}
(hα : is_integral F α)
(h_sep : (minpoly F α).separable)
(h_splits : (minpoly F α).splits (algebra_map F «expr ⟮ , ⟯»(F, [α]))) : «expr = »(fintype.card «expr ≃ₐ[ ] »(«expr ⟮ , ⟯»(F, [α]), F, «expr ⟮ , ⟯»(F, [α])), finrank F «expr ⟮ , ⟯»(F, [α])) :=
begin
  letI [] [":", expr fintype «expr →ₐ[ ] »(«expr ⟮ , ⟯»(F, [α]), F, «expr ⟮ , ⟯»(F, [α]))] [":=", expr intermediate_field.fintype_of_alg_hom_adjoin_integral F hα],
  rw [expr intermediate_field.adjoin.finrank hα] [],
  rw ["<-", expr intermediate_field.card_alg_hom_adjoin_integral F hα h_sep h_splits] [],
  exact [expr fintype.card_congr (alg_equiv_equiv_alg_hom F «expr ⟮ , ⟯»(F, [α]))]
end

-- error in FieldTheory.Galois: ././Mathport/Syntax/Translate/Basic.lean:341:40: in let: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem card_aut_eq_finrank
[finite_dimensional F E]
[is_galois F E] : «expr = »(fintype.card «expr ≃ₐ[ ] »(E, F, E), finrank F E) :=
begin
  cases [expr field.exists_primitive_element F E] ["with", ident α, ident hα],
  let [ident iso] [":", expr «expr ≃ₐ[ ] »(«expr ⟮ , ⟯»(F, [α]), F, E)] [":=", expr { to_fun := λ e, e.val,
     inv_fun := λ e, ⟨e, by { rw [expr hα] [], exact [expr intermediate_field.mem_top] }⟩,
     left_inv := λ _, by { ext [] [] [],
       refl },
     right_inv := λ _, rfl,
     map_mul' := λ _ _, rfl,
     map_add' := λ _ _, rfl,
     commutes' := λ _, rfl }],
  have [ident H] [":", expr is_integral F α] [":=", expr is_galois.integral F α],
  have [ident h_sep] [":", expr (minpoly F α).separable] [":=", expr is_galois.separable F α],
  have [ident h_splits] [":", expr (minpoly F α).splits (algebra_map F E)] [":=", expr is_galois.splits F α],
  replace [ident h_splits] [":", expr polynomial.splits (algebra_map F «expr ⟮ , ⟯»(F, [α])) (minpoly F α)] [],
  { have [ident p] [":", expr «expr = »(iso.symm.to_alg_hom.to_ring_hom.comp (algebra_map F E), algebra_map F «expr↥ »(«expr ⟮ , ⟯»(F, [α])))] [],
    { ext [] [] [],
      simp [] [] [] [] [] [] },
    simpa [] [] [] ["[", expr p, "]"] [] ["using", expr polynomial.splits_comp_of_splits (algebra_map F E) iso.symm.to_alg_hom.to_ring_hom h_splits] },
  rw ["<-", expr linear_equiv.finrank_eq iso.to_linear_equiv] [],
  rw ["<-", expr intermediate_field.adjoin_simple.card_aut_eq_finrank F E H h_sep h_splits] [],
  apply [expr fintype.card_congr],
  apply [expr equiv.mk (λ ϕ, iso.trans (trans ϕ iso.symm)) (λ ϕ, iso.symm.trans (trans ϕ iso))],
  { intro [ident ϕ],
    ext1 [] [],
    simp [] [] ["only"] ["[", expr trans_apply, ",", expr apply_symm_apply, "]"] [] [] },
  { intro [ident ϕ],
    ext1 [] [],
    simp [] [] ["only"] ["[", expr trans_apply, ",", expr symm_apply_apply, "]"] [] [] }
end

end IsGalois

end 

section IsGaloisTower

variable (F K E : Type _) [Field F] [Field K] [Field E] {E' : Type _} [Field E'] [Algebra F E']

variable [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

theorem IsGalois.tower_top_of_is_galois [IsGalois F E] : IsGalois K E :=
  { to_is_separable := is_separable_tower_top_of_is_separable F K E, to_normal := Normal.tower_top_of_normal F K E }

variable {F E}

instance (priority := 100) IsGalois.tower_top_intermediate_field (K : IntermediateField F E) [h : IsGalois F E] :
  IsGalois K E :=
  IsGalois.tower_top_of_is_galois F K E

theorem is_galois_iff_is_galois_bot : IsGalois (⊥ : IntermediateField F E) E ↔ IsGalois F E :=
  by 
    split 
    ·
      intro h 
      exact IsGalois.tower_top_of_is_galois (⊥ : IntermediateField F E) F E
    ·
      intro h 
      infer_instance

theorem IsGalois.of_alg_equiv [h : IsGalois F E] (f : E ≃ₐ[F] E') : IsGalois F E' :=
  { to_is_separable := IsSeparable.of_alg_hom F E f.symm, to_normal := Normal.of_alg_equiv f }

theorem AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : IsGalois F E ↔ IsGalois F E' :=
  ⟨fun h =>
      by 
        exact IsGalois.of_alg_equiv f,
    fun h =>
      by 
        exact IsGalois.of_alg_equiv f.symm⟩

theorem is_galois_iff_is_galois_top : IsGalois F (⊤ : IntermediateField F E) ↔ IsGalois F E :=
  IntermediateField.topEquiv.transfer_galois

instance is_galois_bot : IsGalois F (⊥ : IntermediateField F E) :=
  (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)

end IsGaloisTower

section GaloisCorrespondence

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

variable (H : Subgroup (E ≃ₐ[F] E)) (K : IntermediateField F E)

namespace IntermediateField

/-- The intermediate_field fixed by a subgroup -/
def fixed_field : IntermediateField F E :=
  { Carrier := MulAction.FixedPoints H E, zero_mem' := fun g => smul_zero g,
    add_mem' :=
      fun a b hx hy g =>
        by 
          rw [smul_add g a b, hx, hy],
    neg_mem' :=
      fun a hx g =>
        by 
          rw [smul_neg g a, hx],
    one_mem' := fun g => smul_one g,
    mul_mem' :=
      fun a b hx hy g =>
        by 
          rw [smul_mul' g a b, hx, hy],
    inv_mem' :=
      fun a hx g =>
        by 
          rw [smul_inv'' g a, hx],
    algebra_map_mem' := fun a g => commutes g a }

theorem finrank_fixed_field_eq_card [FiniteDimensional F E] : finrank (fixed_field H) E = Fintype.card H :=
  FixedPoints.finrank_eq_card H E

/-- The subgroup fixing an intermediate_field -/
def fixing_subgroup : Subgroup (E ≃ₐ[F] E) :=
  { Carrier := fun ϕ => ∀ x : K, ϕ x = x, one_mem' := fun _ => rfl,
    mul_mem' := fun _ _ hx hy _ => (congr_argₓ _ (hy _)).trans (hx _),
    inv_mem' := fun _ hx _ => (Equiv.symm_apply_eq (to_equiv _)).mpr (hx _).symm }

theorem le_iff_le : K ≤ fixed_field H ↔ H ≤ fixing_subgroup K :=
  ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩

/-- The fixing_subgroup of `K : intermediate_field F E` is isomorphic to `E ≃ₐ[K] E` -/
def fixing_subgroup_equiv : fixing_subgroup K ≃* E ≃ₐ[K] E :=
  { toFun := fun ϕ => of_bijective (AlgHom.mk ϕ (map_one ϕ) (map_mul ϕ) (map_zero ϕ) (map_add ϕ) ϕ.mem) (bijective ϕ),
    invFun :=
      fun ϕ =>
        ⟨of_bijective (AlgHom.mk ϕ ϕ.map_one ϕ.map_mul ϕ.map_zero ϕ.map_add fun r => ϕ.commutes (algebraMap F K r))
            ϕ.bijective,
          ϕ.commutes⟩,
    left_inv :=
      fun _ =>
        by 
          ext 
          rfl,
    right_inv :=
      fun _ =>
        by 
          ext 
          rfl,
    map_mul' :=
      fun _ _ =>
        by 
          ext 
          rfl }

-- error in FieldTheory.Galois: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fixing_subgroup_fixed_field [finite_dimensional F E] : «expr = »(fixing_subgroup (fixed_field H), H) :=
begin
  have [ident H_le] [":", expr «expr ≤ »(H, fixing_subgroup (fixed_field H))] [":=", expr (le_iff_le _ _).mp (le_refl _)],
  suffices [] [":", expr «expr = »(fintype.card H, fintype.card (fixing_subgroup (fixed_field H)))],
  { exact [expr set_like.coe_injective (set.eq_of_inclusion_surjective ((fintype.bijective_iff_injective_and_card (set.inclusion H_le)).mpr ⟨set.inclusion_injective H_le, this⟩).2).symm] },
  apply [expr fintype.card_congr],
  refine [expr (fixed_points.to_alg_hom_equiv H E).trans _],
  refine [expr (alg_equiv_equiv_alg_hom (fixed_field H) E).symm.trans _],
  exact [expr (fixing_subgroup_equiv (fixed_field H)).to_equiv.symm]
end

instance fixed_field.algebra : Algebra K (fixed_field (fixing_subgroup K)) :=
  { smul :=
      fun x y =>
        ⟨x*y,
          fun ϕ =>
            by 
              rw [smul_mul',
                show ϕ • «expr↑ » x = «expr↑ » x by 
                  exact Subtype.mem ϕ x,
                show ϕ • «expr↑ » y = «expr↑ » y by 
                  exact Subtype.mem y ϕ]⟩,
    toFun := fun x => ⟨x, fun ϕ => Subtype.mem ϕ x⟩, map_zero' := rfl, map_add' := fun _ _ => rfl, map_one' := rfl,
    map_mul' := fun _ _ => rfl, commutes' := fun _ _ => mul_commₓ _ _, smul_def' := fun _ _ => rfl }

instance fixed_field.is_scalar_tower : IsScalarTower K (fixed_field (fixing_subgroup K)) E :=
  ⟨fun _ _ _ => mul_assocₓ _ _ _⟩

end IntermediateField

namespace IsGalois

-- error in FieldTheory.Galois: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fixed_field_fixing_subgroup
[finite_dimensional F E]
[h : is_galois F E] : «expr = »(intermediate_field.fixed_field (intermediate_field.fixing_subgroup K), K) :=
begin
  have [ident K_le] [":", expr «expr ≤ »(K, intermediate_field.fixed_field (intermediate_field.fixing_subgroup K))] [":=", expr (intermediate_field.le_iff_le _ _).mpr (le_refl _)],
  suffices [] [":", expr «expr = »(finrank K E, finrank (intermediate_field.fixed_field (intermediate_field.fixing_subgroup K)) E)],
  { exact [expr (intermediate_field.eq_of_le_of_finrank_eq' K_le this).symm] },
  rw ["[", expr intermediate_field.finrank_fixed_field_eq_card, ",", expr fintype.card_congr (intermediate_field.fixing_subgroup_equiv K).to_equiv, "]"] [],
  exact [expr (card_aut_eq_finrank K E).symm]
end

theorem card_fixing_subgroup_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
  Fintype.card (IntermediateField.fixingSubgroup K) = finrank K E :=
  by 
    conv  => toRHS rw [←fixed_field_fixing_subgroup K, IntermediateField.finrank_fixed_field_eq_card]

/-- The Galois correspondence from intermediate fields to subgroups -/
def intermediate_field_equiv_subgroup [FiniteDimensional F E] [IsGalois F E] :
  IntermediateField F E ≃o OrderDual (Subgroup (E ≃ₐ[F] E)) :=
  { toFun := IntermediateField.fixingSubgroup, invFun := IntermediateField.fixedField,
    left_inv := fun K => fixed_field_fixing_subgroup K,
    right_inv := fun H => IntermediateField.fixing_subgroup_fixed_field H,
    map_rel_iff' :=
      fun K L =>
        by 
          rw [←fixed_field_fixing_subgroup L, IntermediateField.le_iff_le, fixed_field_fixing_subgroup L,
            ←OrderDual.dual_le]
          rfl }

/-- The Galois correspondence as a galois_insertion -/
def galois_insertion_intermediate_field_subgroup [FiniteDimensional F E] :
  GaloisInsertion (OrderDual.toDual ∘ (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
    ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘ OrderDual.toDual) :=
  { choice := fun K _ => IntermediateField.fixingSubgroup K, gc := fun K H => (IntermediateField.le_iff_le H K).symm,
    le_l_u := fun H => le_of_eqₓ (IntermediateField.fixing_subgroup_fixed_field H).symm, choice_eq := fun K _ => rfl }

/-- The Galois correspondence as a galois_coinsertion -/
def galois_coinsertion_intermediate_field_subgroup [FiniteDimensional F E] [IsGalois F E] :
  GaloisCoinsertion
    (OrderDual.toDual ∘ (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
    ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘ OrderDual.toDual) :=
  { choice := fun H _ => IntermediateField.fixedField H, gc := fun K H => (IntermediateField.le_iff_le H K).symm,
    u_l_le := fun K => le_of_eqₓ (fixed_field_fixing_subgroup K), choice_eq := fun H _ => rfl }

end IsGalois

end GaloisCorrespondence

section GaloisEquivalentDefinitions

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

namespace IsGalois

theorem is_separable_splitting_field [FiniteDimensional F E] [IsGalois F E] :
  ∃ p : Polynomial F, p.separable ∧ p.is_splitting_field F E :=
  by 
    cases' Field.exists_primitive_element F E with α h1 
    use minpoly F α, separable F α, IsGalois.splits F α 
    rw [eq_top_iff, ←IntermediateField.top_to_subalgebra, ←h1]
    rw [IntermediateField.adjoin_simple_to_subalgebra_of_integral F α (integral F α)]
    apply Algebra.adjoin_mono 
    rw [Set.singleton_subset_iff, Finset.mem_coe, Multiset.mem_to_finset, Polynomial.mem_roots]
    ·
      dsimp only [Polynomial.IsRoot]
      rw [Polynomial.eval_map, ←Polynomial.aeval_def]
      exact minpoly.aeval _ _
    ·
      exact Polynomial.map_ne_zero (minpoly.ne_zero (integral F α))

theorem of_fixed_field_eq_bot [FiniteDimensional F E]
  (h : IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥) : IsGalois F E :=
  by 
    rw [←is_galois_iff_is_galois_bot, ←h]
    exact IsGalois.of_fixed_field E (⊤ : Subgroup (E ≃ₐ[F] E))

-- error in FieldTheory.Galois: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem of_card_aut_eq_finrank
[finite_dimensional F E]
(h : «expr = »(fintype.card «expr ≃ₐ[ ] »(E, F, E), finrank F E)) : is_galois F E :=
begin
  apply [expr of_fixed_field_eq_bot],
  have [ident p] [":", expr «expr < »(0, finrank (intermediate_field.fixed_field («expr⊤»() : subgroup «expr ≃ₐ[ ] »(E, F, E))) E)] [":=", expr finrank_pos],
  rw ["[", "<-", expr intermediate_field.finrank_eq_one_iff, ",", "<-", expr mul_left_inj' (ne_of_lt p).symm, ",", expr finrank_mul_finrank, ",", "<-", expr h, ",", expr one_mul, ",", expr intermediate_field.finrank_fixed_field_eq_card, "]"] [],
  apply [expr fintype.card_congr],
  exact [expr { to_fun := λ g, ⟨g, subgroup.mem_top g⟩,
     inv_fun := coe,
     left_inv := λ g, rfl,
     right_inv := λ _, by { ext [] [] [],
       refl } }]
end

variable {F} {E} {p : Polynomial F}

-- error in FieldTheory.Galois: ././Mathport/Syntax/Translate/Basic.lean:341:40: in let: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem of_separable_splitting_field_aux
[hFE : finite_dimensional F E]
[sp : p.is_splitting_field F E]
(hp : p.separable)
(K : intermediate_field F E)
{x : E}
(hx : «expr ∈ »(x, (p.map (algebra_map F E)).roots)) : «expr = »(fintype.card «expr →ₐ[ ] »((«expr↑ »(«expr ⟮ , ⟯»(K, [x])) : intermediate_field F E), F, E), «expr * »(fintype.card «expr →ₐ[ ] »(K, F, E), finrank K «expr ⟮ , ⟯»(K, [x]))) :=
begin
  have [ident h] [":", expr is_integral K x] [":=", expr is_integral_of_is_scalar_tower x (is_integral_of_noetherian (is_noetherian.iff_fg.2 hFE) x)],
  have [ident h1] [":", expr «expr ≠ »(p, 0)] [":=", expr λ
   hp, by rwa ["[", expr hp, ",", expr polynomial.map_zero, ",", expr polynomial.roots_zero, "]"] ["at", ident hx]],
  have [ident h2] [":", expr «expr ∣ »(minpoly K x, p.map (algebra_map F K))] [],
  { apply [expr minpoly.dvd],
    rw ["[", expr polynomial.aeval_def, ",", expr polynomial.eval₂_map, ",", "<-", expr polynomial.eval_map, "]"] [],
    exact [expr (polynomial.mem_roots (polynomial.map_ne_zero h1)).mp hx] },
  let [ident key_equiv] [":", expr «expr ≃ »(«expr →ₐ[ ] »((«expr↑ »(«expr ⟮ , ⟯»(K, [x])) : intermediate_field F E), F, E), «exprΣ , »((f : «expr →ₐ[ ] »(K, F, E)), @alg_hom K «expr ⟮ , ⟯»(K, [x]) E _ _ _ _ (ring_hom.to_algebra f)))] [":=", expr equiv.trans (alg_equiv.arrow_congr (intermediate_field.lift2_alg_equiv «expr ⟮ , ⟯»(K, [x])) alg_equiv.refl) alg_hom_equiv_sigma],
  haveI [] [":", expr ∀
   f : «expr →ₐ[ ] »(K, F, E), fintype (@alg_hom K «expr ⟮ , ⟯»(K, [x]) E _ _ _ _ (ring_hom.to_algebra f))] [":=", expr λ
   f, by { apply [expr fintype.of_injective (sigma.mk f) (λ _ _ H, eq_of_heq (sigma.mk.inj H).2)],
     exact [expr fintype.of_equiv _ key_equiv] }],
  rw ["[", expr fintype.card_congr key_equiv, ",", expr fintype.card_sigma, ",", expr intermediate_field.adjoin.finrank h, "]"] [],
  apply [expr finset.sum_const_nat],
  intros [ident f, ident hf],
  rw ["<-", expr @intermediate_field.card_alg_hom_adjoin_integral K _ E _ _ x E _ (ring_hom.to_algebra f) h] [],
  { apply [expr fintype.card_congr],
    refl },
  { exact [expr polynomial.separable.of_dvd ((polynomial.separable_map (algebra_map F K)).mpr hp) h2] },
  { refine [expr polynomial.splits_of_splits_of_dvd _ (polynomial.map_ne_zero h1) _ h2],
    rw ["[", expr polynomial.splits_map_iff, ",", "<-", expr is_scalar_tower.algebra_map_eq, "]"] [],
    exact [expr sp.splits] }
end

-- error in FieldTheory.Galois: ././Mathport/Syntax/Translate/Basic.lean:341:40: in exact: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem of_separable_splitting_field [sp : p.is_splitting_field F E] (hp : p.separable) : is_galois F E :=
begin
  haveI [ident hFE] [":", expr finite_dimensional F E] [":=", expr polynomial.is_splitting_field.finite_dimensional E p],
  let [ident s] [] [":=", expr (p.map (algebra_map F E)).roots.to_finset],
  have [ident adjoin_root] [":", expr «expr = »(intermediate_field.adjoin F «expr↑ »(s), «expr⊤»())] [],
  { apply [expr intermediate_field.to_subalgebra_injective],
    rw ["[", expr intermediate_field.top_to_subalgebra, ",", "<-", expr top_le_iff, ",", "<-", expr sp.adjoin_roots, "]"] [],
    apply [expr intermediate_field.algebra_adjoin_le_adjoin] },
  let [ident P] [":", expr intermediate_field F E → exprProp()] [":=", expr λ
   K, «expr = »(fintype.card «expr →ₐ[ ] »(K, F, E), finrank F K)],
  suffices [] [":", expr P (intermediate_field.adjoin F «expr↑ »(s))],
  { rw [expr adjoin_root] ["at", ident this],
    apply [expr of_card_aut_eq_finrank],
    rw ["<-", expr eq.trans this (linear_equiv.finrank_eq intermediate_field.top_equiv.to_linear_equiv)] [],
    exact [expr fintype.card_congr (equiv.trans (alg_equiv_equiv_alg_hom F E) (alg_equiv.arrow_congr intermediate_field.top_equiv.symm alg_equiv.refl))] },
  apply [expr intermediate_field.induction_on_adjoin_finset s P],
  { have [ident key] [] [":=", expr intermediate_field.card_alg_hom_adjoin_integral F (show is_integral F (0 : E), by exact [expr is_integral_zero])],
    rw ["[", expr minpoly.zero, ",", expr polynomial.nat_degree_X, "]"] ["at", ident key],
    specialize [expr key polynomial.separable_X (polynomial.splits_X (algebra_map F E))],
    rw ["[", "<-", expr @subalgebra.finrank_bot F E _ _ _, ",", "<-", expr intermediate_field.bot_to_subalgebra, "]"] ["at", ident key],
    refine [expr eq.trans _ key],
    apply [expr fintype.card_congr],
    rw [expr intermediate_field.adjoin_zero] [] },
  intros [ident K, ident x, ident hx, ident hK],
  simp [] [] ["only"] ["[", expr P, "]"] [] ["at", "*"],
  rw ["[", expr of_separable_splitting_field_aux hp K (multiset.mem_to_finset.mp hx), ",", expr hK, ",", expr finrank_mul_finrank, "]"] [],
  exact [expr (linear_equiv.finrank_eq (intermediate_field.lift2_alg_equiv «expr ⟮ , ⟯»(K, [x])).to_linear_equiv).symm]
end

/--Equivalent characterizations of a Galois extension of finite degree-/
theorem tfae [FiniteDimensional F E] :
  tfae
    [IsGalois F E, IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥, Fintype.card (E ≃ₐ[F] E) = finrank F E,
      ∃ p : Polynomial F, p.separable ∧ p.is_splitting_field F E] :=
  by 
    tfaeHave 1 → 2
    ·
      exact fun h => OrderIso.map_bot (@intermediate_field_equiv_subgroup F _ E _ _ _ h).symm 
    tfaeHave 1 → 3
    ·
      intro 
      exact card_aut_eq_finrank F E 
    tfaeHave 1 → 4
    ·
      intro 
      exact is_separable_splitting_field F E 
    tfaeHave 2 → 1
    ·
      exact of_fixed_field_eq_bot F E 
    tfaeHave 3 → 1
    ·
      exact of_card_aut_eq_finrank F E 
    tfaeHave 4 → 1
    ·
      rintro ⟨h, hp1, _⟩
      exact of_separable_splitting_field hp1 
    tfaeFinish

end IsGalois

end GaloisEquivalentDefinitions

