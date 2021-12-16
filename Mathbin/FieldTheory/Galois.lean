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


noncomputable section 

open_locale Classical

open FiniteDimensional AlgEquiv

section 

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

/-- A field extension E/F is galois if it is both separable and normal. Note that in mathlib
a separable extension of fields is by definition algebraic. -/
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

-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
theorem intermediate_field.adjoin_simple.card_aut_eq_finrank [FiniteDimensional F E] {α : E} (hα : IsIntegral F α)
  (h_sep : (minpoly F α).Separable)
  (h_splits :
    (minpoly F α).Splits
      (algebraMap F
        («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»"))) :
  Fintype.card
      («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»" ≃ₐ[F]
        «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»") =
    finrank F («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»") :=
  by 
    let this' :
      Fintype
        («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»" →ₐ[F]
          «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»") :=
      IntermediateField.fintypeOfAlgHomAdjoinIntegral F hα 
    rw [IntermediateField.adjoin.finrank hα]
    rw [←IntermediateField.card_alg_hom_adjoin_integral F hα h_sep h_splits]
    exact
      Fintype.card_congr
        (algEquivEquivAlgHom F
          («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»"))

-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
theorem card_aut_eq_finrank [FiniteDimensional F E] [IsGalois F E] : Fintype.card (E ≃ₐ[F] E) = finrank F E :=
  by 
    cases' Field.exists_primitive_element F E with α hα 
    let iso :
      «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»" ≃ₐ[F] E :=
      { toFun := fun e => e.val,
        invFun :=
          fun e =>
            ⟨e,
              by 
                rw [hα]
                exact IntermediateField.mem_top⟩,
        left_inv :=
          fun _ =>
            by 
              ext 
              rfl,
        right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
    have H : IsIntegral F α := IsGalois.integral F α 
    have h_sep : (minpoly F α).Separable := IsGalois.separable F α 
    have h_splits : (minpoly F α).Splits (algebraMap F E) := IsGalois.splits F α 
    replace h_splits :
      Polynomial.Splits
        (algebraMap F
          («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»"))
        (minpoly F α)
    ·
      have p :
        iso.symm.to_alg_hom.to_ring_hom.comp (algebraMap F E) =
          algebraMap F
            (↥«expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»")
      ·
        ext 
        simp 
      simpa [p] using Polynomial.splits_comp_of_splits (algebraMap F E) iso.symm.to_alg_hom.to_ring_hom h_splits 
    rw [←LinearEquiv.finrank_eq iso.to_linear_equiv]
    rw [←intermediate_field.adjoin_simple.card_aut_eq_finrank F E H h_sep h_splits]
    apply Fintype.card_congr 
    apply Equivₓ.mk (fun ϕ => iso.trans (trans ϕ iso.symm)) fun ϕ => iso.symm.trans (trans ϕ iso)
    ·
      intro ϕ 
      ext1 
      simp only [trans_apply, apply_symm_apply]
    ·
      intro ϕ 
      ext1 
      simp only [trans_apply, symm_apply_apply]

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
    constructor
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
    inv_mem' := fun _ hx _ => (Equivₓ.symm_apply_eq (to_equiv _)).mpr (hx _).symm }

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

theorem fixing_subgroup_fixed_field [FiniteDimensional F E] : fixing_subgroup (fixed_field H) = H :=
  by 
    have H_le : H ≤ fixing_subgroup (fixed_field H) := (le_iff_le _ _).mp (le_reflₓ _)
    suffices  : Fintype.card H = Fintype.card (fixing_subgroup (fixed_field H))
    ·
      exact
        SetLike.coe_injective
          (Set.eq_of_inclusion_surjective
              ((Fintype.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
                  ⟨Set.inclusion_injective H_le, this⟩).2).symm
            
    apply Fintype.card_congr 
    refine' (FixedPoints.toAlgHomEquiv H E).trans _ 
    refine' (algEquivEquivAlgHom (fixed_field H) E).symm.trans _ 
    exact (fixing_subgroup_equiv (fixed_field H)).toEquiv.symm

instance fixed_field.algebra : Algebra K (fixed_field (fixing_subgroup K)) :=
  { smul :=
      fun x y =>
        ⟨x*y,
          fun ϕ =>
            by 
              rw [smul_mul',
                show ϕ • ↑x = ↑x by 
                  exact Subtype.mem ϕ x,
                show ϕ • ↑y = ↑y by 
                  exact Subtype.mem y ϕ]⟩,
    toFun := fun x => ⟨x, fun ϕ => Subtype.mem ϕ x⟩, map_zero' := rfl, map_add' := fun _ _ => rfl, map_one' := rfl,
    map_mul' := fun _ _ => rfl, commutes' := fun _ _ => mul_commₓ _ _, smul_def' := fun _ _ => rfl }

instance fixed_field.is_scalar_tower : IsScalarTower K (fixed_field (fixing_subgroup K)) E :=
  ⟨fun _ _ _ => mul_assocₓ _ _ _⟩

end IntermediateField

namespace IsGalois

theorem fixed_field_fixing_subgroup [FiniteDimensional F E] [h : IsGalois F E] :
  IntermediateField.fixedField (IntermediateField.fixingSubgroup K) = K :=
  by 
    have K_le : K ≤ IntermediateField.fixedField (IntermediateField.fixingSubgroup K) :=
      (IntermediateField.le_iff_le _ _).mpr (le_reflₓ _)
    suffices  : finrank K E = finrank (IntermediateField.fixedField (IntermediateField.fixingSubgroup K)) E
    ·
      exact (IntermediateField.eq_of_le_of_finrank_eq' K_le this).symm 
    rw [IntermediateField.finrank_fixed_field_eq_card,
      Fintype.card_congr (IntermediateField.fixingSubgroupEquiv K).toEquiv]
    exact (card_aut_eq_finrank K E).symm

theorem card_fixing_subgroup_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
  Fintype.card (IntermediateField.fixingSubgroup K) = finrank K E :=
  by 
    conv  => rhs rw [←fixed_field_fixing_subgroup K, IntermediateField.finrank_fixed_field_eq_card]

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

theorem of_card_aut_eq_finrank [FiniteDimensional F E] (h : Fintype.card (E ≃ₐ[F] E) = finrank F E) : IsGalois F E :=
  by 
    apply of_fixed_field_eq_bot 
    have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E := finrank_pos 
    rw [←IntermediateField.finrank_eq_one_iff, ←mul_left_inj' (ne_of_ltₓ p).symm, finrank_mul_finrank, ←h, one_mulₓ,
      IntermediateField.finrank_fixed_field_eq_card]
    apply Fintype.card_congr 
    exact
      { toFun := fun g => ⟨g, Subgroup.mem_top g⟩, invFun := coeₓ, left_inv := fun g => rfl,
        right_inv :=
          fun _ =>
            by 
              ext 
              rfl }

variable {F} {E} {p : Polynomial F}

-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
theorem of_separable_splitting_field_aux [hFE : FiniteDimensional F E] [sp : p.is_splitting_field F E]
  (hp : p.separable) (K : IntermediateField F E) {x : E} (hx : x ∈ (p.map (algebraMap F E)).roots) :
  Fintype.card
      ((↑«expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»" :
        IntermediateField F E) →ₐ[F]
        E) =
    Fintype.card
        (K →ₐ[F]
          E)*finrank K
        («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»") :=
  by 
    have h : IsIntegral K x :=
      is_integral_of_is_scalar_tower x (is_integral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x)
    have h1 : p ≠ 0 :=
      fun hp =>
        by 
          rwa [hp, Polynomial.map_zero, Polynomial.roots_zero] at hx 
    have h2 : minpoly K x ∣ p.map (algebraMap F K)
    ·
      apply minpoly.dvd 
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, ←Polynomial.eval_map]
      exact (Polynomial.mem_roots (Polynomial.map_ne_zero h1)).mp hx 
    let key_equiv :
      ((↑«expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»" :
          IntermediateField F E) →ₐ[F]
          E) ≃
        Σ f : K →ₐ[F] E,
          @AlgHom K
            («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»") E _ _
            _ _ (RingHom.toAlgebra f) :=
      Equivₓ.trans
        (AlgEquiv.arrowCongr
          (IntermediateField.lift2AlgEquiv
            («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»"))
          AlgEquiv.refl)
        algHomEquivSigma 
    have  :
      ∀ f : K →ₐ[F] E,
        Fintype
          (@AlgHom K
            («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»") E _ _
            _ _ (RingHom.toAlgebra f)) :=
      fun f =>
        by 
          apply Fintype.ofInjective (Sigma.mk f) fun _ _ H => eq_of_heq (Sigma.mk.inj H).2 
          exact Fintype.ofEquiv _ key_equiv 
    rw [Fintype.card_congr key_equiv, Fintype.card_sigma, IntermediateField.adjoin.finrank h]
    apply Finset.sum_const_nat 
    intro f hf 
    rw [←@IntermediateField.card_alg_hom_adjoin_integral K _ E _ _ x E _ (RingHom.toAlgebra f) h]
    ·
      apply Fintype.card_congr 
      rfl
    ·
      exact Polynomial.Separable.of_dvd ((Polynomial.separable_map (algebraMap F K)).mpr hp) h2
    ·
      refine' Polynomial.splits_of_splits_of_dvd _ (Polynomial.map_ne_zero h1) _ h2 
      rw [Polynomial.splits_map_iff, ←IsScalarTower.algebra_map_eq]
      exact sp.splits

-- ././Mathport/Syntax/Translate/Basic.lean:600:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»
theorem of_separable_splitting_field [sp : p.is_splitting_field F E] (hp : p.separable) : IsGalois F E :=
  by 
    have hFE : FiniteDimensional F E := Polynomial.IsSplittingField.finite_dimensional E p 
    let s := (p.map (algebraMap F E)).roots.toFinset 
    have adjoin_root : IntermediateField.adjoin F (↑s) = ⊤
    ·
      apply IntermediateField.to_subalgebra_injective 
      rw [IntermediateField.top_to_subalgebra, ←top_le_iff, ←sp.adjoin_roots]
      apply IntermediateField.algebra_adjoin_le_adjoin 
    let P : IntermediateField F E → Prop := fun K => Fintype.card (K →ₐ[F] E) = finrank F K 
    suffices  : P (IntermediateField.adjoin F (↑s))
    ·
      rw [AdjoinRoot] at this 
      apply of_card_aut_eq_finrank 
      rw [←Eq.trans this (LinearEquiv.finrank_eq intermediate_field.top_equiv.to_linear_equiv)]
      exact
        Fintype.card_congr
          (Equivₓ.trans (algEquivEquivAlgHom F E) (AlgEquiv.arrowCongr intermediate_field.top_equiv.symm AlgEquiv.refl))
    apply IntermediateField.induction_on_adjoin_finset s P
    ·
      have key :=
        IntermediateField.card_alg_hom_adjoin_integral F
          (show IsIntegral F (0 : E)by 
            exact is_integral_zero)
      rw [minpoly.zero, Polynomial.nat_degree_X] at key 
      specialize key Polynomial.separable_X (Polynomial.splits_X (algebraMap F E))
      rw [←@Subalgebra.finrank_bot F E _ _ _, ←IntermediateField.bot_to_subalgebra] at key 
      refine' Eq.trans _ key 
      apply Fintype.card_congr 
      rw [IntermediateField.adjoin_zero]
    intro K x hx hK 
    simp only [P] at *
    rw [of_separable_splitting_field_aux hp K (multiset.mem_to_finset.mp hx), hK, finrank_mul_finrank]
    exact
      (LinearEquiv.finrank_eq
          (IntermediateField.lift2AlgEquiv
              («expr ⟮ , ⟯» K
                "././Mathport/Syntax/Translate/Basic.lean:601:61: unsupported notation `«expr ⟮ , ⟯»")).toLinearEquiv).symm

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

