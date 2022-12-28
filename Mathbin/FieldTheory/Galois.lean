/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz

! This file was ported from Lean 3 source module field_theory.galois
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.FieldTheory.Normal
import Mathbin.FieldTheory.PrimitiveElement
import Mathbin.FieldTheory.Fixed
import Mathbin.GroupTheory.GroupAction.FixingSubgroup

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `is_galois F E` where `E` is an extension of `F`
- `fixed_field H` where `H : subgroup (E ≃ₐ[F] E)`
- `fixing_subgroup K` where `K : intermediate_field F E`
- `galois_correspondence` where `E/F` is finite dimensional and Galois

## Main results

- `intermediate_field.fixing_subgroup_fixed_field` : If `E/F` is finite dimensional (but not
  necessarily Galois) then `fixing_subgroup (fixed_field H) = H`
- `intermediate_field.fixed_field_fixing_subgroup`: If `E/F` is finite dimensional and Galois
  then `fixed_field (fixing_subgroup K) = K`

Together, these two results prove the Galois correspondence.

- `is_galois.tfae` : Equivalent characterizations of a Galois extension of finite degree
-/


open Polynomial

open FiniteDimensional AlgEquiv

section

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

/-- A field extension E/F is galois if it is both separable and normal. Note that in mathlib
a separable extension of fields is by definition algebraic. -/
class IsGalois : Prop where
  [to_is_separable : IsSeparable F E]
  [toNormal : Normal F E]
#align is_galois IsGalois

variable {F E}

theorem is_galois_iff : IsGalois F E ↔ IsSeparable F E ∧ Normal F E :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h =>
    { to_is_separable := h.1
      toNormal := h.2 }⟩
#align is_galois_iff is_galois_iff

attribute [instance] IsGalois.to_is_separable IsGalois.toNormal

-- see Note [lower instance priority]
variable (F E)

namespace IsGalois

instance self : IsGalois F F :=
  ⟨⟩
#align is_galois.self IsGalois.self

variable (F) {E}

theorem integral [IsGalois F E] (x : E) : IsIntegral F x :=
  toNormal.IsIntegral x
#align is_galois.integral IsGalois.integral

theorem separable [IsGalois F E] (x : E) : (minpoly F x).Separable :=
  IsSeparable.separable F x
#align is_galois.separable IsGalois.separable

theorem splits [IsGalois F E] (x : E) : (minpoly F x).Splits (algebraMap F E) :=
  Normal.splits' x
#align is_galois.splits IsGalois.splits

variable (F E)

instance ofFixedField (G : Type _) [Group G] [Finite G] [MulSemiringAction G E] :
    IsGalois (FixedPoints.subfield G E) E :=
  ⟨⟩
#align is_galois.of_fixed_field IsGalois.ofFixedField

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem IntermediateField.AdjoinSimple.card_aut_eq_finrank [FiniteDimensional F E] {α : E}
    (hα : IsIntegral F α) (h_sep : (minpoly F α).Separable)
    (h_splits : (minpoly F α).Splits (algebraMap F F⟮⟯)) :
    Fintype.card (F⟮⟯ ≃ₐ[F] F⟮⟯) = finrank F F⟮⟯ :=
  by
  letI : Fintype (F⟮⟯ →ₐ[F] F⟮⟯) := IntermediateField.fintypeOfAlgHomAdjoinIntegral F hα
  rw [IntermediateField.adjoin.finrank hα]
  rw [← IntermediateField.card_alg_hom_adjoin_integral F hα h_sep h_splits]
  exact Fintype.card_congr (algEquivEquivAlgHom F F⟮⟯)
#align
  is_galois.intermediate_field.adjoin_simple.card_aut_eq_finrank IsGalois.IntermediateField.AdjoinSimple.card_aut_eq_finrank

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem card_aut_eq_finrank [FiniteDimensional F E] [IsGalois F E] :
    Fintype.card (E ≃ₐ[F] E) = finrank F E :=
  by
  cases' Field.exists_primitive_element F E with α hα
  let iso : F⟮⟯ ≃ₐ[F] E :=
    { toFun := fun e => e.val
      invFun := fun e =>
        ⟨e, by
          rw [hα]
          exact IntermediateField.mem_top⟩
      left_inv := fun _ => by
        ext
        rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have H : IsIntegral F α := IsGalois.integral F α
  have h_sep : (minpoly F α).Separable := IsGalois.separable F α
  have h_splits : (minpoly F α).Splits (algebraMap F E) := IsGalois.splits F α
  replace h_splits : Polynomial.Splits (algebraMap F F⟮⟯) (minpoly F α)
  · have p : iso.symm.to_alg_hom.to_ring_hom.comp (algebraMap F E) = algebraMap F ↥F⟮⟯ :=
      by
      ext
      simp
    simpa [p] using
      Polynomial.splits_comp_of_splits (algebraMap F E) iso.symm.to_alg_hom.to_ring_hom h_splits
  rw [← LinearEquiv.finrank_eq iso.to_linear_equiv]
  rw [← intermediate_field.adjoin_simple.card_aut_eq_finrank F E H h_sep h_splits]
  apply Fintype.card_congr
  apply Equiv.mk (fun ϕ => iso.trans (trans ϕ iso.symm)) fun ϕ => iso.symm.trans (trans ϕ iso)
  · intro ϕ
    ext1
    simp only [trans_apply, apply_symm_apply]
  · intro ϕ
    ext1
    simp only [trans_apply, symm_apply_apply]
#align is_galois.card_aut_eq_finrank IsGalois.card_aut_eq_finrank

end IsGalois

end

section IsGaloisTower

variable (F K E : Type _) [Field F] [Field K] [Field E] {E' : Type _} [Field E'] [Algebra F E']

variable [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

theorem IsGalois.towerTopOfIsGalois [IsGalois F E] : IsGalois K E :=
  { to_is_separable := is_separable_tower_top_of_is_separable F K E
    toNormal := Normal.towerTopOfNormal F K E }
#align is_galois.tower_top_of_is_galois IsGalois.towerTopOfIsGalois

variable {F E}

-- see Note [lower instance priority]
instance (priority := 100) IsGalois.towerTopIntermediateField (K : IntermediateField F E)
    [h : IsGalois F E] : IsGalois K E :=
  IsGalois.towerTopOfIsGalois F K E
#align is_galois.tower_top_intermediate_field IsGalois.towerTopIntermediateField

theorem is_galois_iff_is_galois_bot : IsGalois (⊥ : IntermediateField F E) E ↔ IsGalois F E :=
  by
  constructor
  · intro h
    exact IsGalois.towerTopOfIsGalois (⊥ : IntermediateField F E) F E
  · intro h
    infer_instance
#align is_galois_iff_is_galois_bot is_galois_iff_is_galois_bot

theorem IsGalois.ofAlgEquiv [h : IsGalois F E] (f : E ≃ₐ[F] E') : IsGalois F E' :=
  { to_is_separable := IsSeparable.of_alg_hom F E f.symm
    toNormal := Normal.ofAlgEquiv f }
#align is_galois.of_alg_equiv IsGalois.ofAlgEquiv

theorem AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : IsGalois F E ↔ IsGalois F E' :=
  ⟨fun h => IsGalois.ofAlgEquiv f, fun h => IsGalois.ofAlgEquiv f.symm⟩
#align alg_equiv.transfer_galois AlgEquiv.transfer_galois

theorem is_galois_iff_is_galois_top : IsGalois F (⊤ : IntermediateField F E) ↔ IsGalois F E :=
  (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).transfer_galois
#align is_galois_iff_is_galois_top is_galois_iff_is_galois_top

instance isGaloisBot : IsGalois F (⊥ : IntermediateField F E) :=
  (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)
#align is_galois_bot isGaloisBot

end IsGaloisTower

section GaloisCorrespondence

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

variable (H : Subgroup (E ≃ₐ[F] E)) (K : IntermediateField F E)

/-- The intermediate field of fixed points fixed by a monoid action that commutes with the
`F`-action on `E`. -/
def FixedPoints.intermediateField (M : Type _) [Monoid M] [MulSemiringAction M E]
    [SMulCommClass M F E] : IntermediateField F E :=
  { FixedPoints.subfield M E with
    carrier := MulAction.fixedPoints M E
    algebra_map_mem' := fun a g => by rw [Algebra.algebra_map_eq_smul_one, smul_comm, smul_one] }
#align fixed_points.intermediate_field FixedPoints.intermediateField

namespace IntermediateField

/-- The intermediate_field fixed by a subgroup -/
def fixedField : IntermediateField F E :=
  FixedPoints.intermediateField H
#align intermediate_field.fixed_field IntermediateField.fixedField

theorem finrank_fixed_field_eq_card [FiniteDimensional F E] [DecidablePred (· ∈ H)] :
    finrank (fixedField H) E = Fintype.card H :=
  FixedPoints.finrank_eq_card H E
#align intermediate_field.finrank_fixed_field_eq_card IntermediateField.finrank_fixed_field_eq_card

/-- The subgroup fixing an intermediate_field -/
def fixingSubgroup : Subgroup (E ≃ₐ[F] E) :=
  fixingSubgroup (E ≃ₐ[F] E) (K : Set E)
#align intermediate_field.fixing_subgroup IntermediateField.fixingSubgroup

theorem le_iff_le : K ≤ fixedField H ↔ H ≤ fixingSubgroup K :=
  ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩
#align intermediate_field.le_iff_le IntermediateField.le_iff_le

/-- The fixing_subgroup of `K : intermediate_field F E` is isomorphic to `E ≃ₐ[K] E` -/
def fixingSubgroupEquiv : fixingSubgroup K ≃* E ≃ₐ[K] E
    where
  toFun ϕ := { AlgEquiv.toRingEquiv ↑ϕ with commutes' := ϕ.Mem }
  invFun ϕ := ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  left_inv _ := by
    ext
    rfl
  right_inv _ := by
    ext
    rfl
  map_mul' _ _ := by
    ext
    rfl
#align intermediate_field.fixing_subgroup_equiv IntermediateField.fixingSubgroupEquiv

theorem fixing_subgroup_fixed_field [FiniteDimensional F E] : fixingSubgroup (fixedField H) = H :=
  by
  have H_le : H ≤ fixingSubgroup (fixed_field H) := (le_iff_le _ _).mp le_rfl
  classical
    suffices Fintype.card H = Fintype.card (fixingSubgroup (fixed_field H)) by
      exact
        SetLike.coe_injective
          (Set.eq_of_inclusion_surjective
              ((Fintype.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
                  ⟨Set.inclusion_injective H_le, this⟩).2).symm
    apply Fintype.card_congr
    refine' (FixedPoints.toAlgHomEquiv H E).trans _
    refine' (algEquivEquivAlgHom (fixed_field H) E).toEquiv.symm.trans _
    exact (fixing_subgroup_equiv (fixed_field H)).toEquiv.symm
#align intermediate_field.fixing_subgroup_fixed_field IntermediateField.fixing_subgroup_fixed_field

instance fixedField.algebra : Algebra K (fixedField (fixingSubgroup K))
    where
  smul x y :=
    ⟨x * y, fun ϕ => by
      rw [smul_mul', show ϕ • ↑x = ↑x from Subtype.mem ϕ x, show ϕ • ↑y = ↑y from Subtype.mem y ϕ]⟩
  toFun x := ⟨x, fun ϕ => Subtype.mem ϕ x⟩
  map_zero' := rfl
  map_add' _ _ := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl
#align intermediate_field.fixed_field.algebra IntermediateField.fixedField.algebra

instance fixedField.is_scalar_tower : IsScalarTower K (fixedField (fixingSubgroup K)) E :=
  ⟨fun _ _ _ => mul_assoc _ _ _⟩
#align intermediate_field.fixed_field.is_scalar_tower IntermediateField.fixedField.is_scalar_tower

end IntermediateField

namespace IsGalois

theorem fixed_field_fixing_subgroup [FiniteDimensional F E] [h : IsGalois F E] :
    IntermediateField.fixedField (IntermediateField.fixingSubgroup K) = K :=
  by
  have K_le : K ≤ IntermediateField.fixedField (IntermediateField.fixingSubgroup K) :=
    (IntermediateField.le_iff_le _ _).mpr le_rfl
  suffices
    finrank K E = finrank (IntermediateField.fixedField (IntermediateField.fixingSubgroup K)) E by
    exact (IntermediateField.eq_of_le_of_finrank_eq' K_le this).symm
  classical
    rw [IntermediateField.finrank_fixed_field_eq_card,
      Fintype.card_congr (IntermediateField.fixingSubgroupEquiv K).toEquiv]
    exact (card_aut_eq_finrank K E).symm
#align is_galois.fixed_field_fixing_subgroup IsGalois.fixed_field_fixing_subgroup

theorem card_fixing_subgroup_eq_finrank [DecidablePred (· ∈ IntermediateField.fixingSubgroup K)]
    [FiniteDimensional F E] [IsGalois F E] :
    Fintype.card (IntermediateField.fixingSubgroup K) = finrank K E := by
  conv =>
    rhs
    rw [← fixed_field_fixing_subgroup K, IntermediateField.finrank_fixed_field_eq_card]
#align is_galois.card_fixing_subgroup_eq_finrank IsGalois.card_fixing_subgroup_eq_finrank

/-- The Galois correspondence from intermediate fields to subgroups -/
def intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ
    where
  toFun := IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField
  left_inv K := fixed_field_fixing_subgroup K
  right_inv H := IntermediateField.fixing_subgroup_fixed_field H
  map_rel_iff' K L :=
    by
    rw [← fixed_field_fixing_subgroup L, IntermediateField.le_iff_le, fixed_field_fixing_subgroup L]
    rfl
#align is_galois.intermediate_field_equiv_subgroup IsGalois.intermediateFieldEquivSubgroup

/-- The Galois correspondence as a galois_insertion -/
def galoisInsertionIntermediateFieldSubgroup [FiniteDimensional F E] :
    GaloisInsertion
      (OrderDual.toDual ∘
        (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘
        OrderDual.toDual)
    where
  choice K _ := IntermediateField.fixingSubgroup K
  gc K H := (IntermediateField.le_iff_le H K).symm
  le_l_u H := le_of_eq (IntermediateField.fixing_subgroup_fixed_field H).symm
  choice_eq K _ := rfl
#align
  is_galois.galois_insertion_intermediate_field_subgroup IsGalois.galoisInsertionIntermediateFieldSubgroup

/-- The Galois correspondence as a galois_coinsertion -/
def galoisCoinsertionIntermediateFieldSubgroup [FiniteDimensional F E] [IsGalois F E] :
    GaloisCoinsertion
      (OrderDual.toDual ∘
        (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘
        OrderDual.toDual)
    where
  choice H _ := IntermediateField.fixedField H
  gc K H := (IntermediateField.le_iff_le H K).symm
  u_l_le K := le_of_eq (fixed_field_fixing_subgroup K)
  choice_eq H _ := rfl
#align
  is_galois.galois_coinsertion_intermediate_field_subgroup IsGalois.galoisCoinsertionIntermediateFieldSubgroup

end IsGalois

end GaloisCorrespondence

section GaloisEquivalentDefinitions

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

namespace IsGalois

theorem is_separable_splitting_field [FiniteDimensional F E] [IsGalois F E] :
    ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E :=
  by
  cases' Field.exists_primitive_element F E with α h1
  use minpoly F α, separable F α, IsGalois.splits F α
  rw [eq_top_iff, ← IntermediateField.top_to_subalgebra, ← h1]
  rw [IntermediateField.adjoin_simple_to_subalgebra_of_integral (integral F α)]
  apply Algebra.adjoin_mono
  rw [Set.singleton_subset_iff, Finset.mem_coe, Multiset.mem_to_finset, Polynomial.mem_roots]
  · dsimp only [Polynomial.IsRoot]
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  · exact Polynomial.map_ne_zero (minpoly.ne_zero (integral F α))
#align is_galois.is_separable_splitting_field IsGalois.is_separable_splitting_field

theorem ofFixedFieldEqBot [FiniteDimensional F E]
    (h : IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥) : IsGalois F E :=
  by
  rw [← is_galois_iff_is_galois_bot, ← h]
  classical exact IsGalois.ofFixedField E (⊤ : Subgroup (E ≃ₐ[F] E))
#align is_galois.of_fixed_field_eq_bot IsGalois.ofFixedFieldEqBot

theorem ofCardAutEqFinrank [FiniteDimensional F E] (h : Fintype.card (E ≃ₐ[F] E) = finrank F E) :
    IsGalois F E := by
  apply of_fixed_field_eq_bot
  have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E := finrank_pos
  classical
    rw [← IntermediateField.finrank_eq_one_iff, ← mul_left_inj' (ne_of_lt p).symm,
      finrank_mul_finrank, ← h, one_mul, IntermediateField.finrank_fixed_field_eq_card]
    apply Fintype.card_congr
    exact
      { toFun := fun g => ⟨g, Subgroup.mem_top g⟩
        invFun := coe
        left_inv := fun g => rfl
        right_inv := fun _ => by
          ext
          rfl }
#align is_galois.of_card_aut_eq_finrank IsGalois.ofCardAutEqFinrank

variable {F} {E} {p : F[X]}

/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:192:11: unsupported (impossible) -/
theorem of_separable_splitting_field_aux [hFE : FiniteDimensional F E] [sp : p.IsSplittingField F E]
    (hp : p.Separable) (K : Type _) [Field K] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    {x : E} (hx : x ∈ (p.map (algebraMap F E)).roots)
    -- these are both implied by `hFE`, but as they carry data this makes the lemma more general
    [Fintype (K →ₐ[F] E)]
    [Fintype (K⟮⟯.restrictScalars F →ₐ[F] E)] :
    Fintype.card (K⟮⟯.restrictScalars F →ₐ[F] E) = Fintype.card (K →ₐ[F] E) * finrank K K⟮⟯ :=
  by
  have h : IsIntegral K x :=
    is_integral_of_is_scalar_tower (is_integral_of_noetherian (IsNoetherian.iff_fg.2 hFE) x)
  have h1 : p ≠ 0 := fun hp => by rwa [hp, Polynomial.map_zero, Polynomial.roots_zero] at hx
  have h2 : minpoly K x ∣ p.map (algebraMap F K) :=
    by
    apply minpoly.dvd
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← Polynomial.eval_map, ←
      IsScalarTower.algebra_map_eq]
    exact (Polynomial.mem_roots (Polynomial.map_ne_zero h1)).mp hx
  let key_equiv :
    (K⟮⟯.restrictScalars F →ₐ[F] E) ≃
      Σf : K →ₐ[F] E, @AlgHom K K⟮⟯ E _ _ _ _ (RingHom.toAlgebra f) :=
    by
    change (K⟮⟯ →ₐ[F] E) ≃ Σf : K →ₐ[F] E, _
    exact algHomEquivSigma
  haveI : ∀ f : K →ₐ[F] E, Fintype (@AlgHom K K⟮⟯ E _ _ _ _ (RingHom.toAlgebra f)) := fun f =>
    by
    apply Fintype.ofInjective (Sigma.mk f) fun _ _ H => eq_of_heq (Sigma.mk.inj H).2
    exact Fintype.ofEquiv _ key_equiv
  rw [Fintype.card_congr key_equiv, Fintype.card_sigma, IntermediateField.adjoin.finrank h]
  apply Finset.sum_const_nat
  intro f hf
  rw [← @IntermediateField.card_alg_hom_adjoin_integral K _ E _ _ x E _ (RingHom.toAlgebra f) h]
  · apply Fintype.card_congr
    rfl
  · exact Polynomial.Separable.of_dvd ((Polynomial.separable_map (algebraMap F K)).mpr hp) h2
  · refine' Polynomial.splits_of_splits_of_dvd _ (Polynomial.map_ne_zero h1) _ h2
    rw [Polynomial.splits_map_iff, ← IsScalarTower.algebra_map_eq]
    exact sp.splits
#align is_galois.of_separable_splitting_field_aux IsGalois.of_separable_splitting_field_aux

theorem ofSeparableSplittingField [sp : p.IsSplittingField F E] (hp : p.Separable) : IsGalois F E :=
  by
  haveI hFE : FiniteDimensional F E := Polynomial.IsSplittingField.finite_dimensional E p
  letI := Classical.decEq E
  let s := (p.map (algebraMap F E)).roots.toFinset
  have adjoin_root : IntermediateField.adjoin F ↑s = ⊤ :=
    by
    apply IntermediateField.to_subalgebra_injective
    rw [IntermediateField.top_to_subalgebra, ← top_le_iff, ← sp.adjoin_roots]
    apply IntermediateField.algebra_adjoin_le_adjoin
  let P : IntermediateField F E → Prop := fun K => Fintype.card (K →ₐ[F] E) = finrank F K
  suffices P (IntermediateField.adjoin F ↑s)
    by
    rw [AdjoinRoot] at this
    apply of_card_aut_eq_finrank
    rw [← Eq.trans this (LinearEquiv.finrank_eq intermediate_field.top_equiv.to_linear_equiv)]
    exact
      Fintype.card_congr
        ((algEquivEquivAlgHom F E).toEquiv.trans
          (intermediate_field.top_equiv.symm.arrow_congr AlgEquiv.refl))
  apply IntermediateField.induction_on_adjoin_finset s P
  · have key :=
      IntermediateField.card_alg_hom_adjoin_integral F
        (show IsIntegral F (0 : E) from is_integral_zero)
    rw [minpoly.zero, Polynomial.nat_degree_X] at key
    specialize key Polynomial.separable_X (Polynomial.splits_X (algebraMap F E))
    rw [← @Subalgebra.finrank_bot F E _ _ _, ← IntermediateField.bot_to_subalgebra] at key
    refine' Eq.trans _ key
    apply Fintype.card_congr
    rw [IntermediateField.adjoin_zero]
  intro K x hx hK
  simp only [P] at *
  rw [of_separable_splitting_field_aux hp K (multiset.mem_to_finset.mp hx), hK, finrank_mul_finrank]
  symm
  refine' LinearEquiv.finrank_eq _
  rfl
#align is_galois.of_separable_splitting_field IsGalois.ofSeparableSplittingField

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Equivalent characterizations of a Galois extension of finite degree-/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `tfae [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `FiniteDimensional [`F `E]) "]")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tfae
         [(«term[_]»
           "["
           [(Term.app `IsGalois [`F `E])
            ","
            («term_=_»
             (Term.app
              `IntermediateField.fixedField
              [(Term.typeAscription
                "("
                (Order.BoundedOrder.«term⊤» "⊤")
                ":"
                [(Term.app `Subgroup [(Algebra.Algebra.Equiv.«term_≃ₐ[_]_» `E " ≃ₐ[" `F "] " `E)])]
                ")")])
             "="
             (Order.BoundedOrder.«term⊥» "⊥"))
            ","
            («term_=_»
             (Term.app `Fintype.card [(Algebra.Algebra.Equiv.«term_≃ₐ[_]_» `E " ≃ₐ[" `F "] " `E)])
             "="
             (Term.app `finrank [`F `E]))
            ","
            («term∃_,_»
             "∃"
             (Lean.explicitBinders
              (Lean.unbracketedExplicitBinders
               [(Lean.binderIdent `p)]
               [":" (Polynomial.Data.Polynomial.Basic.polynomial `F "[X]")]))
             ","
             («term_∧_»
              (Term.proj `p "." `Separable)
              "∧"
              (Term.app (Term.proj `p "." `IsSplittingField) [`F `E])))]
           "]")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.fun
               "fun"
               (Term.basicFun
                [`h]
                []
                "=>"
                (Term.app
                 `OrderIso.map_bot
                 [(Term.proj
                   (Term.app
                    (Term.explicit "@" `intermediate_field_equiv_subgroup)
                    [`F (Term.hole "_") `E (Term.hole "_") (Term.hole "_") (Term.hole "_") `h])
                   "."
                   `symm)]))))])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "3"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [])
             []
             (Tactic.exact "exact" (Term.app `card_aut_eq_finrank [`F `E]))])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "4"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [])
             []
             (Tactic.exact "exact" (Term.app `is_separable_splitting_field [`F `E]))])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "1"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.app `of_fixed_field_eq_bot [`F `E]))])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "1"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact "exact" (Term.app `of_card_aut_eq_finrank [`F `E]))])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "1"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp1)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.exact "exact" (Term.app `of_separable_splitting_field [`hp1]))])
           []
           (Tactic.tfaeFinish "tfae_finish")])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "2"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [`h]
               []
               "=>"
               (Term.app
                `OrderIso.map_bot
                [(Term.proj
                  (Term.app
                   (Term.explicit "@" `intermediate_field_equiv_subgroup)
                   [`F (Term.hole "_") `E (Term.hole "_") (Term.hole "_") (Term.hole "_") `h])
                  "."
                  `symm)]))))])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "3"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [])
            []
            (Tactic.exact "exact" (Term.app `card_aut_eq_finrank [`F `E]))])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "4"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [])
            []
            (Tactic.exact "exact" (Term.app `is_separable_splitting_field [`F `E]))])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "1"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `of_fixed_field_eq_bot [`F `E]))])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "1"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact "exact" (Term.app `of_card_aut_eq_finrank [`F `E]))])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "1"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp1)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.exact "exact" (Term.app `of_separable_splitting_field [`hp1]))])
          []
          (Tactic.tfaeFinish "tfae_finish")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeFinish "tfae_finish")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp1)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.exact "exact" (Term.app `of_separable_splitting_field [`hp1]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `of_separable_splitting_field [`hp1]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `of_separable_splitting_field [`hp1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of_separable_splitting_field
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hp1)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« → »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ↔ »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ← »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Equivalent characterizations of a Galois extension of finite degree-/
  theorem
    tfae
    [ FiniteDimensional F E ]
      :
        Tfae
          [
            IsGalois F E
              ,
              IntermediateField.fixedField ( ⊤ : Subgroup E ≃ₐ[ F ] E ) = ⊥
              ,
              Fintype.card E ≃ₐ[ F ] E = finrank F E
              ,
              ∃ p : F [X] , p . Separable ∧ p . IsSplittingField F E
            ]
    :=
      by
        tfae_have 1 → 2
          · exact fun h => OrderIso.map_bot @ intermediate_field_equiv_subgroup F _ E _ _ _ h . symm
          tfae_have 1 → 3
          · intro exact card_aut_eq_finrank F E
          tfae_have 1 → 4
          · intro exact is_separable_splitting_field F E
          tfae_have 2 → 1
          · exact of_fixed_field_eq_bot F E
          tfae_have 3 → 1
          · exact of_card_aut_eq_finrank F E
          tfae_have 4 → 1
          · rintro ⟨ h , hp1 , _ ⟩ exact of_separable_splitting_field hp1
          tfae_finish
#align is_galois.tfae IsGalois.tfae

end IsGalois

end GaloisEquivalentDefinitions

