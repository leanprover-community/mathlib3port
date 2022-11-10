/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.FieldTheory.IntermediateField
import Mathbin.RingTheory.Adjoin.Field

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : K[X]` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : K[X]` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `polynomial.splitting_field f`: A fixed splitting field of the polynomial `f`.
* `polynomial.is_splitting_field`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `polynomial.is_splitting_field.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.
* `polynomial.is_splitting_field.alg_equiv`: Every splitting field of a polynomial `f` is isomorphic
  to `splitting_field f` and thus, being a splitting field is unique up to isomorphism.

-/


noncomputable section

open Classical BigOperators Polynomial

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : K[X]) : K[X] :=
  if H : ∃ g, Irreducible g ∧ g ∣ f then Classical.choose H else x

theorem irreducible_factor (f : K[X]) : Irreducible (factor f) := by
  rw [factor]
  split_ifs with H
  · exact (Classical.choose_spec H).1
    
  · exact irreducible_X
    

/-- See note [fact non-instances]. -/
theorem fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f)) :=
  ⟨irreducible_factor f⟩

attribute [local instance] fact_irreducible_factor

theorem factor_dvd_of_not_is_unit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f := by
  by_cases hf2:f = 0
  · rw [hf2]
    exact dvd_zero _
    
  rw [factor, dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.choose_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2

theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {f : K[X]} (hf : f.natDegree ≠ 0) : factor f ∣ f :=
  factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - c (AdjoinRoot.root f.factor))

theorem X_sub_C_mul_remove_factor (f : K[X]) (hf : f.natDegree ≠ 0) :
    (X - c (AdjoinRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f :=
  let ⟨g, hg⟩ := factor_dvd_of_nat_degree_ne_zero hf
  mul_div_by_monic_eq_iff_is_root.2 <| by
    rw [is_root.def, eval_map, hg, eval₂_mul, ← hg, AdjoinRoot.eval₂_root, zero_mul]

theorem nat_degree_remove_factor (f : K[X]) : f.removeFactor.natDegree = f.natDegree - 1 := by
  rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map, nat_degree_X_sub_C]

theorem nat_degree_remove_factor' {f : K[X]} {n : ℕ} (hfn : f.natDegree = n + 1) : f.removeFactor.natDegree = n := by
  rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial, which removes
`n` (arbitrarily-chosen) factors.

Uses recursion on the degree. For better definitional behaviour, structures
including `splitting_field_aux` (such as instances) should be defined using
this recursion in each field, rather than defining the whole tuple through
recursion.
-/
def SplittingFieldAux (n : ℕ) : ∀ {K : Type u} [Field K], ∀ f : K[X], Type u :=
  (Nat.recOn n fun K _ _ => K) fun n ih K _ f => ih f.remove_factor

namespace SplittingFieldAux

theorem succ (n : ℕ) (f : K[X]) : SplittingFieldAux (n + 1) f = SplittingFieldAux n f.removeFactor :=
  rfl

instance field (n : ℕ) : ∀ {K : Type u} [Field K], ∀ {f : K[X]}, Field (splitting_field_aux n f) :=
  (Nat.recOn n fun K _ _ => ‹Field K›) fun n ih K _ f => ih

instance inhabited {n : ℕ} {f : K[X]} : Inhabited (SplittingFieldAux n f) :=
  ⟨37⟩

/-
Note that the recursive nature of this definition and `splitting_field_aux.field` creates
non-definitionally-equal diamonds in the `ℕ`- and `ℤ`- actions.
```lean
example (n : ℕ) {K : Type u} [field K] {f : K[X]} (hfn : f.nat_degree = n) :
    (add_comm_monoid.nat_module : module ℕ (splitting_field_aux n f hfn)) =
  @algebra.to_module _ _ _ _ (splitting_field_aux.algebra n _ hfn) :=
rfl  -- fails
```
It's not immediately clear whether this _can_ be fixed; the failure is much the same as the reason
that the following fails:
```lean
def cases_twice {α} (a₀ aₙ : α) : ℕ → α × α
| 0 := (a₀, a₀)
| (n + 1) := (aₙ, aₙ)

example (x : ℕ) {α} (a₀ aₙ : α) : (cases_twice a₀ aₙ x).1 = (cases_twice a₀ aₙ x).2 := rfl  -- fails
```
We don't really care at this point because this is an implementation detail (which is why this is
not a docstring), but we do in `splitting_field.algebra'` below. -/
instance algebra (n : ℕ) :
    ∀ (R : Type _) {K : Type u} [CommSemiring R] [Field K],
      ∀ [Algebra R K] {f : K[X]}, Algebra R (splitting_field_aux n f) :=
  (Nat.recOn n fun R K _ _ _ _ => ‹Algebra R K›) fun n ih R K _ _ _ f => ih R

instance is_scalar_tower (n : ℕ) :
    ∀ (R₁ R₂ : Type _) {K : Type u} [CommSemiring R₁] [CommSemiring R₂] [HasSmul R₁ R₂] [Field K],
      ∀ [Algebra R₁ K] [Algebra R₂ K],
        ∀ [IsScalarTower R₁ R₂ K] {f : K[X]}, IsScalarTower R₁ R₂ (splitting_field_aux n f) :=
  (Nat.recOn n fun R₁ R₂ K _ _ _ _ _ _ _ _ => ‹IsScalarTower R₁ R₂ K›) fun n ih R₁ R₂ K _ _ _ _ _ _ _ f => ih R₁ R₂

instance algebra''' {n : ℕ} {f : K[X]} : Algebra (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  SplittingFieldAux.algebra n _

instance algebra' {n : ℕ} {f : K[X]} : Algebra (AdjoinRoot f.factor) (SplittingFieldAux n.succ f) :=
  splitting_field_aux.algebra'''

instance algebra'' {n : ℕ} {f : K[X]} : Algebra K (SplittingFieldAux n f.removeFactor) :=
  SplittingFieldAux.algebra n K

instance scalar_tower' {n : ℕ} {f : K[X]} :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  haveI-- finding this instance ourselves makes things faster
   : IsScalarTower K (AdjoinRoot f.factor) (AdjoinRoot f.factor) := IsScalarTower.right
  splitting_field_aux.is_scalar_tower n K (AdjoinRoot f.factor)

instance scalar_tower {n : ℕ} {f : K[X]} : IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux (n + 1) f) :=
  splitting_field_aux.scalar_tower'

theorem algebra_map_succ (n : ℕ) (f : K[X]) :
    algebraMap K (splitting_field_aux (n + 1) f) =
      (algebraMap (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor)).comp (AdjoinRoot.of f.factor) :=
  IsScalarTower.algebra_map_eq _ _ _

protected theorem splits (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n), splits (algebraMap K <| splitting_field_aux n f) f :=
  (Nat.recOn n fun K _ _ hf =>
      splits_of_degree_le_one _ (le_trans degree_le_nat_degree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih K _ f hf => by
    skip
    rw [← splits_id_iff_splits, algebra_map_succ, ← map_map, splits_id_iff_splits, ←
      X_sub_C_mul_remove_factor f fun h => by
        rw [h] at hf
        cases hf]
    exact splits_mul _ (splits_X_sub_C _) (ih _ (nat_degree_remove_factor' hf))

theorem exists_lift (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n) {L : Type _} [Field L],
        ∀ (j : K →+* L) (hf : splits j f), ∃ k : splitting_field_aux n f →+* L, k.comp (algebraMap _ _) = j :=
  (Nat.recOn n fun K _ _ _ L _ j _ => ⟨j, j.comp_id⟩) fun n ih K _ f hf L _ j hj =>
    have hndf : f.nat_degree ≠ 0 := by
      intro h
      rw [h] at hf
      cases hf
    have hfn0 : f ≠ 0 := by
      intro h
      rw [h] at hndf
      exact hndf rfl
    let ⟨r, hr⟩ :=
      exists_root_of_splits _ (splits_of_splits_of_dvd j hfn0 hj (factor_dvd_of_nat_degree_ne_zero hndf))
        (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1)
    have hmf0 : map (AdjoinRoot.of f.factor) f ≠ 0 := map_ne_zero hfn0
    have hsf : splits (AdjoinRoot.lift j r hr) f.remove_factor := by
      rw [← X_sub_C_mul_remove_factor _ hndf] at hmf0
      refine' (splits_of_splits_mul _ hmf0 _).2
      rwa [X_sub_C_mul_remove_factor _ hndf, ← splits_id_iff_splits, map_map, AdjoinRoot.lift_comp_of,
        splits_id_iff_splits]
    let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (AdjoinRoot.lift j r hr) hsf
    ⟨k, by rw [algebra_map_succ, ← RingHom.comp_assoc, hk, AdjoinRoot.lift_comp_of]⟩

theorem adjoin_roots (n : ℕ) :
    ∀ {K : Type u} [Field K],
      ∀ (f : K[X]) (hfn : f.natDegree = n),
        Algebra.adjoin K
            (↑(f.map <| algebraMap K <| splitting_field_aux n f).roots.toFinset : Set (splitting_field_aux n f)) =
          ⊤ :=
  (Nat.recOn n fun K _ f hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩) fun n ih K _ f hfn => by
    have hndf : f.nat_degree ≠ 0 := by
      intro h
      rw [h] at hfn
      cases hfn
    have hfn0 : f ≠ 0 := by
      intro h
      rw [h] at hndf
      exact hndf rfl
    have hmf0 : map (algebraMap K (splitting_field_aux n.succ f)) f ≠ 0 := map_ne_zero hfn0
    rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_remove_factor _ hndf, Polynomial.map_mul] at hmf0⊢
    rw [roots_mul hmf0, Polynomial.map_sub, map_X, map_C, roots_X_sub_C, Multiset.to_finset_add, Finset.coe_union,
      Multiset.to_finset_singleton, Finset.coe_singleton, Algebra.adjoin_union_eq_adjoin_adjoin, ← Set.image_singleton,
      Algebra.adjoin_algebra_map K (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor),
      AdjoinRoot.adjoin_root_eq_top, Algebra.map_top,
      IsScalarTower.adjoin_range_to_alg_hom K (AdjoinRoot f.factor) (splitting_field_aux n f.remove_factor),
      ih _ (nat_degree_remove_factor' hfn), Subalgebra.restrict_scalars_top]

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
def SplittingField (f : K[X]) :=
  SplittingFieldAux f.natDegree f

namespace SplittingField

variable (f : K[X])

instance : Field (SplittingField f) :=
  SplittingFieldAux.field _

instance inhabited : Inhabited (SplittingField f) :=
  ⟨37⟩

/-- This should be an instance globally, but it creates diamonds with the `ℕ`, `ℤ`, and `ℚ` algebras
(via their `smul` and `to_fun` fields):

```lean
example :
  (algebra_nat : algebra ℕ (splitting_field f)) = splitting_field.algebra' f :=
rfl  -- fails

example :
  (algebra_int _ : algebra ℤ (splitting_field f)) = splitting_field.algebra' f :=
rfl  -- fails

example [char_zero K] [char_zero (splitting_field f)] :
  (algebra_rat : algebra ℚ (splitting_field f)) = splitting_field.algebra' f :=
rfl  -- fails
```

Until we resolve these diamonds, it's more convenient to only turn this instance on with
`local attribute [instance]` in places where the benefit of having the instance outweighs the cost.

In the meantime, the `splitting_field.algebra` instance below is immune to these particular diamonds
since `K = ℕ` and `K = ℤ` are not possible due to the `field K` assumption. Diamonds in
`algebra ℚ (splitting_field f)` instances are still possible via this instance unfortunately, but
these are less common as they require suitable `char_zero` instances to be present.
-/
instance algebra' {R} [CommSemiring R] [Algebra R K] : Algebra R (SplittingField f) :=
  SplittingFieldAux.algebra _ _

instance : Algebra K (SplittingField f) :=
  SplittingFieldAux.algebra _ _

protected theorem splits : Splits (algebraMap K (SplittingField f)) f :=
  SplittingFieldAux.splits _ _ rfl

variable [Algebra K L] (hb : Splits (algebraMap K L) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : SplittingField f →ₐ[K] L :=
  { Classical.choose (SplittingFieldAux.exists_lift _ _ _ _ hb) with
    commutes' := fun r =>
      haveI := Classical.choose_spec (splitting_field_aux.exists_lift _ _ rfl _ hb)
      RingHom.ext_iff.1 this r }

theorem adjoin_roots :
    Algebra.adjoin K (↑(f.map (algebraMap K <| SplittingField f)).roots.toFinset : Set (SplittingField f)) = ⊤ :=
  SplittingFieldAux.adjoin_roots _ _ rfl

theorem adjoin_root_set : Algebra.adjoin K (f.RootSet f.SplittingField) = ⊤ :=
  adjoin_roots f

end SplittingField

variable (K L) [Algebra K L]

/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`Splits] [] -/
/- ./././Mathport/Syntax/Translate/Command.lean:353:30: infer kinds are unsupported in Lean 4: #[`adjoin_roots] [] -/
/-- Typeclass characterising splitting fields. -/
class IsSplittingField (f : K[X]) : Prop where
  Splits : Splits (algebraMap K L) f
  adjoin_roots : Algebra.adjoin K (↑(f.map (algebraMap K L)).roots.toFinset : Set L) = ⊤

namespace IsSplittingField

variable {K}

instance splittingField (f : K[X]) : IsSplittingField K (SplittingField f) f :=
  ⟨SplittingField.splits f, SplittingField.adjoin_roots f⟩

section ScalarTower

variable {K L F} [Algebra F K] [Algebra F L] [IsScalarTower F K L]

variable {K}

instance map (f : F[X]) [IsSplittingField F L f] : IsSplittingField K L (f.map <| algebraMap F K) :=
  ⟨by
    rw [splits_map_iff, ← IsScalarTower.algebra_map_eq]
    exact splits L f,
    Subalgebra.restrict_scalars_injective F <| by
      rw [map_map, ← IsScalarTower.algebra_map_eq, Subalgebra.restrict_scalars_top, eq_top_iff, ← adjoin_roots L f,
        Algebra.adjoin_le_iff]
      exact fun x hx => @Algebra.subset_adjoin K _ _ _ _ _ _ hx⟩

variable {K} (L)

theorem splits_iff (f : K[X]) [IsSplittingField K L f] :
    Polynomial.Splits (RingHom.id K) f ↔ (⊤ : Subalgebra K L) = ⊥ :=
  ⟨fun h =>
    eq_bot_iff.2 <|
      adjoin_roots L f ▸
        (roots_map (algebraMap K L) h).symm ▸
          Algebra.adjoin_le_iff.2 fun y hy =>
            let ⟨x, hxs, hxy⟩ := Finset.mem_image.1 (by rwa [Multiset.to_finset_map] at hy)
            hxy ▸ SetLike.mem_coe.2 <| Subalgebra.algebra_map_mem _ _,
    fun h =>
    @RingEquiv.to_ring_hom_refl K _ ▸
      RingEquiv.self_trans_symm (RingEquiv.ofBijective _ <| Algebra.bijective_algebra_map_iff.2 h) ▸ by
        rw [RingEquiv.to_ring_hom_trans]
        exact splits_comp_of_splits _ _ (splits L f)⟩

theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [IsSplittingField F K f]
    [IsSplittingField K L (g.map <| algebraMap F K)] : IsSplittingField F L (f * g) :=
  ⟨(IsScalarTower.algebra_map_eq F K L).symm ▸
      splitsMul _ (splitsCompOfSplits _ _ (splits K f)) ((splits_map_iff _ _).1 (splits L <| g.map <| algebraMap F K)),
    by
    rw [Polynomial.map_mul, roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebraMap F L) ≠ 0) (map_ne_zero hg)),
      Multiset.to_finset_add, Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin,
      IsScalarTower.algebra_map_eq F K L, ← map_map,
      roots_map (algebraMap K L) ((splits_id_iff_splits <| algebraMap F K).2 <| splits K f), Multiset.to_finset_map,
      Finset.coe_image, Algebra.adjoin_algebra_map, adjoin_roots, Algebra.map_top,
      IsScalarTower.adjoin_range_to_alg_hom, ← map_map, adjoin_roots, Subalgebra.restrict_scalars_top]⟩

end ScalarTower

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [Algebra K F] (f : K[X]) [IsSplittingField K L f] (hf : Polynomial.Splits (algebraMap K F) f) : L →ₐ[K] F :=
  if hf0 : f = 0 then
    (Algebra.ofId K F).comp <|
      (Algebra.botEquiv K L : (⊥ : Subalgebra K L) →ₐ[K] K).comp <| by
        rw [← (splits_iff L f).1 (show f.splits (RingHom.id K) from hf0.symm ▸ splits_zero _)]
        exact Algebra.toTop
  else
    AlgHom.comp
      (by
        rw [← adjoin_roots L f]
        exact
          Classical.choice
            ((lift_of_splits _) fun y hy =>
              have : aeval y f = 0 :=
                (eval₂_eq_eval_map _).trans <| (mem_roots <| map_ne_zero hf0).1 (multiset.mem_to_finset.mp hy)
              ⟨is_algebraic_iff_is_integral.1 ⟨f, hf0, this⟩,
                splits_of_splits_of_dvd _ hf0 hf <| minpoly.dvd _ _ this⟩))
      Algebra.toTop

theorem finiteDimensional (f : K[X]) [IsSplittingField K L f] : FiniteDimensional K L :=
  ⟨@Algebra.top_to_submodule K L _ _ _ ▸
      adjoin_roots L f ▸
        fg_adjoin_of_finite (Finset.finite_to_set _) fun y hy =>
          if hf : f = 0 then by
            rw [hf, Polynomial.map_zero, roots_zero] at hy
            cases hy
          else
            is_algebraic_iff_is_integral.1
              ⟨f, hf, (eval₂_eq_eval_map _).trans <| (mem_roots <| map_ne_zero hf).1 (Multiset.mem_to_finset.mp hy)⟩⟩

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def algEquiv (f : K[X]) [IsSplittingField K L f] : L ≃ₐ[K] SplittingField f := by
  refine'
    AlgEquiv.ofBijective (lift L f <| splits (splitting_field f) f)
      ⟨RingHom.injective (lift L f <| splits (splitting_field f) f).toRingHom, _⟩
  haveI := FiniteDimensional (splitting_field f) f
  haveI := FiniteDimensional L f
  have : FiniteDimensional.finrank K L = FiniteDimensional.finrank K (splitting_field f) :=
    le_antisymm
      (LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (lift L f <| splits (splitting_field f) f).toLinearMap from
          RingHom.injective (lift L f <| splits (splitting_field f) f : L →+* f.splitting_field)))
      (LinearMap.finrank_le_finrank_of_injective
        (show Function.Injective (lift (splitting_field f) f <| splits L f).toLinearMap from
          RingHom.injective (lift (splitting_field f) f <| splits L f : f.splitting_field →+* L)))
  change Function.Surjective (lift L f <| splits (splitting_field f) f).toLinearMap
  refine' (LinearMap.injective_iff_surjective_of_finrank_eq_finrank this).1 _
  exact RingHom.injective (lift L f <| splits (splitting_field f) f : L →+* f.splitting_field)

theorem ofAlgEquiv [Algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [IsSplittingField K F p] : IsSplittingField K L p := by
  constructor
  · rw [← f.to_alg_hom.comp_algebra_map]
    exact splits_comp_of_splits _ _ (splits F p)
    
  · rw [← (Algebra.range_top_iff_surjective f.to_alg_hom).mpr f.surjective, ← root_set,
      adjoin_root_set_eq_range (splits F p), root_set, adjoin_roots F p]
    

end IsSplittingField

end SplittingField

end Polynomial

namespace IntermediateField

open Polynomial

variable [Field K] [Field L] [Algebra K L] {p : K[X]}

theorem splitsOfSplits {F : IntermediateField K L} (h : p.Splits (algebraMap K L)) (hF : ∀ x ∈ p.RootSet L, x ∈ F) :
    p.Splits (algebraMap K F) := by
  simp_rw [root_set, Finset.mem_coe, Multiset.mem_to_finset] at hF
  rw [splits_iff_exists_multiset]
  refine' ⟨Multiset.pmap Subtype.mk _ hF, map_injective _ (algebraMap F L).Injective _⟩
  conv_lhs =>
    rw [Polynomial.map_map, ← IsScalarTower.algebra_map_eq, eq_prod_roots_of_splits h, ← Multiset.pmap_eq_map _ _ _ hF]
  simp_rw [Polynomial.map_mul, Polynomial.map_multiset_prod, Multiset.map_pmap, Polynomial.map_sub, map_C, map_X]
  rfl

end IntermediateField

