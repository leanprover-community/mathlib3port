import Mathbin.FieldTheory.IntermediateField
import Mathbin.FieldTheory.SplittingField
import Mathbin.FieldTheory.Separable
import Mathbin.RingTheory.AdjoinRoot
import Mathbin.RingTheory.PowerBasis

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `algebra.adjoin K {x}` might not include `x⁻¹`.

## Main results

- `adjoin_adjoin_left`: adjoining S and then T is the same as adjoining `S ∪ T`.
- `bot_eq_top_of_dim_adjoin_eq_one`: if `F⟮x⟯` has dimension `1` over `F` for every `x`
  in `E` then `F = E`

## Notation

 - `F⟮α⟯`: adjoin a single element `α` to `F`.
-/


open FiniteDimensional Polynomial

open_locale Classical

namespace IntermediateField

section AdjoinDef

variable (F : Type _) [Field F] {E : Type _} [Field E] [Algebra F E] (S : Set E)

/--  `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.Range (algebraMap F E) ∪ S) with
    algebra_map_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

end AdjoinDef

section Lattice

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

@[simp]
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ≤ T :=
  ⟨fun H => le_transₓ (le_transₓ (Set.subset_union_right _ _) Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.Range (algebraMap F E) ∪ S) T.to_subfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

theorem gc : GaloisConnection (adjoin F : Set E → IntermediateField F E) coeₓ := fun _ _ => adjoin_le_iff

/--  Galois insertion between `adjoin` and `coe`. -/
def gi : GaloisInsertion (adjoin F : Set E → IntermediateField F E) coeₓ :=
  { choice := fun S _ => adjoin F S, gc := IntermediateField.gc,
    le_l_u := fun S => (IntermediateField.gc (S : Set E) (adjoin F S)).1 $ le_reflₓ _, choice_eq := fun _ _ => rfl }

instance : CompleteLattice (IntermediateField F E) :=
  GaloisInsertion.liftCompleteLattice IntermediateField.gi

instance : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩

theorem mem_bot {x : E} : x ∈ (⊥ : IntermediateField F E) ↔ x ∈ Set.Range (algebraMap F E) := by
  suffices Set.Range (algebraMap F E) = (⊥ : IntermediateField F E)by
    rw [this]
    rfl
  ·
    change Set.Range (algebraMap F E) = Subfield.closure (Set.Range (algebraMap F E) ∪ ∅)
    simp [← Set.image_univ, ← RingHom.map_field_closure]

theorem mem_top {x : E} : x ∈ (⊤ : IntermediateField F E) :=
  Subfield.subset_closure $ Or.inr trivialₓ

@[simp]
theorem bot_to_subalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ := by
  ext
  rw [mem_to_subalgebra, Algebra.mem_bot, mem_bot]

@[simp]
theorem top_to_subalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤ := by
  ext
  rw [mem_to_subalgebra, iff_true_right Algebra.mem_top]
  exact mem_top

/--   Construct an algebra isomorphism from an equality of intermediate fields -/
@[simps apply]
def equiv_of_eq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T := by
  refine' { toFun := fun x => ⟨x, _⟩, invFun := fun x => ⟨x, _⟩, .. } <;> tidy

@[simp]
theorem equiv_of_eq_symm {S T : IntermediateField F E} (h : S = T) : (equiv_of_eq h).symm = equiv_of_eq h.symm :=
  rfl

@[simp]
theorem equiv_of_eq_rfl (S : IntermediateField F E) : equiv_of_eq (rfl : S = S) = AlgEquiv.refl := by
  ext
  rfl

@[simp]
theorem equiv_of_eq_trans {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U) :
    (equiv_of_eq hST).trans (equiv_of_eq hTU) = equiv_of_eq (trans hST hTU) :=
  rfl

variable (F E)

/--  The bottom intermediate_field is isomorphic to the field. -/
noncomputable def bot_equiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_to_subalgebra).trans (Algebra.botEquiv F E)

variable {F E}

@[simp]
theorem bot_equiv_def (x : F) : bot_equiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x :=
  AlgEquiv.commutes (bot_equiv F E) x

noncomputable instance algebra_over_bot : Algebra (⊥ : IntermediateField F E) F :=
  (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra

instance is_scalar_tower_over_bot : IsScalarTower (⊥ : IntermediateField F E) F E :=
  IsScalarTower.of_algebra_map_eq
    (by
      intro x
      let ϕ := Algebra.ofId F (⊥ : Subalgebra F E)
      let ψ := AlgEquiv.ofBijective ϕ (Algebra.botEquiv F E).symm.Bijective
      change (↑x : E) = ↑ψ (ψ.symm ⟨x, _⟩)
      rw [AlgEquiv.apply_symm_apply ψ ⟨x, _⟩]
      rfl)

/--  The top intermediate_field is isomorphic to the field. -/
noncomputable def top_equiv : (⊤ : IntermediateField F E) ≃ₐ[F] E :=
  (Subalgebra.equivOfEq _ _ top_to_subalgebra).trans Algebra.topEquiv

@[simp]
theorem top_equiv_def (x : (⊤ : IntermediateField F E)) : top_equiv x = ↑x := by
  suffices Algebra.toTop (top_equiv x) = Algebra.toTop (x : E)by
    rwa [Subtype.ext_iff] at this
  exact
    AlgEquiv.apply_symm_apply
      (AlgEquiv.ofBijective Algebra.toTop
        ⟨fun _ _ => Subtype.mk.injₓ, fun x =>
          ⟨x.val, by
            ext
            rfl⟩⟩ :
        E ≃ₐ[F] (⊤ : Subalgebra F E))
      (Subalgebra.equivOfEq _ _ top_to_subalgebra x)

@[simp]
theorem coe_bot_eq_self (K : IntermediateField F E) : ↑(⊥ : IntermediateField K E) = K := by
  ext
  rw [mem_lift2, mem_bot]
  exact set.ext_iff.mp Subtype.range_coe x

@[simp]
theorem coe_top_eq_top (K : IntermediateField F E) : ↑(⊤ : IntermediateField K E) = (⊤ : IntermediateField F E) :=
  SetLike.ext_iff.mpr $ fun _ => mem_lift2.trans (iff_of_true mem_top mem_top)

end Lattice

section AdjoinDef

variable (F : Type _) [Field F] {E : Type _} [Field E] [Algebra F E] (S : Set E)

theorem adjoin_eq_range_algebra_map_adjoin : (adjoin F S : Set E) = Set.Range (algebraMap (adjoin F S) E) :=
  Subtype.range_coe.symm

theorem adjoin.algebra_map_mem (x : F) : algebraMap F E x ∈ adjoin F S :=
  IntermediateField.algebra_map_mem (adjoin F S) x

theorem adjoin.range_algebra_map_subset : Set.Range (algebraMap F E) ⊆ adjoin F S := by
  intro x hx
  cases' hx with f hf
  rw [← hf]
  exact adjoin.algebra_map_mem F S f

-- failed to format: format: uncaught backtrack exception
instance adjoin.field_coe : CoeTₓ F ( adjoin F S ) where coe x := ⟨ algebraMap F E x , adjoin.algebra_map_mem F S x ⟩

theorem subset_adjoin : S ⊆ adjoin F S := fun x hx => Subfield.subset_closure (Or.inr hx)

-- failed to format: format: uncaught backtrack exception
instance adjoin.set_coe : CoeTₓ S ( adjoin F S ) where coe x := ⟨ x , subset_adjoin F S ( Subtype.mem x ) ⟩

@[mono]
theorem adjoin.mono (T : Set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
  GaloisConnection.monotone_l gc h

theorem adjoin_contains_field_as_subfield (F : Subfield E) : (F : Set E) ⊆ adjoin F S := fun x hx =>
  adjoin.algebra_map_mem F S ⟨x, hx⟩

theorem subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T ⊆ F) : T ⊆ adjoin F S := fun x hx =>
  (adjoin F S).algebra_map_mem ⟨x, HT hx⟩

theorem subset_adjoin_of_subset_right {T : Set E} (H : T ⊆ S) : T ⊆ adjoin F S := fun x hx => subset_adjoin F S (H hx)

@[simp]
theorem adjoin_empty (F E : Type _) [Field F] [Field E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥ :=
  eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))

/--  If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
theorem adjoin_le_subfield {K : Subfield E} (HF : Set.Range (algebraMap F E) ⊆ K) (HS : S ⊆ K) :
    (adjoin F S).toSubfield ≤ K := by
  apply subfield.closure_le.mpr
  rw [Set.union_subset_iff]
  exact ⟨HF, HS⟩

theorem adjoin_subset_adjoin_iff {F' : Type _} [Field F'] [Algebra F' E] {S S' : Set E} :
    (adjoin F S : Set E) ⊆ adjoin F' S' ↔ Set.Range (algebraMap F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
  ⟨fun h => ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩, fun ⟨hF, hS⟩ =>
    Subfield.closure_le.mpr (Set.union_subset hF hS)⟩

/--  `F[S][T] = F[S ∪ T]` -/
theorem adjoin_adjoin_left (T : Set E) : ↑adjoin (adjoin F S) T = adjoin F (S ∪ T) := by
  rw [SetLike.ext'_iff]
  change ↑adjoin (adjoin F S) T = _
  apply Set.eq_of_subset_of_subset <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  ·
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact adjoin.mono _ _ _ (Set.subset_union_left _ _) hx
  ·
    exact subset_adjoin_of_subset_right _ _ (Set.subset_union_right _ _)
  ·
    exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _)
  ·
    exact Set.union_subset (subset_adjoin_of_subset_left _ (subset_adjoin _ _)) (subset_adjoin _ _)

@[simp]
theorem adjoin_insert_adjoin (x : E) : adjoin F (insert x (adjoin F S : Set E)) = adjoin F (insert x S) :=
  le_antisymmₓ
    (adjoin_le_iff.mpr
      (Set.insert_subset.mpr
        ⟨subset_adjoin _ _ (Set.mem_insert _ _),
          adjoin_le_iff.mpr (subset_adjoin_of_subset_right _ _ (Set.subset_insert _ _))⟩))
    (adjoin.mono _ _ _ (Set.insert_subset_insert (subset_adjoin _ _)))

/--  `F[S][T] = F[T][S]` -/
theorem adjoin_adjoin_comm (T : Set E) : ↑adjoin (adjoin F S) T = (↑adjoin (adjoin F T) S : IntermediateField F E) := by
  rw [adjoin_adjoin_left, adjoin_adjoin_left, Set.union_comm]

theorem adjoin_map {E' : Type _} [Field E'] [Algebra F E'] (f : E →ₐ[F] E') : (adjoin F S).map f = adjoin F (f '' S) :=
  by
  ext x
  show
    x ∈ (Subfield.closure (Set.Range (algebraMap F E) ∪ S)).map (f : E →+* E') ↔
      x ∈ Subfield.closure (Set.Range (algebraMap F E') ∪ f '' S)
  rw [RingHom.map_field_closure, Set.image_union, ← Set.range_comp, ← RingHom.coe_comp, f.comp_algebra_map]
  rfl

theorem algebra_adjoin_le_adjoin : Algebra.adjoin F S ≤ (adjoin F S).toSubalgebra :=
  Algebra.adjoin_le (subset_adjoin _ _)

theorem adjoin_eq_algebra_adjoin (inv_mem : ∀, ∀ x ∈ Algebra.adjoin F S, ∀, x⁻¹ ∈ Algebra.adjoin F S) :
    (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  le_antisymmₓ
    (show
      adjoin F S ≤
        { Algebra.adjoin F S with neg_mem' := fun x => (Algebra.adjoin F S).neg_mem, inv_mem' := inv_mem } from
      adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)

theorem eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E) (h : K.to_subalgebra = Algebra.adjoin F S) :
    K = adjoin F S := by
  apply to_subalgebra_injective
  rw [h]
  refine' (adjoin_eq_algebra_adjoin _ _ _).symm
  intro x
  convert K.inv_mem
  rw [← h]
  rfl

@[elab_as_eliminator]
theorem adjoin_induction {s : Set E} {p : E → Prop} {x} (h : x ∈ adjoin F s) (Hs : ∀, ∀ x ∈ s, ∀, p x)
    (Hmap : ∀ x, p (algebraMap F E x)) (Hadd : ∀ x y, p x → p y → p (x+y)) (Hneg : ∀ x, p x → p (-x))
    (Hinv : ∀ x, p x → p (x⁻¹)) (Hmul : ∀ x y, p x → p y → p (x*y)) : p x :=
  Subfield.closure_induction h (fun x hx => Or.cases_on hx (fun ⟨x, hx⟩ => hx ▸ Hmap x) (Hs x))
    ((algebraMap F E).map_one ▸ Hmap 1) Hadd Hneg Hinv Hmul

/-- 
Variation on `set.insert` to enable good notation for adjoining elements to fields.
Used to preferentially use `singleton` rather than `insert` when adjoining one element.
-/
class insert {α : Type _} (s : Set α) where
  insert : α → Set α

-- failed to format: format: uncaught backtrack exception
instance
  ( priority := 1000 )
  insert_empty
  { α : Type _ } : insert ( ∅ : Set α )
  where insert x := @ singleton _ _ Set.hasSingleton x

-- failed to format: format: uncaught backtrack exception
instance ( priority := 900 ) insert_nonempty { α : Type _ } ( s : Set α ) : insert s where insert x := Set.Insert x s

-- ././Mathport/Syntax/Translate/Basic.lean:333:9: unsupported: advanced prec syntax
-- ././Mathport/Syntax/Translate/Basic.lean:1233:9: unsupported: advanced notation (l:(foldr `, ` (h t, insert.insert t h) «expr∅»()))
notation3:999 K "⟮"  "⟯" => adjoin K l

section AdjoinSimple

variable (α : E)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem mem_adjoin_simple_self :
    α ∈ «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" :=
  subset_adjoin F {α} (Set.mem_singleton α)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  generator of `F⟮α⟯` -/
def adjoin_simple.gen :
    «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" :=
  ⟨α, mem_adjoin_simple_self F α⟩

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_simple.algebra_map_gen :
    algebraMap («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") E
        (adjoin_simple.gen F α) =
      α :=
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_simple.is_integral_gen : IsIntegral F (adjoin_simple.gen F α) ↔ IsIntegral F α := by
  conv_rhs => rw [← adjoin_simple.algebra_map_gen F α]
  rw
    [is_integral_algebra_map_iff
      (algebraMap («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»")
          E).Injective]
  infer_instance

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin_simple_adjoin_simple (β : E) :
    ↑«expr ⟮ , ⟯» («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»")
          "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" =
      «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" :=
  adjoin_adjoin_left _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin_simple_comm (β : E) :
    ↑«expr ⟮ , ⟯» («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»")
          "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" =
      (↑«expr ⟮ , ⟯»
          («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»")
          "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" :
        IntermediateField F E) :=
  adjoin_adjoin_comm _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin_simple_to_subalgebra_of_integral (hα : IsIntegral F α) :
    («expr ⟮ , ⟯» F
          "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»").toSubalgebra =
      Algebra.adjoin F {α} :=
  by
  apply adjoin_eq_algebra_adjoin
  intro x hx
  by_cases' x = 0
  ·
    rw [h, inv_zero]
    exact Subalgebra.zero_mem (Algebra.adjoin F {α})
  let ϕ := AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly F α
  have := minpoly.irreducible hα
  suffices (ϕ ⟨x, hx⟩*ϕ ⟨x, hx⟩⁻¹) = 1by
    convert Subtype.mem (ϕ.symm (ϕ ⟨x, hx⟩⁻¹))
    refine' (eq_inv_of_mul_right_eq_one _).symm
    apply_fun ϕ.symm  at this
    rw [AlgEquiv.map_one, AlgEquiv.map_mul, AlgEquiv.symm_apply_apply] at this
    rw [← Subsemiring.coe_one, ← this, Subsemiring.coe_mul, Subtype.coe_mk]
  rw [mul_inv_cancel (mt (fun key => _) h)]
  rw [← ϕ.map_zero] at key
  change ↑(⟨x, hx⟩ : Algebra.adjoin F {α}) = _
  rw [ϕ.injective key, Subalgebra.coe_zero]

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E] {α : E} {S : Set E}

@[simp]
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : IntermediateField F E) := by
  rw [eq_bot_iff, adjoin_le_iff]
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_simple_eq_bot_iff :
    «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" = ⊥ ↔
      α ∈ (⊥ : IntermediateField F E) :=
  by
  rw [adjoin_eq_bot_iff]
  exact Set.singleton_subset_iff

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_zero :
    «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_one :
    «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_int (n : ℤ) :
    «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (coe_int_mem ⊥ n)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_nat (n : ℕ) :
    «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (coe_int_mem ⊥ n)

section AdjoinDim

open FiniteDimensional Module

variable {K L : IntermediateField F E}

@[simp]
theorem dim_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥ := by
  rw [← to_subalgebra_eq_iff, ← dim_eq_dim_subalgebra, Subalgebra.dim_eq_one_iff, bot_to_subalgebra]

@[simp]
theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ := by
  rw [← to_subalgebra_eq_iff, ← finrank_eq_finrank_subalgebra, Subalgebra.finrank_eq_one_iff, bot_to_subalgebra]

theorem dim_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans dim_eq_one_iff adjoin_eq_bot_iff

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem dim_adjoin_simple_eq_one_iff :
    Module.rank F
          («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") =
        1 ↔
      α ∈ (⊥ : IntermediateField F E) :=
  by
  rw [dim_adjoin_eq_one_iff]
  exact Set.singleton_subset_iff

theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem finrank_adjoin_simple_eq_one_iff :
    finrank F («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") =
        1 ↔
      α ∈ (⊥ : IntermediateField F E) :=
  by
  rw [finrank_adjoin_eq_one_iff]
  exact Set.singleton_subset_iff

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_dim_adjoin_eq_one
    (h :
      ∀ x : E,
        Module.rank F
            («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") =
          1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext
  rw [iff_true_right IntermediateField.mem_top]
  exact dim_adjoin_simple_eq_one_iff.mp (h x)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem bot_eq_top_of_finrank_adjoin_eq_one
    (h :
      ∀ x : E,
        finrank F
            («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") =
          1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  ext
  rw [iff_true_right IntermediateField.mem_top]
  exact finrank_adjoin_simple_eq_one_iff.mp (h x)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem subsingleton_of_dim_adjoin_eq_one
    (h :
      ∀ x : E,
        Module.rank F
            («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") =
          1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_dim_adjoin_eq_one h)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem subsingleton_of_finrank_adjoin_eq_one
    (h :
      ∀ x : E,
        finrank F
            («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") =
          1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h :
      ∀ x : E,
        finrank F
            («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") ≤
          1) :
    (⊥ : IntermediateField F E) = ⊤ := by
  apply bot_eq_top_of_finrank_adjoin_eq_one
  exact fun x => by
    linarith [h x,
      show
        0 <
          finrank F
            («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") from
        finrank_pos]

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem subsingleton_of_finrank_adjoin_le_one [FiniteDimensional F E]
    (h :
      ∀ x : E,
        finrank F
            («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") ≤
          1) :
    Subsingleton (IntermediateField F E) :=
  subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

end AdjoinDim

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E] {α : E}

variable {K : Type _} [Field K] [Algebra F K]

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem minpoly_gen {α : E} (h : IsIntegral F α) : minpoly F (adjoin_simple.gen F α) = minpoly F α := by
  rw [← adjoin_simple.algebra_map_gen F α] at h
  have inj :=
    (algebraMap («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»")
        E).Injective
  exact
    minpoly.eq_of_algebra_map_eq inj ((is_integral_algebra_map_iff inj).mp h) (adjoin_simple.algebra_map_gen _ _).symm

variable (F)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem aeval_gen_minpoly (α : E) : aeval (adjoin_simple.gen F α) (minpoly F α) = 0 := by
  ext
  convert minpoly.aeval F α
  conv in aeval α => rw [← adjoin_simple.algebra_map_gen F α]
  exact
    IsScalarTower.algebra_map_aeval F
      («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") E _ _

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  algebra isomorphism between `adjoin_root` and `F⟮α⟯` -/
noncomputable def adjoin_root_equiv_adjoin (h : IsIntegral F α) :
    AdjoinRoot (minpoly F α) ≃ₐ[F]
      «expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" :=
  AlgEquiv.ofBijective (AdjoinRoot.liftHom (minpoly F α) (adjoin_simple.gen F α) (aeval_gen_minpoly F α))
    (by
      set f := AdjoinRoot.lift _ _ (aeval_gen_minpoly F α : _)
      have := minpoly.irreducible h
      constructor
      ·
        exact RingHom.injective f
      ·
        suffices
          («expr ⟮ , ⟯» F
                "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»").toSubfield ≤
            RingHom.fieldRange
              ((«expr ⟮ , ⟯» F
                        "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»").toSubfield.Subtype.comp
                f)by
          exact fun x => Exists.cases_on (this (Subtype.mem x)) fun y hy => ⟨y, Subtype.ext hy⟩
        exact
          subfield.closure_le.mpr
            (Set.union_subset
              (fun x hx =>
                Exists.cases_on hx fun y hy =>
                  ⟨y, by
                    rw [RingHom.comp_apply, AdjoinRoot.lift_of]
                    exact hy⟩)
              (set.singleton_subset_iff.mpr
                ⟨AdjoinRoot.root (minpoly F α), by
                  rw [RingHom.comp_apply, AdjoinRoot.lift_root]
                  rfl⟩)))

theorem adjoin_root_equiv_adjoin_apply_root (h : IsIntegral F α) :
    adjoin_root_equiv_adjoin F h (AdjoinRoot.root (minpoly F α)) = adjoin_simple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)

section PowerBasis

variable {L : Type _} [Field L] [Algebra K L]

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable def power_basis_aux {x : L} (hx : IsIntegral K x) :
    Basis (Finₓ (minpoly K x).natDegree) K
      («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") :=
  (AdjoinRoot.powerBasis (minpoly.ne_zero hx)).Basis.map (adjoin_root_equiv_adjoin K hx).toLinearEquiv

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps]
noncomputable def adjoin.power_basis {x : L} (hx : IsIntegral K x) :
    PowerBasis K
      («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") :=
  { gen := adjoin_simple.gen K x, dim := (minpoly K x).natDegree, Basis := power_basis_aux hx,
    basis_eq_pow := fun i => by
      rw [power_basis_aux, Basis.map_apply, PowerBasis.basis_eq_pow, AlgEquiv.to_linear_equiv_apply, AlgEquiv.map_pow,
        AdjoinRoot.power_basis_gen, adjoin_root_equiv_adjoin_apply_root] }

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin.finite_dimensional {x : L} (hx : IsIntegral K x) :
    FiniteDimensional K
      («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") :=
  PowerBasis.finite_dimensional (adjoin.power_basis hx)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin.finrank {x : L} (hx : IsIntegral K x) :
    FiniteDimensional.finrank K
        («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") =
      (minpoly K x).natDegree :=
  by
  rw [PowerBasis.finrank (adjoin.power_basis hx : _)]
  rfl

end PowerBasis

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
noncomputable def alg_hom_adjoin_integral_equiv (h : IsIntegral F α) :
    («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" →ₐ[F] K) ≃
      { x // x ∈ ((minpoly F α).map (algebraMap F K)).roots } :=
  (adjoin.power_basis h).liftEquiv'.trans
    ((Equivₓ.refl _).subtypeEquiv fun x => by
      rw [adjoin.power_basis_gen, minpoly_gen h, Equivₓ.refl_apply])

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
noncomputable def fintype_of_alg_hom_adjoin_integral (h : IsIntegral F α) :
    Fintype
      («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" →ₐ[F] K) :=
  PowerBasis.AlgHom.fintype (adjoin.power_basis h)

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem card_alg_hom_adjoin_integral (h : IsIntegral F α) (h_sep : (minpoly F α).Separable)
    (h_splits : (minpoly F α).Splits (algebraMap F K)) :
    @Fintype.card
        («expr ⟮ , ⟯» F "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" →ₐ[F] K)
        (fintype_of_alg_hom_adjoin_integral F h) =
      (minpoly F α).natDegree :=
  by
  rw [AlgHom.card_of_power_basis] <;>
    simp only [adjoin.power_basis_dim, adjoin.power_basis_gen, minpoly_gen h, h_sep, h_splits]

end AdjoinIntegralElement

section Induction

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

/--  An intermediate field `S` is finitely generated if there exists `t : finset E` such that
`intermediate_field.adjoin F t = S`. -/
def fg (S : IntermediateField F E) : Prop :=
  ∃ t : Finset E, adjoin F (↑t) = S

theorem fg_adjoin_finset (t : Finset E) : (adjoin F (↑t : Set E)).Fg :=
  ⟨t, rfl⟩

theorem fg_def {S : IntermediateField F E} : S.fg ↔ ∃ t : Set E, Set.Finite t ∧ adjoin F t = S :=
  ⟨fun ⟨t, ht⟩ => ⟨↑t, Set.finite_mem_finset t, ht⟩, fun ⟨t, ht1, ht2⟩ =>
    ⟨ht1.to_finset, by
      rwa [Set.Finite.coe_to_finset]⟩⟩

theorem fg_bot : (⊥ : IntermediateField F E).Fg :=
  ⟨∅, adjoin_empty F E⟩

theorem fg_of_fg_to_subalgebra (S : IntermediateField F E) (h : S.to_subalgebra.fg) : S.fg := by
  cases' h with t ht
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩

theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.fg :=
  S.fg_of_fg_to_subalgebra S.to_subalgebra.fg_of_noetherian

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem induction_on_adjoin_finset (S : Finset E) (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih :
      ∀ K : IntermediateField F E,
        ∀ x ∈ S,
          ∀,
            P K →
              P
                (↑«expr ⟮ , ⟯» K
                    "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»")) :
    P (adjoin F (↑S)) := by
  apply Finset.induction_on' S
  ·
    exact base
  ·
    intro a s h1 _ _ h4
    rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    exact ih (adjoin F s) a h1 h4

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem induction_on_adjoin_fg (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih :
      ∀ K : IntermediateField F E x : E,
        P K → P (↑«expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»"))
    (K : IntermediateField F E) (hK : K.fg) : P K := by
  obtain ⟨S, rfl⟩ := hK
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem induction_on_adjoin [fd : FiniteDimensional F E] (P : IntermediateField F E → Prop) (base : P ⊥)
    (ih :
      ∀ K : IntermediateField F E x : E,
        P K → P (↑«expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»"))
    (K : IntermediateField F E) : P K := by
  let this' : IsNoetherian F E := IsNoetherian.iff_fg.2 inferInstance
  exact induction_on_adjoin_fg P base ih K K.fg_of_noetherian

end Induction

section AlgHomMkAdjoinSplits

variable (F E K : Type _) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] {S : Set E}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [(Command.docComment "/--" " Lifts `L → K` of `F → K` -/")] [] [] [] [] [])
 (Command.def
  "def"
  (Command.declId `lifts [])
  (Command.optDeclSig [] [])
  (Command.declValSimple
   ":="
   (Init.Data.Sigma.Basic.«termΣ_,_»
    "Σ"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Term.app `IntermediateField [`F `E])]))
    ", "
    (Algebra.Algebra.Basic.«term_→ₐ[_]_» `L " →ₐ[" `F "] " `K))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Data.Sigma.Basic.«termΣ_,_»
   "Σ"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `L)] [":" (Term.app `IntermediateField [`F `E])]))
   ", "
   (Algebra.Algebra.Basic.«term_→ₐ[_]_» `L " →ₐ[" `F "] " `K))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Data.Sigma.Basic.«termΣ_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Algebra.Basic.«term_→ₐ[_]_» `L " →ₐ[" `F "] " `K)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Algebra.Basic.«term_→ₐ[_]_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  `L
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- Lifts `L → K` of `F → K` -/ def lifts := Σ L : IntermediateField F E , L →ₐ[ F ] K

variable {F E K}

-- failed to format: format: uncaught backtrack exception
instance
  : PartialOrderₓ ( lifts F E K )
  where
    le x y := x . 1 ≤ y . 1 ∧ ∀ s : x . 1 t : y . 1 , ( s : E ) = t → x . 2 s = y . 2 t
      le_refl x := ⟨ le_reflₓ x . 1 , fun s t hst => congr_argₓ x . 2 ( Subtype.ext hst ) ⟩
      le_trans
        x y z hxy hyz
        :=
        ⟨
          le_transₓ hxy . 1 hyz . 1
            ,
            fun s u hsu => Eq.trans ( hxy . 2 s ⟨ s , hxy . 1 s.mem ⟩ rfl ) ( hyz . 2 ⟨ s , hxy . 1 s.mem ⟩ u hsu )
          ⟩
      le_antisymm
        :=
        by
          rintro ⟨ x1 , x2 ⟩ ⟨ y1 , y2 ⟩ ⟨ hxy1 , hxy2 ⟩ ⟨ hyx1 , hyx2 ⟩
            have : x1 = y1 := le_antisymmₓ hxy1 hyx1
            subst this
            congr
            exact AlgHom.ext fun s => hxy2 s s rfl

-- failed to format: format: uncaught backtrack exception
noncomputable
  instance
    : OrderBot ( lifts F E K )
    where
      bot := ⟨ ⊥ , ( Algebra.ofId F K ) . comp ( bot_equiv F E ) . toAlgHom ⟩
        bot_le
          x
          :=
          ⟨
            bot_le
              ,
              fun
                s t hst
                  =>
                  by
                    cases' intermediate_field.mem_bot.mp s.mem with u hu
                      rw [ show s = ( algebraMap F _ ) u from Subtype.ext hu.symm , AlgHom.commutes ]
                      rw [ show t = ( algebraMap F _ ) u from Subtype.ext ( Eq.trans hu hst ) . symm , AlgHom.commutes ]
            ⟩

noncomputable instance : Inhabited (lifts F E K) :=
  ⟨⊥⟩

theorem lifts.eq_of_le {x y : lifts F E K} (hxy : x ≤ y) (s : x.1) : x.2 s = y.2 ⟨s, hxy.1 s.mem⟩ :=
  hxy.2 s ⟨s, hxy.1 s.mem⟩ rfl

theorem lifts.exists_max_two {c : Set (lifts F E K)} {x y : lifts F E K} (hc : Zorn.Chain (· ≤ ·) c)
    (hx : x ∈ Set.Insert ⊥ c) (hy : y ∈ Set.Insert ⊥ c) : ∃ z : lifts F E K, z ∈ Set.Insert ⊥ c ∧ x ≤ z ∧ y ≤ z := by
  cases' (Zorn.chain_insert hc fun _ _ _ => Or.inl bot_le).total_of_refl hx hy with hxy hyx
  ·
    exact ⟨y, hy, hxy, le_reflₓ y⟩
  ·
    exact ⟨x, hx, le_reflₓ x, hyx⟩

theorem lifts.exists_max_three {c : Set (lifts F E K)} {x y z : lifts F E K} (hc : Zorn.Chain (· ≤ ·) c)
    (hx : x ∈ Set.Insert ⊥ c) (hy : y ∈ Set.Insert ⊥ c) (hz : z ∈ Set.Insert ⊥ c) :
    ∃ w : lifts F E K, w ∈ Set.Insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w := by
  obtain ⟨v, hv, hxv, hyv⟩ := lifts.exists_max_two hc hx hy
  obtain ⟨w, hw, hzw, hvw⟩ := lifts.exists_max_two hc hz hv
  exact ⟨w, hw, le_transₓ hxv hvw, le_transₓ hyv hvw, hzw⟩

/--  An upper bound on a chain of lifts -/
def lifts.upper_bound_intermediate_field {c : Set (lifts F E K)} (hc : Zorn.Chain (· ≤ ·) c) : IntermediateField F E :=
  { Carrier := fun s => ∃ x : lifts F E K, x ∈ Set.Insert ⊥ c ∧ (s ∈ x.1 : Prop),
    zero_mem' := ⟨⊥, Set.mem_insert ⊥ c, zero_mem ⊥⟩, one_mem' := ⟨⊥, Set.mem_insert ⊥ c, one_mem ⊥⟩,
    neg_mem' := by
      rintro _ ⟨x, y, h⟩
      exact ⟨x, ⟨y, x.1.neg_mem h⟩⟩,
    inv_mem' := by
      rintro _ ⟨x, y, h⟩
      exact ⟨x, ⟨y, x.1.inv_mem h⟩⟩,
    add_mem' := by
      rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
      obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy
      exact ⟨z, hz, z.1.add_mem (hxz.1 ha) (hyz.1 hb)⟩,
    mul_mem' := by
      rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
      obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy
      exact ⟨z, hz, z.1.mul_mem (hxz.1 ha) (hyz.1 hb)⟩,
    algebra_map_mem' := fun s => ⟨⊥, Set.mem_insert ⊥ c, algebra_map_mem ⊥ s⟩ }

/--  The lift on the upper bound on a chain of lifts -/
noncomputable def lifts.upper_bound_alg_hom {c : Set (lifts F E K)} (hc : Zorn.Chain (· ≤ ·) c) :
    lifts.upper_bound_intermediate_field hc →ₐ[F] K :=
  { toFun := fun s => (Classical.some s.mem).2 ⟨s, (Classical.some_spec s.mem).2⟩, map_zero' := AlgHom.map_zero _,
    map_one' := AlgHom.map_one _,
    map_add' := fun s t => by
      obtain ⟨w, hw, hxw, hyw, hzw⟩ :=
        lifts.exists_max_three hc (Classical.some_spec s.mem).1 (Classical.some_spec t.mem).1
          (Classical.some_spec (s+t).Mem).1
      rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ← w.2.map_add]
      rfl,
    map_mul' := fun s t => by
      obtain ⟨w, hw, hxw, hyw, hzw⟩ :=
        lifts.exists_max_three hc (Classical.some_spec s.mem).1 (Classical.some_spec t.mem).1
          (Classical.some_spec (s*t).Mem).1
      rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ← w.2.map_mul]
      rfl,
    commutes' := fun _ => AlgHom.commutes _ _ }

/--  An upper bound on a chain of lifts -/
noncomputable def lifts.upper_bound {c : Set (lifts F E K)} (hc : Zorn.Chain (· ≤ ·) c) : lifts F E K :=
  ⟨lifts.upper_bound_intermediate_field hc, lifts.upper_bound_alg_hom hc⟩

theorem lifts.exists_upper_bound (c : Set (lifts F E K)) (hc : Zorn.Chain (· ≤ ·) c) : ∃ ub, ∀, ∀ a ∈ c, ∀, a ≤ ub :=
  ⟨lifts.upper_bound hc, by
    intro x hx
    constructor
    ·
      exact fun s hs => ⟨x, Set.mem_insert_of_mem ⊥ hx, hs⟩
    ·
      intro s t hst
      change x.2 s = (Classical.some t.mem).2 ⟨t, (Classical.some_spec t.mem).2⟩
      obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc (Set.mem_insert_of_mem ⊥ hx) (Classical.some_spec t.mem).1
      rw [lifts.eq_of_le hxz, lifts.eq_of_le hyz]
      exact congr_argₓ z.2 (Subtype.ext hst)⟩

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  Extend a lift `x : lifts F E K` to an element `s : E` whose conjugates are all in `K` -/
noncomputable def lifts.lift_of_splits (x : lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : lifts F E K :=
  let h3 : IsIntegral x.1 s := is_integral_of_is_scalar_tower s h1
  let key : (minpoly x.1 s).Splits x.2.toRingHom :=
    splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero h1))
      ((splits_map_iff _ _).mpr
        (by
          convert h2
          exact RingHom.ext fun y => x.2.commutes y))
      (minpoly.dvd_map_of_is_scalar_tower _ _ _)
  ⟨↑«expr ⟮ , ⟯» x.1 "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»",
    (@algHomEquivSigma F x.1
          (↑«expr ⟮ , ⟯» x.1 "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" :
            IntermediateField F E)
          K _ _ _ _ _ _ _
          (IntermediateField.algebra
            («expr ⟮ , ⟯» x.1 "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»"))
          (IsScalarTower.of_algebra_map_eq fun _ => rfl)).invFun
      ⟨x.2,
        (@alg_hom_adjoin_integral_equiv x.1 _ E _ _ s K _ x.2.toRingHom.toAlgebra h3).invFun
          ⟨root_of_splits x.2.toRingHom key (ne_of_gtₓ (minpoly.degree_pos h3)), by
            simp_rw [mem_roots (map_ne_zero (minpoly.ne_zero h3)), is_root, ← eval₂_eq_eval_map]
            exact map_root_of_splits x.2.toRingHom key (ne_of_gtₓ (minpoly.degree_pos h3))⟩⟩⟩

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
theorem lifts.le_lifts_of_splits (x : lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : x ≤ x.lift_of_splits h1 h2 :=
  ⟨fun z hz =>
    algebra_map_mem
      («expr ⟮ , ⟯» x.1 "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»") ⟨z, hz⟩,
    fun t u htu =>
    Eq.symm
      (by
        rw [←
          show
            algebraMap x.1
                («expr ⟮ , ⟯» x.1 "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»")
                t =
              u from
            Subtype.ext htu]
        let this' : Algebra x.1 K := x.2.toRingHom.toAlgebra
        exact AlgHom.commutes _ t)⟩

theorem lifts.mem_lifts_of_splits (x : lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : s ∈ (x.lift_of_splits h1 h2).1 :=
  mem_adjoin_simple_self x.1 s

theorem lifts.exists_lift_of_splits (x : lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : ∃ y, x ≤ y ∧ s ∈ y.1 :=
  ⟨x.lift_of_splits h1 h2, x.le_lifts_of_splits h1 h2, x.mem_lifts_of_splits h1 h2⟩

theorem alg_hom_mk_adjoin_splits (hK : ∀, ∀ s ∈ S, ∀, IsIntegral F (s : E) ∧ (minpoly F s).Splits (algebraMap F K)) :
    Nonempty (adjoin F S →ₐ[F] K) := by
  obtain ⟨x : lifts F E K, hx⟩ := Zorn.zorn_partial_order lifts.exists_upper_bound
  refine'
    ⟨AlgHom.mk (fun s => x.2 ⟨s, adjoin_le_iff.mpr (fun s hs => _) s.mem⟩) x.2.map_one
        (fun s t => x.2.map_mul ⟨s, _⟩ ⟨t, _⟩) x.2.map_zero (fun s t => x.2.map_add ⟨s, _⟩ ⟨t, _⟩) x.2.commutes⟩
  rcases x.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
  rwa [hx y h1] at h2

theorem alg_hom_mk_adjoin_splits' (hS : adjoin F S = ⊤)
    (hK : ∀, ∀ x ∈ S, ∀, IsIntegral F (x : E) ∧ (minpoly F x).Splits (algebraMap F K)) : Nonempty (E →ₐ[F] K) := by
  cases' alg_hom_mk_adjoin_splits hK with ϕ
  rw [hS] at ϕ
  exact ⟨ϕ.comp top_equiv.symm.to_alg_hom⟩

end AlgHomMkAdjoinSplits

end IntermediateField

section PowerBasis

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

namespace PowerBasis

open IntermediateField

-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:680:4: warning: unsupported notation `«expr ⟮ , ⟯»
-- ././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»
/--  `pb.equiv_adjoin_simple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
noncomputable def equiv_adjoin_simple (pb : PowerBasis K L) :
    «expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»" ≃ₐ[K] L :=
  (adjoin.power_basis pb.is_integral_gen).equivOfMinpoly pb
    (minpoly.eq_of_algebra_map_eq
      (algebraMap («expr ⟮ , ⟯» K "././Mathport/Syntax/Translate/Basic.lean:681:61: unsupported notation `«expr ⟮ , ⟯»")
          L).Injective
      (adjoin.power_basis pb.is_integral_gen).is_integral_gen
      (by
        rw [adjoin.power_basis_gen, adjoin_simple.algebra_map_gen]))

@[simp]
theorem equiv_adjoin_simple_aeval (pb : PowerBasis K L) (f : Polynomial K) :
    pb.equiv_adjoin_simple (aeval (adjoin_simple.gen K pb.gen) f) = aeval pb.gen f :=
  equiv_of_minpoly_aeval _ pb _ f

@[simp]
theorem equiv_adjoin_simple_gen (pb : PowerBasis K L) : pb.equiv_adjoin_simple (adjoin_simple.gen K pb.gen) = pb.gen :=
  equiv_of_minpoly_gen _ pb _

@[simp]
theorem equiv_adjoin_simple_symm_aeval (pb : PowerBasis K L) (f : Polynomial K) :
    pb.equiv_adjoin_simple.symm (aeval pb.gen f) = aeval (adjoin_simple.gen K pb.gen) f := by
  rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_aeval, adjoin.power_basis_gen]

@[simp]
theorem equiv_adjoin_simple_symm_gen (pb : PowerBasis K L) :
    pb.equiv_adjoin_simple.symm pb.gen = adjoin_simple.gen K pb.gen := by
  rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_gen, adjoin.power_basis_gen]

end PowerBasis

end PowerBasis

