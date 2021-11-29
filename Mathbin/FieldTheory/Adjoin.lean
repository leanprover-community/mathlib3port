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

variable(F : Type _)[Field F]{E : Type _}[Field E][Algebra F E](S : Set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.Range (algebraMap F E) ∪ S) with
    algebra_map_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

end AdjoinDef

section Lattice

variable{F : Type _}[Field F]{E : Type _}[Field E][Algebra F E]

@[simp]
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ≤ T :=
  ⟨fun H => le_transₓ (le_transₓ (Set.subset_union_right _ _) Subfield.subset_closure) H,
    fun H =>
      (@Subfield.closure_le E _ (Set.Range (algebraMap F E) ∪ S) T.to_subfield).mpr
        (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

theorem gc : GaloisConnection (adjoin F : Set E → IntermediateField F E) coeₓ :=
  fun _ _ => adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
def gi : GaloisInsertion (adjoin F : Set E → IntermediateField F E) coeₓ :=
  { choice := fun S _ => adjoin F S, gc := IntermediateField.gc,
    le_l_u := fun S => (IntermediateField.gc (S : Set E) (adjoin F S)).1$ le_reflₓ _, choice_eq := fun _ _ => rfl }

instance  : CompleteLattice (IntermediateField F E) :=
  GaloisInsertion.liftCompleteLattice IntermediateField.gi

instance  : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩

theorem mem_bot {x : E} : x ∈ (⊥ : IntermediateField F E) ↔ x ∈ Set.Range (algebraMap F E) :=
  by 
    suffices  : Set.Range (algebraMap F E) = (⊥ : IntermediateField F E)
    ·
      rw [this]
      rfl
    ·
      change Set.Range (algebraMap F E) = Subfield.closure (Set.Range (algebraMap F E) ∪ ∅)
      simp [←Set.image_univ, ←RingHom.map_field_closure]

theorem mem_top {x : E} : x ∈ (⊤ : IntermediateField F E) :=
  Subfield.subset_closure$ Or.inr trivialₓ

@[simp]
theorem bot_to_subalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ :=
  by 
    ext 
    rw [mem_to_subalgebra, Algebra.mem_bot, mem_bot]

@[simp]
theorem top_to_subalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤ :=
  by 
    ext 
    rw [mem_to_subalgebra, iff_true_right Algebra.mem_top]
    exact mem_top

/--  Construct an algebra isomorphism from an equality of intermediate fields -/
@[simps apply]
def equiv_of_eq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T :=
  by 
    refine' { toFun := fun x => ⟨x, _⟩, invFun := fun x => ⟨x, _⟩, .. } <;> tidy

@[simp]
theorem equiv_of_eq_symm {S T : IntermediateField F E} (h : S = T) : (equiv_of_eq h).symm = equiv_of_eq h.symm :=
  rfl

@[simp]
theorem equiv_of_eq_rfl (S : IntermediateField F E) : equiv_of_eq (rfl : S = S) = AlgEquiv.refl :=
  by 
    ext 
    rfl

@[simp]
theorem equiv_of_eq_trans {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U) :
  (equiv_of_eq hST).trans (equiv_of_eq hTU) = equiv_of_eq (trans hST hTU) :=
  rfl

variable(F E)

/-- The bottom intermediate_field is isomorphic to the field. -/
noncomputable def bot_equiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_to_subalgebra).trans (Algebra.botEquiv F E)

variable{F E}

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
      change («expr↑ » x : E) = «expr↑ » (ψ (ψ.symm ⟨x, _⟩))
      rw [AlgEquiv.apply_symm_apply ψ ⟨x, _⟩]
      rfl)

/-- The top intermediate_field is isomorphic to the field. -/
noncomputable def top_equiv : (⊤ : IntermediateField F E) ≃ₐ[F] E :=
  (Subalgebra.equivOfEq _ _ top_to_subalgebra).trans Algebra.topEquiv

@[simp]
theorem top_equiv_def (x : (⊤ : IntermediateField F E)) : top_equiv x = «expr↑ » x :=
  by 
    suffices  : Algebra.toTop (top_equiv x) = Algebra.toTop (x : E)
    ·
      rwa [Subtype.ext_iff] at this 
    exact
      AlgEquiv.apply_symm_apply
        (AlgEquiv.ofBijective Algebra.toTop
          ⟨fun _ _ => Subtype.mk.injₓ,
            fun x =>
              ⟨x.val,
                by 
                  ext 
                  rfl⟩⟩ :
        E ≃ₐ[F] (⊤ : Subalgebra F E))
        (Subalgebra.equivOfEq _ _ top_to_subalgebra x)

@[simp]
theorem coe_bot_eq_self (K : IntermediateField F E) : «expr↑ » (⊥ : IntermediateField K E) = K :=
  by 
    ext 
    rw [mem_lift2, mem_bot]
    exact set.ext_iff.mp Subtype.range_coe x

@[simp]
theorem coe_top_eq_top (K : IntermediateField F E) :
  «expr↑ » (⊤ : IntermediateField K E) = (⊤ : IntermediateField F E) :=
  SetLike.ext_iff.mpr$ fun _ => mem_lift2.trans (iff_of_true mem_top mem_top)

end Lattice

section AdjoinDef

variable(F : Type _)[Field F]{E : Type _}[Field E][Algebra F E](S : Set E)

theorem adjoin_eq_range_algebra_map_adjoin : (adjoin F S : Set E) = Set.Range (algebraMap (adjoin F S) E) :=
  Subtype.range_coe.symm

theorem adjoin.algebra_map_mem (x : F) : algebraMap F E x ∈ adjoin F S :=
  IntermediateField.algebra_map_mem (adjoin F S) x

theorem adjoin.range_algebra_map_subset : Set.Range (algebraMap F E) ⊆ adjoin F S :=
  by 
    intro x hx 
    cases' hx with f hf 
    rw [←hf]
    exact adjoin.algebra_map_mem F S f

instance adjoin.field_coe : CoeTₓ F (adjoin F S) :=
  { coe := fun x => ⟨algebraMap F E x, adjoin.algebra_map_mem F S x⟩ }

theorem subset_adjoin : S ⊆ adjoin F S :=
  fun x hx => Subfield.subset_closure (Or.inr hx)

instance adjoin.set_coe : CoeTₓ S (adjoin F S) :=
  { coe := fun x => ⟨x, subset_adjoin F S (Subtype.mem x)⟩ }

@[mono]
theorem adjoin.mono (T : Set E) (h : S ⊆ T) : adjoin F S ≤ adjoin F T :=
  GaloisConnection.monotone_l gc h

theorem adjoin_contains_field_as_subfield (F : Subfield E) : (F : Set E) ⊆ adjoin F S :=
  fun x hx => adjoin.algebra_map_mem F S ⟨x, hx⟩

theorem subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T ⊆ F) : T ⊆ adjoin F S :=
  fun x hx => (adjoin F S).algebra_map_mem ⟨x, HT hx⟩

theorem subset_adjoin_of_subset_right {T : Set E} (H : T ⊆ S) : T ⊆ adjoin F S :=
  fun x hx => subset_adjoin F S (H hx)

@[simp]
theorem adjoin_empty (F E : Type _) [Field F] [Field E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥ :=
  eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
theorem adjoin_le_subfield {K : Subfield E} (HF : Set.Range (algebraMap F E) ⊆ K) (HS : S ⊆ K) :
  (adjoin F S).toSubfield ≤ K :=
  by 
    apply subfield.closure_le.mpr 
    rw [Set.union_subset_iff]
    exact ⟨HF, HS⟩

theorem adjoin_subset_adjoin_iff {F' : Type _} [Field F'] [Algebra F' E] {S S' : Set E} :
  (adjoin F S : Set E) ⊆ adjoin F' S' ↔ Set.Range (algebraMap F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
  ⟨fun h => ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩,
    fun ⟨hF, hS⟩ => Subfield.closure_le.mpr (Set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
theorem adjoin_adjoin_left (T : Set E) : «expr↑ » (adjoin (adjoin F S) T) = adjoin F (S ∪ T) :=
  by 
    rw [SetLike.ext'_iff]
    change «expr↑ » (adjoin (adjoin F S) T) = _ 
    apply Set.eq_of_subset_of_subset <;> rw [adjoin_subset_adjoin_iff] <;> split 
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

/-- `F[S][T] = F[T][S]` -/
theorem adjoin_adjoin_comm (T : Set E) :
  «expr↑ » (adjoin (adjoin F S) T) = («expr↑ » (adjoin (adjoin F T) S) : IntermediateField F E) :=
  by 
    rw [adjoin_adjoin_left, adjoin_adjoin_left, Set.union_comm]

theorem adjoin_map {E' : Type _} [Field E'] [Algebra F E'] (f : E →ₐ[F] E') : (adjoin F S).map f = adjoin F (f '' S) :=
  by 
    ext x 
    show
      x ∈ (Subfield.closure (Set.Range (algebraMap F E) ∪ S)).map (f : E →+* E') ↔
        x ∈ Subfield.closure (Set.Range (algebraMap F E') ∪ f '' S)
    rw [RingHom.map_field_closure, Set.image_union, ←Set.range_comp, ←RingHom.coe_comp, f.comp_algebra_map]
    rfl

theorem algebra_adjoin_le_adjoin : Algebra.adjoin F S ≤ (adjoin F S).toSubalgebra :=
  Algebra.adjoin_le (subset_adjoin _ _)

theorem adjoin_eq_algebra_adjoin (inv_mem : ∀ x (_ : x ∈ Algebra.adjoin F S), x⁻¹ ∈ Algebra.adjoin F S) :
  (adjoin F S).toSubalgebra = Algebra.adjoin F S :=
  le_antisymmₓ
    (show
      adjoin F S ≤
        { Algebra.adjoin F S with neg_mem' := fun x => (Algebra.adjoin F S).neg_mem, inv_mem' := inv_mem } from
      adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)

theorem eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E) (h : K.to_subalgebra = Algebra.adjoin F S) :
  K = adjoin F S :=
  by 
    apply to_subalgebra_injective 
    rw [h]
    refine' (adjoin_eq_algebra_adjoin _ _ _).symm 
    intro x 
    convert K.inv_mem 
    rw [←h]
    rfl

@[elab_as_eliminator]
theorem adjoin_induction {s : Set E} {p : E → Prop} {x} (h : x ∈ adjoin F s) (Hs : ∀ x (_ : x ∈ s), p x)
  (Hmap : ∀ x, p (algebraMap F E x)) (Hadd : ∀ x y, p x → p y → p (x+y)) (Hneg : ∀ x, p x → p (-x))
  (Hinv : ∀ x, p x → p (x⁻¹)) (Hmul : ∀ x y, p x → p y → p (x*y)) : p x :=
  Subfield.closure_induction h (fun x hx => Or.cases_on hx (fun ⟨x, hx⟩ => hx ▸ Hmap x) (Hs x))
    ((algebraMap F E).map_one ▸ Hmap 1) Hadd Hneg Hinv Hmul

/--
Variation on `set.insert` to enable good notation for adjoining elements to fields.
Used to preferentially use `singleton` rather than `insert` when adjoining one element.
-/
class insert{α : Type _}(s : Set α) where 
  insert : α → Set α

instance (priority := 1000)insert_empty {α : Type _} : insert (∅ : Set α) :=
  { insert := fun x => @singleton _ _ Set.hasSingleton x }

instance (priority := 900)insert_nonempty {α : Type _} (s : Set α) : insert s :=
  { insert := fun x => Set.Insert x s }

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:265:9: unsupported: advanced prec syntax
notation K `⟮`:std.prec.max_plus l:(foldr `, ` (h t, insert.insert t h) «expr∅»()) `⟯` := adjoin K l

section AdjoinSimple

variable(α : E)

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem mem_adjoin_simple_self : «expr ∈ »(α, «expr ⟮ , ⟯»(F, [α])) := subset_adjoin F {α} (set.mem_singleton α)

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- generator of `F⟮α⟯` -/ def adjoin_simple.gen : «expr ⟮ , ⟯»(F, [α]) := ⟨α, mem_adjoin_simple_self F α⟩

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_simple.algebra_map_gen : «expr = »(algebra_map «expr ⟮ , ⟯»(F, [α]) E (adjoin_simple.gen F α), α) :=
rfl

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:341:40: in rw: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
@[simp] theorem adjoin_simple.is_integral_gen : «expr ↔ »(is_integral F (adjoin_simple.gen F α), is_integral F α) :=
by { conv_rhs [] [] { rw ["<-", expr adjoin_simple.algebra_map_gen F α] },
  rw [expr is_integral_algebra_map_iff (algebra_map «expr ⟮ , ⟯»(F, [α]) E).injective] [],
  apply_instance }

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin_simple_adjoin_simple
(β : E) : «expr = »(«expr↑ »(«expr ⟮ , ⟯»(«expr ⟮ , ⟯»(F, [α]), [β])), «expr ⟮ , ⟯»(F, [α, β])) :=
adjoin_adjoin_left _ _ _

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin_simple_comm
(β : E) : «expr = »(«expr↑ »(«expr ⟮ , ⟯»(«expr ⟮ , ⟯»(F, [α]), [β])), («expr↑ »(«expr ⟮ , ⟯»(«expr ⟮ , ⟯»(F, [β]), [α])) : intermediate_field F E)) :=
adjoin_adjoin_comm _ _ _

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin_simple_to_subalgebra_of_integral
(hα : is_integral F α) : «expr = »(«expr ⟮ , ⟯»(F, [α]).to_subalgebra, algebra.adjoin F {α}) :=
begin
  apply [expr adjoin_eq_algebra_adjoin],
  intros [ident x, ident hx],
  by_cases [expr «expr = »(x, 0)],
  { rw ["[", expr h, ",", expr inv_zero, "]"] [],
    exact [expr subalgebra.zero_mem (algebra.adjoin F {α})] },
  let [ident ϕ] [] [":=", expr alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly F α],
  haveI [] [] [":=", expr minpoly.irreducible hα],
  suffices [] [":", expr «expr = »(«expr * »(ϕ ⟨x, hx⟩, «expr ⁻¹»(ϕ ⟨x, hx⟩)), 1)],
  { convert [] [expr subtype.mem (ϕ.symm «expr ⁻¹»(ϕ ⟨x, hx⟩))] [],
    refine [expr (eq_inv_of_mul_right_eq_one _).symm],
    apply_fun [expr ϕ.symm] ["at", ident this] [],
    rw ["[", expr alg_equiv.map_one, ",", expr alg_equiv.map_mul, ",", expr alg_equiv.symm_apply_apply, "]"] ["at", ident this],
    rw ["[", "<-", expr subsemiring.coe_one, ",", "<-", expr this, ",", expr subsemiring.coe_mul, ",", expr subtype.coe_mk, "]"] [] },
  rw [expr mul_inv_cancel (mt (λ key, _) h)] [],
  rw ["<-", expr ϕ.map_zero] ["at", ident key],
  change [expr «expr = »(«expr↑ »((⟨x, hx⟩ : algebra.adjoin F {α})), _)] [] [],
  rw ["[", expr ϕ.injective key, ",", expr subalgebra.coe_zero, "]"] []
end

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable{F : Type _}[Field F]{E : Type _}[Field E][Algebra F E]{α : E}{S : Set E}

@[simp]
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : IntermediateField F E) :=
  by 
    rw [eq_bot_iff, adjoin_le_iff]
    rfl

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
@[simp]
theorem adjoin_simple_eq_bot_iff : «expr ↔ »(«expr = »(«expr ⟮ , ⟯»(F, [α]), «expr⊥»()), «expr ∈ »(α, («expr⊥»() : intermediate_field F E))) :=
by { rw [expr adjoin_eq_bot_iff] [],
  exact [expr set.singleton_subset_iff] }

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
@[simp] theorem adjoin_zero : «expr = »(«expr ⟮ , ⟯»(F, [(0 : E)]), «expr⊥»()) :=
adjoin_simple_eq_bot_iff.mpr (zero_mem «expr⊥»())

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
@[simp] theorem adjoin_one : «expr = »(«expr ⟮ , ⟯»(F, [(1 : E)]), «expr⊥»()) :=
adjoin_simple_eq_bot_iff.mpr (one_mem «expr⊥»())

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
@[simp] theorem adjoin_int (n : exprℤ()) : «expr = »(«expr ⟮ , ⟯»(F, [(n : E)]), «expr⊥»()) :=
adjoin_simple_eq_bot_iff.mpr (coe_int_mem «expr⊥»() n)

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
@[simp] theorem adjoin_nat (n : exprℕ()) : «expr = »(«expr ⟮ , ⟯»(F, [(n : E)]), «expr⊥»()) :=
adjoin_simple_eq_bot_iff.mpr (coe_int_mem «expr⊥»() n)

section AdjoinDim

open FiniteDimensional Module

variable{K L : IntermediateField F E}

@[simp]
theorem dim_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥ :=
  by 
    rw [←to_subalgebra_eq_iff, ←dim_eq_dim_subalgebra, Subalgebra.dim_eq_one_iff, bot_to_subalgebra]

@[simp]
theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ :=
  by 
    rw [←to_subalgebra_eq_iff, ←finrank_eq_finrank_subalgebra, Subalgebra.finrank_eq_one_iff, bot_to_subalgebra]

theorem dim_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans dim_eq_one_iff adjoin_eq_bot_iff

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem dim_adjoin_simple_eq_one_iff : «expr ↔ »(«expr = »(module.rank F «expr ⟮ , ⟯»(F, [α]), 1), «expr ∈ »(α, («expr⊥»() : intermediate_field F E))) :=
by { rw [expr dim_adjoin_eq_one_iff] [],
  exact [expr set.singleton_subset_iff] }

theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem finrank_adjoin_simple_eq_one_iff : «expr ↔ »(«expr = »(finrank F «expr ⟮ , ⟯»(F, [α]), 1), «expr ∈ »(α, («expr⊥»() : intermediate_field F E))) :=
by { rw ["[", expr finrank_adjoin_eq_one_iff, "]"] [],
  exact [expr set.singleton_subset_iff] }

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_dim_adjoin_eq_one
(h : ∀
 x : E, «expr = »(module.rank F «expr ⟮ , ⟯»(F, [x]), 1)) : «expr = »((«expr⊥»() : intermediate_field F E), «expr⊤»()) :=
begin
  ext [] [] [],
  rw [expr iff_true_right intermediate_field.mem_top] [],
  exact [expr dim_adjoin_simple_eq_one_iff.mp (h x)]
end

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem bot_eq_top_of_finrank_adjoin_eq_one
(h : ∀
 x : E, «expr = »(finrank F «expr ⟮ , ⟯»(F, [x]), 1)) : «expr = »((«expr⊥»() : intermediate_field F E), «expr⊤»()) :=
begin
  ext [] [] [],
  rw [expr iff_true_right intermediate_field.mem_top] [],
  exact [expr finrank_adjoin_simple_eq_one_iff.mp (h x)]
end

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem subsingleton_of_dim_adjoin_eq_one
(h : ∀ x : E, «expr = »(module.rank F «expr ⟮ , ⟯»(F, [x]), 1)) : subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_dim_adjoin_eq_one h)

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem subsingleton_of_finrank_adjoin_eq_one
(h : ∀ x : E, «expr = »(finrank F «expr ⟮ , ⟯»(F, [x]), 1)) : subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_eq_one h)

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:341:40: in exact: ././Mathport/Syntax/Translate/Basic.lean:341:40: in linarith: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
theorem bot_eq_top_of_finrank_adjoin_le_one
[finite_dimensional F E]
(h : ∀
 x : E, «expr ≤ »(finrank F «expr ⟮ , ⟯»(F, [x]), 1)) : «expr = »((«expr⊥»() : intermediate_field F E), «expr⊤»()) :=
begin
  apply [expr bot_eq_top_of_finrank_adjoin_eq_one],
  exact [expr λ
   x, by linarith [] [] ["[", expr h x, ",", expr show «expr < »(0, finrank F «expr ⟮ , ⟯»(F, [x])), from finrank_pos, "]"]]
end

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem subsingleton_of_finrank_adjoin_le_one
[finite_dimensional F E]
(h : ∀ x : E, «expr ≤ »(finrank F «expr ⟮ , ⟯»(F, [x]), 1)) : subsingleton (intermediate_field F E) :=
subsingleton_of_bot_eq_top (bot_eq_top_of_finrank_adjoin_le_one h)

end AdjoinDim

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

variable{F : Type _}[Field F]{E : Type _}[Field E][Algebra F E]{α : E}

variable{K : Type _}[Field K][Algebra F K]

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:341:40: in have: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem minpoly_gen {α : E} (h : is_integral F α) : «expr = »(minpoly F (adjoin_simple.gen F α), minpoly F α) :=
begin
  rw ["<-", expr adjoin_simple.algebra_map_gen F α] ["at", ident h],
  have [ident inj] [] [":=", expr (algebra_map «expr ⟮ , ⟯»(F, [α]) E).injective],
  exact [expr minpoly.eq_of_algebra_map_eq inj ((is_integral_algebra_map_iff inj).mp h) (adjoin_simple.algebra_map_gen _ _).symm]
end

variable(F)

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:341:40: in exact: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem aeval_gen_minpoly (α : E) : «expr = »(aeval (adjoin_simple.gen F α) (minpoly F α), 0) :=
begin
  ext [] [] [],
  convert [] [expr minpoly.aeval F α] [],
  conv [] ["in", expr aeval α] { rw ["[", "<-", expr adjoin_simple.algebra_map_gen F α, "]"] },
  exact [expr is_scalar_tower.algebra_map_aeval F «expr ⟮ , ⟯»(F, [α]) E _ _]
end

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:341:40: in suffices: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- algebra isomorphism between `adjoin_root` and `F⟮α⟯` -/
noncomputable
def adjoin_root_equiv_adjoin
(h : is_integral F α) : «expr ≃ₐ[ ] »(adjoin_root (minpoly F α), F, «expr ⟮ , ⟯»(F, [α])) :=
alg_equiv.of_bijective (adjoin_root.lift_hom (minpoly F α) (adjoin_simple.gen F α) (aeval_gen_minpoly F α)) (begin
   set [] [ident f] [] [":="] [expr adjoin_root.lift _ _ (aeval_gen_minpoly F α : _)] [],
   haveI [] [] [":=", expr minpoly.irreducible h],
   split,
   { exact [expr ring_hom.injective f] },
   { suffices [] [":", expr «expr ≤ »(«expr ⟮ , ⟯»(F, [α]).to_subfield, ring_hom.field_range («expr ⟮ , ⟯»(F, [α]).to_subfield.subtype.comp f))],
     { exact [expr λ x, Exists.cases_on (this (subtype.mem x)) (λ y hy, ⟨y, subtype.ext hy⟩)] },
     exact [expr subfield.closure_le.mpr (set.union_subset (λ
        x
        hx, Exists.cases_on hx (λ
         y
         hy, ⟨y, by { rw ["[", expr ring_hom.comp_apply, ",", expr adjoin_root.lift_of, "]"] [],
            exact [expr hy] }⟩)) (set.singleton_subset_iff.mpr ⟨adjoin_root.root (minpoly F α), by { rw ["[", expr ring_hom.comp_apply, ",", expr adjoin_root.lift_root, "]"] [],
           refl }⟩))] }
 end)

theorem adjoin_root_equiv_adjoin_apply_root (h : IsIntegral F α) :
  adjoin_root_equiv_adjoin F h (AdjoinRoot.root (minpoly F α)) = adjoin_simple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)

section PowerBasis

variable{L : Type _}[Field L][Algebra K L]

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
noncomputable
def power_basis_aux {x : L} (hx : is_integral K x) : basis (fin (minpoly K x).nat_degree) K «expr ⟮ , ⟯»(K, [x]) :=
(adjoin_root.power_basis (minpoly.ne_zero hx)).basis.map (adjoin_root_equiv_adjoin K hx).to_linear_equiv

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
where `d` is the degree of the minimal polynomial of `x`. -/
@[simps #[]]
noncomputable
def adjoin.power_basis {x : L} (hx : is_integral K x) : power_basis K «expr ⟮ , ⟯»(K, [x]) :=
{ gen := adjoin_simple.gen K x,
  dim := (minpoly K x).nat_degree,
  basis := power_basis_aux hx,
  basis_eq_pow := λ
  i, by rw ["[", expr power_basis_aux, ",", expr basis.map_apply, ",", expr power_basis.basis_eq_pow, ",", expr alg_equiv.to_linear_equiv_apply, ",", expr alg_equiv.map_pow, ",", expr adjoin_root.power_basis_gen, ",", expr adjoin_root_equiv_adjoin_apply_root, "]"] [] }

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin.finite_dimensional {x : L} (hx : is_integral K x) : finite_dimensional K «expr ⟮ , ⟯»(K, [x]) :=
power_basis.finite_dimensional (adjoin.power_basis hx)

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem adjoin.finrank
{x : L}
(hx : is_integral K x) : «expr = »(finite_dimensional.finrank K «expr ⟮ , ⟯»(K, [x]), (minpoly K x).nat_degree) :=
begin
  rw [expr power_basis.finrank (adjoin.power_basis hx : _)] [],
  refl
end

end PowerBasis

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
of `minpoly α` in `K`. -/
noncomputable
def alg_hom_adjoin_integral_equiv
(h : is_integral F α) : «expr ≃ »(«expr →ₐ[ ] »(«expr ⟮ , ⟯»(F, [α]), F, K), {x // «expr ∈ »(x, ((minpoly F α).map (algebra_map F K)).roots)}) :=
(adjoin.power_basis h).lift_equiv'.trans ((equiv.refl _).subtype_equiv (λ
  x, by rw ["[", expr adjoin.power_basis_gen, ",", expr minpoly_gen h, ",", expr equiv.refl_apply, "]"] []))

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/
noncomputable
def fintype_of_alg_hom_adjoin_integral (h : is_integral F α) : fintype «expr →ₐ[ ] »(«expr ⟮ , ⟯»(F, [α]), F, K) :=
power_basis.alg_hom.fintype (adjoin.power_basis h)

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem card_alg_hom_adjoin_integral
(h : is_integral F α)
(h_sep : (minpoly F α).separable)
(h_splits : (minpoly F α).splits (algebra_map F K)) : «expr = »(@fintype.card «expr →ₐ[ ] »(«expr ⟮ , ⟯»(F, [α]), F, K) (fintype_of_alg_hom_adjoin_integral F h), (minpoly F α).nat_degree) :=
begin
  rw [expr alg_hom.card_of_power_basis] []; simp [] [] ["only"] ["[", expr adjoin.power_basis_dim, ",", expr adjoin.power_basis_gen, ",", expr minpoly_gen h, ",", expr h_sep, ",", expr h_splits, "]"] [] []
end

end AdjoinIntegralElement

section Induction

variable{F : Type _}[Field F]{E : Type _}[Field E][Algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : finset E` such that
`intermediate_field.adjoin F t = S`. -/
def fg (S : IntermediateField F E) : Prop :=
  ∃ t : Finset E, adjoin F («expr↑ » t) = S

theorem fg_adjoin_finset (t : Finset E) : (adjoin F («expr↑ » t : Set E)).Fg :=
  ⟨t, rfl⟩

theorem fg_def {S : IntermediateField F E} : S.fg ↔ ∃ t : Set E, Set.Finite t ∧ adjoin F t = S :=
  ⟨fun ⟨t, ht⟩ => ⟨«expr↑ » t, Set.finite_mem_finset t, ht⟩,
    fun ⟨t, ht1, ht2⟩ =>
      ⟨ht1.to_finset,
        by 
          rwa [Set.Finite.coe_to_finset]⟩⟩

theorem fg_bot : (⊥ : IntermediateField F E).Fg :=
  ⟨∅, adjoin_empty F E⟩

theorem fg_of_fg_to_subalgebra (S : IntermediateField F E) (h : S.to_subalgebra.fg) : S.fg :=
  by 
    cases' h with t ht 
    exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩

theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.fg :=
  S.fg_of_fg_to_subalgebra S.to_subalgebra.fg_of_noetherian

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem induction_on_adjoin_finset
(S : finset E)
(P : intermediate_field F E → exprProp())
(base : P «expr⊥»())
(ih : ∀
 (K : intermediate_field F E)
 (x «expr ∈ » S), P K → P «expr↑ »(«expr ⟮ , ⟯»(K, [x]))) : P (adjoin F «expr↑ »(S)) :=
begin
  apply [expr finset.induction_on' S],
  { exact [expr base] },
  { intros [ident a, ident s, ident h1, "_", "_", ident h4],
    rw ["[", expr finset.coe_insert, ",", expr set.insert_eq, ",", expr set.union_comm, ",", "<-", expr adjoin_adjoin_left, "]"] [],
    exact [expr ih (adjoin F s) a h1 h4] }
end

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem induction_on_adjoin_fg
(P : intermediate_field F E → exprProp())
(base : P «expr⊥»())
(ih : ∀ (K : intermediate_field F E) (x : E), P K → P «expr↑ »(«expr ⟮ , ⟯»(K, [x])))
(K : intermediate_field F E)
(hK : K.fg) : P K :=
begin
  obtain ["⟨", ident S, ",", ident rfl, "⟩", ":=", expr hK],
  exact [expr induction_on_adjoin_finset S P base (λ K x _ hK, ih K x hK)]
end

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem induction_on_adjoin
[fd : finite_dimensional F E]
(P : intermediate_field F E → exprProp())
(base : P «expr⊥»())
(ih : ∀ (K : intermediate_field F E) (x : E), P K → P «expr↑ »(«expr ⟮ , ⟯»(K, [x])))
(K : intermediate_field F E) : P K :=
begin
  letI [] [":", expr is_noetherian F E] [":=", expr is_noetherian.iff_fg.2 infer_instance],
  exact [expr induction_on_adjoin_fg P base ih K K.fg_of_noetherian]
end

end Induction

section AlgHomMkAdjoinSplits

variable(F E K : Type _)[Field F][Field E][Field K][Algebra F E][Algebra F K]{S : Set E}

/-- Lifts `L → K` of `F → K` -/
def lifts :=
  ΣL : IntermediateField F E, L →ₐ[F] K

variable{F E K}

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance : partial_order (lifts F E K) :=
{ le := λ x y, «expr ∧ »(«expr ≤ »(x.1, y.1), ∀ (s : x.1) (t : y.1), «expr = »((s : E), t) → «expr = »(x.2 s, y.2 t)),
  le_refl := λ x, ⟨le_refl x.1, λ s t hst, congr_arg x.2 (subtype.ext hst)⟩,
  le_trans := λ
  x
  y
  z
  hxy
  hyz, ⟨le_trans hxy.1 hyz.1, λ s u hsu, eq.trans (hxy.2 s ⟨s, hxy.1 s.mem⟩ rfl) (hyz.2 ⟨s, hxy.1 s.mem⟩ u hsu)⟩,
  le_antisymm := begin
    rintros ["⟨", ident x1, ",", ident x2, "⟩", "⟨", ident y1, ",", ident y2, "⟩", "⟨", ident hxy1, ",", ident hxy2, "⟩", "⟨", ident hyx1, ",", ident hyx2, "⟩"],
    have [] [":", expr «expr = »(x1, y1)] [":=", expr le_antisymm hxy1 hyx1],
    subst [expr this],
    congr,
    exact [expr alg_hom.ext (λ s, hxy2 s s rfl)]
  end }

noncomputable instance  : OrderBot (lifts F E K) :=
  { bot := ⟨⊥, (Algebra.ofId F K).comp (bot_equiv F E).toAlgHom⟩,
    bot_le :=
      fun x =>
        ⟨bot_le,
          fun s t hst =>
            by 
              cases' intermediate_field.mem_bot.mp s.mem with u hu 
              rw [show s = (algebraMap F _) u from Subtype.ext hu.symm, AlgHom.commutes]
              rw [show t = (algebraMap F _) u from Subtype.ext (Eq.trans hu hst).symm, AlgHom.commutes]⟩ }

noncomputable instance  : Inhabited (lifts F E K) :=
  ⟨⊥⟩

theorem lifts.eq_of_le {x y : lifts F E K} (hxy : x ≤ y) (s : x.1) : x.2 s = y.2 ⟨s, hxy.1 s.mem⟩ :=
  hxy.2 s ⟨s, hxy.1 s.mem⟩ rfl

theorem lifts.exists_max_two {c : Set (lifts F E K)} {x y : lifts F E K} (hc : Zorn.Chain (· ≤ ·) c)
  (hx : x ∈ Set.Insert ⊥ c) (hy : y ∈ Set.Insert ⊥ c) : ∃ z : lifts F E K, z ∈ Set.Insert ⊥ c ∧ x ≤ z ∧ y ≤ z :=
  by 
    cases' (Zorn.chain_insert hc fun _ _ _ => Or.inl bot_le).total_of_refl hx hy with hxy hyx
    ·
      exact ⟨y, hy, hxy, le_reflₓ y⟩
    ·
      exact ⟨x, hx, le_reflₓ x, hyx⟩

theorem lifts.exists_max_three {c : Set (lifts F E K)} {x y z : lifts F E K} (hc : Zorn.Chain (· ≤ ·) c)
  (hx : x ∈ Set.Insert ⊥ c) (hy : y ∈ Set.Insert ⊥ c) (hz : z ∈ Set.Insert ⊥ c) :
  ∃ w : lifts F E K, w ∈ Set.Insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w :=
  by 
    obtain ⟨v, hv, hxv, hyv⟩ := lifts.exists_max_two hc hx hy 
    obtain ⟨w, hw, hzw, hvw⟩ := lifts.exists_max_two hc hz hv 
    exact ⟨w, hw, le_transₓ hxv hvw, le_transₓ hyv hvw, hzw⟩

/-- An upper bound on a chain of lifts -/
def lifts.upper_bound_intermediate_field {c : Set (lifts F E K)} (hc : Zorn.Chain (· ≤ ·) c) : IntermediateField F E :=
  { Carrier := fun s => ∃ x : lifts F E K, x ∈ Set.Insert ⊥ c ∧ (s ∈ x.1 : Prop),
    zero_mem' := ⟨⊥, Set.mem_insert ⊥ c, zero_mem ⊥⟩, one_mem' := ⟨⊥, Set.mem_insert ⊥ c, one_mem ⊥⟩,
    neg_mem' :=
      by 
        rintro _ ⟨x, y, h⟩
        exact ⟨x, ⟨y, x.1.neg_mem h⟩⟩,
    inv_mem' :=
      by 
        rintro _ ⟨x, y, h⟩
        exact ⟨x, ⟨y, x.1.inv_mem h⟩⟩,
    add_mem' :=
      by 
        rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy 
        exact ⟨z, hz, z.1.add_mem (hxz.1 ha) (hyz.1 hb)⟩,
    mul_mem' :=
      by 
        rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
        obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy 
        exact ⟨z, hz, z.1.mul_mem (hxz.1 ha) (hyz.1 hb)⟩,
    algebra_map_mem' := fun s => ⟨⊥, Set.mem_insert ⊥ c, algebra_map_mem ⊥ s⟩ }

/-- The lift on the upper bound on a chain of lifts -/
noncomputable def lifts.upper_bound_alg_hom {c : Set (lifts F E K)} (hc : Zorn.Chain (· ≤ ·) c) :
  lifts.upper_bound_intermediate_field hc →ₐ[F] K :=
  { toFun := fun s => (Classical.some s.mem).2 ⟨s, (Classical.some_spec s.mem).2⟩, map_zero' := AlgHom.map_zero _,
    map_one' := AlgHom.map_one _,
    map_add' :=
      fun s t =>
        by 
          obtain ⟨w, hw, hxw, hyw, hzw⟩ :=
            lifts.exists_max_three hc (Classical.some_spec s.mem).1 (Classical.some_spec t.mem).1
              (Classical.some_spec (s+t).Mem).1
          rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ←w.2.map_add]
          rfl,
    map_mul' :=
      fun s t =>
        by 
          obtain ⟨w, hw, hxw, hyw, hzw⟩ :=
            lifts.exists_max_three hc (Classical.some_spec s.mem).1 (Classical.some_spec t.mem).1
              (Classical.some_spec (s*t).Mem).1
          rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ←w.2.map_mul]
          rfl,
    commutes' := fun _ => AlgHom.commutes _ _ }

/-- An upper bound on a chain of lifts -/
noncomputable def lifts.upper_bound {c : Set (lifts F E K)} (hc : Zorn.Chain (· ≤ ·) c) : lifts F E K :=
  ⟨lifts.upper_bound_intermediate_field hc, lifts.upper_bound_alg_hom hc⟩

theorem lifts.exists_upper_bound (c : Set (lifts F E K)) (hc : Zorn.Chain (· ≤ ·) c) : ∃ ub, ∀ a (_ : a ∈ c), a ≤ ub :=
  ⟨lifts.upper_bound hc,
    by 
      intro x hx 
      split 
      ·
        exact fun s hs => ⟨x, Set.mem_insert_of_mem ⊥ hx, hs⟩
      ·
        intro s t hst 
        change x.2 s = (Classical.some t.mem).2 ⟨t, (Classical.some_spec t.mem).2⟩
        obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc (Set.mem_insert_of_mem ⊥ hx) (Classical.some_spec t.mem).1
        rw [lifts.eq_of_le hxz, lifts.eq_of_le hyz]
        exact congr_argₓ z.2 (Subtype.ext hst)⟩

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- Extend a lift `x : lifts F E K` to an element `s : E` whose conjugates are all in `K` -/
noncomputable
def lifts.lift_of_splits
(x : lifts F E K)
{s : E}
(h1 : is_integral F s)
(h2 : (minpoly F s).splits (algebra_map F K)) : lifts F E K :=
let h3 : is_integral x.1 s := is_integral_of_is_scalar_tower s h1 in
let key : (minpoly x.1 s).splits x.2.to_ring_hom := splits_of_splits_of_dvd _ (map_ne_zero (minpoly.ne_zero h1)) ((splits_map_iff _ _).mpr (by { convert [] [expr h2] [],
        exact [expr ring_hom.ext (λ y, x.2.commutes y)] })) (minpoly.dvd_map_of_is_scalar_tower _ _ _) in
⟨«expr↑ »(«expr ⟮ , ⟯»(x.1, [s])), (@alg_hom_equiv_sigma F x.1 («expr↑ »(«expr ⟮ , ⟯»(x.1, [s])) : intermediate_field F E) K _ _ _ _ _ _ _ (intermediate_field.algebra «expr ⟮ , ⟯»(x.1, [s])) (is_scalar_tower.of_algebra_map_eq (λ
    _, rfl))).inv_fun ⟨x.2, (@alg_hom_adjoin_integral_equiv x.1 _ E _ _ s K _ x.2.to_ring_hom.to_algebra h3).inv_fun ⟨root_of_splits x.2.to_ring_hom key (ne_of_gt (minpoly.degree_pos h3)), by { simp_rw ["[", expr mem_roots (map_ne_zero (minpoly.ne_zero h3)), ",", expr is_root, ",", "<-", expr eval₂_eq_eval_map, "]"] [],
     exact [expr map_root_of_splits x.2.to_ring_hom key (ne_of_gt (minpoly.degree_pos h3))] }⟩⟩⟩

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
theorem lifts.le_lifts_of_splits
(x : lifts F E K)
{s : E}
(h1 : is_integral F s)
(h2 : (minpoly F s).splits (algebra_map F K)) : «expr ≤ »(x, x.lift_of_splits h1 h2) :=
⟨λ
 z
 hz, algebra_map_mem «expr ⟮ , ⟯»(x.1, [s]) ⟨z, hz⟩, λ
 t
 u
 htu, eq.symm (begin
    rw ["[", "<-", expr show «expr = »(algebra_map x.1 «expr ⟮ , ⟯»(x.1, [s]) t, u), from subtype.ext htu, "]"] [],
    letI [] [":", expr algebra x.1 K] [":=", expr x.2.to_ring_hom.to_algebra],
    exact [expr alg_hom.commutes _ t]
  end)⟩

theorem lifts.mem_lifts_of_splits (x : lifts F E K) {s : E} (h1 : IsIntegral F s)
  (h2 : (minpoly F s).Splits (algebraMap F K)) : s ∈ (x.lift_of_splits h1 h2).1 :=
  mem_adjoin_simple_self x.1 s

theorem lifts.exists_lift_of_splits (x : lifts F E K) {s : E} (h1 : IsIntegral F s)
  (h2 : (minpoly F s).Splits (algebraMap F K)) : ∃ y, x ≤ y ∧ s ∈ y.1 :=
  ⟨x.lift_of_splits h1 h2, x.le_lifts_of_splits h1 h2, x.mem_lifts_of_splits h1 h2⟩

theorem alg_hom_mk_adjoin_splits (hK : ∀ s (_ : s ∈ S), IsIntegral F (s : E) ∧ (minpoly F s).Splits (algebraMap F K)) :
  Nonempty (adjoin F S →ₐ[F] K) :=
  by 
    obtain ⟨x : lifts F E K, hx⟩ := Zorn.zorn_partial_order lifts.exists_upper_bound 
    refine'
      ⟨AlgHom.mk (fun s => x.2 ⟨s, adjoin_le_iff.mpr (fun s hs => _) s.mem⟩) x.2.map_one
          (fun s t => x.2.map_mul ⟨s, _⟩ ⟨t, _⟩) x.2.map_zero (fun s t => x.2.map_add ⟨s, _⟩ ⟨t, _⟩) x.2.commutes⟩
    rcases x.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
    rwa [hx y h1] at h2

theorem alg_hom_mk_adjoin_splits' (hS : adjoin F S = ⊤)
  (hK : ∀ x (_ : x ∈ S), IsIntegral F (x : E) ∧ (minpoly F x).Splits (algebraMap F K)) : Nonempty (E →ₐ[F] K) :=
  by 
    cases' alg_hom_mk_adjoin_splits hK with ϕ 
    rw [hS] at ϕ 
    exact ⟨ϕ.comp top_equiv.symm.to_alg_hom⟩

end AlgHomMkAdjoinSplits

end IntermediateField

section PowerBasis

variable{K L : Type _}[Field K][Field L][Algebra K L]

namespace PowerBasis

open IntermediateField

-- error in FieldTheory.Adjoin: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr ⟮ , ⟯»
/-- `pb.equiv_adjoin_simple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/
noncomputable
def equiv_adjoin_simple (pb : power_basis K L) : «expr ≃ₐ[ ] »(«expr ⟮ , ⟯»(K, [pb.gen]), K, L) :=
(adjoin.power_basis pb.is_integral_gen).equiv_of_minpoly pb (minpoly.eq_of_algebra_map_eq (algebra_map «expr ⟮ , ⟯»(K, [pb.gen]) L).injective (adjoin.power_basis pb.is_integral_gen).is_integral_gen (by rw ["[", expr adjoin.power_basis_gen, ",", expr adjoin_simple.algebra_map_gen, "]"] []))

@[simp]
theorem equiv_adjoin_simple_aeval (pb : PowerBasis K L) (f : Polynomial K) :
  pb.equiv_adjoin_simple (aeval (adjoin_simple.gen K pb.gen) f) = aeval pb.gen f :=
  equiv_of_minpoly_aeval _ pb _ f

@[simp]
theorem equiv_adjoin_simple_gen (pb : PowerBasis K L) : pb.equiv_adjoin_simple (adjoin_simple.gen K pb.gen) = pb.gen :=
  equiv_of_minpoly_gen _ pb _

@[simp]
theorem equiv_adjoin_simple_symm_aeval (pb : PowerBasis K L) (f : Polynomial K) :
  pb.equiv_adjoin_simple.symm (aeval pb.gen f) = aeval (adjoin_simple.gen K pb.gen) f :=
  by 
    rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_aeval, adjoin.power_basis_gen]

@[simp]
theorem equiv_adjoin_simple_symm_gen (pb : PowerBasis K L) :
  pb.equiv_adjoin_simple.symm pb.gen = adjoin_simple.gen K pb.gen :=
  by 
    rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_gen, adjoin.power_basis_gen]

end PowerBasis

end PowerBasis

