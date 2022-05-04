/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathbin.FieldTheory.IntermediateField
import Mathbin.FieldTheory.Separable
import Mathbin.RingTheory.TensorProduct

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

open Classical Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type _) [Field F] {E : Type _} [Field E] [Algebra F E] (S : Set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.Range (algebraMap F E) ∪ S) with
    algebra_map_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

end AdjoinDef

section Lattice

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

@[simp]
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S ≤ T ↔ S ≤ T :=
  ⟨fun H => le_transₓ (le_transₓ (Set.subset_union_right _ _) Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.Range (algebraMap F E) ∪ S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

theorem gc : GaloisConnection (adjoin F : Set E → IntermediateField F E) coe := fun _ _ => adjoin_le_iff

/-- Galois insertion between `adjoin` and `coe`. -/
def gi : GaloisInsertion (adjoin F : Set E → IntermediateField F E) coe where
  choice := fun s hs => (adjoin F s).copy s <| le_antisymmₓ (gc.le_u_l s) hs
  gc := IntermediateField.gc
  le_l_u := fun S => (IntermediateField.gc (S : Set E) (adjoin F S)).1 <| le_rfl
  choice_eq := fun _ _ => copy_eq _ _ _

instance : CompleteLattice (IntermediateField F E) :=
  GaloisInsertion.liftCompleteLattice IntermediateField.gi

instance : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩

theorem coe_bot : ↑(⊥ : IntermediateField F E) = Set.Range (algebraMap F E) := by
  change ↑(Subfield.closure (Set.Range (algebraMap F E) ∪ ∅)) = Set.Range (algebraMap F E)
  simp [← Set.image_univ, ← RingHom.map_field_closure]

theorem mem_bot {x : E} : x ∈ (⊥ : IntermediateField F E) ↔ x ∈ Set.Range (algebraMap F E) :=
  Set.ext_iff.mp coe_bot x

@[simp]
theorem bot_to_subalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ := by
  ext
  rw [mem_to_subalgebra, Algebra.mem_bot, mem_bot]

@[simp]
theorem coe_top : ↑(⊤ : IntermediateField F E) = (Set.Univ : Set E) :=
  rfl

@[simp]
theorem mem_top {x : E} : x ∈ (⊤ : IntermediateField F E) :=
  trivialₓ

@[simp]
theorem top_to_subalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤ :=
  rfl

@[simp]
theorem top_to_subfield : (⊤ : IntermediateField F E).toSubfield = ⊤ :=
  rfl

@[simp, norm_cast]
theorem coe_inf (S T : IntermediateField F E) : (↑(S⊓T) : Set E) = S ∩ T :=
  rfl

@[simp]
theorem mem_inf {S T : IntermediateField F E} {x : E} : x ∈ S⊓T ↔ x ∈ S ∧ x ∈ T :=
  Iff.rfl

@[simp]
theorem inf_to_subalgebra (S T : IntermediateField F E) : (S⊓T).toSubalgebra = S.toSubalgebra⊓T.toSubalgebra :=
  rfl

@[simp]
theorem inf_to_subfield (S T : IntermediateField F E) : (S⊓T).toSubfield = S.toSubfield⊓T.toSubfield :=
  rfl

@[simp, norm_cast]
theorem coe_Inf (S : Set (IntermediateField F E)) : (↑(inf S) : Set E) = inf (coe '' S) :=
  rfl

@[simp]
theorem Inf_to_subalgebra (S : Set (IntermediateField F E)) : (inf S).toSubalgebra = inf (to_subalgebra '' S) :=
  SetLike.coe_injective <| by
    simp [Set.sUnion_image]

@[simp]
theorem Inf_to_subfield (S : Set (IntermediateField F E)) : (inf S).toSubfield = inf (to_subfield '' S) :=
  SetLike.coe_injective <| by
    simp [Set.sUnion_image]

@[simp, norm_cast]
theorem coe_infi {ι : Sort _} (S : ι → IntermediateField F E) : (↑(infi S) : Set E) = ⋂ i, S i := by
  simp [infi]

@[simp]
theorem infi_to_subalgebra {ι : Sort _} (S : ι → IntermediateField F E) :
    (infi S).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
  SetLike.coe_injective <| by
    simp [infi]

@[simp]
theorem infi_to_subfield {ι : Sort _} (S : ι → IntermediateField F E) : (infi S).toSubfield = ⨅ i, (S i).toSubfield :=
  SetLike.coe_injective <| by
    simp [infi]

/-- Construct an algebra isomorphism from an equality of intermediate fields -/
@[simps apply]
def equivOfEq {S T : IntermediateField F E} (h : S = T) : S ≃ₐ[F] T := by
  refine' { toFun := fun x => ⟨x, _⟩, invFun := fun x => ⟨x, _⟩, .. } <;> tidy

@[simp]
theorem equiv_of_eq_symm {S T : IntermediateField F E} (h : S = T) : (equivOfEq h).symm = equivOfEq h.symm :=
  rfl

@[simp]
theorem equiv_of_eq_rfl (S : IntermediateField F E) : equivOfEq (rfl : S = S) = AlgEquiv.refl := by
  ext
  rfl

@[simp]
theorem equiv_of_eq_trans {S T U : IntermediateField F E} (hST : S = T) (hTU : T = U) :
    (equivOfEq hST).trans (equivOfEq hTU) = equivOfEq (trans hST hTU) :=
  rfl

variable (F E)

/-- The bottom intermediate_field is isomorphic to the field. -/
noncomputable def botEquiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_to_subalgebra).trans (Algebra.botEquiv F E)

variable {F E}

@[simp]
theorem bot_equiv_def (x : F) : botEquiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x :=
  AlgEquiv.commutes (botEquiv F E) x

noncomputable instance algebraOverBot : Algebra (⊥ : IntermediateField F E) F :=
  (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra

instance is_scalar_tower_over_bot : IsScalarTower (⊥ : IntermediateField F E) F E :=
  IsScalarTower.of_algebra_map_eq
    (by
      intro x
      let ϕ := Algebra.ofId F (⊥ : Subalgebra F E)
      let ψ := AlgEquiv.ofBijective ϕ (Algebra.botEquiv F E).symm.Bijective
      change (↑x : E) = ↑(ψ (ψ.symm ⟨x, _⟩))
      rw [AlgEquiv.apply_symm_apply ψ ⟨x, _⟩]
      rfl)

/-- The top intermediate_field is isomorphic to the field.

This is the intermediate field version of `subalgebra.top_equiv`. -/
@[simps apply]
def topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E :=
  (Subalgebra.equivOfEq _ _ top_to_subalgebra).trans Subalgebra.topEquiv

@[simp]
theorem top_equiv_symm_apply_coe (a : E) : ↑(topEquiv.symm a : (⊤ : IntermediateField F E)) = a :=
  rfl

@[simp]
theorem coe_bot_eq_self (K : IntermediateField F E) : ↑(⊥ : IntermediateField K E) = K := by
  ext
  rw [mem_lift2, mem_bot]
  exact set.ext_iff.mp Subtype.range_coe x

@[simp]
theorem coe_top_eq_top (K : IntermediateField F E) : ↑(⊤ : IntermediateField K E) = (⊤ : IntermediateField F E) :=
  SetLike.ext_iff.mpr fun _ => mem_lift2.trans (iff_of_true mem_top mem_top)

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

instance adjoin.fieldCoe : CoeTₓ F (adjoin F S) where
  coe := fun x => ⟨algebraMap F E x, adjoin.algebra_map_mem F S x⟩

theorem subset_adjoin : S ⊆ adjoin F S := fun x hx => Subfield.subset_closure (Or.inr hx)

instance adjoin.setCoe : CoeTₓ S (adjoin F S) where
  coe := fun x => ⟨x, subset_adjoin F S (Subtype.mem x)⟩

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

@[simp]
theorem adjoin_univ (F E : Type _) [Field F] [Field E] [Algebra F E] : adjoin F (Set.Univ : Set E) = ⊤ :=
  eq_top_iff.mpr <| subset_adjoin _ _

/-- If `K` is a field with `F ⊆ K` and `S ⊆ K` then `adjoin F S ≤ K`. -/
theorem adjoin_le_subfield {K : Subfield E} (HF : Set.Range (algebraMap F E) ⊆ K) (HS : S ⊆ K) :
    (adjoin F S).toSubfield ≤ K := by
  apply subfield.closure_le.mpr
  rw [Set.union_subset_iff]
  exact ⟨HF, HS⟩

theorem adjoin_subset_adjoin_iff {F' : Type _} [Field F'] [Algebra F' E] {S S' : Set E} :
    (adjoin F S : Set E) ⊆ adjoin F' S' ↔ Set.Range (algebraMap F E) ⊆ adjoin F' S' ∧ S ⊆ adjoin F' S' :=
  ⟨fun h => ⟨trans (adjoin.range_algebra_map_subset _ _) h, trans (subset_adjoin _ _) h⟩, fun ⟨hF, hS⟩ =>
    Subfield.closure_le.mpr (Set.union_subset hF hS)⟩

/-- `F[S][T] = F[S ∪ T]` -/
theorem adjoin_adjoin_left (T : Set E) : ↑(adjoin (adjoin F S) T) = adjoin F (S ∪ T) := by
  rw [SetLike.ext'_iff]
  change ↑(adjoin (adjoin F S) T) = _
  apply Set.eq_of_subset_of_subset <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact adjoin.mono _ _ _ (Set.subset_union_left _ _) hx
    
  · exact subset_adjoin_of_subset_right _ _ (Set.subset_union_right _ _)
    
  · exact subset_adjoin_of_subset_left _ (adjoin.range_algebra_map_subset _ _)
    
  · exact Set.union_subset (subset_adjoin_of_subset_left _ (subset_adjoin _ _)) (subset_adjoin _ _)
    

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
    ↑(adjoin (adjoin F S) T) = (↑(adjoin (adjoin F T) S) : IntermediateField F E) := by
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
      adjoin F S ≤ { Algebra.adjoin F S with neg_mem' := fun x => (Algebra.adjoin F S).neg_mem, inv_mem' := inv_mem }
      from adjoin_le_iff.mpr Algebra.subset_adjoin)
    (algebra_adjoin_le_adjoin _ _)

theorem eq_adjoin_of_eq_algebra_adjoin (K : IntermediateField F E) (h : K.toSubalgebra = Algebra.adjoin F S) :
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
    (Hmap : ∀ x, p (algebraMap F E x)) (Hadd : ∀ x y, p x → p y → p (x + y)) (Hneg : ∀ x, p x → p (-x))
    (Hinv : ∀ x, p x → p x⁻¹) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  Subfield.closure_induction h (fun x hx => Or.cases_on hx (fun ⟨x, hx⟩ => hx ▸ Hmap x) (Hs x))
    ((algebraMap F E).map_one ▸ Hmap 1) Hadd Hneg Hinv Hmul

/-- Variation on `set.insert` to enable good notation for adjoining elements to fields.
Used to preferentially use `singleton` rather than `insert` when adjoining one element.
-/
--this definition of notation is courtesy of Kyle Miller on zulip
class Insert {α : Type _} (s : Set α) where
  insert : α → Set α

instance (priority := 1000) insertEmpty {α : Type _} : Insert (∅ : Set α) where
  insert := fun x => @singleton _ _ Set.hasSingleton x

instance (priority := 900) insertNonempty {α : Type _} (s : Set α) : Insert s where
  insert := fun x => Set.Insert x s

-- mathport name: «expr ⟮ ,⟯»
notation3:max K "⟮" (l,* => foldr (h t => Insert.Insert t h) ∅) "⟯" => adjoin K l

section AdjoinSimple

variable (α : E)

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `mem_adjoin_simple_self [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_∈_»
     `α
     "∈"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))))
  (Command.declValSimple
   ":="
   (Term.app `subset_adjoin [`F (Set.«term{_}» "{" [`α] "}") (Term.app `Set.mem_singleton [`α])])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `subset_adjoin [`F (Set.«term{_}» "{" [`α] "}") (Term.app `Set.mem_singleton [`α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set.mem_singleton [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set.mem_singleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Set.mem_singleton [`α]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_}» "{" [`α] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subset_adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_∈_»
   `α
   "∈"
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  mem_adjoin_simple_self
  : α ∈ F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
  := subset_adjoin F { α } Set.mem_singleton α

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [(Command.docComment "/--" "generator of `F⟮α⟯` -/")] [] [] [] [] [])
 (Command.def
  "def"
  (Command.declId `AdjoinSimple.gen [])
  (Command.optDeclSig
   []
   [(Term.typeSpec
     ":"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))])
  (Command.declValSimple ":=" (Term.anonymousCtor "⟨" [`α "," (Term.app `mem_adjoin_simple_self [`F `α])] "⟩") [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`α "," (Term.app `mem_adjoin_simple_self [`F `α])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mem_adjoin_simple_self [`F `α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_adjoin_simple_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- generator of `F⟮α⟯` -/
  def
    AdjoinSimple.gen
    : F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
    := ⟨ α , mem_adjoin_simple_self F α ⟩

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `AdjoinSimple.algebra_map_gen [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `algebraMap
      [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       `E
       (Term.app `AdjoinSimple.gen [`F `α])])
     "="
     `α)))
  (Command.declValSimple ":=" `rfl [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    `algebraMap
    [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     `E
     (Term.app `AdjoinSimple.gen [`F `α])])
   "="
   `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `algebraMap
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `E
    (Term.app `AdjoinSimple.gen [`F `α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `AdjoinSimple.gen [`F `α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AdjoinSimple.gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `AdjoinSimple.gen [`F `α]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
@[ simp ]
  theorem
    AdjoinSimple.algebra_map_gen
    :
      algebraMap
          F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ E AdjoinSimple.gen F α
        =
        α
    := rfl

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `AdjoinSimple.is_integral_gen [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_↔_» (Term.app `IsIntegral [`F (Term.app `AdjoinSimple.gen [`F `α])]) "↔" (Term.app `IsIntegral [`F `α]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Mathlib.Tactic.Conv.convRHS
         "conv_rhs"
         []
         []
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group
             (Tactic.Conv.convRw__
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`F `α]))] "]"))
             [])])))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `is_integral_algebra_map_iff
             [(Term.proj
               (Term.app
                `algebraMap
                [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `F
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 `E])
               "."
               `Injective)]))]
          "]")
         [])
        [])
       (group (Tactic.tacticInfer_instance "infer_instance") [])])))
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
     [(group
       (Mathlib.Tactic.Conv.convRHS
        "conv_rhs"
        []
        []
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`F `α]))] "]"))
            [])])))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app
            `is_integral_algebra_map_iff
            [(Term.proj
              (Term.app
               `algebraMap
               [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                `E])
              "."
              `Injective)]))]
         "]")
        [])
       [])
      (group (Tactic.tacticInfer_instance "infer_instance") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticInfer_instance "infer_instance")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       `is_integral_algebra_map_iff
       [(Term.proj
         (Term.app
          `algebraMap
          [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `F
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")
           `E])
         "."
         `Injective)]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `is_integral_algebra_map_iff
   [(Term.proj
     (Term.app
      `algebraMap
      [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       `E])
     "."
     `Injective)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `algebraMap
    [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     `E])
   "."
   `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `algebraMap
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
@[ simp ]
  theorem
    AdjoinSimple.is_integral_gen
    : IsIntegral F AdjoinSimple.gen F α ↔ IsIntegral F α
    :=
      by
        conv_rhs => rw [ ← adjoin_simple.algebra_map_gen F α ]
          rw
            [
              is_integral_algebra_map_iff
                algebraMap F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ E
                  .
                  Injective
              ]
          infer_instance

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin_simple_adjoin_simple [])
  (Command.declSig
   [(Term.explicitBinder "(" [`β] [":" `E] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (coeNotation
      "↑"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))
     "="
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))))
  (Command.declValSimple ":=" (Term.app `adjoin_adjoin_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin_adjoin_left [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_adjoin_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (coeNotation
    "↑"
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯"))
   "="
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  adjoin_simple_adjoin_simple
  ( β : E )
    :
      ↑
          F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
            ⟮
            "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"
            ⟯
        =
        F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
  := adjoin_adjoin_left _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin_simple_comm [])
  (Command.declSig
   [(Term.explicitBinder "(" [`β] [":" `E] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (coeNotation
      "↑"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))
     "="
     (Term.paren
      "("
      [(coeNotation
        "↑"
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          `F
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯")
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯"))
       [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
      ")"))))
  (Command.declValSimple ":=" (Term.app `adjoin_adjoin_comm [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin_adjoin_comm [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_adjoin_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (coeNotation
    "↑"
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯"))
   "="
   (Term.paren
    "("
    [(coeNotation
      "↑"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))
     [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
    ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(coeNotation
     "↑"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))
    [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (coeNotation
   "↑"
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  adjoin_simple_comm
  ( β : E )
    :
      ↑
          F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
            ⟮
            "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"
            ⟯
        =
        (
          ↑
              F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                ⟮
                "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"
                ⟯
            : IntermediateField F E
          )
  := adjoin_adjoin_comm _ _ _

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin_simple_to_subalgebra_of_integral [])
  (Command.declSig
   [(Term.explicitBinder "(" [`hα] [":" (Term.app `IsIntegral [`F `α])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.proj
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "."
      `toSubalgebra)
     "="
     (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" `adjoin_eq_algebra_adjoin) [])
       (group (Tactic.intro "intro" [`x `hx]) [])
       (group (Tactic.byCases' "by_cases'" [] («term_=_» `x "=" (num "0"))) [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `inv_zero)] "]") [])
           [])
          (group
           (Tactic.exact
            "exact"
            (Term.app `Subalgebra.zero_mem [(Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")])]))
           [])])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl `ϕ [] [] ":=" (Term.app `AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly [`F `α]))))
        [])
       (group
        (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `minpoly.irreducible [`hα]))))
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term_=_»
           («term_*_»
            (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
            "*"
            («term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹"))
           "="
           (num "1"))
          (Term.byTactic'
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.convert
                "convert"
                []
                (Term.app
                 `Subtype.mem
                 [(Term.app `ϕ.symm [(«term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹")])])
                [])
               [])
              (group
               (Tactic.refine' "refine'" (Term.proj (Term.app `eq_inv_of_mul_right_eq_one [(Term.hole "_")]) "." `symm))
               [])
              (group
               (Tactic.applyFun "apply_fun" `ϕ.symm [(Tactic.location "at" (Tactic.locationHyp [`this] []))] [])
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `AlgEquiv.map_one)
                  ","
                  (Tactic.rwRule [] `AlgEquiv.map_mul)
                  ","
                  (Tactic.rwRule [] `AlgEquiv.symm_apply_apply)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] `Subsemiring.coe_one)
                  ","
                  (Tactic.rwRule ["←"] `this)
                  ","
                  (Tactic.rwRule [] `Subsemiring.coe_mul)
                  ","
                  (Tactic.rwRule [] `Subtype.coe_mk)]
                 "]")
                [])
               [])])))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `mul_inv_cancel
             [(Term.app
               `mt
               [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`key] [])] "=>" (Term.hole "_"))) `h])]))]
          "]")
         [])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `ϕ.map_zero)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`key] []))])
        [])
       (group
        (Tactic.change
         "change"
         («term_=_»
          (coeNotation
           "↑"
           (Term.paren
            "("
            [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
             [(Term.typeAscription ":" (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]))]]
            ")"))
          "="
          (Term.hole "_"))
         [])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `ϕ.injective [`key])) "," (Tactic.rwRule [] `Subalgebra.coe_zero)]
          "]")
         [])
        [])])))
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
     [(group (Tactic.apply "apply" `adjoin_eq_algebra_adjoin) [])
      (group (Tactic.intro "intro" [`x `hx]) [])
      (group (Tactic.byCases' "by_cases'" [] («term_=_» `x "=" (num "0"))) [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `inv_zero)] "]") [])
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app `Subalgebra.zero_mem [(Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")])]))
          [])])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl `ϕ [] [] ":=" (Term.app `AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly [`F `α]))))
       [])
      (group
       (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `minpoly.irreducible [`hα]))))
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term_=_»
          («term_*_»
           (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
           "*"
           («term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹"))
          "="
          (num "1"))
         (Term.byTactic'
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.convert
               "convert"
               []
               (Term.app
                `Subtype.mem
                [(Term.app `ϕ.symm [(«term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹")])])
               [])
              [])
             (group
              (Tactic.refine' "refine'" (Term.proj (Term.app `eq_inv_of_mul_right_eq_one [(Term.hole "_")]) "." `symm))
              [])
             (group
              (Tactic.applyFun "apply_fun" `ϕ.symm [(Tactic.location "at" (Tactic.locationHyp [`this] []))] [])
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `AlgEquiv.map_one)
                 ","
                 (Tactic.rwRule [] `AlgEquiv.map_mul)
                 ","
                 (Tactic.rwRule [] `AlgEquiv.symm_apply_apply)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
              [])
             (group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule ["←"] `Subsemiring.coe_one)
                 ","
                 (Tactic.rwRule ["←"] `this)
                 ","
                 (Tactic.rwRule [] `Subsemiring.coe_mul)
                 ","
                 (Tactic.rwRule [] `Subtype.coe_mk)]
                "]")
               [])
              [])])))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app
            `mul_inv_cancel
            [(Term.app
              `mt
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`key] [])] "=>" (Term.hole "_"))) `h])]))]
         "]")
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `ϕ.map_zero)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`key] []))])
       [])
      (group
       (Tactic.change
        "change"
        («term_=_»
         (coeNotation
          "↑"
          (Term.paren
           "("
           [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
            [(Term.typeAscription ":" (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]))]]
           ")"))
         "="
         (Term.hole "_"))
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `ϕ.injective [`key])) "," (Tactic.rwRule [] `Subalgebra.coe_zero)]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `ϕ.injective [`key])) "," (Tactic.rwRule [] `Subalgebra.coe_zero)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subalgebra.coe_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ϕ.injective [`key])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `key
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ϕ.injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.change
   "change"
   («term_=_»
    (coeNotation
     "↑"
     (Term.paren
      "("
      [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
       [(Term.typeAscription ":" (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]))]]
      ")"))
    "="
    (Term.hole "_"))
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (coeNotation
    "↑"
    (Term.paren
     "("
     [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
      [(Term.typeAscription ":" (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]))]]
     ")"))
   "="
   (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (coeNotation
   "↑"
   (Term.paren
    "("
    [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
     [(Term.typeAscription ":" (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]))]]
    ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
    [(Term.typeAscription ":" (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_}» "{" [`α] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Algebra.adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 1024, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `ϕ.map_zero)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`key] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `key
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ϕ.map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       `mul_inv_cancel
       [(Term.app `mt [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`key] [])] "=>" (Term.hole "_"))) `h])]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mul_inv_cancel
   [(Term.app `mt [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`key] [])] "=>" (Term.hole "_"))) `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mt [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`key] [])] "=>" (Term.hole "_"))) `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`key] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`key] [])] "=>" (Term.hole "_"))) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `mt
   [(Term.paren "(" [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`key] [])] "=>" (Term.hole "_"))) []] ")") `h])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_inv_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term_=_»
     («term_*_»
      (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
      "*"
      («term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹"))
     "="
     (num "1"))
    (Term.byTactic'
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.convert
          "convert"
          []
          (Term.app
           `Subtype.mem
           [(Term.app `ϕ.symm [(«term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹")])])
          [])
         [])
        (group
         (Tactic.refine' "refine'" (Term.proj (Term.app `eq_inv_of_mul_right_eq_one [(Term.hole "_")]) "." `symm))
         [])
        (group (Tactic.applyFun "apply_fun" `ϕ.symm [(Tactic.location "at" (Tactic.locationHyp [`this] []))] []) [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `AlgEquiv.map_one)
            ","
            (Tactic.rwRule [] `AlgEquiv.map_mul)
            ","
            (Tactic.rwRule [] `AlgEquiv.symm_apply_apply)]
           "]")
          [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule ["←"] `Subsemiring.coe_one)
            ","
            (Tactic.rwRule ["←"] `this)
            ","
            (Tactic.rwRule [] `Subsemiring.coe_mul)
            ","
            (Tactic.rwRule [] `Subtype.coe_mk)]
           "]")
          [])
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `Subsemiring.coe_one)
     ","
     (Tactic.rwRule ["←"] `this)
     ","
     (Tactic.rwRule [] `Subsemiring.coe_mul)
     ","
     (Tactic.rwRule [] `Subtype.coe_mk)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subsemiring.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Subsemiring.coe_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `AlgEquiv.map_one)
     ","
     (Tactic.rwRule [] `AlgEquiv.map_mul)
     ","
     (Tactic.rwRule [] `AlgEquiv.symm_apply_apply)]
    "]")
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgEquiv.symm_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgEquiv.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgEquiv.map_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.applyFun "apply_fun" `ϕ.symm [(Tactic.location "at" (Tactic.locationHyp [`this] []))] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ϕ.symm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine' "refine'" (Term.proj (Term.app `eq_inv_of_mul_right_eq_one [(Term.hole "_")]) "." `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `eq_inv_of_mul_right_eq_one [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `eq_inv_of_mul_right_eq_one [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `eq_inv_of_mul_right_eq_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `eq_inv_of_mul_right_eq_one [(Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert
   "convert"
   []
   (Term.app
    `Subtype.mem
    [(Term.app `ϕ.symm [(«term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹")])])
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Subtype.mem
   [(Term.app `ϕ.symm [(«term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ϕ.symm [(«term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ϕ.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `ϕ.symm
   [(«term_⁻¹» (Term.paren "(" [(Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) []] ")") "⁻¹")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subtype.mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   («term_*_»
    (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
    "*"
    («term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹"))
   "="
   (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_*_»
   (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
   "*"
   («term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_⁻¹» (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Term.app `ϕ [(Term.anonymousCtor "⟨" [`x "," `hx] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`x "," `hx] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `minpoly.irreducible [`hα]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.irreducible [`hα])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hα
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.irreducible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl (Term.letIdDecl `ϕ [] [] ":=" (Term.app `AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly [`F `α]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly [`F `α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `inv_zero)] "]") [])
     [])
    (group
     (Tactic.exact
      "exact"
      (Term.app `Subalgebra.zero_mem [(Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")])]))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `Subalgebra.zero_mem [(Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Subalgebra.zero_mem [(Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_}» "{" [`α] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Algebra.adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subalgebra.zero_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h) "," (Tactic.rwRule [] `inv_zero)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inv_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.byCases' "by_cases'" [] («term_=_» `x "=" (num "0")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» `x "=" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x `hx])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `adjoin_eq_algebra_adjoin)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin_eq_algebra_adjoin
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.proj
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    "."
    `toSubalgebra)
   "="
   (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Algebra.adjoin [`F (Set.«term{_}» "{" [`α] "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_}» "{" [`α] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Algebra.adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.proj
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "."
   `toSubalgebra)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  adjoin_simple_to_subalgebra_of_integral
  ( hα : IsIntegral F α )
    :
      F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ . toSubalgebra
        =
        Algebra.adjoin F { α }
  :=
    by
      apply adjoin_eq_algebra_adjoin
        intro x hx
        by_cases' x = 0
        · rw [ h , inv_zero ] exact Subalgebra.zero_mem Algebra.adjoin F { α }
        let ϕ := AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly F α
        have := minpoly.irreducible hα
        suffices
          ϕ ⟨ x , hx ⟩ * ϕ ⟨ x , hx ⟩ ⁻¹ = 1
            by
              convert Subtype.mem ϕ.symm ϕ ⟨ x , hx ⟩ ⁻¹
                refine' eq_inv_of_mul_right_eq_one _ . symm
                apply_fun ϕ.symm at this
                rw [ AlgEquiv.map_one , AlgEquiv.map_mul , AlgEquiv.symm_apply_apply ] at this
                rw [ ← Subsemiring.coe_one , ← this , Subsemiring.coe_mul , Subtype.coe_mk ]
        rw [ mul_inv_cancel mt fun key => _ h ]
        rw [ ← ϕ.map_zero ] at key
        change ↑ ( ⟨ x , hx ⟩ : Algebra.adjoin F { α } ) = _
        rw [ ϕ.injective key , Subalgebra.coe_zero ]

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E] {α : E} {S : Set E}

@[simp]
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S ⊆ (⊥ : IntermediateField F E) := by
  rw [eq_bot_iff, adjoin_le_iff]
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin_simple_eq_bot_iff [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_↔_»
     («term_=_»
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "="
      (Order.BoundedOrder.«term⊥» "⊥"))
     "↔"
     («term_∈_»
      `α
      "∈"
      (Term.paren
       "("
       [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
       ")")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `adjoin_eq_bot_iff)] "]") []) [])
       (group (Tactic.exact "exact" `Set.singleton_subset_iff) [])])))
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
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `adjoin_eq_bot_iff)] "]") []) [])
      (group (Tactic.exact "exact" `Set.singleton_subset_iff) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `Set.singleton_subset_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.singleton_subset_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `adjoin_eq_bot_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin_eq_bot_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_↔_»
   («term_=_»
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    "="
    (Order.BoundedOrder.«term⊥» "⊥"))
   "↔"
   («term_∈_»
    `α
    "∈"
    (Term.paren
     "("
     [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
     ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∈_»
   `α
   "∈"
   (Term.paren
    "("
    [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
    ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `α
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
  («term_=_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "="
   (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
@[ simp ]
  theorem
    adjoin_simple_eq_bot_iff
    :
      F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊥
        ↔
        α ∈ ( ⊥ : IntermediateField F E )
    := by rw [ adjoin_eq_bot_iff ] exact Set.singleton_subset_iff

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin_zero [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     "="
     (Order.BoundedOrder.«term⊥» "⊥"))))
  (Command.declValSimple
   ":="
   (Term.app (Term.proj `adjoin_simple_eq_bot_iff "." `mpr) [(Term.app `zero_mem [(Order.BoundedOrder.«term⊥» "⊥")])])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `adjoin_simple_eq_bot_iff "." `mpr) [(Term.app `zero_mem [(Order.BoundedOrder.«term⊥» "⊥")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `zero_mem [(Order.BoundedOrder.«term⊥» "⊥")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `zero_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `zero_mem [(Order.BoundedOrder.«term⊥» "⊥")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `adjoin_simple_eq_bot_iff "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `adjoin_simple_eq_bot_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "="
   (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
@[ simp ]
  theorem
    adjoin_zero
    : F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊥
    := adjoin_simple_eq_bot_iff . mpr zero_mem ⊥

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin_one [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     "="
     (Order.BoundedOrder.«term⊥» "⊥"))))
  (Command.declValSimple
   ":="
   (Term.app (Term.proj `adjoin_simple_eq_bot_iff "." `mpr) [(Term.app `one_mem [(Order.BoundedOrder.«term⊥» "⊥")])])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `adjoin_simple_eq_bot_iff "." `mpr) [(Term.app `one_mem [(Order.BoundedOrder.«term⊥» "⊥")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `one_mem [(Order.BoundedOrder.«term⊥» "⊥")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `one_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `one_mem [(Order.BoundedOrder.«term⊥» "⊥")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `adjoin_simple_eq_bot_iff "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `adjoin_simple_eq_bot_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "="
   (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
@[ simp ]
  theorem
    adjoin_one
    : F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊥
    := adjoin_simple_eq_bot_iff . mpr one_mem ⊥

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin_int [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (Int.termℤ "ℤ")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     "="
     (Order.BoundedOrder.«term⊥» "⊥"))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj `adjoin_simple_eq_bot_iff "." `mpr)
    [(Term.app `coe_int_mem [(Order.BoundedOrder.«term⊥» "⊥") `n])])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `adjoin_simple_eq_bot_iff "." `mpr)
   [(Term.app `coe_int_mem [(Order.BoundedOrder.«term⊥» "⊥") `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `coe_int_mem [(Order.BoundedOrder.«term⊥» "⊥") `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `coe_int_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `coe_int_mem [(Order.BoundedOrder.«term⊥» "⊥") `n]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `adjoin_simple_eq_bot_iff "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `adjoin_simple_eq_bot_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "="
   (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
@[ simp ]
  theorem
    adjoin_int
    ( n : ℤ ) : F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊥
    := adjoin_simple_eq_bot_iff . mpr coe_int_mem ⊥ n

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  []
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin_nat [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     "="
     (Order.BoundedOrder.«term⊥» "⊥"))))
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj `adjoin_simple_eq_bot_iff "." `mpr)
    [(Term.app `coe_int_mem [(Order.BoundedOrder.«term⊥» "⊥") `n])])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `adjoin_simple_eq_bot_iff "." `mpr)
   [(Term.app `coe_int_mem [(Order.BoundedOrder.«term⊥» "⊥") `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `coe_int_mem [(Order.BoundedOrder.«term⊥» "⊥") `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Order.BoundedOrder.«term⊥»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `coe_int_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `coe_int_mem [(Order.BoundedOrder.«term⊥» "⊥") `n]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `adjoin_simple_eq_bot_iff "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `adjoin_simple_eq_bot_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "="
   (Order.BoundedOrder.«term⊥» "⊥"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
@[ simp ]
  theorem
    adjoin_nat
    ( n : ℕ ) : F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = ⊥
    := adjoin_simple_eq_bot_iff . mpr coe_int_mem ⊥ n

section AdjoinDim

open FiniteDimensional Module

variable {K L : IntermediateField F E}

@[simp]
theorem dim_eq_one_iff : Module.rank F K = 1 ↔ K = ⊥ := by
  rw [← to_subalgebra_eq_iff, ← dim_eq_dim_subalgebra, Subalgebra.dim_eq_one_iff, bot_to_subalgebra]

@[simp]
theorem finrank_eq_one_iff : finrank F K = 1 ↔ K = ⊥ := by
  rw [← to_subalgebra_eq_iff, ← finrank_eq_finrank_subalgebra, Subalgebra.finrank_eq_one_iff, bot_to_subalgebra]

@[simp]
theorem dim_bot : Module.rank F (⊥ : IntermediateField F E) = 1 := by
  rw [dim_eq_one_iff]

@[simp]
theorem finrank_bot : finrank F (⊥ : IntermediateField F E) = 1 := by
  rw [finrank_eq_one_iff]

theorem dim_adjoin_eq_one_iff : Module.rank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans dim_eq_one_iff adjoin_eq_bot_iff

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `dim_adjoin_simple_eq_one_iff [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_↔_»
     («term_=_»
      (Term.app
       `Module.rank
       [`F
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")])
      "="
      (num "1"))
     "↔"
     («term_∈_»
      `α
      "∈"
      (Term.paren
       "("
       [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
       ")")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dim_adjoin_eq_one_iff)] "]") []) [])
       (group (Tactic.exact "exact" `Set.singleton_subset_iff) [])])))
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
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dim_adjoin_eq_one_iff)] "]") []) [])
      (group (Tactic.exact "exact" `Set.singleton_subset_iff) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `Set.singleton_subset_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.singleton_subset_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `dim_adjoin_eq_one_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `dim_adjoin_eq_one_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_↔_»
   («term_=_»
    (Term.app
     `Module.rank
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])
    "="
    (num "1"))
   "↔"
   («term_∈_»
    `α
    "∈"
    (Term.paren
     "("
     [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
     ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∈_»
   `α
   "∈"
   (Term.paren
    "("
    [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
    ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `α
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
  («term_=_»
   (Term.app
    `Module.rank
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")])
   "="
   (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `Module.rank
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  dim_adjoin_simple_eq_one_iff
  :
    Module.rank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = 1
      ↔
      α ∈ ( ⊥ : IntermediateField F E )
  := by rw [ dim_adjoin_eq_one_iff ] exact Set.singleton_subset_iff

theorem finrank_adjoin_eq_one_iff : finrank F (adjoin F S) = 1 ↔ S ⊆ (⊥ : IntermediateField F E) :=
  Iff.trans finrank_eq_one_iff adjoin_eq_bot_iff

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `finrank_adjoin_simple_eq_one_iff [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_↔_»
     («term_=_»
      (Term.app
       `finrank
       [`F
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")])
      "="
      (num "1"))
     "↔"
     («term_∈_»
      `α
      "∈"
      (Term.paren
       "("
       [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
       ")")))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `finrank_adjoin_eq_one_iff)] "]") []) [])
       (group (Tactic.exact "exact" `Set.singleton_subset_iff) [])])))
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
     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `finrank_adjoin_eq_one_iff)] "]") []) [])
      (group (Tactic.exact "exact" `Set.singleton_subset_iff) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `Set.singleton_subset_iff)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.singleton_subset_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `finrank_adjoin_eq_one_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `finrank_adjoin_eq_one_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_↔_»
   («term_=_»
    (Term.app
     `finrank
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])
    "="
    (num "1"))
   "↔"
   («term_∈_»
    `α
    "∈"
    (Term.paren
     "("
     [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
     ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∈_»
   `α
   "∈"
   (Term.paren
    "("
    [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
    ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `α
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
  («term_=_»
   (Term.app
    `finrank
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")])
   "="
   (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `finrank
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  finrank_adjoin_simple_eq_one_iff
  :
    finrank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = 1
      ↔
      α ∈ ( ⊥ : IntermediateField F E )
  := by rw [ finrank_adjoin_eq_one_iff ] exact Set.singleton_subset_iff

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `bot_eq_top_of_dim_adjoin_eq_one [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`h]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
       ","
       («term_=_»
        (Term.app
         `Module.rank
         [`F
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")])
        "="
        (num "1")))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.paren
      "("
      [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
      ")")
     "="
     (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `iff_true_right [`IntermediateField.mem_top]))] "]")
         [])
        [])
       (group (Tactic.exact "exact" (Term.app `dim_adjoin_simple_eq_one_iff.mp [(Term.app `h [`x])])) [])])))
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
     [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `iff_true_right [`IntermediateField.mem_top]))] "]")
        [])
       [])
      (group (Tactic.exact "exact" (Term.app `dim_adjoin_simple_eq_one_iff.mp [(Term.app `h [`x])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `dim_adjoin_simple_eq_one_iff.mp [(Term.app `h [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dim_adjoin_simple_eq_one_iff.mp [(Term.app `h [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `h [`x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dim_adjoin_simple_eq_one_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `iff_true_right [`IntermediateField.mem_top]))] "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `iff_true_right [`IntermediateField.mem_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IntermediateField.mem_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `iff_true_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.paren
    "("
    [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
    ")")
   "="
   (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren
   "("
   [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
   ","
   («term_=_»
    (Term.app
     `Module.rank
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])
    "="
    (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    `Module.rank
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")])
   "="
   (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `Module.rank
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- If `F⟮x⟯` has dimension `1` over `F` for every `x ∈ E` then `F = E`. -/
  theorem
    bot_eq_top_of_dim_adjoin_eq_one
    (
        h
        : ∀ x : E , Module.rank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = 1
        )
      : ( ⊥ : IntermediateField F E ) = ⊤
    := by ext rw [ iff_true_right IntermediateField.mem_top ] exact dim_adjoin_simple_eq_one_iff.mp h x

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `bot_eq_top_of_finrank_adjoin_eq_one [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`h]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
       ","
       («term_=_»
        (Term.app
         `finrank
         [`F
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")])
        "="
        (num "1")))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.paren
      "("
      [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
      ")")
     "="
     (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `iff_true_right [`IntermediateField.mem_top]))] "]")
         [])
        [])
       (group (Tactic.exact "exact" (Term.app `finrank_adjoin_simple_eq_one_iff.mp [(Term.app `h [`x])])) [])])))
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
     [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `iff_true_right [`IntermediateField.mem_top]))] "]")
        [])
       [])
      (group (Tactic.exact "exact" (Term.app `finrank_adjoin_simple_eq_one_iff.mp [(Term.app `h [`x])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `finrank_adjoin_simple_eq_one_iff.mp [(Term.app `h [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `finrank_adjoin_simple_eq_one_iff.mp [(Term.app `h [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `h [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `h [`x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `finrank_adjoin_simple_eq_one_iff.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `iff_true_right [`IntermediateField.mem_top]))] "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `iff_true_right [`IntermediateField.mem_top])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IntermediateField.mem_top
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `iff_true_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.paren
    "("
    [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
    ")")
   "="
   (Order.BoundedOrder.«term⊤» "⊤"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Order.BoundedOrder.«term⊤» "⊤")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.paren
   "("
   [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Order.BoundedOrder.«term⊥» "⊥")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
   ","
   («term_=_»
    (Term.app
     `finrank
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])
    "="
    (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    `finrank
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")])
   "="
   (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `finrank
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  bot_eq_top_of_finrank_adjoin_eq_one
  ( h : ∀ x : E , finrank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = 1 )
    : ( ⊥ : IntermediateField F E ) = ⊤
  := by ext rw [ iff_true_right IntermediateField.mem_top ] exact finrank_adjoin_simple_eq_one_iff.mp h x

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `subsingleton_of_dim_adjoin_eq_one [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`h]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
       ","
       («term_=_»
        (Term.app
         `Module.rank
         [`F
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")])
        "="
        (num "1")))]
     []
     ")")]
   (Term.typeSpec ":" (Term.app `Subsingleton [(Term.app `IntermediateField [`F `E])])))
  (Command.declValSimple
   ":="
   (Term.app `subsingleton_of_bot_eq_top [(Term.app `bot_eq_top_of_dim_adjoin_eq_one [`h])])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `subsingleton_of_bot_eq_top [(Term.app `bot_eq_top_of_dim_adjoin_eq_one [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bot_eq_top_of_dim_adjoin_eq_one [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bot_eq_top_of_dim_adjoin_eq_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `bot_eq_top_of_dim_adjoin_eq_one [`h]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subsingleton_of_bot_eq_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `Subsingleton [(Term.app `IntermediateField [`F `E])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `IntermediateField [`F `E]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subsingleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
   ","
   («term_=_»
    (Term.app
     `Module.rank
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])
    "="
    (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    `Module.rank
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")])
   "="
   (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `Module.rank
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  subsingleton_of_dim_adjoin_eq_one
  ( h : ∀ x : E , Module.rank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = 1 )
    : Subsingleton IntermediateField F E
  := subsingleton_of_bot_eq_top bot_eq_top_of_dim_adjoin_eq_one h

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `subsingleton_of_finrank_adjoin_eq_one [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`h]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
       ","
       («term_=_»
        (Term.app
         `finrank
         [`F
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")])
        "="
        (num "1")))]
     []
     ")")]
   (Term.typeSpec ":" (Term.app `Subsingleton [(Term.app `IntermediateField [`F `E])])))
  (Command.declValSimple
   ":="
   (Term.app `subsingleton_of_bot_eq_top [(Term.app `bot_eq_top_of_finrank_adjoin_eq_one [`h])])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `subsingleton_of_bot_eq_top [(Term.app `bot_eq_top_of_finrank_adjoin_eq_one [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bot_eq_top_of_finrank_adjoin_eq_one [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bot_eq_top_of_finrank_adjoin_eq_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `bot_eq_top_of_finrank_adjoin_eq_one [`h]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subsingleton_of_bot_eq_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `Subsingleton [(Term.app `IntermediateField [`F `E])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `IntermediateField [`F `E]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subsingleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
   ","
   («term_=_»
    (Term.app
     `finrank
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])
    "="
    (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    `finrank
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")])
   "="
   (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `finrank
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  subsingleton_of_finrank_adjoin_eq_one
  ( h : ∀ x : E , finrank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ = 1 )
    : Subsingleton IntermediateField F E
  := subsingleton_of_bot_eq_top bot_eq_top_of_finrank_adjoin_eq_one h

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `bot_eq_top_of_finrank_adjoin_le_one [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `FiniteDimensional [`F `E]) "]")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
       ","
       («term_≤_»
        (Term.app
         `finrank
         [`F
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")])
        "≤"
        (num "1")))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.paren
      "("
      [(Order.BoundedOrder.«term⊥» "⊥") [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
      ")")
     "="
     (Order.BoundedOrder.«term⊤» "⊤"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" `bot_eq_top_of_finrank_adjoin_eq_one) [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.linarith
                 "linarith"
                 []
                 []
                 ["["
                  [(Term.app `h [`x])
                   ","
                   (Term.show
                    "show"
                    («term_<_»
                     (num "0")
                     "<"
                     (Term.app
                      `finrank
                      [`F
                       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                        `F
                        "⟮"
                        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                        "⟯")]))
                    (Term.fromTerm "from" `finrank_pos))]
                  "]"])
                [])]))))))
        [])])))
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
     [(group (Tactic.apply "apply" `bot_eq_top_of_finrank_adjoin_eq_one) [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.linarith
                "linarith"
                []
                []
                ["["
                 [(Term.app `h [`x])
                  ","
                  (Term.show
                   "show"
                   («term_<_»
                    (num "0")
                    "<"
                    (Term.app
                     `finrank
                     [`F
                      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                       `F
                       "⟮"
                       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                       "⟯")]))
                   (Term.fromTerm "from" `finrank_pos))]
                 "]"])
               [])]))))))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x] [])]
     "=>"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.linarith
           "linarith"
           []
           []
           ["["
            [(Term.app `h [`x])
             ","
             (Term.show
              "show"
              («term_<_»
               (num "0")
               "<"
               (Term.app
                `finrank
                [`F
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `F
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")]))
              (Term.fromTerm "from" `finrank_pos))]
            "]"])
          [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.linarith
          "linarith"
          []
          []
          ["["
           [(Term.app `h [`x])
            ","
            (Term.show
             "show"
             («term_<_»
              (num "0")
              "<"
              (Term.app
               `finrank
               [`F
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")]))
             (Term.fromTerm "from" `finrank_pos))]
           "]"])
         [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.linarith
        "linarith"
        []
        []
        ["["
         [(Term.app `h [`x])
          ","
          (Term.show
           "show"
           («term_<_»
            (num "0")
            "<"
            (Term.app
             `finrank
             [`F
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `F
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯")]))
           (Term.fromTerm "from" `finrank_pos))]
         "]"])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.linarith
   "linarith"
   []
   []
   ["["
    [(Term.app `h [`x])
     ","
     (Term.show
      "show"
      («term_<_»
       (num "0")
       "<"
       (Term.app
        `finrank
        [`F
         (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          `F
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯")]))
      (Term.fromTerm "from" `finrank_pos))]
    "]"])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   («term_<_»
    (num "0")
    "<"
    (Term.app
     `finrank
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")]))
   (Term.fromTerm "from" `finrank_pos))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `finrank_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_<_»
   (num "0")
   "<"
   (Term.app
    `finrank
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `finrank
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- If `F⟮x⟯` has dimension `≤1` over `F` for every `x ∈ E` then `F = E`. -/
  theorem
    bot_eq_top_of_finrank_adjoin_le_one
    [ FiniteDimensional F E ]
        (
          h
          : ∀ x : E , finrank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ ≤ 1
          )
      : ( ⊥ : IntermediateField F E ) = ⊤
    :=
      by
        apply bot_eq_top_of_finrank_adjoin_eq_one
          exact
            fun
              x
                =>
                by
                  linarith
                    [
                      h x
                        ,
                        show
                          0
                            <
                            finrank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                          from finrank_pos
                      ]

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `subsingleton_of_finrank_adjoin_le_one [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `FiniteDimensional [`F `E]) "]")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
       ","
       («term_≤_»
        (Term.app
         `finrank
         [`F
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")])
        "≤"
        (num "1")))]
     []
     ")")]
   (Term.typeSpec ":" (Term.app `Subsingleton [(Term.app `IntermediateField [`F `E])])))
  (Command.declValSimple
   ":="
   (Term.app `subsingleton_of_bot_eq_top [(Term.app `bot_eq_top_of_finrank_adjoin_le_one [`h])])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `subsingleton_of_bot_eq_top [(Term.app `bot_eq_top_of_finrank_adjoin_le_one [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `bot_eq_top_of_finrank_adjoin_le_one [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `bot_eq_top_of_finrank_adjoin_le_one
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `bot_eq_top_of_finrank_adjoin_le_one [`h]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subsingleton_of_bot_eq_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `Subsingleton [(Term.app `IntermediateField [`F `E])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `IntermediateField [`F `E]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subsingleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
   ","
   («term_≤_»
    (Term.app
     `finrank
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])
    "≤"
    (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.app
    `finrank
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")])
   "≤"
   (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (num "1")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `finrank
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  subsingleton_of_finrank_adjoin_le_one
  [ FiniteDimensional F E ]
      ( h : ∀ x : E , finrank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ ≤ 1 )
    : Subsingleton IntermediateField F E
  := subsingleton_of_bot_eq_top bot_eq_top_of_finrank_adjoin_le_one h

end AdjoinDim

end AdjoinIntermediateFieldLattice

section AdjoinIntegralElement

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E] {α : E}

variable {K : Type _} [Field K] [Algebra F K]

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `minpoly_gen [])
  (Command.declSig
   [(Term.implicitBinder "{" [`α] [":" `E] "}")
    (Term.explicitBinder "(" [`h] [":" (Term.app `IsIntegral [`F `α])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_» (Term.app `minpoly [`F (Term.app `AdjoinSimple.gen [`F `α])]) "=" (Term.app `minpoly [`F `α]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`F `α]))] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`inj []]
           []
           ":="
           (Term.proj
            (Term.app
             `algebraMap
             [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `F
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯")
              `E])
            "."
            `Injective))))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `minpoly.eq_of_algebra_map_eq
          [`inj
           (Term.app (Term.proj (Term.app `is_integral_algebra_map_iff [`inj]) "." `mp) [`h])
           (Term.proj (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]) "." `symm)]))
        [])])))
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
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`F `α]))] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`inj []]
          []
          ":="
          (Term.proj
           (Term.app
            `algebraMap
            [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `F
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯")
             `E])
           "."
           `Injective))))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `minpoly.eq_of_algebra_map_eq
         [`inj
          (Term.app (Term.proj (Term.app `is_integral_algebra_map_iff [`inj]) "." `mp) [`h])
          (Term.proj (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]) "." `symm)]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `minpoly.eq_of_algebra_map_eq
    [`inj
     (Term.app (Term.proj (Term.app `is_integral_algebra_map_iff [`inj]) "." `mp) [`h])
     (Term.proj (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]) "." `symm)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `minpoly.eq_of_algebra_map_eq
   [`inj
    (Term.app (Term.proj (Term.app `is_integral_algebra_map_iff [`inj]) "." `mp) [`h])
    (Term.proj (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]) "." `symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin_simple.algebra_map_gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `adjoin_simple.algebra_map_gen [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj (Term.app `is_integral_algebra_map_iff [`inj]) "." `mp) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `is_integral_algebra_map_iff [`inj]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `is_integral_algebra_map_iff [`inj])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `is_integral_algebra_map_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `is_integral_algebra_map_iff [`inj]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj (Term.paren "(" [(Term.app `is_integral_algebra_map_iff [`inj]) []] ")") "." `mp) [`h]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `inj
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.eq_of_algebra_map_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`inj []]
     []
     ":="
     (Term.proj
      (Term.app
       `algebraMap
       [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        `E])
      "."
      `Injective))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    `algebraMap
    [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     `E])
   "."
   `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `algebraMap
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  minpoly_gen
  { α : E } ( h : IsIntegral F α ) : minpoly F AdjoinSimple.gen F α = minpoly F α
  :=
    by
      rw [ ← adjoin_simple.algebra_map_gen F α ] at h
        have
          inj
            :=
            algebraMap F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ E . Injective
        exact
          minpoly.eq_of_algebra_map_eq
            inj is_integral_algebra_map_iff inj . mp h adjoin_simple.algebra_map_gen _ _ . symm

variable (F)

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `aeval_gen_minpoly [])
  (Command.declSig
   [(Term.explicitBinder "(" [`α] [":" `E] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_» (Term.app `aeval [(Term.app `AdjoinSimple.gen [`F `α]) (Term.app `minpoly [`F `α])]) "=" (num "0"))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
       (group (Tactic.convert "convert" [] (Term.app `minpoly.aeval [`F `α]) []) [])
       (group
        (Tactic.Conv.conv
         "conv"
         []
         ["in" (Term.app `aeval [`α])]
         "=>"
         (Tactic.Conv.convSeq
          (Tactic.Conv.convSeq1Indented
           [(group
             (Tactic.Conv.convRw__
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`F `α]))] "]"))
             [])])))
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `IsScalarTower.algebra_map_aeval
          [`F
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `F
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")
           `E
           (Term.hole "_")
           (Term.hole "_")]))
        [])])))
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
     [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
      (group (Tactic.convert "convert" [] (Term.app `minpoly.aeval [`F `α]) []) [])
      (group
       (Tactic.Conv.conv
        "conv"
        []
        ["in" (Term.app `aeval [`α])]
        "=>"
        (Tactic.Conv.convSeq
         (Tactic.Conv.convSeq1Indented
          [(group
            (Tactic.Conv.convRw__
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `adjoin_simple.algebra_map_gen [`F `α]))] "]"))
            [])])))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `IsScalarTower.algebra_map_aeval
         [`F
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")
          `E
          (Term.hole "_")
          (Term.hole "_")]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `IsScalarTower.algebra_map_aeval
    [`F
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     `E
     (Term.hole "_")
     (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `IsScalarTower.algebra_map_aeval
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `E
    (Term.hole "_")
    (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  aeval_gen_minpoly
  ( α : E ) : aeval AdjoinSimple.gen F α minpoly F α = 0
  :=
    by
      ext
        convert minpoly.aeval F α
        conv in aeval α => rw [ ← adjoin_simple.algebra_map_gen F α ]
        exact
          IsScalarTower.algebra_map_aeval
            F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ E _ _

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "algebra isomorphism between `adjoin_root` and `F⟮α⟯` -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `adjoinRootEquivAdjoin [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`h] [":" (Term.app `IsIntegral [`F `α])] [] ")")]
   [(Term.typeSpec
     ":"
     (Algebra.Algebra.Basic.«term_≃ₐ[_]_»
      (Term.app `AdjoinRoot [(Term.app `minpoly [`F `α])])
      " ≃ₐ["
      `F
      "] "
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")))])
  (Command.declValSimple
   ":="
   (Term.app
    `AlgEquiv.ofBijective
    [(Term.app
      `AdjoinRoot.liftHom
      [(Term.app `minpoly [`F `α]) (Term.app `AdjoinSimple.gen [`F `α]) (Term.app `aeval_gen_minpoly [`F `α])])
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `f
            []
            ":="
            (Term.app
             `AdjoinRoot.lift
             [(Term.hole "_")
              (Term.hole "_")
              (Term.paren "(" [(Term.app `aeval_gen_minpoly [`F `α]) [(Term.typeAscription ":" (Term.hole "_"))]] ")")])
            []))
          [])
         (group
          (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `minpoly.irreducible [`h]))))
          [])
         (group (Tactic.constructor "constructor") [])
         (group («tactic·.__;_» "·" [(group (Tactic.exact "exact" (Term.app `RingHom.injective [`f])) [])]) [])
         (group
          («tactic·.__;_»
           "·"
           [(group
             (Tactic.tacticSuffices_
              "suffices"
              (Term.sufficesDecl
               []
               («term_≤_»
                (Term.proj
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `F
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 "."
                 `toSubfield)
                "≤"
                (Term.app
                 `RingHom.fieldRange
                 [(Term.app
                   (Term.proj
                    (Term.proj
                     (Term.proj
                      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                       `F
                       "⟮"
                       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                       "⟯")
                      "."
                      `toSubfield)
                     "."
                     `Subtype)
                    "."
                    `comp)
                   [`f])]))
               (Term.byTactic'
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.exact
                     "exact"
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`x] [])]
                       "=>"
                       (Term.app
                        `Exists.cases_on
                        [(Term.app `this [(Term.app `Subtype.mem [`x])])
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder [`y `hy] [])]
                           "=>"
                           (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))]))))
                    [])])))))
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               `subfield.closure_le.mpr
               [(Term.app
                 `Set.union_subset
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x `hx] [])]
                    "=>"
                    (Term.app
                     `Exists.cases_on
                     [`hx
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`y `hy] [])]
                        "=>"
                        (Term.anonymousCtor
                         "⟨"
                         [`y
                          ","
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group
                               (Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq
                                 "["
                                 [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                                 "]")
                                [])
                               [])
                              (group (Tactic.exact "exact" `hy) [])])))]
                         "⟩")))])))
                  (Term.app
                   `set.singleton_subset_iff.mpr
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
                             "]")
                            [])
                           [])
                          (group (Tactic.tacticRfl "rfl") [])])))]
                     "⟩")])])]))
             [])])
          [])])))])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `AlgEquiv.ofBijective
   [(Term.app
     `AdjoinRoot.liftHom
     [(Term.app `minpoly [`F `α]) (Term.app `AdjoinSimple.gen [`F `α]) (Term.app `aeval_gen_minpoly [`F `α])])
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Mathlib.Tactic.set
          "set"
          []
          (Mathlib.Tactic.setArgsRest
           `f
           []
           ":="
           (Term.app
            `AdjoinRoot.lift
            [(Term.hole "_")
             (Term.hole "_")
             (Term.paren "(" [(Term.app `aeval_gen_minpoly [`F `α]) [(Term.typeAscription ":" (Term.hole "_"))]] ")")])
           []))
         [])
        (group
         (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `minpoly.irreducible [`h]))))
         [])
        (group (Tactic.constructor "constructor") [])
        (group («tactic·.__;_» "·" [(group (Tactic.exact "exact" (Term.app `RingHom.injective [`f])) [])]) [])
        (group
         («tactic·.__;_»
          "·"
          [(group
            (Tactic.tacticSuffices_
             "suffices"
             (Term.sufficesDecl
              []
              («term_≤_»
               (Term.proj
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                "."
                `toSubfield)
               "≤"
               (Term.app
                `RingHom.fieldRange
                [(Term.app
                  (Term.proj
                   (Term.proj
                    (Term.proj
                     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                      `F
                      "⟮"
                      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                      "⟯")
                     "."
                     `toSubfield)
                    "."
                    `Subtype)
                   "."
                   `comp)
                  [`f])]))
              (Term.byTactic'
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.exact
                    "exact"
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`x] [])]
                      "=>"
                      (Term.app
                       `Exists.cases_on
                       [(Term.app `this [(Term.app `Subtype.mem [`x])])
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`y `hy] [])]
                          "=>"
                          (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))]))))
                   [])])))))
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              `subfield.closure_le.mpr
              [(Term.app
                `Set.union_subset
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`x `hx] [])]
                   "=>"
                   (Term.app
                    `Exists.cases_on
                    [`hx
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`y `hy] [])]
                       "=>"
                       (Term.anonymousCtor
                        "⟨"
                        [`y
                         ","
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(group
                              (Tactic.rwSeq
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                                "]")
                               [])
                              [])
                             (group (Tactic.exact "exact" `hy) [])])))]
                        "⟩")))])))
                 (Term.app
                  `set.singleton_subset_iff.mpr
                  [(Term.anonymousCtor
                    "⟨"
                    [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
                            "]")
                           [])
                          [])
                         (group (Tactic.tacticRfl "rfl") [])])))]
                    "⟩")])])]))
            [])])
         [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Mathlib.Tactic.set
        "set"
        []
        (Mathlib.Tactic.setArgsRest
         `f
         []
         ":="
         (Term.app
          `AdjoinRoot.lift
          [(Term.hole "_")
           (Term.hole "_")
           (Term.paren "(" [(Term.app `aeval_gen_minpoly [`F `α]) [(Term.typeAscription ":" (Term.hole "_"))]] ")")])
         []))
       [])
      (group
       (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `minpoly.irreducible [`h]))))
       [])
      (group (Tactic.constructor "constructor") [])
      (group («tactic·.__;_» "·" [(group (Tactic.exact "exact" (Term.app `RingHom.injective [`f])) [])]) [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            («term_≤_»
             (Term.proj
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `F
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯")
              "."
              `toSubfield)
             "≤"
             (Term.app
              `RingHom.fieldRange
              [(Term.app
                (Term.proj
                 (Term.proj
                  (Term.proj
                   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    `F
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯")
                   "."
                   `toSubfield)
                  "."
                  `Subtype)
                 "."
                 `comp)
                [`f])]))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.exact
                  "exact"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x] [])]
                    "=>"
                    (Term.app
                     `Exists.cases_on
                     [(Term.app `this [(Term.app `Subtype.mem [`x])])
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`y `hy] [])]
                        "=>"
                        (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))]))))
                 [])])))))
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            `subfield.closure_le.mpr
            [(Term.app
              `Set.union_subset
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`x `hx] [])]
                 "=>"
                 (Term.app
                  `Exists.cases_on
                  [`hx
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`y `hy] [])]
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [`y
                       ","
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                              "]")
                             [])
                            [])
                           (group (Tactic.exact "exact" `hy) [])])))]
                      "⟩")))])))
               (Term.app
                `set.singleton_subset_iff.mpr
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
                   ","
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
                          "]")
                         [])
                        [])
                       (group (Tactic.tacticRfl "rfl") [])])))]
                  "⟩")])])]))
          [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.tacticSuffices_
      "suffices"
      (Term.sufficesDecl
       []
       («term_≤_»
        (Term.proj
         (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          `F
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯")
         "."
         `toSubfield)
        "≤"
        (Term.app
         `RingHom.fieldRange
         [(Term.app
           (Term.proj
            (Term.proj
             (Term.proj
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `F
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯")
              "."
              `toSubfield)
             "."
             `Subtype)
            "."
            `comp)
           [`f])]))
       (Term.byTactic'
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x] [])]
               "=>"
               (Term.app
                `Exists.cases_on
                [(Term.app `this [(Term.app `Subtype.mem [`x])])
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`y `hy] [])]
                   "=>"
                   (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))]))))
            [])])))))
     [])
    (group
     (Tactic.exact
      "exact"
      (Term.app
       `subfield.closure_le.mpr
       [(Term.app
         `Set.union_subset
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x `hx] [])]
            "=>"
            (Term.app
             `Exists.cases_on
             [`hx
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`y `hy] [])]
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [`y
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                         "]")
                        [])
                       [])
                      (group (Tactic.exact "exact" `hy) [])])))]
                 "⟩")))])))
          (Term.app
           `set.singleton_subset_iff.mpr
           [(Term.anonymousCtor
             "⟨"
             [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
                     "]")
                    [])
                   [])
                  (group (Tactic.tacticRfl "rfl") [])])))]
             "⟩")])])]))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `subfield.closure_le.mpr
    [(Term.app
      `Set.union_subset
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x `hx] [])]
         "=>"
         (Term.app
          `Exists.cases_on
          [`hx
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`y `hy] [])]
             "=>"
             (Term.anonymousCtor
              "⟨"
              [`y
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                      "]")
                     [])
                    [])
                   (group (Tactic.exact "exact" `hy) [])])))]
              "⟩")))])))
       (Term.app
        `set.singleton_subset_iff.mpr
        [(Term.anonymousCtor
          "⟨"
          [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
                  "]")
                 [])
                [])
               (group (Tactic.tacticRfl "rfl") [])])))]
          "⟩")])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `subfield.closure_le.mpr
   [(Term.app
     `Set.union_subset
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x `hx] [])]
        "=>"
        (Term.app
         `Exists.cases_on
         [`hx
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`y `hy] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [`y
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                     "]")
                    [])
                   [])
                  (group (Tactic.exact "exact" `hy) [])])))]
             "⟩")))])))
      (Term.app
       `set.singleton_subset_iff.mpr
       [(Term.anonymousCtor
         "⟨"
         [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
                 "]")
                [])
               [])
              (group (Tactic.tacticRfl "rfl") [])])))]
         "⟩")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Set.union_subset
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x `hx] [])]
      "=>"
      (Term.app
       `Exists.cases_on
       [`hx
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`y `hy] [])]
          "=>"
          (Term.anonymousCtor
           "⟨"
           [`y
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                   "]")
                  [])
                 [])
                (group (Tactic.exact "exact" `hy) [])])))]
           "⟩")))])))
    (Term.app
     `set.singleton_subset_iff.mpr
     [(Term.anonymousCtor
       "⟨"
       [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
               "]")
              [])
             [])
            (group (Tactic.tacticRfl "rfl") [])])))]
       "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `set.singleton_subset_iff.mpr
   [(Term.anonymousCtor
     "⟨"
     [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
      ","
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
             "]")
            [])
           [])
          (group (Tactic.tacticRfl "rfl") [])])))]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
           "]")
          [])
         [])
        (group (Tactic.tacticRfl "rfl") [])])))]
   "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)] "]")
        [])
       [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)] "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AdjoinRoot.lift_root
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `RingHom.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `AdjoinRoot.root [(Term.app `minpoly [`F `α])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly [`F `α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly [`F `α]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AdjoinRoot.root
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `set.singleton_subset_iff.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `set.singleton_subset_iff.mpr
   [(Term.anonymousCtor
     "⟨"
     [(Term.app `AdjoinRoot.root [(Term.paren "(" [(Term.app `minpoly [`F `α]) []] ")")])
      ","
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
             "]")
            [])
           [])
          (group (Tactic.tacticRfl "rfl") [])])))]
     "⟩")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x `hx] [])]
    "=>"
    (Term.app
     `Exists.cases_on
     [`hx
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`y `hy] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [`y
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                 "]")
                [])
               [])
              (group (Tactic.exact "exact" `hy) [])])))]
         "⟩")))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Exists.cases_on
   [`hx
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y `hy] [])]
      "=>"
      (Term.anonymousCtor
       "⟨"
       [`y
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
               "]")
              [])
             [])
            (group (Tactic.exact "exact" `hy) [])])))]
       "⟩")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y `hy] [])]
    "=>"
    (Term.anonymousCtor
     "⟨"
     [`y
      ","
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
             "]")
            [])
           [])
          (group (Tactic.exact "exact" `hy) [])])))]
     "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`y
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)] "]")
          [])
         [])
        (group (Tactic.exact "exact" `hy) [])])))]
   "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)] "]")
        [])
       [])
      (group (Tactic.exact "exact" `hy) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `hy)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)] "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AdjoinRoot.lift_of
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `RingHom.comp_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Exists.cases_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x `hx] [])]
    "=>"
    (Term.app
     `Exists.cases_on
     [`hx
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`y `hy] [])]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [`y
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                 "]")
                [])
               [])
              (group (Tactic.exact "exact" `hy) [])])))]
         "⟩")))])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set.union_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Set.union_subset
   [(Term.paren
     "("
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x `hx] [])]
        "=>"
        (Term.app
         `Exists.cases_on
         [`hx
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`y `hy] [])]
            "=>"
            (Term.anonymousCtor
             "⟨"
             [`y
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_of)]
                     "]")
                    [])
                   [])
                  (group (Tactic.exact "exact" `hy) [])])))]
             "⟩")))])))
      []]
     ")")
    (Term.paren
     "("
     [(Term.app
       `set.singleton_subset_iff.mpr
       [(Term.anonymousCtor
         "⟨"
         [(Term.app `AdjoinRoot.root [(Term.paren "(" [(Term.app `minpoly [`F `α]) []] ")")])
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `RingHom.comp_apply) "," (Tactic.rwRule [] `AdjoinRoot.lift_root)]
                 "]")
                [])
               [])
              (group (Tactic.tacticRfl "rfl") [])])))]
         "⟩")])
      []]
     ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `subfield.closure_le.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticSuffices_
   "suffices"
   (Term.sufficesDecl
    []
    («term_≤_»
     (Term.proj
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "."
      `toSubfield)
     "≤"
     (Term.app
      `RingHom.fieldRange
      [(Term.app
        (Term.proj
         (Term.proj
          (Term.proj
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `F
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")
           "."
           `toSubfield)
          "."
          `Subtype)
         "."
         `comp)
        [`f])]))
    (Term.byTactic'
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.exact
          "exact"
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`x] [])]
            "=>"
            (Term.app
             `Exists.cases_on
             [(Term.app `this [(Term.app `Subtype.mem [`x])])
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`y `hy] [])]
                "=>"
                (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))]))))
         [])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`x] [])]
     "=>"
     (Term.app
      `Exists.cases_on
      [(Term.app `this [(Term.app `Subtype.mem [`x])])
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`y `hy] [])]
         "=>"
         (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.app
     `Exists.cases_on
     [(Term.app `this [(Term.app `Subtype.mem [`x])])
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`y `hy] [])]
        "=>"
        (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Exists.cases_on
   [(Term.app `this [(Term.app `Subtype.mem [`x])])
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y `hy] [])]
      "=>"
      (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`y `hy] [])]
    "=>"
    (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`y "," (Term.app `Subtype.ext [`hy])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Subtype.ext [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subtype.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `this [(Term.app `Subtype.mem [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Subtype.mem [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subtype.mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Subtype.mem [`x]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `this [(Term.paren "(" [(Term.app `Subtype.mem [`x]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Exists.cases_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_≤_»
   (Term.proj
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    "."
    `toSubfield)
   "≤"
   (Term.app
    `RingHom.fieldRange
    [(Term.app
      (Term.proj
       (Term.proj
        (Term.proj
         (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          `F
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯")
         "."
         `toSubfield)
        "."
        `Subtype)
       "."
       `comp)
      [`f])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `RingHom.fieldRange
   [(Term.app
     (Term.proj
      (Term.proj
       (Term.proj
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        "."
        `toSubfield)
       "."
       `Subtype)
      "."
      `comp)
     [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.proj
     (Term.proj
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      "."
      `toSubfield)
     "."
     `Subtype)
    "."
    `comp)
   [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.proj
    (Term.proj
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     "."
     `toSubfield)
    "."
    `Subtype)
   "."
   `comp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj
   (Term.proj
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    "."
    `toSubfield)
   "."
   `Subtype)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   "."
   `toSubfield)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- algebra isomorphism between `adjoin_root` and `F⟮α⟯` -/ noncomputable
  def
    adjoinRootEquivAdjoin
    ( h : IsIntegral F α )
      : AdjoinRoot minpoly F α ≃ₐ[ F ] F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
    :=
      AlgEquiv.ofBijective
        AdjoinRoot.liftHom minpoly F α AdjoinSimple.gen F α aeval_gen_minpoly F α
          by
            set f := AdjoinRoot.lift _ _ ( aeval_gen_minpoly F α : _ )
              have := minpoly.irreducible h
              constructor
              · exact RingHom.injective f
              ·
                suffices
                    F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ . toSubfield
                        ≤
                        RingHom.fieldRange
                          F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ . toSubfield
                                .
                                Subtype
                              .
                              comp
                            f
                      by exact fun x => Exists.cases_on this Subtype.mem x fun y hy => ⟨ y , Subtype.ext hy ⟩
                  exact
                    subfield.closure_le.mpr
                      Set.union_subset
                        fun
                            x hx
                              =>
                              Exists.cases_on
                                hx fun y hy => ⟨ y , by rw [ RingHom.comp_apply , AdjoinRoot.lift_of ] exact hy ⟩
                          set.singleton_subset_iff.mpr
                            ⟨ AdjoinRoot.root minpoly F α , by rw [ RingHom.comp_apply , AdjoinRoot.lift_root ] rfl ⟩

theorem adjoin_root_equiv_adjoin_apply_root (h : IsIntegral F α) :
    adjoinRootEquivAdjoin F h (AdjoinRoot.root (minpoly F α)) = AdjoinSimple.gen F α :=
  AdjoinRoot.lift_root (aeval_gen_minpoly F α)

section PowerBasis

variable {L : Type _} [Field L] [Algebra K L]

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,\nwhere `d` is the degree of the minimal polynomial of `x`. -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `powerBasisAux [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`x] [":" `L] "}")
    (Term.explicitBinder "(" [`hx] [":" (Term.app `IsIntegral [`K `x])] [] ")")]
   [(Term.typeSpec
     ":"
     (Term.app
      `Basis
      [(Term.app `Finₓ [(Term.proj (Term.app `minpoly [`K `x]) "." `natDegree)])
       `K
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")]))])
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj (Term.proj (Term.app `AdjoinRoot.powerBasis [(Term.app `minpoly.ne_zero [`hx])]) "." `Basis) "." `map)
    [(Term.proj (Term.app `adjoinRootEquivAdjoin [`K `hx]) "." `toLinearEquiv)])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.proj (Term.app `AdjoinRoot.powerBasis [(Term.app `minpoly.ne_zero [`hx])]) "." `Basis) "." `map)
   [(Term.proj (Term.app `adjoinRootEquivAdjoin [`K `hx]) "." `toLinearEquiv)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `adjoinRootEquivAdjoin [`K `hx]) "." `toLinearEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `adjoinRootEquivAdjoin [`K `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoinRootEquivAdjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `adjoinRootEquivAdjoin [`K `hx]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj (Term.app `AdjoinRoot.powerBasis [(Term.app `minpoly.ne_zero [`hx])]) "." `Basis) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `AdjoinRoot.powerBasis [(Term.app `minpoly.ne_zero [`hx])]) "." `Basis)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `AdjoinRoot.powerBasis [(Term.app `minpoly.ne_zero [`hx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.ne_zero [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly.ne_zero [`hx]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AdjoinRoot.powerBasis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `AdjoinRoot.powerBasis [(Term.paren "(" [(Term.app `minpoly.ne_zero [`hx]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `Basis
   [(Term.app `Finₓ [(Term.proj (Term.app `minpoly [`K `x]) "." `natDegree)])
    `K
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/--
      The elements `1, x, ..., x ^ (d - 1)` form a basis for `K⟮x⟯`,
      where `d` is the degree of the minimal polynomial of `x`. -/
    noncomputable
  def
    powerBasisAux
    { x : L } ( hx : IsIntegral K x )
      :
        Basis
          Finₓ minpoly K x . natDegree
            K
            K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
    := AdjoinRoot.powerBasis minpoly.ne_zero hx . Basis . map adjoinRootEquivAdjoin K hx . toLinearEquiv

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,\nwhere `d` is the degree of the minimal polynomial of `x`. -/")]
  [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] []))] "]")]
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `adjoin.powerBasis [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`x] [":" `L] "}")
    (Term.explicitBinder "(" [`hx] [":" (Term.app `IsIntegral [`K `x])] [] ")")]
   [(Term.typeSpec
     ":"
     (Term.app
      `PowerBasis
      [`K
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")]))])
  (Command.whereStructInst
   "where"
   [(group
     (Command.whereStructField (Term.letDecl (Term.letIdDecl `gen [] [] ":=" (Term.app `AdjoinSimple.gen [`K `x]))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl (Term.letIdDecl `dim [] [] ":=" (Term.proj (Term.app `minpoly [`K `x]) "." `natDegree))))
     [])
    (group
     (Command.whereStructField (Term.letDecl (Term.letIdDecl `Basis [] [] ":=" (Term.app `powerBasisAux [`hx]))))
     [])
    (group
     (Command.whereStructField
      (Term.letDecl
       (Term.letIdDecl
        `basis_eq_pow
        []
        []
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`i] [])]
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `power_basis_aux)
                  ","
                  (Tactic.rwRule [] `Basis.map_apply)
                  ","
                  (Tactic.rwRule [] `PowerBasis.basis_eq_pow)
                  ","
                  (Tactic.rwRule [] `AlgEquiv.to_linear_equiv_apply)
                  ","
                  (Tactic.rwRule [] `AlgEquiv.map_pow)
                  ","
                  (Tactic.rwRule [] `AdjoinRoot.power_basis_gen)
                  ","
                  (Tactic.rwRule [] `adjoin_root_equiv_adjoin_apply_root)]
                 "]")
                [])
               [])]))))))))
     [])])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `power_basis_aux)
            ","
            (Tactic.rwRule [] `Basis.map_apply)
            ","
            (Tactic.rwRule [] `PowerBasis.basis_eq_pow)
            ","
            (Tactic.rwRule [] `AlgEquiv.to_linear_equiv_apply)
            ","
            (Tactic.rwRule [] `AlgEquiv.map_pow)
            ","
            (Tactic.rwRule [] `AdjoinRoot.power_basis_gen)
            ","
            (Tactic.rwRule [] `adjoin_root_equiv_adjoin_apply_root)]
           "]")
          [])
         [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `power_basis_aux)
          ","
          (Tactic.rwRule [] `Basis.map_apply)
          ","
          (Tactic.rwRule [] `PowerBasis.basis_eq_pow)
          ","
          (Tactic.rwRule [] `AlgEquiv.to_linear_equiv_apply)
          ","
          (Tactic.rwRule [] `AlgEquiv.map_pow)
          ","
          (Tactic.rwRule [] `AdjoinRoot.power_basis_gen)
          ","
          (Tactic.rwRule [] `adjoin_root_equiv_adjoin_apply_root)]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `power_basis_aux)
     ","
     (Tactic.rwRule [] `Basis.map_apply)
     ","
     (Tactic.rwRule [] `PowerBasis.basis_eq_pow)
     ","
     (Tactic.rwRule [] `AlgEquiv.to_linear_equiv_apply)
     ","
     (Tactic.rwRule [] `AlgEquiv.map_pow)
     ","
     (Tactic.rwRule [] `AdjoinRoot.power_basis_gen)
     ","
     (Tactic.rwRule [] `adjoin_root_equiv_adjoin_apply_root)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin_root_equiv_adjoin_apply_root
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AdjoinRoot.power_basis_gen
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgEquiv.map_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgEquiv.to_linear_equiv_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `PowerBasis.basis_eq_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Basis.map_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `power_basis_aux
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `powerBasisAux [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `powerBasisAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.proj (Term.app `minpoly [`K `x]) "." `natDegree)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `minpoly [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly [`K `x]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `AdjoinSimple.gen [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AdjoinSimple.gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `PowerBasis
   [`K
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/--
      The power basis `1, x, ..., x ^ (d - 1)` for `K⟮x⟯`,
      where `d` is the degree of the minimal polynomial of `x`. -/
    @[ simps ]
    noncomputable
  def
    adjoin.powerBasis
    { x : L } ( hx : IsIntegral K x )
      : PowerBasis K K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
    where
      gen := AdjoinSimple.gen K x
        dim := minpoly K x . natDegree
        Basis := powerBasisAux hx
        basis_eq_pow
          :=
          fun
            i
              =>
              by
                rw
                  [
                    power_basis_aux
                      ,
                      Basis.map_apply
                      ,
                      PowerBasis.basis_eq_pow
                      ,
                      AlgEquiv.to_linear_equiv_apply
                      ,
                      AlgEquiv.map_pow
                      ,
                      AdjoinRoot.power_basis_gen
                      ,
                      adjoin_root_equiv_adjoin_apply_root
                    ]

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin.finite_dimensional [])
  (Command.declSig
   [(Term.implicitBinder "{" [`x] [":" `L] "}")
    (Term.explicitBinder "(" [`hx] [":" (Term.app `IsIntegral [`K `x])] [] ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `FiniteDimensional
     [`K
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])))
  (Command.declValSimple ":=" (Term.app `PowerBasis.finite_dimensional [(Term.app `adjoin.powerBasis [`hx])]) [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `PowerBasis.finite_dimensional [(Term.app `adjoin.powerBasis [`hx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin.powerBasis [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin.powerBasis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `adjoin.powerBasis [`hx]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `PowerBasis.finite_dimensional
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `FiniteDimensional
   [`K
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  adjoin.finite_dimensional
  { x : L } ( hx : IsIntegral K x )
    : FiniteDimensional K K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
  := PowerBasis.finite_dimensional adjoin.powerBasis hx

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `adjoin.finrank [])
  (Command.declSig
   [(Term.implicitBinder "{" [`x] [":" `L] "}")
    (Term.explicitBinder "(" [`hx] [":" (Term.app `IsIntegral [`K `x])] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `FiniteDimensional.finrank
      [`K
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")])
     "="
     (Term.proj (Term.app `minpoly [`K `x]) "." `natDegree))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app
             `PowerBasis.finrank
             [(Term.paren
               "("
               [(Term.app `adjoin.power_basis [`hx]) [(Term.typeAscription ":" (Term.hole "_"))]]
               ")")]))]
          "]")
         [])
        [])
       (group (Tactic.tacticRfl "rfl") [])])))
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
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.app
            `PowerBasis.finrank
            [(Term.paren "(" [(Term.app `adjoin.power_basis [`hx]) [(Term.typeAscription ":" (Term.hole "_"))]] ")")]))]
         "]")
        [])
       [])
      (group (Tactic.tacticRfl "rfl") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.app
       `PowerBasis.finrank
       [(Term.paren "(" [(Term.app `adjoin.power_basis [`hx]) [(Term.typeAscription ":" (Term.hole "_"))]] ")")]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `PowerBasis.finrank
   [(Term.paren "(" [(Term.app `adjoin.power_basis [`hx]) [(Term.typeAscription ":" (Term.hole "_"))]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [(Term.app `adjoin.power_basis [`hx]) [(Term.typeAscription ":" (Term.hole "_"))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `adjoin.power_basis [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin.power_basis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `PowerBasis.finrank
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    `FiniteDimensional.finrank
    [`K
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")])
   "="
   (Term.proj (Term.app `minpoly [`K `x]) "." `natDegree))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `minpoly [`K `x]) "." `natDegree)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `minpoly [`K `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly [`K `x]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `FiniteDimensional.finrank
   [`K
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  adjoin.finrank
  { x : L } ( hx : IsIntegral K x )
    :
      FiniteDimensional.finrank K K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
        =
        minpoly K x . natDegree
  := by rw [ PowerBasis.finrank ( adjoin.power_basis hx : _ ) ] rfl

end PowerBasis

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots\nof `minpoly α` in `K`. -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `algHomAdjoinIntegralEquiv [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`h] [":" (Term.app `IsIntegral [`F `α])] [] ")")]
   [(Term.typeSpec
     ":"
     (Logic.Equiv.Basic.«term_≃_»
      (Algebra.Algebra.Basic.«term_→ₐ[_]_»
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       " →ₐ["
       `F
       "] "
       `K)
      " ≃ "
      («term{__:_//_}»
       "{"
       `x
       []
       "//"
       («term_∈_»
        `x
        "∈"
        (Term.proj
         (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `map) [(Term.app `algebraMap [`F `K])])
         "."
         `roots))
       "}")))])
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj (Term.proj (Term.app `adjoin.powerBasis [`h]) "." `liftEquiv') "." `trans)
    [(Term.app
      (Term.proj (Term.app `Equivₓ.refl [(Term.hole "_")]) "." `subtypeEquiv)
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`x] [])]
         "=>"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `adjoin.power_basis_gen)
                 ","
                 (Tactic.rwRule [] (Term.app `minpoly_gen [`h]))
                 ","
                 (Tactic.rwRule [] `Equivₓ.refl_apply)]
                "]")
               [])
              [])])))))])])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.proj (Term.app `adjoin.powerBasis [`h]) "." `liftEquiv') "." `trans)
   [(Term.app
     (Term.proj (Term.app `Equivₓ.refl [(Term.hole "_")]) "." `subtypeEquiv)
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`x] [])]
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `adjoin.power_basis_gen)
                ","
                (Tactic.rwRule [] (Term.app `minpoly_gen [`h]))
                ","
                (Tactic.rwRule [] `Equivₓ.refl_apply)]
               "]")
              [])
             [])])))))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `Equivₓ.refl [(Term.hole "_")]) "." `subtypeEquiv)
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `adjoin.power_basis_gen)
              ","
              (Tactic.rwRule [] (Term.app `minpoly_gen [`h]))
              ","
              (Tactic.rwRule [] `Equivₓ.refl_apply)]
             "]")
            [])
           [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`x] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `adjoin.power_basis_gen)
            ","
            (Tactic.rwRule [] (Term.app `minpoly_gen [`h]))
            ","
            (Tactic.rwRule [] `Equivₓ.refl_apply)]
           "]")
          [])
         [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `adjoin.power_basis_gen)
          ","
          (Tactic.rwRule [] (Term.app `minpoly_gen [`h]))
          ","
          (Tactic.rwRule [] `Equivₓ.refl_apply)]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `adjoin.power_basis_gen)
     ","
     (Tactic.rwRule [] (Term.app `minpoly_gen [`h]))
     ","
     (Tactic.rwRule [] `Equivₓ.refl_apply)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Equivₓ.refl_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly_gen [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly_gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin.power_basis_gen
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `Equivₓ.refl [(Term.hole "_")]) "." `subtypeEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Equivₓ.refl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Equivₓ.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Equivₓ.refl [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj (Term.paren "(" [(Term.app `Equivₓ.refl [(Term.hole "_")]) []] ")") "." `subtypeEquiv)
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`x] [])]
      "=>"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `adjoin.power_basis_gen)
              ","
              (Tactic.rwRule [] (Term.app `minpoly_gen [`h]))
              ","
              (Tactic.rwRule [] `Equivₓ.refl_apply)]
             "]")
            [])
           [])])))))])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj (Term.app `adjoin.powerBasis [`h]) "." `liftEquiv') "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `adjoin.powerBasis [`h]) "." `liftEquiv')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `adjoin.powerBasis [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin.powerBasis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `adjoin.powerBasis [`h]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Logic.Equiv.Basic.«term_≃_»
   (Algebra.Algebra.Basic.«term_→ₐ[_]_»
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    " →ₐ["
    `F
    "] "
    `K)
   " ≃ "
   («term{__:_//_}»
    "{"
    `x
    []
    "//"
    («term_∈_»
     `x
     "∈"
     (Term.proj
      (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `map) [(Term.app `algebraMap [`F `K])])
      "."
      `roots))
    "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term{__:_//_}»
   "{"
   `x
   []
   "//"
   («term_∈_»
    `x
    "∈"
    (Term.proj (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `map) [(Term.app `algebraMap [`F `K])]) "." `roots))
   "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∈_»
   `x
   "∈"
   (Term.proj (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `map) [(Term.app `algebraMap [`F `K])]) "." `roots))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `map) [(Term.app `algebraMap [`F `K])]) "." `roots)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `map) [(Term.app `algebraMap [`F `K])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `algebraMap [`F `K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `algebraMap [`F `K]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `minpoly [`F `α]) "." `map)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `minpoly [`F `α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly [`F `α]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj (Term.paren "(" [(Term.app `minpoly [`F `α]) []] ")") "." `map)
   [(Term.paren "(" [(Term.app `algebraMap [`F `K]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (Algebra.Algebra.Basic.«term_→ₐ[_]_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   " →ₐ["
   `F
   "] "
   `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/--
      Algebra homomorphism `F⟮α⟯ →ₐ[F] K` are in bijection with the set of roots
      of `minpoly α` in `K`. -/
    noncomputable
  def
    algHomAdjoinIntegralEquiv
    ( h : IsIntegral F α )
      :
        F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ →ₐ[ F ] K
          ≃
          { x // x ∈ minpoly F α . map algebraMap F K . roots }
    :=
      adjoin.powerBasis h . liftEquiv' . trans
        Equivₓ.refl _ . subtypeEquiv fun x => by rw [ adjoin.power_basis_gen , minpoly_gen h , Equivₓ.refl_apply ]

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `fintypeOfAlgHomAdjoinIntegral [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`h] [":" (Term.app `IsIntegral [`F `α])] [] ")")]
   [(Term.typeSpec
     ":"
     (Term.app
      `Fintype
      [(Algebra.Algebra.Basic.«term_→ₐ[_]_»
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        " →ₐ["
        `F
        "] "
        `K)]))])
  (Command.declValSimple ":=" (Term.app `PowerBasis.AlgHom.fintype [(Term.app `adjoin.powerBasis [`h])]) [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `PowerBasis.AlgHom.fintype [(Term.app `adjoin.powerBasis [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin.powerBasis [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin.powerBasis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `adjoin.powerBasis [`h]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `PowerBasis.AlgHom.fintype
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `Fintype
   [(Algebra.Algebra.Basic.«term_→ₐ[_]_»
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     " →ₐ["
     `F
     "] "
     `K)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Algebra.Basic.«term_→ₐ[_]_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Algebra.Basic.«term_→ₐ[_]_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Algebra.Basic.«term_→ₐ[_]_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   " →ₐ["
   `F
   "] "
   `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- Fintype of algebra homomorphism `F⟮α⟯ →ₐ[F] K` -/ noncomputable
  def
    fintypeOfAlgHomAdjoinIntegral
    ( h : IsIntegral F α )
      : Fintype F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ →ₐ[ F ] K
    := PowerBasis.AlgHom.fintype adjoin.powerBasis h

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `card_alg_hom_adjoin_integral [])
  (Command.declSig
   [(Term.explicitBinder "(" [`h] [":" (Term.app `IsIntegral [`F `α])] [] ")")
    (Term.explicitBinder "(" [`h_sep] [":" (Term.proj (Term.app `minpoly [`F `α]) "." `Separable)] [] ")")
    (Term.explicitBinder
     "("
     [`h_splits]
     [":" (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `Splits) [(Term.app `algebraMap [`F `K])])]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      (Term.explicit "@" `Fintype.card)
      [(Algebra.Algebra.Basic.«term_→ₐ[_]_»
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        " →ₐ["
        `F
        "] "
        `K)
       (Term.app `fintypeOfAlgHomAdjoinIntegral [`F `h])])
     "="
     (Term.proj (Term.app `minpoly [`F `α]) "." `natDegree))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.«tactic_<;>_»
         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `AlgHom.card_of_power_basis)] "]") [])
         "<;>"
         (Tactic.simp
          "simp"
          []
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] `adjoin.power_basis_dim)
            ","
            (Tactic.simpLemma [] [] `adjoin.power_basis_gen)
            ","
            (Tactic.simpLemma [] [] (Term.app `minpoly_gen [`h]))
            ","
            (Tactic.simpLemma [] [] `h_sep)
            ","
            (Tactic.simpLemma [] [] `h_splits)]
           "]"]
          []))
        [])])))
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
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `AlgHom.card_of_power_basis)] "]") [])
        "<;>"
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `adjoin.power_basis_dim)
           ","
           (Tactic.simpLemma [] [] `adjoin.power_basis_gen)
           ","
           (Tactic.simpLemma [] [] (Term.app `minpoly_gen [`h]))
           ","
           (Tactic.simpLemma [] [] `h_sep)
           ","
           (Tactic.simpLemma [] [] `h_splits)]
          "]"]
         []))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `AlgHom.card_of_power_basis)] "]") [])
   "<;>"
   (Tactic.simp
    "simp"
    []
    []
    ["only"]
    ["["
     [(Tactic.simpLemma [] [] `adjoin.power_basis_dim)
      ","
      (Tactic.simpLemma [] [] `adjoin.power_basis_gen)
      ","
      (Tactic.simpLemma [] [] (Term.app `minpoly_gen [`h]))
      ","
      (Tactic.simpLemma [] [] `h_sep)
      ","
      (Tactic.simpLemma [] [] `h_splits)]
     "]"]
    []))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `adjoin.power_basis_dim)
     ","
     (Tactic.simpLemma [] [] `adjoin.power_basis_gen)
     ","
     (Tactic.simpLemma [] [] (Term.app `minpoly_gen [`h]))
     ","
     (Tactic.simpLemma [] [] `h_sep)
     ","
     (Tactic.simpLemma [] [] `h_splits)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_splits
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_sep
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly_gen [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly_gen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin.power_basis_gen
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin.power_basis_dim
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `AlgHom.card_of_power_basis)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `AlgHom.card_of_power_basis
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    (Term.explicit "@" `Fintype.card)
    [(Algebra.Algebra.Basic.«term_→ₐ[_]_»
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      " →ₐ["
      `F
      "] "
      `K)
     (Term.app `fintypeOfAlgHomAdjoinIntegral [`F `h])])
   "="
   (Term.proj (Term.app `minpoly [`F `α]) "." `natDegree))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `minpoly [`F `α]) "." `natDegree)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `minpoly [`F `α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly [`F `α]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   (Term.explicit "@" `Fintype.card)
   [(Algebra.Algebra.Basic.«term_→ₐ[_]_»
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     " →ₐ["
     `F
     "] "
     `K)
    (Term.app `fintypeOfAlgHomAdjoinIntegral [`F `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `fintypeOfAlgHomAdjoinIntegral [`F `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `fintypeOfAlgHomAdjoinIntegral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `fintypeOfAlgHomAdjoinIntegral [`F `h]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Algebra.Basic.«term_→ₐ[_]_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Algebra.Basic.«term_→ₐ[_]_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Algebra.Algebra.Basic.«term_→ₐ[_]_»
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯")
   " →ₐ["
   `F
   "] "
   `K)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `F
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  card_alg_hom_adjoin_integral
  ( h : IsIntegral F α ) ( h_sep : minpoly F α . Separable ) ( h_splits : minpoly F α . Splits algebraMap F K )
    :
      @ Fintype.card
          F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ →ₐ[ F ] K
            fintypeOfAlgHomAdjoinIntegral F h
        =
        minpoly F α . natDegree
  :=
    by
      rw [ AlgHom.card_of_power_basis ]
        <;>
        simp only [ adjoin.power_basis_dim , adjoin.power_basis_gen , minpoly_gen h , h_sep , h_splits ]

end AdjoinIntegralElement

section Induction

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : finset E` such that
`intermediate_field.adjoin F t = S`. -/
def Fg (S : IntermediateField F E) : Prop :=
  ∃ t : Finset E, adjoin F ↑t = S

theorem fg_adjoin_finset (t : Finset E) : (adjoin F (↑t : Set E)).Fg :=
  ⟨t, rfl⟩

theorem fg_def {S : IntermediateField F E} : S.Fg ↔ ∃ t : Set E, Set.Finite t ∧ adjoin F t = S :=
  ⟨fun ⟨t, ht⟩ => ⟨↑t, Set.finite_mem_finset t, ht⟩, fun ⟨t, ht1, ht2⟩ =>
    ⟨ht1.toFinset, by
      rwa [Set.Finite.coe_to_finset]⟩⟩

theorem fg_bot : (⊥ : IntermediateField F E).Fg :=
  ⟨∅, adjoin_empty F E⟩

theorem fg_of_fg_to_subalgebra (S : IntermediateField F E) (h : S.toSubalgebra.Fg) : S.Fg := by
  cases' h with t ht
  exact ⟨t, (eq_adjoin_of_eq_algebra_adjoin _ _ _ ht.symm).symm⟩

theorem fg_of_noetherian (S : IntermediateField F E) [IsNoetherian F E] : S.Fg :=
  S.fg_of_fg_to_subalgebra S.toSubalgebra.fg_of_noetherian

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `induction_on_adjoin_finset [])
  (Command.declSig
   [(Term.explicitBinder "(" [`S] [":" (Term.app `Finset [`E])] [] ")")
    (Term.explicitBinder
     "("
     [`P]
     [":" (Term.arrow (Term.app `IntermediateField [`F `E]) "→" (Term.prop "Prop"))]
     []
     ")")
    (Term.explicitBinder "(" [`base] [":" (Term.app `P [(Order.BoundedOrder.«term⊥» "⊥")])] [] ")")
    (Term.explicitBinder
     "("
     [`ih]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])]
       ","
       (Mathlib.ExtendedBinder.«term∀__,_»
        "∀"
        (Lean.binderIdent `x)
        («binderTerm∈_» "∈" `S)
        ","
        (Term.forall
         "∀"
         []
         ","
         (Term.arrow
          (Term.app `P [`K])
          "→"
          (Term.app
           `P
           [(coeNotation
             "↑"
             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `K
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯"))])))))]
     []
     ")")]
   (Term.typeSpec ":" (Term.app `P [(Term.app `adjoin [`F (coeNotation "↑" `S)])])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" (Term.app `Finset.induction_on' [`S])) [])
       (group («tactic·.__;_» "·" [(group (Tactic.exact "exact" `base) [])]) [])
       (group
        («tactic·.__;_»
         "·"
         [(group (Tactic.intro "intro" [`a `s `h1 (Term.hole "_") (Term.hole "_") `h4]) [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Finset.coe_insert)
              ","
              (Tactic.rwRule [] `Set.insert_eq)
              ","
              (Tactic.rwRule [] `Set.union_comm)
              ","
              (Tactic.rwRule ["←"] `adjoin_adjoin_left)]
             "]")
            [])
           [])
          (group (Tactic.exact "exact" (Term.app `ih [(Term.app `adjoin [`F `s]) `a `h1 `h4])) [])])
        [])])))
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
     [(group (Tactic.apply "apply" (Term.app `Finset.induction_on' [`S])) [])
      (group («tactic·.__;_» "·" [(group (Tactic.exact "exact" `base) [])]) [])
      (group
       («tactic·.__;_»
        "·"
        [(group (Tactic.intro "intro" [`a `s `h1 (Term.hole "_") (Term.hole "_") `h4]) [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Finset.coe_insert)
             ","
             (Tactic.rwRule [] `Set.insert_eq)
             ","
             (Tactic.rwRule [] `Set.union_comm)
             ","
             (Tactic.rwRule ["←"] `adjoin_adjoin_left)]
            "]")
           [])
          [])
         (group (Tactic.exact "exact" (Term.app `ih [(Term.app `adjoin [`F `s]) `a `h1 `h4])) [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_»
   "·"
   [(group (Tactic.intro "intro" [`a `s `h1 (Term.hole "_") (Term.hole "_") `h4]) [])
    (group
     (Tactic.rwSeq
      "rw"
      []
      (Tactic.rwRuleSeq
       "["
       [(Tactic.rwRule [] `Finset.coe_insert)
        ","
        (Tactic.rwRule [] `Set.insert_eq)
        ","
        (Tactic.rwRule [] `Set.union_comm)
        ","
        (Tactic.rwRule ["←"] `adjoin_adjoin_left)]
       "]")
      [])
     [])
    (group (Tactic.exact "exact" (Term.app `ih [(Term.app `adjoin [`F `s]) `a `h1 `h4])) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `ih [(Term.app `adjoin [`F `s]) `a `h1 `h4]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ih [(Term.app `adjoin [`F `s]) `a `h1 `h4])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h4
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `adjoin [`F `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `adjoin [`F `s]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ih
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `Finset.coe_insert)
     ","
     (Tactic.rwRule [] `Set.insert_eq)
     ","
     (Tactic.rwRule [] `Set.union_comm)
     ","
     (Tactic.rwRule ["←"] `adjoin_adjoin_left)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin_adjoin_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.union_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.insert_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.coe_insert
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`a `s `h1 (Term.hole "_") (Term.hole "_") `h4])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h4
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `h1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_» "·" [(group (Tactic.exact "exact" `base) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `base)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `base
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" (Term.app `Finset.induction_on' [`S]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.induction_on' [`S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.induction_on'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `P [(Term.app `adjoin [`F (coeNotation "↑" `S)])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `adjoin [`F (coeNotation "↑" `S)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (coeNotation "↑" `S)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `S
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 1024, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `adjoin [`F (coeNotation "↑" `S)]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])]
   ","
   (Mathlib.ExtendedBinder.«term∀__,_»
    "∀"
    (Lean.binderIdent `x)
    («binderTerm∈_» "∈" `S)
    ","
    (Term.forall
     "∀"
     []
     ","
     (Term.arrow
      (Term.app `P [`K])
      "→"
      (Term.app
       `P
       [(coeNotation
         "↑"
         (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          `K
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯"))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.ExtendedBinder.«term∀__,_»
   "∀"
   (Lean.binderIdent `x)
   («binderTerm∈_» "∈" `S)
   ","
   (Term.forall
    "∀"
    []
    ","
    (Term.arrow
     (Term.app `P [`K])
     "→"
     (Term.app
      `P
      [(coeNotation
        "↑"
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `K
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   []
   ","
   (Term.arrow
    (Term.app `P [`K])
    "→"
    (Term.app
     `P
     [(coeNotation
       "↑"
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   (Term.app `P [`K])
   "→"
   (Term.app
    `P
    [(coeNotation
      "↑"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `P
   [(coeNotation
     "↑"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (coeNotation
   "↑"
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `K
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  induction_on_adjoin_finset
  ( S : Finset E )
      ( P : IntermediateField F E → Prop )
      ( base : P ⊥ )
      (
        ih
        :
          ∀
            K : IntermediateField F E
            ,
            ∀ x ∈ S , ∀ , P K → P ↑ K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
        )
    : P adjoin F ↑ S
  :=
    by
      apply Finset.induction_on' S
        · exact base
        ·
          intro a s h1 _ _ h4
            rw [ Finset.coe_insert , Set.insert_eq , Set.union_comm , ← adjoin_adjoin_left ]
            exact ih adjoin F s a h1 h4

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `induction_on_adjoin_fg [])
  (Command.declSig
   [(Term.explicitBinder
     "("
     [`P]
     [":" (Term.arrow (Term.app `IntermediateField [`F `E]) "→" (Term.prop "Prop"))]
     []
     ")")
    (Term.explicitBinder "(" [`base] [":" (Term.app `P [(Order.BoundedOrder.«term⊥» "⊥")])] [] ")")
    (Term.explicitBinder
     "("
     [`ih]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
        (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
       ","
       (Term.arrow
        (Term.app `P [`K])
        "→"
        (Term.app
         `P
         [(coeNotation
           "↑"
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `K
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯"))])))]
     []
     ")")
    (Term.explicitBinder "(" [`K] [":" (Term.app `IntermediateField [`F `E])] [] ")")
    (Term.explicitBinder "(" [`hK] [":" (Term.proj `K "." `Fg)] [] ")")]
   (Term.typeSpec ":" (Term.app `P [`K])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
             "⟩")])]
         []
         [":=" [`hK]])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `induction_on_adjoin_finset
          [`S
           `P
           `base
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`K `x (Term.hole "_") `hK] [])] "=>" (Term.app `ih [`K `x `hK])))]))
        [])])))
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
     [(group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
            "⟩")])]
        []
        [":=" [`hK]])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `induction_on_adjoin_finset
         [`S
          `P
          `base
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`K `x (Term.hole "_") `hK] [])] "=>" (Term.app `ih [`K `x `hK])))]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `induction_on_adjoin_finset
    [`S
     `P
     `base
     (Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [`K `x (Term.hole "_") `hK] [])] "=>" (Term.app `ih [`K `x `hK])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `induction_on_adjoin_finset
   [`S
    `P
    `base
    (Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`K `x (Term.hole "_") `hK] [])] "=>" (Term.app `ih [`K `x `hK])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`K `x (Term.hole "_") `hK] [])] "=>" (Term.app `ih [`K `x `hK])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ih [`K `x `hK])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hK
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ih
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `base
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `induction_on_adjoin_finset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
       "⟩")])]
   []
   [":=" [`hK]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hK
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `P [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `K "." `Fg)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
    (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
   ","
   (Term.arrow
    (Term.app `P [`K])
    "→"
    (Term.app
     `P
     [(coeNotation
       "↑"
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   (Term.app `P [`K])
   "→"
   (Term.app
    `P
    [(coeNotation
      "↑"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `P
   [(coeNotation
     "↑"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (coeNotation
   "↑"
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `K
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  induction_on_adjoin_fg
  ( P : IntermediateField F E → Prop )
      ( base : P ⊥ )
      (
        ih
        :
          ∀
            K : IntermediateField F E x : E
            ,
            P K → P ↑ K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
        )
      ( K : IntermediateField F E )
      ( hK : K . Fg )
    : P K
  := by obtain ⟨ S , rfl ⟩ := hK exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `induction_on_adjoin [])
  (Command.declSig
   [(Term.instBinder "[" [`fd ":"] (Term.app `FiniteDimensional [`F `E]) "]")
    (Term.explicitBinder
     "("
     [`P]
     [":" (Term.arrow (Term.app `IntermediateField [`F `E]) "→" (Term.prop "Prop"))]
     []
     ")")
    (Term.explicitBinder "(" [`base] [":" (Term.app `P [(Order.BoundedOrder.«term⊥» "⊥")])] [] ")")
    (Term.explicitBinder
     "("
     [`ih]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
        (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
       ","
       (Term.arrow
        (Term.app `P [`K])
        "→"
        (Term.app
         `P
         [(coeNotation
           "↑"
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `K
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯"))])))]
     []
     ")")
    (Term.explicitBinder "(" [`K] [":" (Term.app `IntermediateField [`F `E])] [] ")")]
   (Term.typeSpec ":" (Term.app `P [`K])))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Lean.termThis "this")
           []
           [(Term.typeSpec ":" (Term.app `IsNoetherian [`F `E]))]
           ":="
           (Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`inferInstance]))))
        [])
       (group (Tactic.exact "exact" (Term.app `induction_on_adjoin_fg [`P `base `ih `K `K.fg_of_noetherian])) [])])))
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
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Lean.termThis "this")
          []
          [(Term.typeSpec ":" (Term.app `IsNoetherian [`F `E]))]
          ":="
          (Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`inferInstance]))))
       [])
      (group (Tactic.exact "exact" (Term.app `induction_on_adjoin_fg [`P `base `ih `K `K.fg_of_noetherian])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `induction_on_adjoin_fg [`P `base `ih `K `K.fg_of_noetherian]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `induction_on_adjoin_fg [`P `base `ih `K `K.fg_of_noetherian])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K.fg_of_noetherian
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ih
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `base
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `induction_on_adjoin_fg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Lean.termThis "this")
     []
     [(Term.typeSpec ":" (Term.app `IsNoetherian [`F `E]))]
     ":="
     (Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`inferInstance]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`inferInstance])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `IsNoetherian.iff_fg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IsNoetherian [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsNoetherian
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Lean.termThis "this")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app `P [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `P
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`K] [(Term.typeSpec ":" (Term.app `IntermediateField [`F `E]))])
    (Term.simpleBinder [`x] [(Term.typeSpec ":" `E)])]
   ","
   (Term.arrow
    (Term.app `P [`K])
    "→"
    (Term.app
     `P
     [(coeNotation
       "↑"
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   (Term.app `P [`K])
   "→"
   (Term.app
    `P
    [(coeNotation
      "↑"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `P
   [(coeNotation
     "↑"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'coeNotation', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (coeNotation
   "↑"
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `K
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  induction_on_adjoin
  [ fd : FiniteDimensional F E ]
      ( P : IntermediateField F E → Prop )
      ( base : P ⊥ )
      (
        ih
        :
          ∀
            K : IntermediateField F E x : E
            ,
            P K → P ↑ K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
        )
      ( K : IntermediateField F E )
    : P K
  :=
    by
      let this : IsNoetherian F E := IsNoetherian.iff_fg . 2 inferInstance
        exact induction_on_adjoin_fg P base ih K K.fg_of_noetherian

end Induction

section AlgHomMkAdjoinSplits

variable (F E K : Type _) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] {S : Set E}

/-- Lifts `L → K` of `F → K` -/
def Lifts :=
  ΣL : IntermediateField F E, L →ₐ[F] K

variable {F E K}

instance : PartialOrderₓ (Lifts F E K) where
  le := fun x y => x.1 ≤ y.1 ∧ ∀ s : x.1 t : y.1, (s : E) = t → x.2 s = y.2 t
  le_refl := fun x => ⟨le_reflₓ x.1, fun s t hst => congr_argₓ x.2 (Subtype.ext hst)⟩
  le_trans := fun x y z hxy hyz =>
    ⟨le_transₓ hxy.1 hyz.1, fun s u hsu => Eq.trans (hxy.2 s ⟨s, hxy.1 s.Mem⟩ rfl) (hyz.2 ⟨s, hxy.1 s.Mem⟩ u hsu)⟩
  le_antisymm := by
    rintro ⟨x1, x2⟩ ⟨y1, y2⟩ ⟨hxy1, hxy2⟩ ⟨hyx1, hyx2⟩
    obtain rfl : x1 = y1 := le_antisymmₓ hxy1 hyx1
    congr
    exact AlgHom.ext fun s => hxy2 s s rfl

noncomputable instance : OrderBot (Lifts F E K) where
  bot := ⟨⊥, (Algebra.ofId F K).comp (botEquiv F E).toAlgHom⟩
  bot_le := fun x =>
    ⟨bot_le, fun s t hst => by
      cases' intermediate_field.mem_bot.mp s.mem with u hu
      rw [show s = (algebraMap F _) u from Subtype.ext hu.symm, AlgHom.commutes]
      rw [show t = (algebraMap F _) u from Subtype.ext (Eq.trans hu hst).symm, AlgHom.commutes]⟩

noncomputable instance : Inhabited (Lifts F E K) :=
  ⟨⊥⟩

theorem Lifts.eq_of_le {x y : Lifts F E K} (hxy : x ≤ y) (s : x.1) : x.2 s = y.2 ⟨s, hxy.1 s.Mem⟩ :=
  hxy.2 s ⟨s, hxy.1 s.Mem⟩ rfl

theorem Lifts.exists_max_two {c : Set (Lifts F E K)} {x y : Lifts F E K} (hc : IsChain (· ≤ ·) c)
    (hx : x ∈ Set.Insert ⊥ c) (hy : y ∈ Set.Insert ⊥ c) : ∃ z : Lifts F E K, z ∈ Set.Insert ⊥ c ∧ x ≤ z ∧ y ≤ z := by
  cases' (hc.insert fun _ _ _ => Or.inl bot_le).Total hx hy with hxy hyx
  · exact ⟨y, hy, hxy, le_reflₓ y⟩
    
  · exact ⟨x, hx, le_reflₓ x, hyx⟩
    

theorem Lifts.exists_max_three {c : Set (Lifts F E K)} {x y z : Lifts F E K} (hc : IsChain (· ≤ ·) c)
    (hx : x ∈ Set.Insert ⊥ c) (hy : y ∈ Set.Insert ⊥ c) (hz : z ∈ Set.Insert ⊥ c) :
    ∃ w : Lifts F E K, w ∈ Set.Insert ⊥ c ∧ x ≤ w ∧ y ≤ w ∧ z ≤ w := by
  obtain ⟨v, hv, hxv, hyv⟩ := lifts.exists_max_two hc hx hy
  obtain ⟨w, hw, hzw, hvw⟩ := lifts.exists_max_two hc hz hv
  exact ⟨w, hw, le_transₓ hxv hvw, le_transₓ hyv hvw, hzw⟩

/-- An upper bound on a chain of lifts -/
def Lifts.upperBoundIntermediateField {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) : IntermediateField F E where
  Carrier := fun s => ∃ x : Lifts F E K, x ∈ Set.Insert ⊥ c ∧ (s ∈ x.1 : Prop)
  zero_mem' := ⟨⊥, Set.mem_insert ⊥ c, zero_mem ⊥⟩
  one_mem' := ⟨⊥, Set.mem_insert ⊥ c, one_mem ⊥⟩
  neg_mem' := by
    rintro _ ⟨x, y, h⟩
    exact ⟨x, ⟨y, x.1.neg_mem h⟩⟩
  inv_mem' := by
    rintro _ ⟨x, y, h⟩
    exact ⟨x, ⟨y, x.1.inv_mem h⟩⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy
    exact ⟨z, hz, z.1.add_mem (hxz.1 ha) (hyz.1 hb)⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc hx hy
    exact ⟨z, hz, z.1.mul_mem (hxz.1 ha) (hyz.1 hb)⟩
  algebra_map_mem' := fun s => ⟨⊥, Set.mem_insert ⊥ c, algebra_map_mem ⊥ s⟩

/-- The lift on the upper bound on a chain of lifts -/
noncomputable def Lifts.upperBoundAlgHom {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) :
    Lifts.upperBoundIntermediateField hc →ₐ[F] K where
  toFun := fun s => (Classical.some s.Mem).2 ⟨s, (Classical.some_spec s.Mem).2⟩
  map_zero' := AlgHom.map_zero _
  map_one' := AlgHom.map_one _
  map_add' := fun s t => by
    obtain ⟨w, hw, hxw, hyw, hzw⟩ :=
      lifts.exists_max_three hc (Classical.some_spec s.mem).1 (Classical.some_spec t.mem).1
        (Classical.some_spec (s + t).Mem).1
    rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ← w.2.map_add]
    rfl
  map_mul' := fun s t => by
    obtain ⟨w, hw, hxw, hyw, hzw⟩ :=
      lifts.exists_max_three hc (Classical.some_spec s.mem).1 (Classical.some_spec t.mem).1
        (Classical.some_spec (s * t).Mem).1
    rw [lifts.eq_of_le hxw, lifts.eq_of_le hyw, lifts.eq_of_le hzw, ← w.2.map_mul]
    rfl
  commutes' := fun _ => AlgHom.commutes _ _

/-- An upper bound on a chain of lifts -/
noncomputable def Lifts.upperBound {c : Set (Lifts F E K)} (hc : IsChain (· ≤ ·) c) : Lifts F E K :=
  ⟨Lifts.upperBoundIntermediateField hc, Lifts.upperBoundAlgHom hc⟩

theorem Lifts.exists_upper_bound (c : Set (Lifts F E K)) (hc : IsChain (· ≤ ·) c) : ∃ ub, ∀, ∀ a ∈ c, ∀, a ≤ ub :=
  ⟨Lifts.upperBound hc, by
    intro x hx
    constructor
    · exact fun s hs => ⟨x, Set.mem_insert_of_mem ⊥ hx, hs⟩
      
    · intro s t hst
      change x.2 s = (Classical.some t.mem).2 ⟨t, (Classical.some_spec t.mem).2⟩
      obtain ⟨z, hz, hxz, hyz⟩ := lifts.exists_max_two hc (Set.mem_insert_of_mem ⊥ hx) (Classical.some_spec t.mem).1
      rw [lifts.eq_of_le hxz, lifts.eq_of_le hyz]
      exact congr_argₓ z.2 (Subtype.ext hst)
      ⟩

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "Extend a lift `x : lifts F E K` to an element `s : E` whose conjugates are all in `K` -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `Lifts.liftOfSplits [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`x] [":" (Term.app `Lifts [`F `E `K])] [] ")")
    (Term.implicitBinder "{" [`s] [":" `E] "}")
    (Term.explicitBinder "(" [`h1] [":" (Term.app `IsIntegral [`F `s])] [] ")")
    (Term.explicitBinder
     "("
     [`h2]
     [":" (Term.app (Term.proj (Term.app `minpoly [`F `s]) "." `Splits) [(Term.app `algebraMap [`F `K])])]
     []
     ")")]
   [(Term.typeSpec ":" (Term.app `Lifts [`F `E `K]))])
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl
     (Term.letIdDecl
      `h3
      []
      [(Term.typeSpec ":" (Term.app `IsIntegral [(Term.proj `x "." (fieldIdx "1")) `s]))]
      ":="
      (Term.app `is_integral_of_is_scalar_tower [`s `h1])))
    []
    (Term.let
     "let"
     (Term.letDecl
      (Term.letIdDecl
       `key
       []
       [(Term.typeSpec
         ":"
         (Term.app
          (Term.proj (Term.app `minpoly [(Term.proj `x "." (fieldIdx "1")) `s]) "." `Splits)
          [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)]))]
       ":="
       (Term.app
        `splits_of_splits_of_dvd
        [(Term.hole "_")
         (Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h1])])
         (Term.app
          (Term.proj (Term.app `splits_map_iff [(Term.hole "_") (Term.hole "_")]) "." `mpr)
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.convert "convert" [] `h2 []) [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `RingHom.ext
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`y] [])]
                     "=>"
                     (Term.app (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `commutes) [`y])))]))
                [])])))])
         (Term.app `minpoly.dvd_map_of_is_scalar_tower [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])))
     []
     (Term.anonymousCtor
      "⟨"
      [(coeNotation
        "↑"
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         (Term.proj `x "." (fieldIdx "1"))
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯"))
       ","
       (Term.app
        (Term.proj
         (Term.app
          (Term.explicit "@" `algHomEquivSigma)
          [`F
           (Term.proj `x "." (fieldIdx "1"))
           (Term.paren
            "("
            [(coeNotation
              "↑"
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               (Term.proj `x "." (fieldIdx "1"))
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯"))
             [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
            ")")
           `K
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.hole "_")
           (Term.app
            `IntermediateField.algebra
            [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              (Term.proj `x "." (fieldIdx "1"))
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯")])
           (Term.app
            `IsScalarTower.of_algebra_map_eq
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])])
         "."
         `invFun)
        [(Term.anonymousCtor
          "⟨"
          [(Term.proj `x "." (fieldIdx "2"))
           ","
           (Term.app
            (Term.proj
             (Term.app
              (Term.explicit "@" `algHomAdjoinIntegralEquiv)
              [(Term.proj `x "." (fieldIdx "1"))
               (Term.hole "_")
               `E
               (Term.hole "_")
               (Term.hole "_")
               `s
               `K
               (Term.hole "_")
               (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
               `h3])
             "."
             `invFun)
            [(Term.anonymousCtor
              "⟨"
              [(Term.app
                `rootOfSplits
                [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
                 `key
                 (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
               ","
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Mathlib.Tactic.tacticSimp_rw___
                     "simp_rw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        []
                        (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
                       ","
                       (Tactic.rwRule [] `is_root)
                       ","
                       (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
                      "]")
                     [])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `map_root_of_splits
                      [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
                       `key
                       (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
                    [])])))]
              "⟩")])]
          "⟩")])]
      "⟩")))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `h3
     []
     [(Term.typeSpec ":" (Term.app `IsIntegral [(Term.proj `x "." (fieldIdx "1")) `s]))]
     ":="
     (Term.app `is_integral_of_is_scalar_tower [`s `h1])))
   []
   (Term.let
    "let"
    (Term.letDecl
     (Term.letIdDecl
      `key
      []
      [(Term.typeSpec
        ":"
        (Term.app
         (Term.proj (Term.app `minpoly [(Term.proj `x "." (fieldIdx "1")) `s]) "." `Splits)
         [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)]))]
      ":="
      (Term.app
       `splits_of_splits_of_dvd
       [(Term.hole "_")
        (Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h1])])
        (Term.app
         (Term.proj (Term.app `splits_map_iff [(Term.hole "_") (Term.hole "_")]) "." `mpr)
         [(Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.convert "convert" [] `h2 []) [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `RingHom.ext
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`y] [])]
                    "=>"
                    (Term.app (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `commutes) [`y])))]))
               [])])))])
        (Term.app `minpoly.dvd_map_of_is_scalar_tower [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])))
    []
    (Term.anonymousCtor
     "⟨"
     [(coeNotation
       "↑"
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        (Term.proj `x "." (fieldIdx "1"))
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯"))
      ","
      (Term.app
       (Term.proj
        (Term.app
         (Term.explicit "@" `algHomEquivSigma)
         [`F
          (Term.proj `x "." (fieldIdx "1"))
          (Term.paren
           "("
           [(coeNotation
             "↑"
             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              (Term.proj `x "." (fieldIdx "1"))
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯"))
            [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
           ")")
          `K
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.hole "_")
          (Term.app
           `IntermediateField.algebra
           [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             (Term.proj `x "." (fieldIdx "1"))
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯")])
          (Term.app
           `IsScalarTower.of_algebra_map_eq
           [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])])
        "."
        `invFun)
       [(Term.anonymousCtor
         "⟨"
         [(Term.proj `x "." (fieldIdx "2"))
          ","
          (Term.app
           (Term.proj
            (Term.app
             (Term.explicit "@" `algHomAdjoinIntegralEquiv)
             [(Term.proj `x "." (fieldIdx "1"))
              (Term.hole "_")
              `E
              (Term.hole "_")
              (Term.hole "_")
              `s
              `K
              (Term.hole "_")
              (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
              `h3])
            "."
            `invFun)
           [(Term.anonymousCtor
             "⟨"
             [(Term.app
               `rootOfSplits
               [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
                `key
                (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
              ","
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Mathlib.Tactic.tacticSimp_rw___
                    "simp_rw"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       []
                       (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
                      ","
                      (Tactic.rwRule [] `is_root)
                      ","
                      (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
                     "]")
                    [])
                   [])
                  (group
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `map_root_of_splits
                     [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
                      `key
                      (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
                   [])])))]
             "⟩")])]
         "⟩")])]
     "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `key
     []
     [(Term.typeSpec
       ":"
       (Term.app
        (Term.proj (Term.app `minpoly [(Term.proj `x "." (fieldIdx "1")) `s]) "." `Splits)
        [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)]))]
     ":="
     (Term.app
      `splits_of_splits_of_dvd
      [(Term.hole "_")
       (Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h1])])
       (Term.app
        (Term.proj (Term.app `splits_map_iff [(Term.hole "_") (Term.hole "_")]) "." `mpr)
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group (Tactic.convert "convert" [] `h2 []) [])
             (group
              (Tactic.exact
               "exact"
               (Term.app
                `RingHom.ext
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`y] [])]
                   "=>"
                   (Term.app (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `commutes) [`y])))]))
              [])])))])
       (Term.app `minpoly.dvd_map_of_is_scalar_tower [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])))
   []
   (Term.anonymousCtor
    "⟨"
    [(coeNotation
      "↑"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       (Term.proj `x "." (fieldIdx "1"))
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))
     ","
     (Term.app
      (Term.proj
       (Term.app
        (Term.explicit "@" `algHomEquivSigma)
        [`F
         (Term.proj `x "." (fieldIdx "1"))
         (Term.paren
          "("
          [(coeNotation
            "↑"
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             (Term.proj `x "." (fieldIdx "1"))
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯"))
           [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
          ")")
         `K
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.hole "_")
         (Term.app
          `IntermediateField.algebra
          [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            (Term.proj `x "." (fieldIdx "1"))
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯")])
         (Term.app
          `IsScalarTower.of_algebra_map_eq
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])])
       "."
       `invFun)
      [(Term.anonymousCtor
        "⟨"
        [(Term.proj `x "." (fieldIdx "2"))
         ","
         (Term.app
          (Term.proj
           (Term.app
            (Term.explicit "@" `algHomAdjoinIntegralEquiv)
            [(Term.proj `x "." (fieldIdx "1"))
             (Term.hole "_")
             `E
             (Term.hole "_")
             (Term.hole "_")
             `s
             `K
             (Term.hole "_")
             (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
             `h3])
           "."
           `invFun)
          [(Term.anonymousCtor
            "⟨"
            [(Term.app
              `rootOfSplits
              [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
               `key
               (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Mathlib.Tactic.tacticSimp_rw___
                   "simp_rw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule
                      []
                      (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
                     ","
                     (Tactic.rwRule [] `is_root)
                     ","
                     (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.exact
                   "exact"
                   (Term.app
                    `map_root_of_splits
                    [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
                     `key
                     (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
                  [])])))]
            "⟩")])]
        "⟩")])]
    "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(coeNotation
     "↑"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      (Term.proj `x "." (fieldIdx "1"))
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))
    ","
    (Term.app
     (Term.proj
      (Term.app
       (Term.explicit "@" `algHomEquivSigma)
       [`F
        (Term.proj `x "." (fieldIdx "1"))
        (Term.paren
         "("
         [(coeNotation
           "↑"
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            (Term.proj `x "." (fieldIdx "1"))
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯"))
          [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
         ")")
        `K
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.hole "_")
        (Term.app
         `IntermediateField.algebra
         [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           (Term.proj `x "." (fieldIdx "1"))
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")])
        (Term.app
         `IsScalarTower.of_algebra_map_eq
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])])
      "."
      `invFun)
     [(Term.anonymousCtor
       "⟨"
       [(Term.proj `x "." (fieldIdx "2"))
        ","
        (Term.app
         (Term.proj
          (Term.app
           (Term.explicit "@" `algHomAdjoinIntegralEquiv)
           [(Term.proj `x "." (fieldIdx "1"))
            (Term.hole "_")
            `E
            (Term.hole "_")
            (Term.hole "_")
            `s
            `K
            (Term.hole "_")
            (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
            `h3])
          "."
          `invFun)
         [(Term.anonymousCtor
           "⟨"
           [(Term.app
             `rootOfSplits
             [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
              `key
              (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
            ","
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Mathlib.Tactic.tacticSimp_rw___
                  "simp_rw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
                    ","
                    (Tactic.rwRule [] `is_root)
                    ","
                    (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `map_root_of_splits
                   [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
                    `key
                    (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
                 [])])))]
           "⟩")])]
       "⟩")])]
   "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     (Term.explicit "@" `algHomEquivSigma)
     [`F
      (Term.proj `x "." (fieldIdx "1"))
      (Term.paren
       "("
       [(coeNotation
         "↑"
         (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          (Term.proj `x "." (fieldIdx "1"))
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯"))
        [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
       ")")
      `K
      (Term.hole "_")
      (Term.hole "_")
      (Term.hole "_")
      (Term.hole "_")
      (Term.hole "_")
      (Term.hole "_")
      (Term.hole "_")
      (Term.app
       `IntermediateField.algebra
       [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         (Term.proj `x "." (fieldIdx "1"))
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")])
      (Term.app
       `IsScalarTower.of_algebra_map_eq
       [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])])
    "."
    `invFun)
   [(Term.anonymousCtor
     "⟨"
     [(Term.proj `x "." (fieldIdx "2"))
      ","
      (Term.app
       (Term.proj
        (Term.app
         (Term.explicit "@" `algHomAdjoinIntegralEquiv)
         [(Term.proj `x "." (fieldIdx "1"))
          (Term.hole "_")
          `E
          (Term.hole "_")
          (Term.hole "_")
          `s
          `K
          (Term.hole "_")
          (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
          `h3])
        "."
        `invFun)
       [(Term.anonymousCtor
         "⟨"
         [(Term.app
           `rootOfSplits
           [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
            `key
            (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
          ","
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Mathlib.Tactic.tacticSimp_rw___
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
                  ","
                  (Tactic.rwRule [] `is_root)
                  ","
                  (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
                 "]")
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `map_root_of_splits
                 [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
                  `key
                  (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
               [])])))]
         "⟩")])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.proj `x "." (fieldIdx "2"))
    ","
    (Term.app
     (Term.proj
      (Term.app
       (Term.explicit "@" `algHomAdjoinIntegralEquiv)
       [(Term.proj `x "." (fieldIdx "1"))
        (Term.hole "_")
        `E
        (Term.hole "_")
        (Term.hole "_")
        `s
        `K
        (Term.hole "_")
        (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
        `h3])
      "."
      `invFun)
     [(Term.anonymousCtor
       "⟨"
       [(Term.app
         `rootOfSplits
         [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
          `key
          (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Mathlib.Tactic.tacticSimp_rw___
              "simp_rw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
                ","
                (Tactic.rwRule [] `is_root)
                ","
                (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
               "]")
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               `map_root_of_splits
               [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
                `key
                (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
             [])])))]
       "⟩")])]
   "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     (Term.explicit "@" `algHomAdjoinIntegralEquiv)
     [(Term.proj `x "." (fieldIdx "1"))
      (Term.hole "_")
      `E
      (Term.hole "_")
      (Term.hole "_")
      `s
      `K
      (Term.hole "_")
      (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
      `h3])
    "."
    `invFun)
   [(Term.anonymousCtor
     "⟨"
     [(Term.app
       `rootOfSplits
       [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
        `key
        (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
      ","
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Mathlib.Tactic.tacticSimp_rw___
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
              ","
              (Tactic.rwRule [] `is_root)
              ","
              (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
             "]")
            [])
           [])
          (group
           (Tactic.exact
            "exact"
            (Term.app
             `map_root_of_splits
             [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
              `key
              (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
           [])])))]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app
     `rootOfSplits
     [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
      `key
      (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
    ","
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Mathlib.Tactic.tacticSimp_rw___
          "simp_rw"
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
            ","
            (Tactic.rwRule [] `is_root)
            ","
            (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
           "]")
          [])
         [])
        (group
         (Tactic.exact
          "exact"
          (Term.app
           `map_root_of_splits
           [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
            `key
            (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
         [])])))]
   "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Mathlib.Tactic.tacticSimp_rw___
        "simp_rw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
          ","
          (Tactic.rwRule [] `is_root)
          ","
          (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
         "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `map_root_of_splits
         [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
          `key
          (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `map_root_of_splits
    [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
     `key
     (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `map_root_of_splits
   [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
    `key
    (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.degree_pos [`h3])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h3
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.degree_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly.degree_pos [`h3]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ne_of_gtₓ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `ne_of_gtₓ [(Term.paren "(" [(Term.app `minpoly.degree_pos [`h3]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `key
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `map_root_of_splits
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.tacticSimp_rw___
   "simp_rw"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])]))
     ","
     (Tactic.rwRule [] `is_root)
     ","
     (Tactic.rwRule ["←"] `eval₂_eq_eval_map)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `eval₂_eq_eval_map
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_root
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mem_roots [(Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `map_ne_zero [(Term.app `minpoly.ne_zero [`h3])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.ne_zero [`h3])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h3
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly.ne_zero [`h3]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `map_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `map_ne_zero [(Term.paren "(" [(Term.app `minpoly.ne_zero [`h3]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mem_roots
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `rootOfSplits
   [(Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
    `key
    (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ne_of_gtₓ [(Term.app `minpoly.degree_pos [`h3])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `minpoly.degree_pos [`h3])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h3
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `minpoly.degree_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `minpoly.degree_pos [`h3]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ne_of_gtₓ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `ne_of_gtₓ [(Term.paren "(" [(Term.app `minpoly.degree_pos [`h3]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `key
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `rootOfSplits
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app
    (Term.explicit "@" `algHomAdjoinIntegralEquiv)
    [(Term.proj `x "." (fieldIdx "1"))
     (Term.hole "_")
     `E
     (Term.hole "_")
     (Term.hole "_")
     `s
     `K
     (Term.hole "_")
     (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
     `h3])
   "."
   `invFun)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.explicit "@" `algHomAdjoinIntegralEquiv)
   [(Term.proj `x "." (fieldIdx "1"))
    (Term.hole "_")
    `E
    (Term.hole "_")
    (Term.hole "_")
    `s
    `K
    (Term.hole "_")
    (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
    `h3])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h3
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `algHomAdjoinIntegralEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `algHomAdjoinIntegralEquiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.explicit "@" `algHomAdjoinIntegralEquiv)
   [(Term.proj `x "." (fieldIdx "1"))
    (Term.hole "_")
    `E
    (Term.hole "_")
    (Term.hole "_")
    `s
    `K
    (Term.hole "_")
    (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
    `h3])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app
    (Term.explicit "@" `algHomEquivSigma)
    [`F
     (Term.proj `x "." (fieldIdx "1"))
     (Term.paren
      "("
      [(coeNotation
        "↑"
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         (Term.proj `x "." (fieldIdx "1"))
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯"))
       [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
      ")")
     `K
     (Term.hole "_")
     (Term.hole "_")
     (Term.hole "_")
     (Term.hole "_")
     (Term.hole "_")
     (Term.hole "_")
     (Term.hole "_")
     (Term.app
      `IntermediateField.algebra
      [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        (Term.proj `x "." (fieldIdx "1"))
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")])
     (Term.app
      `IsScalarTower.of_algebra_map_eq
      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])])
   "."
   `invFun)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.explicit "@" `algHomEquivSigma)
   [`F
    (Term.proj `x "." (fieldIdx "1"))
    (Term.paren
     "("
     [(coeNotation
       "↑"
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        (Term.proj `x "." (fieldIdx "1"))
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯"))
      [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
     ")")
    `K
    (Term.hole "_")
    (Term.hole "_")
    (Term.hole "_")
    (Term.hole "_")
    (Term.hole "_")
    (Term.hole "_")
    (Term.hole "_")
    (Term.app
     `IntermediateField.algebra
     [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       (Term.proj `x "." (fieldIdx "1"))
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])
    (Term.app
     `IsScalarTower.of_algebra_map_eq
     [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `IsScalarTower.of_algebra_map_eq
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IsScalarTower.of_algebra_map_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `IsScalarTower.of_algebra_map_eq
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl))])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `IntermediateField.algebra
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     (Term.proj `x "." (fieldIdx "1"))
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   (Term.proj `x "." (fieldIdx "1"))
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- Extend a lift `x : lifts F E K` to an element `s : E` whose conjugates are all in `K` -/ noncomputable
  def
    Lifts.liftOfSplits
    ( x : Lifts F E K ) { s : E } ( h1 : IsIntegral F s ) ( h2 : minpoly F s . Splits algebraMap F K ) : Lifts F E K
    :=
      let
        h3 : IsIntegral x . 1 s := is_integral_of_is_scalar_tower s h1
        let
          key
            : minpoly x . 1 s . Splits x . 2 . toRingHom
            :=
            splits_of_splits_of_dvd
              _
                map_ne_zero minpoly.ne_zero h1
                splits_map_iff _ _ . mpr by convert h2 exact RingHom.ext fun y => x . 2 . commutes y
                minpoly.dvd_map_of_is_scalar_tower _ _ _
          ⟨
            ↑ x . 1 ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
              ,
              @ algHomEquivSigma
                    F
                      x . 1
                      (
                        ↑ x . 1 ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                          : IntermediateField F E
                        )
                      K
                      _
                      _
                      _
                      _
                      _
                      _
                      _
                      IntermediateField.algebra
                        x . 1 ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                      IsScalarTower.of_algebra_map_eq fun _ => rfl
                  .
                  invFun
                ⟨
                  x . 2
                    ,
                    @ algHomAdjoinIntegralEquiv x . 1 _ E _ _ s K _ x . 2 . toRingHom . toAlgebra h3 . invFun
                      ⟨
                        rootOfSplits x . 2 . toRingHom key ne_of_gtₓ minpoly.degree_pos h3
                          ,
                          by
                            simp_rw [ mem_roots map_ne_zero minpoly.ne_zero h3 , is_root , ← eval₂_eq_eval_map ]
                              exact map_root_of_splits x . 2 . toRingHom key ne_of_gtₓ minpoly.degree_pos h3
                        ⟩
                  ⟩
            ⟩

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `Lifts.le_lifts_of_splits [])
  (Command.declSig
   [(Term.explicitBinder "(" [`x] [":" (Term.app `Lifts [`F `E `K])] [] ")")
    (Term.implicitBinder "{" [`s] [":" `E] "}")
    (Term.explicitBinder "(" [`h1] [":" (Term.app `IsIntegral [`F `s])] [] ")")
    (Term.explicitBinder
     "("
     [`h2]
     [":" (Term.app (Term.proj (Term.app `minpoly [`F `s]) "." `Splits) [(Term.app `algebraMap [`F `K])])]
     []
     ")")]
   (Term.typeSpec ":" («term_≤_» `x "≤" (Term.app (Term.proj `x "." `lift_of_splits) [`h1 `h2]))))
  (Command.declValSimple
   ":="
   (Term.anonymousCtor
    "⟨"
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`z `hz] [])]
       "=>"
       (Term.app
        `algebra_map_mem
        [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          (Term.proj `x "." (fieldIdx "1"))
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯")
         (Term.anonymousCtor "⟨" [`z "," `hz] "⟩")])))
     ","
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`t `u `htu] [])]
       "=>"
       (Term.app
        `Eq.symm
        [(Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule
                  ["←"]
                  (Term.show
                   "show"
                   («term_=_»
                    (Term.app
                     `algebraMap
                     [(Term.proj `x "." (fieldIdx "1"))
                      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                       (Term.proj `x "." (fieldIdx "1"))
                       "⟮"
                       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                       "⟯")
                      `t])
                    "="
                    `u)
                   (Term.fromTerm "from" (Term.app `Subtype.ext [`htu]))))]
                "]")
               [])
              [])
             (group
              (Tactic.tacticLet_
               "let"
               (Term.letDecl
                (Term.letPatDecl
                 (Lean.termThis "this")
                 []
                 [(Term.typeSpec ":" (Term.app `Algebra [(Term.proj `x "." (fieldIdx "1")) `K]))]
                 ":="
                 (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra))))
              [])
             (group (Tactic.exact "exact" (Term.app `AlgHom.commutes [(Term.hole "_") `t])) [])])))])))]
    "⟩")
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`z `hz] [])]
      "=>"
      (Term.app
       `algebra_map_mem
       [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         (Term.proj `x "." (fieldIdx "1"))
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        (Term.anonymousCtor "⟨" [`z "," `hz] "⟩")])))
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`t `u `htu] [])]
      "=>"
      (Term.app
       `Eq.symm
       [(Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 ["←"]
                 (Term.show
                  "show"
                  («term_=_»
                   (Term.app
                    `algebraMap
                    [(Term.proj `x "." (fieldIdx "1"))
                     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                      (Term.proj `x "." (fieldIdx "1"))
                      "⟮"
                      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                      "⟯")
                     `t])
                   "="
                   `u)
                  (Term.fromTerm "from" (Term.app `Subtype.ext [`htu]))))]
               "]")
              [])
             [])
            (group
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Lean.termThis "this")
                []
                [(Term.typeSpec ":" (Term.app `Algebra [(Term.proj `x "." (fieldIdx "1")) `K]))]
                ":="
                (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra))))
             [])
            (group (Tactic.exact "exact" (Term.app `AlgHom.commutes [(Term.hole "_") `t])) [])])))])))]
   "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`t `u `htu] [])]
    "=>"
    (Term.app
     `Eq.symm
     [(Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               ["←"]
               (Term.show
                "show"
                («term_=_»
                 (Term.app
                  `algebraMap
                  [(Term.proj `x "." (fieldIdx "1"))
                   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    (Term.proj `x "." (fieldIdx "1"))
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯")
                   `t])
                 "="
                 `u)
                (Term.fromTerm "from" (Term.app `Subtype.ext [`htu]))))]
             "]")
            [])
           [])
          (group
           (Tactic.tacticLet_
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Lean.termThis "this")
              []
              [(Term.typeSpec ":" (Term.app `Algebra [(Term.proj `x "." (fieldIdx "1")) `K]))]
              ":="
              (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra))))
           [])
          (group (Tactic.exact "exact" (Term.app `AlgHom.commutes [(Term.hole "_") `t])) [])])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Eq.symm
   [(Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule
             ["←"]
             (Term.show
              "show"
              («term_=_»
               (Term.app
                `algebraMap
                [(Term.proj `x "." (fieldIdx "1"))
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  (Term.proj `x "." (fieldIdx "1"))
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 `t])
               "="
               `u)
              (Term.fromTerm "from" (Term.app `Subtype.ext [`htu]))))]
           "]")
          [])
         [])
        (group
         (Tactic.tacticLet_
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Lean.termThis "this")
            []
            [(Term.typeSpec ":" (Term.app `Algebra [(Term.proj `x "." (fieldIdx "1")) `K]))]
            ":="
            (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra))))
         [])
        (group (Tactic.exact "exact" (Term.app `AlgHom.commutes [(Term.hole "_") `t])) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.show
            "show"
            («term_=_»
             (Term.app
              `algebraMap
              [(Term.proj `x "." (fieldIdx "1"))
               (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                (Term.proj `x "." (fieldIdx "1"))
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                "⟯")
               `t])
             "="
             `u)
            (Term.fromTerm "from" (Term.app `Subtype.ext [`htu]))))]
         "]")
        [])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Lean.termThis "this")
          []
          [(Term.typeSpec ":" (Term.app `Algebra [(Term.proj `x "." (fieldIdx "1")) `K]))]
          ":="
          (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra))))
       [])
      (group (Tactic.exact "exact" (Term.app `AlgHom.commutes [(Term.hole "_") `t])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `AlgHom.commutes [(Term.hole "_") `t]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `AlgHom.commutes [(Term.hole "_") `t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `AlgHom.commutes
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticLet_
   "let"
   (Term.letDecl
    (Term.letPatDecl
     (Lean.termThis "this")
     []
     [(Term.typeSpec ":" (Term.app `Algebra [(Term.proj `x "." (fieldIdx "1")) `K]))]
     ":="
     (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom) "." `toAlgebra)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj `x "." (fieldIdx "2")) "." `toRingHom)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Algebra [(Term.proj `x "." (fieldIdx "1")) `K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj `x "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Algebra
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Lean.termThis "this")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      ["←"]
      (Term.show
       "show"
       («term_=_»
        (Term.app
         `algebraMap
         [(Term.proj `x "." (fieldIdx "1"))
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           (Term.proj `x "." (fieldIdx "1"))
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")
          `t])
        "="
        `u)
       (Term.fromTerm "from" (Term.app `Subtype.ext [`htu]))))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   («term_=_»
    (Term.app
     `algebraMap
     [(Term.proj `x "." (fieldIdx "1"))
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       (Term.proj `x "." (fieldIdx "1"))
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      `t])
    "="
    `u)
   (Term.fromTerm "from" (Term.app `Subtype.ext [`htu])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Subtype.ext [`htu])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `htu
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Subtype.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app
    `algebraMap
    [(Term.proj `x "." (fieldIdx "1"))
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      (Term.proj `x "." (fieldIdx "1"))
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     `t])
   "="
   `u)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `u
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `algebraMap
   [(Term.proj `x "." (fieldIdx "1"))
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     (Term.proj `x "." (fieldIdx "1"))
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   (Term.proj `x "." (fieldIdx "1"))
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  Lifts.le_lifts_of_splits
  ( x : Lifts F E K ) { s : E } ( h1 : IsIntegral F s ) ( h2 : minpoly F s . Splits algebraMap F K )
    : x ≤ x . lift_of_splits h1 h2
  :=
    ⟨
      fun
          z hz
            =>
            algebra_map_mem
              x . 1 ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ ⟨ z , hz ⟩
        ,
        fun
          t u htu
            =>
            Eq.symm
              by
                rw
                    [
                      ←
                        show
                          algebraMap
                              x . 1
                                x . 1 ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                                t
                            =
                            u
                          from Subtype.ext htu
                      ]
                  let this : Algebra x . 1 K := x . 2 . toRingHom . toAlgebra
                  exact AlgHom.commutes _ t
      ⟩

theorem Lifts.mem_lifts_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : s ∈ (x.lift_of_splits h1 h2).1 :=
  mem_adjoin_simple_self x.1 s

theorem Lifts.exists_lift_of_splits (x : Lifts F E K) {s : E} (h1 : IsIntegral F s)
    (h2 : (minpoly F s).Splits (algebraMap F K)) : ∃ y, x ≤ y ∧ s ∈ y.1 :=
  ⟨x.lift_of_splits h1 h2, x.le_lifts_of_splits h1 h2, x.mem_lifts_of_splits h1 h2⟩

theorem alg_hom_mk_adjoin_splits (hK : ∀, ∀ s ∈ S, ∀, IsIntegral F (s : E) ∧ (minpoly F s).Splits (algebraMap F K)) :
    Nonempty (adjoin F S →ₐ[F] K) := by
  obtain ⟨x : lifts F E K, hx⟩ := zorn_partial_order lifts.exists_upper_bound
  refine'
    ⟨AlgHom.mk (fun s => x.2 ⟨s, adjoin_le_iff.mpr (fun s hs => _) s.Mem⟩) x.2.map_one
        (fun s t => x.2.map_mul ⟨s, _⟩ ⟨t, _⟩) x.2.map_zero (fun s t => x.2.map_add ⟨s, _⟩ ⟨t, _⟩) x.2.commutes⟩
  rcases x.exists_lift_of_splits (hK s hs).1 (hK s hs).2 with ⟨y, h1, h2⟩
  rwa [hx y h1] at h2

theorem alg_hom_mk_adjoin_splits' (hS : adjoin F S = ⊤)
    (hK : ∀, ∀ x ∈ S, ∀, IsIntegral F (x : E) ∧ (minpoly F x).Splits (algebraMap F K)) : Nonempty (E →ₐ[F] K) := by
  cases' alg_hom_mk_adjoin_splits hK with ϕ
  rw [hS] at ϕ
  exact ⟨ϕ.comp top_equiv.symm.to_alg_hom⟩

end AlgHomMkAdjoinSplits

section Supremum

theorem le_sup_to_subalgebra {K L : Type _} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L) :
    E1.toSubalgebra⊔E2.toSubalgebra ≤ (E1⊔E2).toSubalgebra :=
  sup_le (show E1 ≤ E1⊔E2 from le_sup_left) (show E2 ≤ E1⊔E2 from le_sup_right)

theorem sup_to_subalgebra {K L : Type _} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)
    [h1 : FiniteDimensional K E1] [h2 : FiniteDimensional K E2] :
    (E1⊔E2).toSubalgebra = E1.toSubalgebra⊔E2.toSubalgebra := by
  let S1 := E1.to_subalgebra
  let S2 := E2.to_subalgebra
  refine'
    le_antisymmₓ
      (show _ ≤ (S1⊔S2).toIntermediateField _ from
        sup_le (show S1 ≤ _ from le_sup_left) (show S2 ≤ _ from le_sup_right))
      (le_sup_to_subalgebra E1 E2)
  suffices IsField ↥(S1⊔S2) by
    intro x hx
    by_cases' hx' : (⟨x, hx⟩ : S1⊔S2) = 0
    · rw [← Subtype.coe_mk x hx, hx', Subalgebra.coe_zero, inv_zero]
      exact (S1⊔S2).zero_mem
      
    · obtain ⟨y, h⟩ := this.mul_inv_cancel hx'
      exact (congr_argₓ (· ∈ S1⊔S2) (eq_inv_of_mul_right_eq_one (subtype.ext_iff.mp h))).mp y.2
      
  exact
    is_field_of_is_integral_of_is_field'
      (is_integral_sup.mpr ⟨Algebra.is_integral_of_finite K E1, Algebra.is_integral_of_finite K E2⟩)
      (Field.to_is_field K)

theorem finite_dimensional_sup {K L : Type _} [Field K] [Field L] [Algebra K L] (E1 E2 : IntermediateField K L)
    [h1 : FiniteDimensional K E1] [h2 : FiniteDimensional K E2] : FiniteDimensional K ↥(E1⊔E2) := by
  let g := Algebra.TensorProduct.productMap E1.val E2.val
  suffices g.range = (E1⊔E2).toSubalgebra by
    have h : FiniteDimensional K g.range.to_submodule := g.to_linear_map.finite_dimensional_range
    rwa [this] at h
  rw [Algebra.TensorProduct.product_map_range, E1.range_val, E2.range_val, sup_to_subalgebra]

end Supremum

end IntermediateField

section PowerBasis

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

namespace PowerBasis

open IntermediateField

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" "`pb.equiv_adjoin_simple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `equivAdjoinSimple [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`pb] [":" (Term.app `PowerBasis [`K `L])] [] ")")]
   [(Term.typeSpec
     ":"
     (Algebra.Algebra.Basic.«term_≃ₐ[_]_»
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      " ≃ₐ["
      `K
      "] "
      `L))])
  (Command.declValSimple
   ":="
   (Term.app
    (Term.proj (Term.app `adjoin.powerBasis [(Term.proj `pb "." `is_integral_gen)]) "." `equivOfMinpoly)
    [`pb
     (Term.app
      `minpoly.eq_of_algebra_map_eq
      [(Term.proj
        (Term.app
         `algebraMap
         [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `K
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")
          `L])
        "."
        `Injective)
       (Term.proj (Term.app `adjoin.powerBasis [(Term.proj `pb "." `is_integral_gen)]) "." `is_integral_gen)
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `adjoin.power_basis_gen) "," (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
              "]")
             [])
            [])])))])])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `adjoin.powerBasis [(Term.proj `pb "." `is_integral_gen)]) "." `equivOfMinpoly)
   [`pb
    (Term.app
     `minpoly.eq_of_algebra_map_eq
     [(Term.proj
       (Term.app
        `algebraMap
        [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
          `K
          "⟮"
          (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
          "⟯")
         `L])
       "."
       `Injective)
      (Term.proj (Term.app `adjoin.powerBasis [(Term.proj `pb "." `is_integral_gen)]) "." `is_integral_gen)
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `adjoin.power_basis_gen) "," (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
             "]")
            [])
           [])])))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `minpoly.eq_of_algebra_map_eq
   [(Term.proj
     (Term.app
      `algebraMap
      [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       `L])
     "."
     `Injective)
    (Term.proj (Term.app `adjoin.powerBasis [(Term.proj `pb "." `is_integral_gen)]) "." `is_integral_gen)
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `adjoin.power_basis_gen) "," (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
           "]")
          [])
         [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `adjoin.power_basis_gen) "," (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `adjoin.power_basis_gen) "," (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin_simple.algebra_map_gen
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `adjoin.power_basis_gen
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `adjoin.power_basis_gen) "," (Tactic.rwRule [] `adjoin_simple.algebra_map_gen)]
         "]")
        [])
       [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `adjoin.powerBasis [(Term.proj `pb "." `is_integral_gen)]) "." `is_integral_gen)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `adjoin.powerBasis [(Term.proj `pb "." `is_integral_gen)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `pb "." `is_integral_gen)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `pb
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `adjoin.powerBasis
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `adjoin.powerBasis [(Term.proj `pb "." `is_integral_gen)]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj
   (Term.app
    `algebraMap
    [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `K
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯")
     `L])
   "."
   `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `algebraMap
   [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `L])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `L
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
/-- `pb.equiv_adjoin_simple` is the equivalence between `K⟮pb.gen⟯` and `L` itself. -/ noncomputable
  def
    equivAdjoinSimple
    ( pb : PowerBasis K L )
      : K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ ≃ₐ[ K ] L
    :=
      adjoin.powerBasis pb . is_integral_gen . equivOfMinpoly
        pb
          minpoly.eq_of_algebra_map_eq
            algebraMap K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ L . Injective
              adjoin.powerBasis pb . is_integral_gen . is_integral_gen
              by rw [ adjoin.power_basis_gen , adjoin_simple.algebra_map_gen ]

@[simp]
theorem equiv_adjoin_simple_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple (aeval (AdjoinSimple.gen K pb.gen) f) = aeval pb.gen f :=
  equiv_of_minpoly_aeval _ pb _ f

@[simp]
theorem equiv_adjoin_simple_gen (pb : PowerBasis K L) : pb.equivAdjoinSimple (AdjoinSimple.gen K pb.gen) = pb.gen :=
  equiv_of_minpoly_gen _ pb _

@[simp]
theorem equiv_adjoin_simple_symm_aeval (pb : PowerBasis K L) (f : K[X]) :
    pb.equivAdjoinSimple.symm (aeval pb.gen f) = aeval (AdjoinSimple.gen K pb.gen) f := by
  rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_aeval, adjoin.power_basis_gen]

@[simp]
theorem equiv_adjoin_simple_symm_gen (pb : PowerBasis K L) :
    pb.equivAdjoinSimple.symm pb.gen = AdjoinSimple.gen K pb.gen := by
  rw [equiv_adjoin_simple, equiv_of_minpoly_symm, equiv_of_minpoly_gen, adjoin.power_basis_gen]

end PowerBasis

end PowerBasis

