/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.ModelTheory.Substructures
import Mathbin.ModelTheory.TermsAndFormulas

/-!
# Elementary Maps Between First-Order Structures

## Main Definitions
* A `first_order.language.elementary_embedding` is an embedding that commutes with the
  realizations of formulas.
* A `first_order.language.elementary_substructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

  -/


open_locale FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable (L : Language) (M : Type _) (N : Type _) {P : Type _} {Q : Type _}

variable [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

/-- An elementary embedding of first-order structures is an embedding that commutes with the
  realizations of formulas. -/
structure ElementaryEmbedding where
  toFun : M → N
  map_formula' : ∀ {n} φ : L.Formula (Finₓ n) x : Finₓ n → M, φ.realize (to_fun ∘ x) ↔ φ.realize x := by
    run_tac
      obviously

-- mathport name: «expr ↪ₑ[ ] »
localized [FirstOrder] notation:25 A " ↪ₑ[" L "] " B => L.ElementaryEmbedding A B

variable {L} {M} {N}

namespace ElementaryEmbedding

instance hasCoeToFun : CoeFun (M ↪ₑ[L] N) fun _ => M → N :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem map_formula (f : M ↪ₑ[L] N) {α : Type} [Fintype α] (φ : L.Formula α) (x : α → M) :
    φ.realize (f ∘ x) ↔ φ.realize x := by
  have g := Fintype.equivFin α
  have h := f.map_formula' (φ.relabel g) (x ∘ g.symm)
  rw [formula.realize_relabel, formula.realize_relabel, Function.comp.assoc x g.symm g, g.symm_comp_self,
    Function.comp.right_id] at h
  rw [← h, iff_eq_eq]
  congr
  ext y
  simp

@[simp]
theorem map_fun (φ : M ↪ₑ[L] N) {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) : φ (funMap f x) = funMap f (φ ∘ x) := by
  have h := φ.map_formula (formula.graph f) (Finₓ.cons (fun_map f x) x)
  rw [formula.realize_graph, Finₓ.comp_cons, formula.realize_graph] at h
  rw [eq_comm, h]

@[simp]
theorem map_constants (φ : M ↪ₑ[L] N) (c : L.Constants) : φ c = c :=
  (φ.map_fun c default).trans fun_map_eq_coe_constants

@[simp]
theorem map_rel (φ : M ↪ₑ[L] N) {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) : RelMap r (φ ∘ x) ↔ RelMap r x :=
  have h := φ.map_formula (r.formula var) x
  h

@[simp]
theorem injective (φ : M ↪ₑ[L] N) : Function.Injective φ := by
  intro x y
  have h := φ.map_formula ((var 0).equal (var 1) : L.formula (Finₓ 2)) fun i => if i = 0 then x else y
  rw [formula.realize_equal, formula.realize_equal] at h
  simp only [Nat.one_ne_zero, term.realize, Finₓ.one_eq_zero_iff, if_true, eq_self_iff_true, Function.comp_app,
    if_false] at h
  exact h.1

/-- An elementary embedding is also a first-order embedding. -/
def toEmbedding (f : M ↪ₑ[L] N) : M ↪[L] N where
  toFun := f
  inj' := f.Injective

/-- An elementary embedding is also a first-order homomorphism. -/
def toHom (f : M ↪ₑ[L] N) : M →[L] N where
  toFun := f

@[simp]
theorem to_embedding_to_hom (f : M ↪ₑ[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
theorem coe_to_hom {f : M ↪ₑ[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl

@[simp]
theorem coe_to_embedding (f : M ↪ₑ[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl

theorem coe_injective : @Function.Injective (M ↪ₑ[L] N) (M → N) coeFn
  | f, g, h => by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iffₓ.1 h x

@[ext]
theorem ext ⦃f g : M ↪ₑ[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {f g : M ↪ₑ[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

variable (L) (M)

/-- The identity elementary embedding from a structure to itself -/
@[refl]
def refl : M ↪ₑ[L] M where
  toFun := id

variable {L} {M}

instance : Inhabited (M ↪ₑ[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of elementary embeddings -/
@[trans]
def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where
  toFun := hnp ∘ hmn

@[simp]
theorem comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of elementary embeddings is associative. -/
theorem comp_assoc (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end ElementaryEmbedding

namespace Equivₓ

/-- A first-order equivalence is also an elementary embedding. -/
def toElementaryEmbedding (f : M ≃[L] N) : M ↪ₑ[L] N where
  toFun := f

@[simp]
theorem to_elementary_embedding_to_embedding (f : M ≃[L] N) : f.toElementaryEmbedding.toEmbedding = f.toEmbedding :=
  rfl

@[simp]
theorem coe_to_elementary_embedding (f : M ≃[L] N) : (f.toElementaryEmbedding : M → N) = (f : M → N) :=
  rfl

end Equivₓ

@[simp]
theorem realize_term_substructure {α : Type _} {S : L.Substructure M} (v : α → S) (t : L.Term α) :
    t.realize (coe ∘ v) = (↑(t.realize v) : M) :=
  S.Subtype.realize_term t

namespace Substructure

@[simp]
theorem realize_bounded_formula_top {α : Type _} {n : ℕ} {φ : L.BoundedFormula α n} {v : α → (⊤ : L.Substructure M)}
    {xs : Finₓ n → (⊤ : L.Substructure M)} : φ.realize v xs ↔ φ.realize ((coe : _ → M) ∘ v) (coe ∘ xs) := by
  rw [← substructure.top_equiv.realize_bounded_formula φ]
  simp

@[simp]
theorem realize_formula_top {α : Type _} {φ : L.Formula α} {v : α → (⊤ : L.Substructure M)} :
    φ.realize v ↔ φ.realize ((coe : (⊤ : L.Substructure M) → M) ∘ v) := by
  rw [← substructure.top_equiv.realize_formula φ]
  simp

/-- A substructure is elementary when every formula applied to a tuple in the subtructure
  agrees with its value in the overall structure. -/
def IsElementary (S : L.Substructure M) : Prop :=
  ∀ {n} φ : L.Formula (Finₓ n) x : Finₓ n → S, φ.realize ((coe : _ → M) ∘ x) ↔ φ.realize x

end Substructure

variable (L) (M)

/-- An elementary substructure is one in which every formula applied to a tuple in the subtructure
  agrees with its value in the overall structure. -/
structure ElementarySubstructure where
  toSubstructure : L.Substructure M
  is_elementary' : to_substructure.IsElementary

variable {L} {M}

namespace ElementarySubstructure

instance : Coe (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨ElementarySubstructure.toSubstructure⟩

instance : SetLike (L.ElementarySubstructure M) M :=
  ⟨fun x => x.toSubstructure.Carrier, fun h => by
    congr
    exact h⟩

@[simp]
theorem is_elementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary :=
  S.is_elementary'

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where
  toFun := coe
  map_formula' := fun n => S.IsElementary

@[simp]
theorem coe_subtype {S : L.ElementarySubstructure M} : ⇑S.Subtype = coe :=
  rfl

/-- The substructure `M` of the structure `M` is elementary. -/
instance : HasTop (L.ElementarySubstructure M) :=
  ⟨⟨⊤, fun n φ x => Substructure.realize_formula_top.symm⟩⟩

instance : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.ElementarySubstructure M) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.ElementarySubstructure M) : Set M) = Set.Univ :=
  rfl

end ElementarySubstructure

end Language

end FirstOrder

