/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathbin.Data.Fin.Tuple.Basic

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions
* A `first_order.language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
* A `first_order.language.Structure` interprets the symbols of a given `first_order.language` in the
  context of a given type.
* A `first_order.language.hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
* A `first_order.language.embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.elementary_embedding`, denoted `M ↪ₑ[L] N`, is an embedding from the
  `L`-structure `M` to the `L`-structure `N` that commutes with the realizations of all formulas.
* A `first_order.language.equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.Lhom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
* `first_order.language.with_constants` is defined so that if `M` is an `L.Structure` and
  `A : set M`, `L.with_constants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v u' v' w

namespace FirstOrder

/-! ### Languages and Structures -/


/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
-- intended to be used with explicit universe parameters
@[nolint check_univs]
structure Language where
  Functions : ℕ → Type u
  Relations : ℕ → Type v

namespace Language

/-- The empty language has no symbols. -/
protected def empty : Language :=
  ⟨fun _ => Pempty, fun _ => Pempty⟩

instance : Inhabited Language :=
  ⟨Language.empty⟩

/-- The sum of two languages consists of the disjoint union of their symbols. -/
protected def sum (L : Language.{u, v}) (L' : Language.{u', v'}) : Language :=
  ⟨fun n => Sum (L.Functions n) (L'.Functions n), fun n => Sum (L.Relations n) (L'.Relations n)⟩

variable (L : Language.{u, v})

/-- The type of constants in a given language. -/
@[nolint has_inhabited_instance]
protected def Constants :=
  L.Functions 0

/-- The type of symbols in a given language. -/
@[nolint has_inhabited_instance]
def Symbols :=
  Sum (Σl, L.Functions l) (Σl, L.Relations l)

/-- A language is relational when it has no function symbols. -/
class IsRelational : Prop where
  empty_functions : ∀ n, IsEmpty (L.Functions n)

/-- A language is algebraic when it has no relation symbols. -/
class IsAlgebraic : Prop where
  empty_relations : ∀ n, IsEmpty (L.Relations n)

variable {L} {L' : Language.{u', v'}}

instance [L.IsRelational] {n : ℕ} : IsEmpty (L.Functions n) :=
  IsRelational.empty_functions n

instance [L.IsAlgebraic] {n : ℕ} : IsEmpty (L.Relations n) :=
  IsAlgebraic.empty_relations n

instance is_relational_of_empty_functions {symb : ℕ → Type _} : IsRelational ⟨fun _ => Pempty, symb⟩ :=
  ⟨fun _ => Pempty.is_empty⟩

instance is_algebraic_of_empty_relations {symb : ℕ → Type _} : IsAlgebraic ⟨symb, fun _ => Pempty⟩ :=
  ⟨fun _ => Pempty.is_empty⟩

instance is_relational_empty : IsRelational Language.empty :=
  language.is_relational_of_empty_functions

instance is_algebraic_empty : IsAlgebraic Language.empty :=
  language.is_algebraic_of_empty_relations

instance is_relational_sum [L.IsRelational] [L'.IsRelational] : IsRelational (L.Sum L') :=
  ⟨fun n => Sum.is_empty⟩

instance is_algebraic_sum [L.IsAlgebraic] [L'.IsAlgebraic] : IsAlgebraic (L.Sum L') :=
  ⟨fun n => Sum.is_empty⟩

variable (L) (M : Type w)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
class Structure where
  funMap : ∀ {n}, L.Functions n → (Finₓ n → M) → M
  RelMap : ∀ {n}, L.Relations n → (Finₓ n → M) → Prop

variable (N : Type _) [L.Structure M] [L.Structure N]

open Structure

/-! ### Maps -/


/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
structure Hom where
  toFun : M → N
  map_fun' : ∀ {n} f : L.Functions n x, to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} r : L.Relations n x, RelMap r x → RelMap r (to_fun ∘ x) := by
    run_tac
      obviously

-- mathport name: «expr →[ ] »
localized [FirstOrder] notation:25 A " →[" L "] " B => L.Hom A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
structure Embedding extends M ↪ N where
  map_fun' : ∀ {n} f : L.Functions n x, to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} r : L.Relations n x, RelMap r (to_fun ∘ x) ↔ RelMap r x := by
    run_tac
      obviously

-- mathport name: «expr ↪[ ] »
localized [FirstOrder] notation:25 A " ↪[" L "] " B => L.Embedding A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure Equiv extends M ≃ N where
  map_fun' : ∀ {n} f : L.Functions n x, to_fun (funMap f x) = funMap f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} r : L.Relations n x, RelMap r (to_fun ∘ x) ↔ RelMap r x := by
    run_tac
      obviously

-- mathport name: «expr ≃[ ] »
localized [FirstOrder] notation:25 A " ≃[" L "] " B => L.Equiv A B

variable {L M N} {P : Type _} [L.Structure P] {Q : Type _} [L.Structure Q]

instance : CoeTₓ L.Constants M :=
  ⟨fun c => funMap c default⟩

theorem fun_map_eq_coe_constants {c : L.Constants} {x : Finₓ 0 → M} : funMap c x = c :=
  congr rfl (funext Finₓ.elim0)

/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
theorem nonempty_of_nonempty_constants [h : Nonempty L.Constants] : Nonempty M :=
  h.map coe

namespace Hom

instance hasCoeToFun : CoeFun (M →[L] N) fun _ => M → N :=
  ⟨toFun⟩

@[simp]
theorem to_fun_eq_coe {f : M →[L] N} : f.toFun = (f : M → N) :=
  rfl

theorem coe_injective : @Function.Injective (M →[L] N) (M → N) coeFn
  | f, g, h => by
    cases f
    cases g
    cases h
    rfl

@[ext]
theorem ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

@[simp]
theorem map_fun (φ : M →[L] N) {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) : φ (funMap f x) = funMap f (φ ∘ x) :=
  φ.map_fun' f x

@[simp]
theorem map_constants (φ : M →[L] N) (c : L.Constants) : φ c = c :=
  (φ.map_fun c default).trans (congr rfl (funext default))

@[simp]
theorem map_rel (φ : M →[L] N) {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) : RelMap r x → RelMap r (φ ∘ x) :=
  φ.map_rel' r x

variable (L) (M)

/-- The identity map from a structure to itself -/
@[refl]
def id : M →[L] M where
  toFun := id

variable {L} {M}

instance : Inhabited (M →[L] M) :=
  ⟨id L M⟩

@[simp]
theorem id_apply (x : M) : id L M x = x :=
  rfl

/-- Composition of first-order homomorphisms -/
@[trans]
def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P where
  toFun := hnp ∘ hmn
  map_rel' := fun _ _ _ h => by
    simp [h]

@[simp]
theorem comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end Hom

namespace Embedding

instance hasCoeToFun : CoeFun (M ↪[L] N) fun _ => M → N :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) : φ (funMap f x) = funMap f (φ ∘ x) :=
  φ.map_fun' f x

@[simp]
theorem map_constants (φ : M ↪[L] N) (c : L.Constants) : φ c = c :=
  (φ.map_fun c default).trans (congr rfl (funext default))

@[simp]
theorem map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) : RelMap r (φ ∘ x) ↔ RelMap r x :=
  φ.map_rel' r x

/-- A first-order embedding is also a first-order homomorphism. -/
def toHom (f : M ↪[L] N) : M →[L] N where
  toFun := f

@[simp]
theorem coe_to_hom {f : M ↪[L] N} : (f.toHom : M → N) = f :=
  rfl

theorem coe_injective : @Function.Injective (M ↪[L] N) (M → N) coeFn
  | f, g, h => by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iffₓ.1 h x

@[ext]
theorem ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

theorem injective (f : M ↪[L] N) : Function.Injective f :=
  f.toEmbedding.Injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps]
def ofInjective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : M ↪[L] N :=
  { f with inj' := hf, map_rel' := fun n => (IsAlgebraic.empty_relations n).elim }

@[simp]
theorem coe_fn_of_injective [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : (ofInjective hf : M → N) = f :=
  rfl

@[simp]
theorem of_injective_to_hom [L.IsAlgebraic] {f : M →[L] N} (hf : Function.Injective f) : (ofInjective hf).toHom = f :=
  by
  ext
  simp

variable (L) (M)

/-- The identity embedding from a structure to itself -/
@[refl]
def refl : M ↪[L] M where
  toEmbedding := Function.Embedding.refl M

variable {L} {M}

instance : Inhabited (M ↪[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of first-order embeddings -/
@[trans]
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P where
  toFun := hnp ∘ hmn
  inj' := hnp.Injective.comp hmn.Injective

@[simp]
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order embeddings is associative. -/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem comp_to_hom (hnp : N ↪[L] P) (hmn : M ↪[L] N) : (hnp.comp hmn).toHom = hnp.toHom.comp hmn.toHom := by
  ext
  simp only [coe_to_hom, comp_apply, hom.comp_apply]

end Embedding

namespace Equivₓ

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
def symm (f : M ≃[L] N) : N ≃[L] M :=
  { f.toEquiv.symm with
    map_fun' := fun n f' x => by
      simp only [Equivₓ.to_fun_as_coe]
      rw [Equivₓ.symm_apply_eq]
      refine' Eq.trans _ (f.map_fun' f' (f.to_equiv.symm ∘ x)).symm
      rw [← Function.comp.assoc, Equivₓ.to_fun_as_coe, Equivₓ.self_comp_symm, Function.comp.left_id],
    map_rel' := fun n r x => by
      simp only [Equivₓ.to_fun_as_coe]
      refine' (f.map_rel' r (f.to_equiv.symm ∘ x)).symm.trans _
      rw [← Function.comp.assoc, Equivₓ.to_fun_as_coe, Equivₓ.self_comp_symm, Function.comp.left_id] }

instance hasCoeToFun : CoeFun (M ≃[L] N) fun _ => M → N :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a :=
  f.toEquiv.apply_symm_apply a

@[simp]
theorem symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a :=
  f.toEquiv.symm_apply_apply a

@[simp]
theorem map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) : φ (funMap f x) = funMap f (φ ∘ x) :=
  φ.map_fun' f x

@[simp]
theorem map_constants (φ : M ≃[L] N) (c : L.Constants) : φ c = c :=
  (φ.map_fun c default).trans (congr rfl (funext default))

@[simp]
theorem map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) : RelMap r (φ ∘ x) ↔ RelMap r x :=
  φ.map_rel' r x

/-- A first-order equivalence is also a first-order embedding. -/
def toEmbedding (f : M ≃[L] N) : M ↪[L] N where
  toFun := f
  inj' := f.toEquiv.Injective

/-- A first-order equivalence is also a first-order homomorphism. -/
def toHom (f : M ≃[L] N) : M →[L] N where
  toFun := f

@[simp]
theorem to_embedding_to_hom (f : M ≃[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl

@[simp]
theorem coe_to_hom {f : M ≃[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl

@[simp]
theorem coe_to_embedding (f : M ≃[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl

theorem coe_injective : @Function.Injective (M ≃[L] N) (M → N) coeFn
  | f, g, h => by
    cases f
    cases g
    simp only
    ext x
    exact Function.funext_iffₓ.1 h x

@[ext]
theorem ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

theorem injective (f : M ≃[L] N) : Function.Injective f :=
  f.toEmbedding.Injective

variable (L) (M)

/-- The identity equivalence from a structure to itself -/
@[refl]
def refl : M ≃[L] M where
  toEquiv := Equivₓ.refl M

variable {L} {M}

instance : Inhabited (M ≃[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl

/-- Composition of first-order equivalences -/
@[trans]
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
  { hmn.toEquiv.trans hnp.toEquiv with toFun := hnp ∘ hmn }

@[simp]
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end Equivₓ

section SumStructure

variable (L₁ L₂ : Language) (S : Type _) [L₁.Structure S] [L₂.Structure S]

instance sumStructure : (L₁.Sum L₂).Structure S where
  funMap := fun n => Sum.elim funMap funMap
  RelMap := fun n => Sum.elim RelMap RelMap

variable {L₁ L₂ S}

@[simp]
theorem fun_map_sum_inl {n : ℕ} (f : L₁.Functions n) : @funMap (L₁.Sum L₂) S _ n (Sum.inl f) = funMap f :=
  rfl

@[simp]
theorem fun_map_sum_inr {n : ℕ} (f : L₂.Functions n) : @funMap (L₁.Sum L₂) S _ n (Sum.inr f) = funMap f :=
  rfl

@[simp]
theorem rel_map_sum_inl {n : ℕ} (R : L₁.Relations n) : @RelMap (L₁.Sum L₂) S _ n (Sum.inl R) = RelMap R :=
  rfl

@[simp]
theorem rel_map_sum_inr {n : ℕ} (R : L₂.Relations n) : @RelMap (L₁.Sum L₂) S _ n (Sum.inr R) = RelMap R :=
  rfl

end SumStructure

/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure Lhom (L L' : Language) where
  onFunction : ∀ {n}, L.Functions n → L'.Functions n
  onRelation : ∀ {n}, L.Relations n → L'.Relations n

-- mathport name: «expr →ᴸ »
infixl:10 " →ᴸ " => Lhom

-- \^L
namespace Lhom

variable (ϕ : L →ᴸ L')

/-- The identity language homomorphism. -/
protected def id (L : Language) : L →ᴸ L :=
  ⟨fun n => id, fun n => id⟩

instance : Inhabited (L →ᴸ L) :=
  ⟨Lhom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
protected def sumInl : L →ᴸ L.Sum L' :=
  ⟨fun n => Sum.inl, fun n => Sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
protected def sumInr : L' →ᴸ L.Sum L' :=
  ⟨fun n => Sum.inr, fun n => Sum.inr⟩

variable (L L')

/-- The inclusion of an empty language into any other language. -/
protected def ofIsEmpty [L.IsAlgebraic] [L.IsRelational] : L →ᴸ L' :=
  ⟨fun n => (IsRelational.empty_functions n).elim, fun n => (IsAlgebraic.empty_relations n).elim⟩

variable {L L'}

/-- The composition of two language homomorphisms. -/
@[reducible]
def comp {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) : L1 →ᴸ L3 :=
  ⟨fun n F => g.1 (f.1 F), fun _ R => g.2 (f.2 R)⟩

@[ext]
protected theorem funext {L1} {L2} {F G : L1 →ᴸ L2} (h_fun : F.onFunction = G.onFunction)
    (h_rel : F.onRelation = G.onRelation) : F = G := by
  cases' F with Ff Fr
  cases' G with Gf Gr
  simp only [*]
  exact And.intro h_fun h_rel

-- mathport name: «expr ∘ »
local infixl:60 " ∘ " => Lhom.comp

@[simp]
theorem id_comp {L1 L2} {F : L1 →ᴸ L2} : Lhom.id L2 ∘ F = F := by
  cases F
  rfl

@[simp]
theorem comp_id {L1 L2} {F : L1 →ᴸ L2} : F ∘ Lhom.id L1 = F := by
  cases F
  rfl

/-- A language map defined on two factors of a sum. -/
@[simps]
def sumElim {L'' : Language} (ψ : L'' →ᴸ L') : L.Sum L'' →ᴸ L' where
  onFunction := fun n => Sum.elim (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation := fun n => Sum.elim (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps]
def sumMap {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂) : L.Sum L₁ →ᴸ L'.Sum L₂ where
  onFunction := fun n => Sum.map (fun f => ϕ.onFunction f) fun f => ψ.onFunction f
  onRelation := fun n => Sum.map (fun f => ϕ.onRelation f) fun f => ψ.onRelation f

/-- A language homomorphism is injective when all the maps between symbol types are. -/
protected structure Injective : Prop where
  onFunction {n} : Function.Injective (onFunction ϕ : L.Functions n → L'.Functions n)
  onRelation {n} : Function.Injective (onRelation ϕ : L.Relations n → L'.Relations n)

/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
class IsExpansionOn (M : Type _) [L.Structure M] [L'.Structure M] : Prop where
  map_on_function : ∀ {n} f : L.Functions n x : Finₓ n → M, funMap (ϕ.onFunction f) x = funMap f x
  map_on_relation : ∀ {n} R : L.Relations n x : Finₓ n → M, RelMap (ϕ.onRelation R) x = RelMap R x

attribute [simp] is_expansion_on.map_on_function is_expansion_on.map_on_relation

instance id_is_expansion_on (M : Type _) [L.Structure M] : IsExpansionOn (Lhom.id L) M :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

instance of_is_empty_is_expansion_on (M : Type _) [L.Structure M] [L'.Structure M] [L.IsAlgebraic] [L.IsRelational] :
    IsExpansionOn (Lhom.ofIsEmpty L L') M :=
  ⟨fun n => (IsRelational.empty_functions n).elim, fun n => (IsAlgebraic.empty_relations n).elim⟩

instance sum_elim_is_expansion_on {L'' : Language} (ψ : L'' →ᴸ L') (M : Type _) [L.Structure M] [L'.Structure M]
    [L''.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] : (ϕ.sum_elim ψ).IsExpansionOn M :=
  ⟨fun _ f _ =>
    Sum.casesOn f
      (by
        simp )
      (by
        simp ),
    fun _ R _ =>
    Sum.casesOn R
      (by
        simp )
      (by
        simp )⟩

instance sum_map_is_expansion_on {L₁ L₂ : Language} (ψ : L₁ →ᴸ L₂) (M : Type _) [L.Structure M] [L'.Structure M]
    [L₁.Structure M] [L₂.Structure M] [ϕ.IsExpansionOn M] [ψ.IsExpansionOn M] : (ϕ.sum_map ψ).IsExpansionOn M :=
  ⟨fun _ f _ =>
    Sum.casesOn f
      (by
        simp )
      (by
        simp ),
    fun _ R _ =>
    Sum.casesOn R
      (by
        simp )
      (by
        simp )⟩

end Lhom

section ConstantsOn

variable (α : Type u')

/-- The function symbols of a language with constants indexed by a type. -/
def ConstantsOnFunctions : ℕ → Type u'
  | 0 => α
  | _ => Pempty

instance [h : Inhabited α] : Inhabited (ConstantsOnFunctions α 0) :=
  h

/-- A language with constants indexed by a type. -/
def constantsOn : Language.{u', 0} :=
  ⟨ConstantsOnFunctions α, fun _ => Pempty⟩

variable {α}

@[simp]
theorem constants_on_constants : (constantsOn α).Constants = α :=
  rfl

instance is_algebraic_constants_on : IsAlgebraic (constantsOn α) :=
  language.is_algebraic_of_empty_relations

instance is_relational_constants_on [ie : IsEmpty α] : IsRelational (constantsOn α) :=
  ⟨fun n => Nat.casesOn n ie fun _ => Pempty.is_empty⟩

/-- Gives a `constants_on α` structure to a type by assigning each constant a value. -/
def constantsOn.structure (f : α → M) : (constantsOn α).Structure M where
  funMap := fun n => Nat.casesOn n (fun a _ => f a) fun _ => Pempty.elimₓ
  RelMap := fun _ => Pempty.elimₓ

variable {β : Type v'}

/-- A map between index types induces a map between constant languages. -/
def Lhom.constantsOnMap (f : α → β) : constantsOn α →ᴸ constantsOn β :=
  ⟨fun n => Nat.casesOn n f fun _ => Pempty.elimₓ, fun n => Pempty.elimₓ⟩

theorem constants_on_map_is_expansion_on {f : α → β} {fα : α → M} {fβ : β → M} (h : fβ ∘ f = fα) :
    @Lhom.IsExpansionOn _ _ (Lhom.constantsOnMap f) M (constantsOn.structure fα) (constantsOn.structure fβ) := by
  let this' := constants_on.Structure fα
  let this' := constants_on.Structure fβ
  exact ⟨fun n => Nat.casesOn n (fun F x => (congr_funₓ h F : _)) fun n F => Pempty.elimₓ F, fun _ R => Pempty.elimₓ R⟩

end ConstantsOn

section WithConstants

variable (L)

section

variable (α : Type w)

/-- Extends a language with a constant for each element of a parameter set in `M`. -/
def withConstants : Language.{max u w, v} :=
  L.Sum (constantsOn α)

-- mathport name: «expr [[ ]]»
localized [FirstOrder] notation:95 L "[[" α "]]" => L.withConstants α

/-- The language map adding constants.  -/
def lhomWithConstants : L →ᴸ L[[α]] :=
  Lhom.sum_inl

variable {L}

/-- Adds constants to a language map.  -/
def Lhom.addConstants {L' : Language} (φ : L →ᴸ L') : L[[α]] →ᴸ L'[[α]] :=
  φ.sum_map (Lhom.id _)

instance paramsStructure (A : Set α) : (constantsOn A).Structure α :=
  constantsOn.structure coe

variable (L) (α)

/-- The language map removing an empty constant set.  -/
def lhomTrimEmptyConstants [IsEmpty α] : L[[α]] →ᴸ L :=
  Lhom.sumElim (Lhom.id L) (Lhom.ofIsEmpty (constantsOn α) L)

variable {α} {β : Type _}

/-- The language map extending the constant set.  -/
def lhomWithConstantsMap (f : α → β) : L[[α]] →ᴸ L[[β]] :=
  Lhom.sumMap (Lhom.id L) (Lhom.constantsOnMap f)

@[simp]
theorem Lhom.map_constants_comp_with_constants {f : α → β} :
    (L.lhomWithConstantsMap f).comp (L.lhomWithConstants α) = L.lhomWithConstants β := by
  ext n f R <;> rfl

end

open_locale FirstOrder

variable (A : Set M)

instance withConstantsStructure : L[[A]].Structure M :=
  Language.sumStructure _ _ _

instance trim_empty_constants_is_expansion_on : (L.lhomTrimEmptyConstants (∅ : Set M)).IsExpansionOn M :=
  Lhom.sum_elim_is_expansion_on _ _ _

instance with_constants_expansion : (L.lhomWithConstants A).IsExpansionOn M :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

instance add_constants_expansion {L' : Language} [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    (φ.addConstants A).IsExpansionOn M :=
  Lhom.sum_map_is_expansion_on _ _ M

variable {A} {B : Set M} (h : A ⊆ B)

instance constants_on_map_inclusion_is_expansion_on : (Lhom.constantsOnMap (Set.inclusion h)).IsExpansionOn M :=
  constants_on_map_is_expansion_on rfl

instance map_constants_inclusion_is_expansion_on : (L.lhomWithConstantsMap (Set.inclusion h)).IsExpansionOn M :=
  Lhom.sum_map_is_expansion_on _ _ _

end WithConstants

end Language

end FirstOrder

