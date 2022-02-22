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

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v

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

/-- The type of constants in a given language. -/
@[nolint has_inhabited_instance]
def Const (L : Language) :=
  L.Functions 0

variable (L : Language.{u, v})

/-- A language is relational when it has no function symbols. -/
class IsRelational : Prop where
  empty_functions : ∀ n, L.Functions n → False

/-- A language is algebraic when it has no relation symbols. -/
class IsAlgebraic : Prop where
  empty_relations : ∀ n, L.Relations n → False

variable {L}

instance is_relational_of_empty_functions {symb : ℕ → Type _} : IsRelational ⟨fun _ => Pempty, symb⟩ :=
  ⟨by
    intro n
    apply Pempty.elimₓ⟩

instance is_algebraic_of_empty_relations {symb : ℕ → Type _} : IsAlgebraic ⟨symb, fun _ => Pempty⟩ :=
  ⟨by
    intro n
    apply Pempty.elimₓ⟩

instance is_relational_empty : IsRelational Language.empty :=
  language.is_relational_of_empty_functions

instance is_algebraic_empty : IsAlgebraic Language.empty :=
  language.is_algebraic_of_empty_relations

variable (L) (M : Type _)

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

instance : CoeTₓ L.const M :=
  ⟨fun c => funMap c Finₓ.elim0⟩

theorem fun_map_eq_coe_const {c : L.const} {x : Finₓ 0 → M} : funMap c x = c :=
  congr rfl (funext Finₓ.elim0)

/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
theorem nonempty_of_nonempty_constants [h : Nonempty L.const] : Nonempty M :=
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
theorem map_const (φ : M →[L] N) (c : L.const) : φ c = c :=
  (φ.map_fun c Finₓ.elim0).trans (congr rfl (funext Finₓ.elim0))

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
theorem map_const (φ : M ↪[L] N) (c : L.const) : φ c = c :=
  (φ.map_fun c Finₓ.elim0).trans (congr rfl (funext Finₓ.elim0))

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
  { f with inj' := hf, map_rel' := fun n r => (IsAlgebraic.empty_relations n r).elim }

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
theorem map_const (φ : M ≃[L] N) (c : L.const) : φ c = c :=
  (φ.map_fun c Finₓ.elim0).trans (congr rfl (funext Finₓ.elim0))

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

end Language

end FirstOrder

