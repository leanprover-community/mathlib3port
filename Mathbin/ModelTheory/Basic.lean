import Mathbin.Data.Nat.Basic
import Mathbin.Data.SetLike.Basic
import Mathbin.Data.Set.Lattice
import Mathbin.Order.Closure

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/).

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

/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint check_univs]
structure language where
  Functions : ℕ → Type u
  Relations : ℕ → Type v

namespace Language

/-- The empty language has no symbols. -/
def Empty : language :=
  ⟨fun _ => Pempty, fun _ => Pempty⟩

instance : Inhabited language :=
  ⟨Empty⟩

/-- The type of constants in a given language. -/
@[nolint has_inhabited_instance]
def const (L : language) :=
  L.functions 0

variable (L : language)

/-- A language is relational when it has no function symbols. -/
class is_relational : Prop where
  empty_functions : ∀ n, L.functions n → False

/-- A language is algebraic when it has no relation symbols. -/
class is_algebraic : Prop where
  empty_relations : ∀ n, L.relations n → False

variable {L}

instance is_relational_of_empty_functions {symb : ℕ → Type _} : is_relational ⟨fun _ => Pempty, symb⟩ :=
  ⟨by
    intro n
    apply Pempty.elimₓ⟩

instance is_algebraic_of_empty_relations {symb : ℕ → Type _} : is_algebraic ⟨symb, fun _ => Pempty⟩ :=
  ⟨by
    intro n
    apply Pempty.elimₓ⟩

instance is_relational_empty : is_relational Empty :=
  language.is_relational_of_empty_functions

instance is_algebraic_empty : is_algebraic Empty :=
  language.is_algebraic_of_empty_relations

variable (L) (M : Type _)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
class Structure where
  funMap : ∀ {n}, L.functions n → (Finₓ n → M) → M
  RelMap : ∀ {n}, L.relations n → (Finₓ n → M) → Prop

variable (N : Type _) [L.Structure M] [L.Structure N]

open FirstOrder.Language.Structure

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
protected structure hom where
  toFun : M → N
  map_fun' : ∀ {n} f : L.functions n x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} r : L.relations n x, rel_map r x → rel_map r (to_fun ∘ x) := by
    run_tac
      obviously

localized [FirstOrder] notation:25 A " →[" L "] " B => L.hom A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
protected structure embedding extends M ↪ N where
  map_fun' : ∀ {n} f : L.functions n x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} r : L.relations n x, rel_map r (to_fun ∘ x) ↔ rel_map r x := by
    run_tac
      obviously

localized [FirstOrder] notation:25 A " ↪[" L "] " B => L.embedding A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
protected structure Equivₓ extends M ≃ N where
  map_fun' : ∀ {n} f : L.functions n x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) := by
    run_tac
      obviously
  map_rel' : ∀ {n} r : L.relations n x, rel_map r (to_fun ∘ x) ↔ rel_map r x := by
    run_tac
      obviously

localized [FirstOrder] notation:25 A " ≃[" L "] " B => L.equiv A B

variable {L M N} {P : Type _} [L.Structure P] {Q : Type _} [L.Structure Q]

instance : CoeTₓ L.const M :=
  ⟨fun c => fun_map c Finₓ.elim0⟩

theorem fun_map_eq_coe_const {c : L.const} {x : Finₓ 0 → M} : fun_map c x = c :=
  congr rfl (funext Finₓ.elim0)

namespace Hom

@[simps]
instance CoeFun : CoeFun (M →[L] N) fun _ => M → N :=
  ⟨to_fun⟩

@[simp]
theorem to_fun_eq_coe {f : M →[L] N} : f.to_fun = (f : M → N) :=
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
theorem map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) (x : Finₓ n → M) : φ (fun_map f x) = fun_map f (φ ∘ x) :=
  φ.map_fun' f x

@[simp]
theorem map_const (φ : M →[L] N) (c : L.const) : φ c = c :=
  (φ.map_fun c Finₓ.elim0).trans (congr rfl (funext Finₓ.elim0))

@[simp]
theorem map_rel (φ : M →[L] N) {n : ℕ} (r : L.relations n) (x : Finₓ n → M) : rel_map r x → rel_map r (φ ∘ x) :=
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

@[simps]
instance CoeFun : CoeFun (M ↪[L] N) fun _ => M → N :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.functions n) (x : Finₓ n → M) : φ (fun_map f x) = fun_map f (φ ∘ x) :=
  φ.map_fun' f x

@[simp]
theorem map_const (φ : M ↪[L] N) (c : L.const) : φ c = c :=
  (φ.map_fun c Finₓ.elim0).trans (congr rfl (funext Finₓ.elim0))

@[simp]
theorem map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.relations n) (x : Finₓ n → M) : rel_map r (φ ∘ x) ↔ rel_map r x :=
  φ.map_rel' r x

/-- A first-order embedding is also a first-order homomorphism. -/
def to_hom (f : M ↪[L] N) : M →[L] N where
  toFun := f

@[simp]
theorem coe_to_hom {f : M ↪[L] N} : (f.to_hom : M → N) = f :=
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
  f.to_embedding.injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps]
def of_injective [L.is_algebraic] {f : M →[L] N} (hf : Function.Injective f) : M ↪[L] N :=
  { f with inj' := hf, map_rel' := fun n r => (is_algebraic.empty_relations n r).elim }

@[simp]
theorem coe_fn_of_injective [L.is_algebraic] {f : M →[L] N} (hf : Function.Injective f) :
    (of_injective hf : M → N) = f :=
  rfl

@[simp]
theorem of_injective_to_hom [L.is_algebraic] {f : M →[L] N} (hf : Function.Injective f) : (of_injective hf).toHom = f :=
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
  inj' := hnp.injective.comp hmn.injective

@[simp]
theorem comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order embeddings is associative. -/
theorem comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end Embedding

namespace Equivₓ

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm]
def symm (f : M ≃[L] N) : N ≃[L] M :=
  { f.to_equiv.symm with
    map_fun' := fun n f' x => by
      simp only [Equivₓ.to_fun_as_coe]
      rw [Equivₓ.symm_apply_eq]
      refine' Eq.trans _ (f.map_fun' f' (f.to_equiv.symm ∘ x)).symm
      rw [← Function.comp.assoc, Equivₓ.to_fun_as_coe, Equivₓ.self_comp_symm, Function.comp.left_id],
    map_rel' := fun n r x => by
      simp only [Equivₓ.to_fun_as_coe]
      refine' (f.map_rel' r (f.to_equiv.symm ∘ x)).symm.trans _
      rw [← Function.comp.assoc, Equivₓ.to_fun_as_coe, Equivₓ.self_comp_symm, Function.comp.left_id] }

@[simps]
instance CoeFun : CoeFun (M ≃[L] N) fun _ => M → N :=
  ⟨fun f => f.to_fun⟩

@[simp]
theorem map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.functions n) (x : Finₓ n → M) : φ (fun_map f x) = fun_map f (φ ∘ x) :=
  φ.map_fun' f x

@[simp]
theorem map_const (φ : M ≃[L] N) (c : L.const) : φ c = c :=
  (φ.map_fun c Finₓ.elim0).trans (congr rfl (funext Finₓ.elim0))

@[simp]
theorem map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.relations n) (x : Finₓ n → M) : rel_map r (φ ∘ x) ↔ rel_map r x :=
  φ.map_rel' r x

/-- A first-order equivalence is also a first-order embedding. -/
def to_embedding (f : M ≃[L] N) : M ↪[L] N where
  toFun := f
  inj' := f.to_equiv.injective

/-- A first-order equivalence is also a first-order embedding. -/
def to_hom (f : M ≃[L] N) : M →[L] N where
  toFun := f

@[simp]
theorem to_embedding_to_hom (f : M ≃[L] N) : f.to_embedding.to_hom = f.to_hom :=
  rfl

@[simp]
theorem coe_to_hom {f : M ≃[L] N} : (f.to_hom : M → N) = (f : M → N) :=
  rfl

@[simp]
theorem coe_to_embedding (f : M ≃[L] N) : (f.to_embedding : M → N) = (f : M → N) :=
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
  f.to_embedding.injective

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
  { hmn.to_equiv.trans hnp.to_equiv with toFun := hnp ∘ hmn }

@[simp]
theorem comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl

/-- Composition of first-order homomorphisms is associative. -/
theorem comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

end Equivₓ

section ClosedUnder

open Set

variable {n : ℕ} (f : L.functions n) (s : Set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
def closed_under : Prop :=
  ∀ x : Finₓ n → M, (∀ i : Finₓ n, x i ∈ s) → fun_map f x ∈ s

variable (L)

@[simp]
theorem closed_under_univ : closed_under f (univ : Set M) := fun _ _ => mem_univ _

variable {L f s} {t : Set M}

namespace ClosedUnder

theorem inter (hs : closed_under f s) (ht : closed_under f t) : closed_under f (s ∩ t) := fun x h =>
  mem_inter (hs x fun i => mem_of_mem_inter_left (h i)) (ht x fun i => mem_of_mem_inter_right (h i))

theorem inf (hs : closed_under f s) (ht : closed_under f t) : closed_under f (s⊓t) :=
  hs.inter ht

variable {S : Set (Set M)}

theorem Inf (hS : ∀ s, s ∈ S → closed_under f s) : closed_under f (Inf S) := fun x h s hs => hS s hs x fun i => h i s hs

end ClosedUnder

end ClosedUnder

variable (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
structure substructure where
  Carrier : Set M
  fun_mem : ∀ {n}, ∀ f : L.functions n, closed_under f carrier

variable {L} {M}

namespace Substructure

instance : SetLike (L.substructure M) M :=
  ⟨substructure.carrier, fun p q h => by
    cases p <;> cases q <;> congr⟩

/-- See Note [custom simps projection] -/
def simps.coe (S : L.substructure M) : Set M :=
  S

initialize_simps_projections Substructure (Carrier → coe)

@[simp]
theorem mem_carrier {s : L.substructure M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {S T : L.substructure M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
protected def copy (S : L.substructure M) (s : Set M) (hs : s = S) : L.substructure M where
  Carrier := s
  fun_mem := fun n f => hs.symm ▸ S.fun_mem f

variable {S : L.substructure M}

@[simp]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl

theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem const_mem {c : L.const} : ↑c ∈ S :=
  mem_carrier.2 (S.fun_mem c _ Finₓ.elim0)

/-- The substructure `M` of the structure `M`. -/
instance : HasTop (L.substructure M) :=
  ⟨{ Carrier := Set.Univ, fun_mem := fun n f x h => Set.mem_univ _ }⟩

instance : Inhabited (L.substructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.substructure M) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.substructure M) : Set M) = Set.Univ :=
  rfl

/-- The inf of two substructures is their intersection. -/
instance : HasInf (L.substructure M) :=
  ⟨fun S₁ S₂ => { Carrier := S₁ ∩ S₂, fun_mem := fun n f => (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
theorem coe_inf (p p' : L.substructure M) : ((p⊓p' : L.substructure M) : Set M) = p ∩ p' :=
  rfl

@[simp]
theorem mem_inf {p p' : L.substructure M} {x : M} : x ∈ p⊓p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl

instance : HasInfₓ (L.substructure M) :=
  ⟨fun s =>
    { Carrier := ⋂ t ∈ s, ↑t,
      fun_mem := fun n f =>
        closed_under.Inf
          (by
            rintro _ ⟨t, rfl⟩
            by_cases' h : t ∈ s
            · simpa [h] using t.fun_mem f
              
            · simp [h]
              ) }⟩

@[simp, norm_cast]
theorem coe_Inf (S : Set (L.substructure M)) : ((Inf S : L.substructure M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl

theorem mem_Inf {S : Set (L.substructure M)} {x : M} : x ∈ Inf S ↔ ∀, ∀ p ∈ S, ∀, x ∈ p :=
  Set.mem_Inter₂

theorem mem_infi {ι : Sort _} {S : ι → L.substructure M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [infi, mem_Inf, Set.forall_range_iff]

@[simp, norm_cast]
theorem coe_infi {ι : Sort _} {S : ι → L.substructure M} : (↑⨅ i, S i : Set M) = ⋂ i, S i := by
  simp only [infi, coe_Inf, Set.bInter_range]

/-- Substructures of a structure form a complete lattice. -/
instance : CompleteLattice (L.substructure M) :=
  { completeLatticeOfInf (L.substructure M) $ fun s =>
      IsGlb.of_image (fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe) is_glb_binfi with
    le := · ≤ ·, lt := · < ·, top := ⊤, le_top := fun S x hx => mem_top x, inf := ·⊓·, inf := HasInfₓ.inf,
    le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩, inf_le_left := fun a b x => And.left,
    inf_le_right := fun a b x => And.right }

variable (L)

/-- The `L.substructure` generated by a set. -/
def closure : LowerAdjoint (coe : L.substructure M → Set M) :=
  ⟨fun s => Inf { S | s ⊆ S }, fun s S =>
    ⟨Set.Subset.trans fun x hx => mem_Inf.2 $ fun S hS => hS hx, fun h => Inf_le h⟩⟩

variable {L} {s : Set M}

theorem mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.substructure M, s ⊆ S → x ∈ S :=
  mem_Inf

/-- The substructure generated by a set includes the set. -/
@[simp]
theorem subset_closure : s ⊆ closure L s :=
  (closure L).le_closure s

theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure L s) : P ∉ s := fun h => hP (subset_closure h)

@[simp]
theorem closed (S : L.substructure M) : (closure L).Closed (S : Set M) :=
  congr rfl ((closure L).eq_of_le Set.Subset.rfl fun x xS => mem_closure.2 fun T hT => hT xS)

open Set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
theorem closure_le : closure L s ≤ S ↔ s ⊆ S :=
  (closure L).closure_le_closed_iff_le s S.closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
  (closure L).Monotone h

theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
  (closure L).eq_of_le h₁ h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure L s) (Hs : ∀, ∀ x ∈ s, ∀, p x)
    (Hfun : ∀ {n : ℕ} f : L.functions n, closed_under f (SetOf p)) : p x :=
  (@closure_le L M _ ⟨SetOf p, fun n => Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_eliminator]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure L s = ⊤) (Hs : ∀, ∀ x ∈ s, ∀, p x)
    (Hfun : ∀ {n : ℕ} f : L.functions n, closed_under f (SetOf p)) : p x := by
  have : ∀, ∀ x ∈ closure L s, ∀, p x := fun x hx => closure_induction hx Hs fun n => Hfun
  simpa [hs] using this x

variable (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : GaloisInsertion (@closure L M _) coe where
  choice := fun s _ => closure L s
  gc := (closure L).gc
  le_l_u := fun s => subset_closure
  choice_eq := fun s h => rfl

variable {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp]
theorem closure_eq : closure L (S : Set M) = S :=
  (substructure.gi L M).l_u_eq S

@[simp]
theorem closure_empty : closure L (∅ : Set M) = ⊥ :=
  (substructure.gi L M).gc.l_bot

@[simp]
theorem closure_univ : closure L (univ : Set M) = ⊤ :=
  @coe_top L M _ ▸ closure_eq ⊤

theorem closure_union (s t : Set M) : closure L (s ∪ t) = closure L s⊔closure L t :=
  (substructure.gi L M).gc.l_sup

theorem closure_Union {ι} (s : ι → Set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
  (substructure.gi L M).gc.l_supr

/-!
### `comap` and `map`
-/


/-- The preimage of a substructure along a homomorphism is a substructure. -/
@[simps]
def comap (φ : M →[L] N) (S : L.substructure N) : L.substructure M where
  Carrier := φ ⁻¹' S
  fun_mem := fun n f x hx => by
    rw [mem_preimage, φ.map_fun]
    exact S.fun_mem f (φ ∘ x) hx

@[simp]
theorem mem_comap {S : L.substructure N} {f : M →[L] N} {x : M} : x ∈ S.comap f ↔ f x ∈ S :=
  Iff.rfl

theorem comap_comap (S : L.substructure P) (g : N →[L] P) (f : M →[L] N) : (S.comap g).comap f = S.comap (g.comp f) :=
  rfl

@[simp]
theorem comap_id (S : L.substructure P) : S.comap (hom.id _ _) = S :=
  ext
    (by
      simp )

/-- The image of a substructure along a homomorphism is a substructure. -/
@[simps]
def map (φ : M →[L] N) (S : L.substructure M) : L.substructure N where
  Carrier := φ '' S
  fun_mem := fun n f x hx =>
    (mem_image _ _ _).1
      ⟨fun_map f fun i => Classical.some (hx i), S.fun_mem f _ fun i => (Classical.some_spec (hx i)).1, by
        simp only [hom.map_fun, SetLike.mem_coe]
        exact congr rfl (funext fun i => (Classical.some_spec (hx i)).2)⟩

@[simp]
theorem mem_map {f : M →[L] N} {S : L.substructure M} {y : N} : y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
  mem_image_iff_bex

theorem mem_map_of_mem (f : M →[L] N) {S : L.substructure M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
  mem_image_of_mem f hx

theorem apply_coe_mem_map (f : M →[L] N) (S : L.substructure M) (x : S) : f x ∈ S.map f :=
  mem_map_of_mem f x.prop

theorem map_map (g : N →[L] P) (f : M →[L] N) : (S.map f).map g = S.map (g.comp f) :=
  SetLike.coe_injective $ image_image _ _ _

theorem map_le_iff_le_comap {f : M →[L] N} {S : L.substructure M} {T : L.substructure N} :
    S.map f ≤ T ↔ S ≤ T.comap f :=
  image_subset_iff

theorem gc_map_comap (f : M →[L] N) : GaloisConnection (map f) (comap f) := fun S T => map_le_iff_le_comap

theorem map_le_of_le_comap {T : L.substructure N} {f : M →[L] N} : S ≤ T.comap f → S.map f ≤ T :=
  (gc_map_comap f).l_le

theorem le_comap_of_map_le {T : L.substructure N} {f : M →[L] N} : S.map f ≤ T → S ≤ T.comap f :=
  (gc_map_comap f).le_u

theorem le_comap_map {f : M →[L] N} : S ≤ (S.map f).comap f :=
  (gc_map_comap f).le_u_l _

theorem map_comap_le {S : L.substructure N} {f : M →[L] N} : (S.comap f).map f ≤ S :=
  (gc_map_comap f).l_u_le _

theorem monotone_map {f : M →[L] N} : Monotone (map f) :=
  (gc_map_comap f).monotone_l

theorem monotone_comap {f : M →[L] N} : Monotone (comap f) :=
  (gc_map_comap f).monotone_u

@[simp]
theorem map_comap_map {f : M →[L] N} : ((S.map f).comap f).map f = S.map f :=
  (gc_map_comap f).l_u_l_eq_l _

@[simp]
theorem comap_map_comap {S : L.substructure N} {f : M →[L] N} : ((S.comap f).map f).comap f = S.comap f :=
  (gc_map_comap f).u_l_u_eq_u _

theorem map_sup (S T : L.substructure M) (f : M →[L] N) : (S⊔T).map f = S.map f⊔T.map f :=
  (gc_map_comap f).l_sup

theorem map_supr {ι : Sort _} (f : M →[L] N) (s : ι → L.substructure M) : (supr s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_supr

theorem comap_inf (S T : L.substructure N) (f : M →[L] N) : (S⊓T).comap f = S.comap f⊓T.comap f :=
  (gc_map_comap f).u_inf

theorem comap_infi {ι : Sort _} (f : M →[L] N) (s : ι → L.substructure N) : (infi s).comap f = ⨅ i, (s i).comap f :=
  (gc_map_comap f).u_infi

@[simp]
theorem map_bot (f : M →[L] N) : (⊥ : L.substructure M).map f = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
theorem comap_top (f : M →[L] N) : (⊤ : L.substructure N).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
theorem map_id (S : L.substructure M) : S.map (hom.id L M) = S :=
  ext fun x => ⟨fun ⟨_, h, rfl⟩ => h, fun h => ⟨_, h, rfl⟩⟩

section GaloisCoinsertion

variable {ι : Type _} {f : M →[L] N} (hf : Function.Injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gci_map_comap : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp [mem_comap, mem_map, hf.eq_iff]

theorem comap_map_eq_of_injective (S : L.substructure M) : (S.map f).comap f = S :=
  (gci_map_comap hf).u_l_eq _

theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gci_map_comap hf).u_surjective

theorem map_injective_of_injective : Function.Injective (map f) :=
  (gci_map_comap hf).l_injective

theorem comap_inf_map_of_injective (S T : L.substructure M) : (S.map f⊓T.map f).comap f = S⊓T :=
  (gci_map_comap hf).u_inf_l _ _

theorem comap_infi_map_of_injective (S : ι → L.substructure M) : (⨅ i, (S i).map f).comap f = infi S :=
  (gci_map_comap hf).u_infi_l _

theorem comap_sup_map_of_injective (S T : L.substructure M) : (S.map f⊔T.map f).comap f = S⊔T :=
  (gci_map_comap hf).u_sup_l _ _

theorem comap_supr_map_of_injective (S : ι → L.substructure M) : (⨆ i, (S i).map f).comap f = supr S :=
  (gci_map_comap hf).u_supr_l _

theorem map_le_map_iff_of_injective {S T : L.substructure M} : S.map f ≤ T.map f ↔ S ≤ T :=
  (gci_map_comap hf).l_le_l_iff

theorem map_strict_mono_of_injective : StrictMono (map f) :=
  (gci_map_comap hf).strict_mono_l

end GaloisCoinsertion

section GaloisInsertion

variable {ι : Type _} {f : M →[L] N} (hf : Function.Surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def gi_map_comap : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x h =>
    let ⟨y, hy⟩ := hf x
    mem_map.2
      ⟨y, by
        simp [hy, h]⟩

theorem map_comap_eq_of_surjective (S : L.substructure N) : (S.comap f).map f = S :=
  (gi_map_comap hf).l_u_eq _

theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (gi_map_comap hf).l_surjective

theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (gi_map_comap hf).u_injective

theorem map_inf_comap_of_surjective (S T : L.substructure N) : (S.comap f⊓T.comap f).map f = S⊓T :=
  (gi_map_comap hf).l_inf_u _ _

theorem map_infi_comap_of_surjective (S : ι → L.substructure N) : (⨅ i, (S i).comap f).map f = infi S :=
  (gi_map_comap hf).l_infi_u _

theorem map_sup_comap_of_surjective (S T : L.substructure N) : (S.comap f⊔T.comap f).map f = S⊔T :=
  (gi_map_comap hf).l_sup_u _ _

theorem map_supr_comap_of_surjective (S : ι → L.substructure N) : (⨆ i, (S i).comap f).map f = supr S :=
  (gi_map_comap hf).l_supr_u _

theorem comap_le_comap_iff_of_surjective {S T : L.substructure N} : S.comap f ≤ T.comap f ↔ S ≤ T :=
  (gi_map_comap hf).u_le_u_iff

theorem comap_strict_mono_of_surjective : StrictMono (comap f) :=
  (gi_map_comap hf).strict_mono_u

end GaloisInsertion

instance induced_Structure {S : L.substructure M} : L.Structure S where
  funMap := fun n f x => ⟨fun_map f fun i => x i, S.fun_mem f (fun i => x i) fun i => (x i).2⟩
  RelMap := fun n r x => rel_map r fun i => (x i : M)

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def Subtype (S : L.substructure M) : S ↪[L] M where
  toFun := coe
  inj' := Subtype.coe_injective

@[simp]
theorem coeSubtype : ⇑S.subtype = coe :=
  rfl

/-- An induction principle on elements of the type `substructure.closure L s`.
If `p` holds for `1` and all elements of `s`, and is preserved under multiplication, then `p`
holds for all elements of the closure of `s`.
The difference with `substructure.closure_induction` is that this acts on the subtype.
-/
@[elab_as_eliminator]
theorem closure_induction' (s : Set M) {p : closure L s → Prop} (Hs : ∀ x h : x ∈ s, p ⟨x, subset_closure h⟩)
    (Hfun : ∀ {n : ℕ} f : L.functions n, closed_under f (SetOf p)) (x : closure L s) : p x :=
  Subtype.recOn x $ fun x hx => by
    refine' Exists.elim _ fun hx : x ∈ closure L s hc : p ⟨x, hx⟩ => hc
    exact
      closure_induction hx (fun x hx => ⟨subset_closure hx, Hs x hx⟩) fun n f x hx =>
        ⟨(closure L s).fun_mem f _ fun i => Classical.some (hx i),
          Hfun f (fun i => ⟨x i, Classical.some (hx i)⟩) fun i => Classical.some_spec (hx i)⟩

end Substructure

namespace Hom

open Substructure

/-- The substructure of elements `x : M` such that `f x = g x` -/
def eq_locus (f g : M →[L] N) : substructure L M where
  Carrier := { x : M | f x = g x }
  fun_mem := fun n fn x hx => by
    have h : f ∘ x = g ∘ x := by
      ext
      repeat'
        rw [Function.comp_applyₓ]
      apply hx
    simp [h]

/-- If two `L.hom`s are equal on a set, then they are equal on its substructure closure. -/
theorem eq_on_closure {f g : M →[L] N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure L s) :=
  show closure L s ≤ f.eq_locus g from closure_le.2 h

theorem eq_of_eq_on_top {f g : M →[L] N} (h : Set.EqOn f g (⊤ : substructure L M)) : f = g :=
  ext $ fun x => h trivialₓ

variable {s : Set M}

theorem eq_of_eq_on_dense (hs : closure L s = ⊤) {f g : M →[L] N} (h : s.eq_on f g) : f = g :=
  eq_of_eq_on_top $ hs ▸ eq_on_closure h

end Hom

end Language

end FirstOrder

