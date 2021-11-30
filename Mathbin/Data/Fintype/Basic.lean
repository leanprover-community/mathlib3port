import Mathbin.Data.Array.Lemmas 
import Mathbin.Data.Finset.Option 
import Mathbin.Data.Finset.Pi 
import Mathbin.Data.Finset.Powerset 
import Mathbin.Data.Finset.Prod 
import Mathbin.Data.List.NodupEquivFin 
import Mathbin.Data.Sym.Basic 
import Mathbin.Data.Ulift 
import Mathbin.GroupTheory.Perm.Basic 
import Mathbin.Order.WellFounded 
import Mathbin.Tactic.Wlog

/-!
# Finite types

This file defines a typeclass to state that a type is finite.

## Main declarations

* `fintype α`:  Typeclass saying that a type is finite. It takes as fields a `finset` and a proof
  that all terms of type `α` are in it.
* `finset.univ`: The finset of all elements of a fintype.
* `fintype.card α`: Cardinality of a fintype. Equal to `finset.univ.card`.
* `perms_of_finset s`: The finset of permutations of the finset `s`.
* `fintype.trunc_equiv_fin`: A fintype `α` is computably equivalent to `fin (card α)`. The
  `trunc`-free, noncomputable version is `fintype.equiv_fin`.
* `fintype.trunc_equiv_of_card_eq` `fintype.equiv_of_card_eq`: Two fintypes of same cardinality are
  equivalent. See above.
* `fin.equiv_iff_eq`: `fin m ≃ fin n` iff `m = n`.
* `infinite α`: Typeclass saying that a type is infinite. Defined as `fintype α → false`.
* `not_fintype`: No `fintype` has an `infinite` instance.
* `infinite.nat_embedding`: An embedding of `ℕ` into an infinite type.

We also provide the following versions of the pigeonholes principle.
* `fintype.exists_ne_map_eq_of_card_lt` and `is_empty_of_card_lt`: Finitely many pigeons and
  pigeonholes. Weak formulation.
* `fintype.exists_ne_map_eq_of_infinite`: Infinitely many pigeons in finitely many pigeonholes.
  Weak formulation.
* `fintype.exists_infinite_fiber`: Infinitely many pigeons in finitely many pigeonholes. Strong
  formulation.

Some more pigeonhole-like statements can be found in `data.fintype.card_embedding`.

## Instances

Among others, we provide `fintype` instances for
* A `subtype` of a fintype. See `fintype.subtype`.
* The `option` of a fintype.
* The product of two fintypes.
* The sum of two fintypes.
* `Prop`.

and `infinite` instances for
* specific types: `ℕ`, `ℤ`
* type constructors: `set α`, `finset α`, `multiset α`, `list α`, `α ⊕ β`, `α × β`

along with some machinery
* Types which have a surjection from/an injection to a `fintype` are themselves fintypes. See
  `fintype.of_injective` and `fintype.of_surjective`.
* Types which have an injection from/a surjection to an `infinite` type are themselves `infinite`.
  See `infinite.of_injective` and `infinite.of_surjective`.
-/


open_locale Nat

universe u v

variable {α β γ : Type _}

/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type _) where 
  elems{} : Finset α 
  complete : ∀ x : α, x ∈ elems

namespace Finset

variable [Fintype α]

/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ : Finset α :=
  Fintype.elems α

@[simp]
theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
  Fintype.complete x

@[simp]
theorem mem_univ_val : ∀ x, x ∈ (univ : Finset α).1 :=
  mem_univ

@[simp]
theorem coe_univ : «expr↑ » (univ : Finset α) = (Set.Univ : Set α) :=
  by 
    ext <;> simp 

theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α :=
  by 
    rw [←coe_nonempty, coe_univ, Set.nonempty_iff_univ_nonempty]

theorem univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty :=
  univ_nonempty_iff.2 ‹_›

theorem univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α :=
  by 
    rw [←not_nonempty_iff, ←univ_nonempty_iff, not_nonempty_iff_eq_empty]

theorem univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅ :=
  univ_eq_empty_iff.2 ‹_›

@[simp]
theorem subset_univ (s : Finset α) : s ⊆ univ :=
  fun a _ => mem_univ a

instance : OrderTop (Finset α) :=
  { top := univ, le_top := subset_univ }

instance [DecidableEq α] : BooleanAlgebra (Finset α) :=
  { Finset.orderTop, Finset.orderBot, Finset.generalizedBooleanAlgebra with Compl := fun s => univ \ s,
    inf_compl_le_bot :=
      fun s x hx =>
        by 
          simpa using hx,
    top_le_sup_compl :=
      fun s x hx =>
        by 
          simp ,
    sdiff_eq :=
      fun s t =>
        by 
          simp [ext_iff, compl] }

theorem compl_eq_univ_sdiff [DecidableEq α] (s : Finset α) : «expr ᶜ» s = univ \ s :=
  rfl

@[simp]
theorem mem_compl [DecidableEq α] {s : Finset α} {x : α} : x ∈ «expr ᶜ» s ↔ x ∉ s :=
  by 
    simp [compl_eq_univ_sdiff]

@[simp, normCast]
theorem coe_compl [DecidableEq α] (s : Finset α) : «expr↑ » («expr ᶜ» s) = «expr ᶜ» («expr↑ » s : Set α) :=
  Set.ext$ fun x => mem_compl

@[simp]
theorem union_compl [DecidableEq α] (s : Finset α) : s ∪ «expr ᶜ» s = Finset.univ :=
  sup_compl_eq_top

@[simp]
theorem insert_compl_self [DecidableEq α] (x : α) : insert x («expr ᶜ» {x} : Finset α) = univ :=
  by 
    ext y 
    simp [eq_or_ne]

@[simp]
theorem compl_filter [DecidableEq α] (p : α → Prop) [DecidablePred p] [∀ x, Decidable ¬p x] :
  «expr ᶜ» (univ.filter p) = univ.filter fun x => ¬p x :=
  (filter_not _ _).symm

theorem eq_univ_iff_forall {s : Finset α} : s = univ ↔ ∀ x, x ∈ s :=
  by 
    simp [ext_iff]

theorem compl_ne_univ_iff_nonempty [DecidableEq α] (s : Finset α) : «expr ᶜ» s ≠ univ ↔ s.nonempty :=
  by 
    simp [eq_univ_iff_forall, Finset.Nonempty]

theorem compl_singleton [DecidableEq α] (a : α) : «expr ᶜ» ({a} : Finset α) = univ.erase a :=
  by 
    rw [compl_eq_univ_sdiff, sdiff_singleton_eq_erase]

@[simp]
theorem univ_inter [DecidableEq α] (s : Finset α) : univ ∩ s = s :=
  ext$
    fun a =>
      by 
        simp 

@[simp]
theorem inter_univ [DecidableEq α] (s : Finset α) : s ∩ univ = s :=
  by 
    rw [inter_comm, univ_inter]

@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (univ : Finset α))] {δ : α → Sort _} (f g : ∀ i, δ i) :
  univ.piecewise f g = f :=
  by 
    ext i 
    simp [piecewise]

theorem piecewise_compl [DecidableEq α] (s : Finset α) [∀ i : α, Decidable (i ∈ s)]
  [∀ i : α, Decidable (i ∈ «expr ᶜ» s)] {δ : α → Sort _} (f g : ∀ i, δ i) :
  («expr ᶜ» s).piecewise f g = s.piecewise g f :=
  by 
    ext i 
    simp [piecewise]

@[simp]
theorem piecewise_erase_univ {δ : α → Sort _} [DecidableEq α] (a : α) (f g : ∀ a, δ a) :
  (Finset.univ.erase a).piecewise f g = Function.update f a (g a) :=
  by 
    rw [←compl_singleton, piecewise_compl, piecewise_singleton]

theorem univ_map_equiv_to_embedding {α β : Type _} [Fintype α] [Fintype β] (e : α ≃ β) :
  univ.map e.to_embedding = univ :=
  eq_univ_iff_forall.mpr
    fun b =>
      mem_map.mpr
        ⟨e.symm b, mem_univ _,
          by 
            simp ⟩

@[simp]
theorem univ_filter_exists (f : α → β) [Fintype β] [DecidablePred fun y => ∃ x, f x = y] [DecidableEq β] :
  (Finset.univ.filter fun y => ∃ x, f x = y) = Finset.univ.Image f :=
  by 
    ext 
    simp 

/-- Note this is a special case of `(finset.image_preimage f univ _).symm`. -/
theorem univ_filter_mem_range (f : α → β) [Fintype β] [DecidablePred fun y => y ∈ Set.Range f] [DecidableEq β] :
  (Finset.univ.filter fun y => y ∈ Set.Range f) = Finset.univ.Image f :=
  univ_filter_exists f

/-- A special case of `finset.sup_eq_supr` that omits the useless `x ∈ univ` binder. -/
theorem sup_univ_eq_supr [CompleteLattice β] (f : α → β) : Finset.univ.sup f = supr f :=
  (sup_eq_supr _ f).trans$ congr_argₓ _$ funext$ fun a => supr_pos (mem_univ _)

/-- A special case of `finset.inf_eq_infi` that omits the useless `x ∈ univ` binder. -/
theorem inf_univ_eq_infi [CompleteLattice β] (f : α → β) : Finset.univ.inf f = infi f :=
  sup_univ_eq_supr
    (by 
      exact f :
    α → OrderDual β)

end Finset

open Finset Function

namespace Fintype

instance decidable_pi_fintype {α} {β : α → Type _} [∀ a, DecidableEq (β a)] [Fintype α] : DecidableEq (∀ a, β a) :=
  fun f g =>
    decidableOfIff (∀ a _ : a ∈ Fintype.elems α, f a = g a)
      (by 
        simp [Function.funext_iffₓ, Fintype.complete])

instance decidable_forall_fintype {p : α → Prop} [DecidablePred p] [Fintype α] : Decidable (∀ a, p a) :=
  decidableOfIff (∀ a _ : a ∈ @univ α _, p a)
    (by 
      simp )

instance decidable_exists_fintype {p : α → Prop} [DecidablePred p] [Fintype α] : Decidable (∃ a, p a) :=
  decidableOfIff (∃ (a : _)(_ : a ∈ @univ α _), p a)
    (by 
      simp )

instance decidable_mem_range_fintype [Fintype α] [DecidableEq β] (f : α → β) : DecidablePred (· ∈ Set.Range f) :=
  fun x => Fintype.decidableExistsFintype

section BundledHoms

instance decidable_eq_equiv_fintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β) :=
  fun a b => decidableOfIff (a.1 = b.1) Equiv.coe_fn_injective.eq_iff

instance decidable_eq_embedding_fintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪ β) :=
  fun a b => decidableOfIff ((a : α → β) = b) Function.Embedding.coe_injective.eq_iff

@[toAdditive]
instance decidable_eq_one_hom_fintype [DecidableEq β] [Fintype α] [HasOne α] [HasOne β] : DecidableEq (OneHom α β) :=
  fun a b => decidableOfIff ((a : α → β) = b) (injective.eq_iff OneHom.coe_inj)

@[toAdditive]
instance decidable_eq_mul_hom_fintype [DecidableEq β] [Fintype α] [Mul α] [Mul β] : DecidableEq (MulHom α β) :=
  fun a b => decidableOfIff ((a : α → β) = b) (injective.eq_iff MulHom.coe_inj)

@[toAdditive]
instance decidable_eq_monoid_hom_fintype [DecidableEq β] [Fintype α] [MulOneClass α] [MulOneClass β] :
  DecidableEq (α →* β) :=
  fun a b => decidableOfIff ((a : α → β) = b) (injective.eq_iff MonoidHom.coe_inj)

instance decidable_eq_monoid_with_zero_hom_fintype [DecidableEq β] [Fintype α] [MulZeroOneClass α] [MulZeroOneClass β] :
  DecidableEq (MonoidWithZeroHom α β) :=
  fun a b => decidableOfIff ((a : α → β) = b) (injective.eq_iff MonoidWithZeroHom.coe_inj)

instance decidable_eq_ring_hom_fintype [DecidableEq β] [Fintype α] [Semiringₓ α] [Semiringₓ β] :
  DecidableEq (α →+* β) :=
  fun a b => decidableOfIff ((a : α → β) = b) (injective.eq_iff RingHom.coe_inj)

end BundledHoms

instance decidable_injective_fintype [DecidableEq α] [DecidableEq β] [Fintype α] :
  DecidablePred (injective : (α → β) → Prop) :=
  fun x =>
    by 
      unfold injective <;> infer_instance

instance decidable_surjective_fintype [DecidableEq β] [Fintype α] [Fintype β] :
  DecidablePred (surjective : (α → β) → Prop) :=
  fun x =>
    by 
      unfold surjective <;> infer_instance

instance decidable_bijective_fintype [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
  DecidablePred (bijective : (α → β) → Prop) :=
  fun x =>
    by 
      unfold bijective <;> infer_instance

instance decidable_right_inverse_fintype [DecidableEq α] [Fintype α] (f : α → β) (g : β → α) :
  Decidable (Function.RightInverse f g) :=
  show Decidable (∀ x, g (f x) = x)by 
    infer_instance

instance decidable_left_inverse_fintype [DecidableEq β] [Fintype β] (f : α → β) (g : β → α) :
  Decidable (Function.LeftInverse f g) :=
  show Decidable (∀ x, f (g x) = x)by 
    infer_instance

theorem exists_max [Fintype α] [Nonempty α] {β : Type _} [LinearOrderₓ β] (f : α → β) : ∃ x₀ : α, ∀ x, f x ≤ f x₀ :=
  by 
    simpa using exists_max_image univ f univ_nonempty

theorem exists_min [Fintype α] [Nonempty α] {β : Type _} [LinearOrderₓ β] (f : α → β) : ∃ x₀ : α, ∀ x, f x₀ ≤ f x :=
  by 
    simpa using exists_min_image univ f univ_nonempty

/-- Construct a proof of `fintype α` from a universal multiset -/
def of_multiset [DecidableEq α] (s : Multiset α) (H : ∀ x : α, x ∈ s) : Fintype α :=
  ⟨s.to_finset,
    by 
      simpa using H⟩

/-- Construct a proof of `fintype α` from a universal list -/
def of_list [DecidableEq α] (l : List α) (H : ∀ x : α, x ∈ l) : Fintype α :=
  ⟨l.to_finset,
    by 
      simpa using H⟩

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_univ_list (α) [fintype α] : «expr∃ , »((l : list α), «expr ∧ »(l.nodup, ∀ x : α, «expr ∈ »(x, l))) :=
let ⟨l, e⟩ := quotient.exists_rep (@univ α _).1 in
by have [] [] [":=", expr and.intro univ.2 mem_univ_val]; exact [expr ⟨_, by rwa ["<-", expr e] ["at", ident this]⟩]

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card α [Fintype α] : ℕ :=
  (@univ α _).card

/-- There is (computably) an equivalence between `α` and `fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `trunc` to
preserve computability.

See `fintype.equiv_fin` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.

See `fintype.trunc_fin_bijection` for a version without `[decidable_eq α]`.
-/
def trunc_equiv_fin α [DecidableEq α] [Fintype α] : Trunc (α ≃ Finₓ (card α)) :=
  by 
    unfold card Finset.card 
    exact
      Quot.recOnSubsingletonₓ (@univ α _).1
        (fun l h : ∀ x : α, x ∈ l nd : l.nodup => Trunc.mk (nd.nth_le_equiv_of_forall_mem_list _ h).symm) mem_univ_val
        univ.2

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- There is (noncomputably) an equivalence between `α` and `fin (card α)`.

See `fintype.trunc_equiv_fin` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.
-/ noncomputable def equiv_fin (α) [fintype α] : «expr ≃ »(α, fin (card α)) :=
by { letI [] [] [":=", expr classical.dec_eq α],
  exact [expr (trunc_equiv_fin α).out] }

/-- There is (computably) a bijection between `fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `trunc` to
preserve computability.

See `fintype.trunc_equiv_fin` for a version that gives an equivalence
given `[decidable_eq α]`.
-/
def trunc_fin_bijection α [Fintype α] : Trunc { f : Finₓ (card α) → α // bijective f } :=
  by 
    dunfold card Finset.card 
    exact
      Quot.recOnSubsingletonₓ (@univ α _).1
        (fun l h : ∀ x : α, x ∈ l nd : l.nodup => Trunc.mk (nd.nth_le_bijection_of_forall_mem_list _ h)) mem_univ_val
        univ.2

instance (α : Type _) : Subsingleton (Fintype α) :=
  ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ =>
      by 
        congr <;> simp [Finset.ext_iff, h₁, h₂]⟩

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def Subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) : Fintype { x // p x } :=
  ⟨⟨Multiset.pmap Subtype.mk s.1 fun x => (H x).1, Multiset.nodup_pmap (fun a _ b _ => congr_argₓ Subtype.val) s.2⟩,
    fun ⟨x, px⟩ => Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
  @card { x // p x } (Fintype.subtype s H) = s.card :=
  Multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) [Fintype { x // p x }] :
  card { x // p x } = s.card :=
  by 
    rw [←subtype_card s H]
    congr

/-- Construct a fintype from a finset with the same elements. -/
def of_finset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
  Fintype.subtype s H

@[simp]
theorem card_of_finset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : @Fintype.card p (of_finset s H) = s.card :=
  Fintype.subtype_card s H

theorem card_of_finset' {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) [Fintype p] : Fintype.card p = s.card :=
  by 
    rw [←card_of_finset s H] <;> congr

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def of_bijective [Fintype α] (f : α → β) (H : Function.Bijective f) : Fintype β :=
  ⟨univ.map ⟨f, H.1⟩,
    fun b =>
      let ⟨a, e⟩ := H.2 b 
      e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def of_surjective [DecidableEq β] [Fintype α] (f : α → β) (H : Function.Surjective f) : Fintype β :=
  ⟨univ.Image f,
    fun b =>
      let ⟨a, e⟩ := H b 
      e ▸ mem_image_of_mem _ (mem_univ _)⟩

end Fintype

section Inv

namespace Function

variable [Fintype α] [DecidableEq β]

namespace Injective

variable {f : α → β} (hf : Function.Injective f)

/--
The inverse of an `hf : injective` function `f : α → β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def inv_of_mem_range : Set.Range f → α :=
  fun b =>
    Finset.choose (fun a => f a = b) Finset.univ
      ((exists_unique_congr
            (by 
              simp )).mp
        (hf.exists_unique_of_mem_range b.property))

theorem left_inv_of_inv_of_mem_range (b : Set.Range f) : f (hf.inv_of_mem_range b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right

@[simp]
theorem right_inv_of_inv_of_mem_range (a : α) : hf.inv_of_mem_range ⟨f a, Set.mem_range_self a⟩ = a :=
  hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right

theorem inv_fun_restrict [Nonempty α] : (Set.Range f).restrict (inv_fun f) = hf.inv_of_mem_range :=
  by 
    ext ⟨b, h⟩
    apply hf 
    simp [hf.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]

theorem inv_of_mem_range_surjective : Function.Surjective hf.inv_of_mem_range :=
  fun a =>
    ⟨⟨f a, Set.mem_range_self a⟩,
      by 
        simp ⟩

end Injective

namespace Embedding

variable (f : α ↪ β) (b : Set.Range f)

/--
The inverse of an embedding `f : α ↪ β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def inv_of_mem_range : α :=
  f.injective.inv_of_mem_range b

@[simp]
theorem left_inv_of_inv_of_mem_range : f (f.inv_of_mem_range b) = b :=
  f.injective.left_inv_of_inv_of_mem_range b

@[simp]
theorem right_inv_of_inv_of_mem_range (a : α) : f.inv_of_mem_range ⟨f a, Set.mem_range_self a⟩ = a :=
  f.injective.right_inv_of_inv_of_mem_range a

theorem inv_fun_restrict [Nonempty α] : (Set.Range f).restrict (inv_fun f) = f.inv_of_mem_range :=
  by 
    ext ⟨b, h⟩
    apply f.injective 
    simp [f.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]

theorem inv_of_mem_range_surjective : Function.Surjective f.inv_of_mem_range :=
  fun a =>
    ⟨⟨f a, Set.mem_range_self a⟩,
      by 
        simp ⟩

end Embedding

end Function

end Inv

namespace Fintype

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
noncomputable
def of_injective [fintype β] (f : α → β) (H : function.injective f) : fintype α :=
by letI [] [] [":=", expr classical.dec]; exact [expr if hα : nonempty α then by letI [] [] [":=", expr classical.inhabited_of_nonempty hα]; exact [expr of_surjective (inv_fun f) (inv_fun_surjective H)] else ⟨«expr∅»(), λ
  x, (hα ⟨x⟩).elim⟩]

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def of_equiv (α : Type _) [Fintype α] (f : α ≃ β) : Fintype β :=
  of_bijective _ f.bijective

theorem of_equiv_card [Fintype α] (f : α ≃ β) : @card β (of_equiv α f) = card α :=
  Multiset.card_map _ _

theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β :=
  by 
    rw [←of_equiv_card f] <;> congr

section 

variable [Fintype α] [Fintype β]

/-- If the cardinality of `α` is `n`, there is computably a bijection between `α` and `fin n`.

See `fintype.equiv_fin_of_card_eq` for the noncomputable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
def trunc_equiv_fin_of_card_eq [DecidableEq α] {n : ℕ} (h : Fintype.card α = n) : Trunc (α ≃ Finₓ n) :=
  (trunc_equiv_fin α).map fun e => e.trans (Finₓ.cast h).toEquiv

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the cardinality of `α` is `n`, there is noncomputably a bijection between `α` and `fin n`.

See `fintype.trunc_equiv_fin_of_card_eq` for the computable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/ noncomputable def equiv_fin_of_card_eq {n : exprℕ()} (h : «expr = »(fintype.card α, n)) : «expr ≃ »(α, fin n) :=
by { letI [] [] [":=", expr classical.dec_eq α],
  exact [expr (trunc_equiv_fin_of_card_eq h).out] }

/-- Two `fintype`s with the same cardinality are (computably) in bijection.

See `fintype.equiv_of_card_eq` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
def trunc_equiv_of_card_eq [DecidableEq α] [DecidableEq β] (h : card α = card β) : Trunc (α ≃ β) :=
  (trunc_equiv_fin_of_card_eq h).bind fun e => (trunc_equiv_fin β).map fun e' => e.trans e'.symm

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Two `fintype`s with the same cardinality are (noncomputably) in bijection.

See `fintype.trunc_equiv_of_card_eq` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/ noncomputable def equiv_of_card_eq (h : «expr = »(card α, card β)) : «expr ≃ »(α, β) :=
by { letI [] [] [":=", expr classical.dec_eq α],
  letI [] [] [":=", expr classical.dec_eq β],
  exact [expr (trunc_equiv_of_card_eq h).out] }

end 

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem card_eq
{α β}
[F : fintype α]
[G : fintype β] : «expr ↔ »(«expr = »(card α, card β), nonempty «expr ≃ »(α, β)) :=
⟨λ h, by { haveI [] [] [":=", expr classical.prop_decidable],
   exact [expr (trunc_equiv_of_card_eq h).nonempty] }, λ ⟨f⟩, card_congr f⟩

/-- Any subsingleton type with a witness is a fintype (with one term). -/
def of_subsingleton (a : α) [Subsingleton α] : Fintype α :=
  ⟨{a}, fun b => Finset.mem_singleton.2 (Subsingleton.elimₓ _ _)⟩

@[simp]
theorem univ_of_subsingleton (a : α) [Subsingleton α] : @univ _ (of_subsingleton a) = {a} :=
  rfl

/-- Note: this lemma is specifically about `fintype.of_subsingleton`. For a statement about
arbitrary `fintype` instances, use either `fintype.card_le_one_iff_subsingleton` or
`fintype.card_unique`. -/
@[simp]
theorem card_of_subsingleton (a : α) [Subsingleton α] : @Fintype.card _ (of_subsingleton a) = 1 :=
  rfl

@[simp]
theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1 :=
  Subsingleton.elimₓ (of_subsingleton$ default α) h ▸ card_of_subsingleton _

instance (priority := 100) of_is_empty [IsEmpty α] : Fintype α :=
  ⟨∅, isEmptyElim⟩

/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `fintype.univ_is_empty`. -/
@[simp, nolint simp_nf]
theorem univ_of_is_empty [IsEmpty α] : @univ α _ = ∅ :=
  rfl

/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `fintype.card_eq_zero_iff`. -/
@[simp]
theorem card_of_is_empty [IsEmpty α] : Fintype.card α = 0 :=
  rfl

open_locale Classical

variable (α)

/-- Any subsingleton type is (noncomputably) a fintype (with zero or one term). -/
noncomputable instance (priority := 5) of_subsingleton' [Subsingleton α] : Fintype α :=
  if h : Nonempty α then of_subsingleton (Nonempty.some h) else @Fintype.ofIsEmpty _$ not_nonempty_iff.mp h

end Fintype

namespace Set

/-- Construct a finset enumerating a set `s`, given a `fintype` instance.  -/
def to_finset (s : Set α) [Fintype s] : Finset α :=
  ⟨(@Finset.univ s _).1.map Subtype.val, Multiset.nodup_map (fun a b => Subtype.eq) Finset.univ.2⟩

@[simp]
theorem mem_to_finset {s : Set α} [Fintype s] {a : α} : a ∈ s.to_finset ↔ a ∈ s :=
  by 
    simp [to_finset]

@[simp]
theorem mem_to_finset_val {s : Set α} [Fintype s] {a : α} : a ∈ s.to_finset.1 ↔ a ∈ s :=
  mem_to_finset

@[simp]
theorem to_finset_card {α : Type _} (s : Set α) [Fintype s] : s.to_finset.card = Fintype.card s :=
  Multiset.card_map Subtype.val Finset.univ.val

@[simp]
theorem coe_to_finset (s : Set α) [Fintype s] : («expr↑ » s.to_finset : Set α) = s :=
  Set.ext$ fun _ => mem_to_finset

@[simp]
theorem to_finset_inj {s t : Set α} [Fintype s] [Fintype t] : s.to_finset = t.to_finset ↔ s = t :=
  ⟨fun h =>
      by 
        rw [←s.coe_to_finset, h, t.coe_to_finset],
    fun h =>
      by 
        simp [h] <;> congr⟩

@[simp, mono]
theorem to_finset_mono {s t : Set α} [Fintype s] [Fintype t] : s.to_finset ⊆ t.to_finset ↔ s ⊆ t :=
  by 
    simp [Finset.subset_iff, Set.subset_def]

@[simp, mono]
theorem to_finset_strict_mono {s t : Set α} [Fintype s] [Fintype t] : s.to_finset ⊂ t.to_finset ↔ s ⊂ t :=
  by 
    rw [←lt_eq_ssubset, ←Finset.lt_iff_ssubset, lt_iff_le_and_ne, lt_iff_le_and_ne]
    simp 

@[simp]
theorem to_finset_disjoint_iff [DecidableEq α] {s t : Set α} [Fintype s] [Fintype t] :
  Disjoint s.to_finset t.to_finset ↔ Disjoint s t :=
  ⟨fun h x hx =>
      h
        (by 
          simpa using hx),
    fun h x hx =>
      h
        (by 
          simpa using hx)⟩

end Set

theorem Finset.card_univ [Fintype α] : (Finset.univ : Finset α).card = Fintype.card α :=
  rfl

theorem Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : s.card = Fintype.card α) : s = univ :=
  eq_of_subset_of_card_le (subset_univ _)$
    by 
      rw [hs, Finset.card_univ]

theorem Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) : s.card = Fintype.card α ↔ s = Finset.univ :=
  ⟨s.eq_univ_of_card,
    by 
      rintro rfl 
      exact Finset.card_univ⟩

theorem Finset.card_le_univ [Fintype α] (s : Finset α) : s.card ≤ Fintype.card α :=
  card_le_of_subset (subset_univ s)

theorem Finset.card_lt_univ_of_not_mem [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s) : s.card < Fintype.card α :=
  card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx'$ mem_univ x)⟩⟩

theorem Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) : s.card < Fintype.card α ↔ s ≠ Finset.univ :=
  s.card_le_univ.lt_iff_ne.trans (not_iff_not_of_iff s.card_eq_iff_eq_univ)

theorem Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset α) :
  («expr ᶜ» s).card < Fintype.card α ↔ s.nonempty :=
  («expr ᶜ» s).card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

theorem Finset.card_univ_diff [DecidableEq α] [Fintype α] (s : Finset α) :
  (Finset.univ \ s).card = Fintype.card α - s.card :=
  Finset.card_sdiff (subset_univ s)

theorem Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) : («expr ᶜ» s).card = Fintype.card α - s.card :=
  Finset.card_univ_diff s

instance (n : ℕ) : Fintype (Finₓ n) :=
  ⟨Finset.finRange n, Finset.mem_fin_range⟩

theorem Finₓ.univ_def (n : ℕ) : (univ : Finset (Finₓ n)) = Finset.finRange n :=
  rfl

@[simp]
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Finₓ n) = n :=
  List.length_fin_range n

@[simp]
theorem Finset.card_fin (n : ℕ) : Finset.card (Finset.univ : Finset (Finₓ n)) = n :=
  by 
    rw [Finset.card_univ, Fintype.card_fin]

/-- `fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
theorem fin_injective : Function.Injective Finₓ :=
  fun m n h => (Fintype.card_fin m).symm.trans$ (Fintype.card_congr$ Equiv.cast h).trans (Fintype.card_fin n)

/-- A reversed version of `fin.cast_eq_cast` that is easier to rewrite with. -/
theorem Finₓ.cast_eq_cast' {n m : ℕ} (h : Finₓ n = Finₓ m) : cast h = «expr⇑ » (Finₓ.cast$ fin_injective h) :=
  (Finₓ.cast_eq_cast _).symm

/-- The cardinality of `fin (bit0 k)` is even, `fact` version.
This `fact` is needed as an instance by `matrix.special_linear_group.has_neg`. -/
theorem Fintype.card_fin_even {k : ℕ} : Fact (Even (Fintype.card (Finₓ (bit0 k)))) :=
  ⟨by 
      rw [Fintype.card_fin]
      exact even_bit0 k⟩

theorem card_finset_fin_le {n : ℕ} (s : Finset (Finₓ n)) : s.card ≤ n :=
  by 
    simpa only [Fintype.card_fin] using s.card_le_univ

theorem Finₓ.equiv_iff_eq {m n : ℕ} : Nonempty (Finₓ m ≃ Finₓ n) ↔ m = n :=
  ⟨fun ⟨h⟩ =>
      by 
        simpa using Fintype.card_congr h,
    fun h => ⟨Equiv.cast$ h ▸ rfl⟩⟩

@[simp]
theorem Finₓ.image_succ_above_univ {n : ℕ} (i : Finₓ (n+1)) : univ.Image i.succ_above = «expr ᶜ» {i} :=
  by 
    ext m 
    simp 

@[simp]
theorem Finₓ.image_succ_univ (n : ℕ) : (univ : Finset (Finₓ n)).Image Finₓ.succ = «expr ᶜ» {0} :=
  by 
    rw [←Finₓ.succ_above_zero, Finₓ.image_succ_above_univ]

@[simp]
theorem Finₓ.image_cast_succ (n : ℕ) : (univ : Finset (Finₓ n)).Image Finₓ.castSucc = «expr ᶜ» {Finₓ.last n} :=
  by 
    rw [←Finₓ.succ_above_last, Finₓ.image_succ_above_univ]

/-- Embed `fin n` into `fin (n + 1)` by prepending zero to the `univ` -/
theorem Finₓ.univ_succ (n : ℕ) : (univ : Finset (Finₓ (n+1))) = insert 0 (univ.Image Finₓ.succ) :=
  by 
    simp 

/-- Embed `fin n` into `fin (n + 1)` by appending a new `fin.last n` to the `univ` -/
theorem Finₓ.univ_cast_succ (n : ℕ) : (univ : Finset (Finₓ (n+1))) = insert (Finₓ.last n) (univ.Image Finₓ.castSucc) :=
  by 
    simp 

/-- Embed `fin n` into `fin (n + 1)` by inserting
around a specified pivot `p : fin (n + 1)` into the `univ` -/
theorem Finₓ.univ_succ_above (n : ℕ) (p : Finₓ (n+1)) :
  (univ : Finset (Finₓ (n+1))) = insert p (univ.Image (Finₓ.succAbove p)) :=
  by 
    simp 

@[instance]
def Unique.fintype {α : Type _} [Unique α] : Fintype α :=
  Fintype.ofSubsingleton (default α)

/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance Fintype.subtypeEq (y : α) : Fintype { x // x = y } :=
  Fintype.subtype {y}
    (by 
      simp )

/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance Fintype.subtypeEq' (y : α) : Fintype { x // y = x } :=
  Fintype.subtype {y}
    (by 
      simp [eq_comm])

@[simp]
theorem univ_unique {α : Type _} [Unique α] [f : Fintype α] : @Finset.univ α _ = {default α} :=
  by 
    rw [Subsingleton.elimₓ f (@Unique.fintype α _)] <;> rfl

@[simp]
theorem univ_is_empty {α : Type _} [IsEmpty α] [Fintype α] : @Finset.univ α _ = ∅ :=
  Finset.ext isEmptyElim

@[simp]
theorem Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] : Fintype.card { x // x = y } = 1 :=
  Fintype.card_unique

@[simp]
theorem Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] : Fintype.card { x // y = x } = 1 :=
  Fintype.card_unique

@[simp]
theorem Fintype.univ_empty : @univ Empty _ = ∅ :=
  rfl

@[simp]
theorem Fintype.card_empty : Fintype.card Empty = 0 :=
  rfl

@[simp]
theorem Fintype.univ_pempty : @univ Pempty _ = ∅ :=
  rfl

@[simp]
theorem Fintype.card_pempty : Fintype.card Pempty = 0 :=
  rfl

instance : Fintype Unit :=
  Fintype.ofSubsingleton ()

theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl

theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl

instance : Fintype PUnit :=
  Fintype.ofSubsingleton PUnit.unit

@[simp]
theorem Fintype.univ_punit : @univ PUnit _ = {PUnit.unit} :=
  rfl

@[simp]
theorem Fintype.card_punit : Fintype.card PUnit = 1 :=
  rfl

instance : Fintype Bool :=
  ⟨⟨tt ::ₘ ff ::ₘ 0,
      by 
        simp ⟩,
    fun x =>
      by 
        cases x <;> simp ⟩

@[simp]
theorem Fintype.univ_bool : @univ Bool _ = {tt, ff} :=
  rfl

instance UnitsInt.fintype : Fintype (Units ℤ) :=
  ⟨{1, -1},
    fun x =>
      by 
        cases Int.units_eq_one_or x <;> simp ⟩

@[simp]
theorem UnitsInt.univ : (Finset.univ : Finset (Units ℤ)) = {1, -1} :=
  rfl

instance Additive.fintype : ∀ [Fintype α], Fintype (Additive α) :=
  id

instance Multiplicative.fintype : ∀ [Fintype α], Fintype (Multiplicative α) :=
  id

@[simp]
theorem Fintype.card_units_int : Fintype.card (Units ℤ) = 2 :=
  rfl

@[simp]
theorem Fintype.card_bool : Fintype.card Bool = 2 :=
  rfl

instance {α : Type _} [Fintype α] : Fintype (Option α) :=
  ⟨univ.insertNone,
    fun a =>
      by 
        simp ⟩

@[simp]
theorem Fintype.card_option {α : Type _} [Fintype α] : Fintype.card (Option α) = Fintype.card α+1 :=
  (Finset.card_cons _).trans$ congr_arg2ₓ _ (card_map _) rfl

instance {α : Type _} (β : α → Type _) [Fintype α] [∀ a, Fintype (β a)] : Fintype (Sigma β) :=
  ⟨univ.Sigma fun _ => univ,
    fun ⟨a, b⟩ =>
      by 
        simp ⟩

@[simp]
theorem Finset.univ_sigma_univ {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] :
  ((univ : Finset α).Sigma fun a => (univ : Finset (β a))) = univ :=
  rfl

instance (α β : Type _) [Fintype α] [Fintype β] : Fintype (α × β) :=
  ⟨univ.product univ,
    fun ⟨a, b⟩ =>
      by 
        simp ⟩

@[simp]
theorem Finset.univ_product_univ {α β : Type _} [Fintype α] [Fintype β] :
  (univ : Finset α).product (univ : Finset β) = univ :=
  rfl

@[simp]
theorem Fintype.card_prod (α β : Type _) [Fintype α] [Fintype β] :
  Fintype.card (α × β) = Fintype.card α*Fintype.card β :=
  card_product _ _

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fintype α :=
  ⟨(Fintype.elems (α × β)).Image Prod.fst,
    fun a =>
      let ⟨b⟩ := ‹Nonempty β›
      by 
        simp  <;> exact ⟨b, Fintype.complete _⟩⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : Fintype β :=
  ⟨(Fintype.elems (α × β)).Image Prod.snd,
    fun b =>
      let ⟨a⟩ := ‹Nonempty α›
      by 
        simp  <;> exact ⟨a, Fintype.complete _⟩⟩

instance (α : Type _) [Fintype α] : Fintype (Ulift α) :=
  Fintype.ofEquiv _ Equiv.ulift.symm

@[simp]
theorem Fintype.card_ulift (α : Type _) [Fintype α] : Fintype.card (Ulift α) = Fintype.card α :=
  Fintype.of_equiv_card _

instance (α : Type _) [Fintype α] : Fintype (Plift α) :=
  Fintype.ofEquiv _ Equiv.plift.symm

@[simp]
theorem Fintype.card_plift (α : Type _) [Fintype α] : Fintype.card (Plift α) = Fintype.card α :=
  Fintype.of_equiv_card _

theorem univ_sum_type {α β : Type _} [Fintype α] [Fintype β] [Fintype (Sum α β)] [DecidableEq (Sum α β)] :
  (univ : Finset (Sum α β)) = map Function.Embedding.inl univ ∪ map Function.Embedding.inr univ :=
  by 
    rw [eq_comm, eq_univ_iff_forall]
    simp only [mem_union, mem_map, exists_prop, mem_univ, true_andₓ]
    rintro (x | y)
    exacts[Or.inl ⟨x, rfl⟩, Or.inr ⟨y, rfl⟩]

instance (α : Type u) (β : Type v) [Fintype α] [Fintype β] : Fintype (Sum α β) :=
  @Fintype.ofEquiv _ _
    (@Sigma.fintype _ (fun b => cond b (Ulift α) (Ulift.{max u v, v} β)) _
      fun b =>
        by 
          cases b <;> apply Ulift.fintype)
    ((Equiv.sumEquivSigmaBool _ _).symm.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift))

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
noncomputable def Fintype.sumLeft {α β} [Fintype (Sum α β)] : Fintype α :=
  Fintype.ofInjective (Sum.inl : α → Sum α β) Sum.inl_injective

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
noncomputable def Fintype.sumRight {α β} [Fintype (Sum α β)] : Fintype β :=
  Fintype.ofInjective (Sum.inr : β → Sum α β) Sum.inr_injective

@[simp]
theorem Fintype.card_sum [Fintype α] [Fintype β] : Fintype.card (Sum α β) = Fintype.card α+Fintype.card β :=
  by 
    classical 
    rw [←Finset.card_univ, univ_sum_type, Finset.card_union_eq]
    ·
      simp [Finset.card_univ]
    ·
      intro x hx 
      suffices  : (∃ a : α, Sum.inl a = x) ∧ ∃ b : β, Sum.inr b = x
      ·
        obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := this 
        simpa using hb 
      simpa using hx

/-- If the subtype of all-but-one elements is a `fintype` then the type itself is a `fintype`. -/
def fintypeOfFintypeNe (a : α) [DecidablePred (· = a)] (h : Fintype { b // b ≠ a }) : Fintype α :=
  Fintype.ofEquiv _$ Equiv.sumCompl (· = a)

section Finset

/-! ### `fintype (s : finset α)` -/


instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩

@[simp]
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl

end Finset

namespace Fintype

variable [Fintype α] [Fintype β]

theorem card_le_of_injective (f : α → β) (hf : Function.Injective f) : card α ≤ card β :=
  Finset.card_le_card_of_inj_on f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h

theorem card_le_of_embedding (f : α ↪ β) : card α ≤ card β :=
  card_le_of_injective f f.2

theorem card_lt_of_injective_of_not_mem (f : α → β) (h : Function.Injective f) {b : β} (w : b ∉ Set.Range f) :
  card α < card β :=
  calc card α = (univ.map ⟨f, h⟩).card := (card_map _).symm 
    _ < card β :=
    Finset.card_lt_univ_of_not_mem$
      by 
        rwa [←mem_coe, coe_map, coe_univ, Set.image_univ]
    

theorem card_lt_of_injective_not_surjective (f : α → β) (h : Function.Injective f) (h' : ¬Function.Surjective f) :
  card α < card β :=
  let ⟨y, hy⟩ := not_forall.1 h' 
  card_lt_of_injective_of_not_mem f h hy

theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
  card_le_of_injective _ (Function.injective_surj_inv h)

/--
The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `fintype` version of `finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
theorem exists_ne_map_eq_of_card_lt (f : α → β) (h : Fintype.card β < Fintype.card α) : ∃ x y, x ≠ y ∧ f x = f y :=
  let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩

theorem card_eq_one_iff : card α = 1 ↔ ∃ x : α, ∀ y, y = x :=
  by 
    rw [←card_unit, card_eq] <;>
      exact
        ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.injective (Subsingleton.elimₓ _ _)⟩,
          fun ⟨x, hx⟩ =>
            ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ => Subsingleton.elimₓ _ _⟩⟩⟩

theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α :=
  by 
    rw [card, Finset.card_eq_zero, univ_eq_empty_iff]

theorem card_eq_zero [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.2 ‹_›

theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
      let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
      ⟨{ default := d, uniq := h }⟩,
    fun ⟨h⟩ =>
      by 
        exact Fintype.card_unique⟩

/-- A `fintype` with cardinality zero is equivalent to `empty`. -/
def card_eq_zero_equiv_equiv_empty : card α = 0 ≃ (α ≃ Empty) :=
  (Equiv.ofIff card_eq_zero_iff).trans (Equiv.equivEmptyEquiv α).symm

theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
  pos_iff_ne_zero.trans$ not_iff_comm.mp$ not_nonempty_iff.trans card_eq_zero_iff.symm

theorem card_pos [h : Nonempty α] : 0 < card α :=
  card_pos_iff.mpr h

theorem card_ne_zero [Nonempty α] : card α ≠ 0 :=
  ne_of_gtₓ card_pos

theorem card_le_one_iff : card α ≤ 1 ↔ ∀ a b : α, a = b :=
  let n := card α 
  have hn : n = card α := rfl 
  match n, hn with 
  | 0 => fun ha => ⟨fun h => fun a => (card_eq_zero_iff.1 ha.symm).elim a, fun _ => ha ▸ Nat.le_succₓ _⟩
  | 1 =>
    fun ha =>
      ⟨fun h =>
          fun a b =>
            let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm 
            by 
              rw [hx a, hx b],
        fun _ => ha ▸ le_reflₓ _⟩
  | n+2 =>
    fun ha =>
      ⟨fun h =>
          by 
            rw [←ha] at h <;>
              exact
                absurd h
                  (by 
                    decide),
        fun h => card_unit ▸ card_le_of_injective (fun _ => ()) fun _ _ _ => h _ _⟩

theorem card_le_one_iff_subsingleton : card α ≤ 1 ↔ Subsingleton α :=
  card_le_one_iff.trans subsingleton_iff.symm

theorem one_lt_card_iff_nontrivial : 1 < card α ↔ Nontrivial α :=
  by 
    classical 
    rw [←not_iff_not]
    pushNeg 
    rw [not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton]

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_ne_of_one_lt_card (h : «expr < »(1, card α)) (a : α) : «expr∃ , »((b : α), «expr ≠ »(b, a)) :=
by { haveI [] [":", expr nontrivial α] [":=", expr one_lt_card_iff_nontrivial.1 h],
  exact [expr exists_ne a] }

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_pair_of_one_lt_card (h : «expr < »(1, card α)) : «expr∃ , »((a b : α), «expr ≠ »(a, b)) :=
by { haveI [] [":", expr nontrivial α] [":=", expr one_lt_card_iff_nontrivial.1 h],
  exact [expr exists_pair_ne α] }

theorem card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
  Fintype.card_eq_one_iff.2 ⟨i, h⟩

theorem one_lt_card [h : Nontrivial α] : 1 < Fintype.card α :=
  Fintype.one_lt_card_iff_nontrivial.mpr h

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem injective_iff_surjective {f : α → α} : «expr ↔ »(injective f, surjective f) :=
by haveI [] [] [":=", expr classical.prop_decidable]; exact [expr have ∀
 {f : α → α}, injective f → surjective f, from λ
 f
 hinj
 x, have h₁ : «expr = »(image f univ, univ) := eq_of_subset_of_card_le (subset_univ _) «expr ▸ »((card_image_of_injective univ hinj).symm, le_refl _),
 have h₂ : «expr ∈ »(x, image f univ) := «expr ▸ »(h₁.symm, mem_univ _),
 exists_of_bex (mem_image.1 h₂),
 ⟨this, λ
  hsurj, has_left_inverse.injective ⟨surj_inv hsurj, left_inverse_of_surjective_of_right_inverse (this (injective_surj_inv _)) (right_inverse_surj_inv _)⟩⟩]

theorem injective_iff_bijective {f : α → α} : injective f ↔ bijective f :=
  by 
    simp [bijective, injective_iff_surjective]

theorem surjective_iff_bijective {f : α → α} : surjective f ↔ bijective f :=
  by 
    simp [bijective, injective_iff_surjective]

theorem injective_iff_surjective_of_equiv {β : Type _} {f : α → β} (e : α ≃ β) : injective f ↔ surjective f :=
  have  : injective (e.symm ∘ f) ↔ surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj =>
      by 
        simpa [Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
    fun hsurj =>
      by 
        simpa [Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

theorem card_of_bijective {f : α → β} (hf : bijective f) : card α = card β :=
  card_congr (Equiv.ofBijective f hf)

theorem bijective_iff_injective_and_card (f : α → β) : bijective f ↔ injective f ∧ card α = card β :=
  by 
    split 
    ·
      intro h 
      exact ⟨h.1, card_of_bijective h⟩
    ·
      rintro ⟨hf, h⟩
      refine' ⟨hf, _⟩
      rwa [←injective_iff_surjective_of_equiv (equiv_of_card_eq h)]

theorem bijective_iff_surjective_and_card (f : α → β) : bijective f ↔ surjective f ∧ card α = card β :=
  by 
    split 
    ·
      intro h 
      exact ⟨h.2, card_of_bijective h⟩
    ·
      rintro ⟨hf, h⟩
      refine' ⟨_, hf⟩
      rwa [injective_iff_surjective_of_equiv (equiv_of_card_eq h)]

theorem right_inverse_of_left_inverse_of_card_le {f : α → β} {g : β → α} (hfg : left_inverse f g)
  (hcard : card α ≤ card β) : RightInverse f g :=
  have hsurj : surjective f := surjective_iff_has_right_inverse.2 ⟨g, hfg⟩
  right_inverse_of_injective_of_left_inverse
    ((bijective_iff_surjective_and_card _).2 ⟨hsurj, le_antisymmₓ hcard (card_le_of_surjective f hsurj)⟩).1 hfg

theorem left_inverse_of_right_inverse_of_card_le {f : α → β} {g : β → α} (hfg : RightInverse f g)
  (hcard : card β ≤ card α) : left_inverse f g :=
  right_inverse_of_left_inverse_of_card_le hfg hcard

end Fintype

theorem Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α → β} :
  «expr↑ » (Finset.image f Finset.univ) = Set.Range f :=
  by 
    ext x 
    simp 

instance List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x ∈ l } :=
  Fintype.ofList l.attach l.mem_attach

instance Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x // x ∈ s } :=
  Fintype.ofMultiset s.attach s.mem_attach

instance Finset.subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩

instance FinsetCoe.fintype (s : Finset α) : Fintype («expr↑ » s : Set α) :=
  Finset.subtype.fintype s

@[simp]
theorem Fintype.card_coe (s : Finset α) : Fintype.card s = s.card :=
  card_attach

theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl

instance Plift.fintypeProp (p : Prop) [Decidable p] : Fintype (Plift p) :=
  ⟨if h : p then {⟨h⟩} else ∅,
    fun ⟨h⟩ =>
      by 
        simp [h]⟩

instance Prop.fintype : Fintype Prop :=
  ⟨⟨True ::ₘ False ::ₘ 0,
      by 
        simp [true_ne_false]⟩,
    Classical.cases
      (by 
        simp )
      (by 
        simp )⟩

@[simp]
theorem Fintype.card_Prop : Fintype.card Prop = 2 :=
  rfl

instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p)
    (by 
      simp )

/-- A set on a fintype, when coerced to a type, is a fintype. -/
def setFintype {α} [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] : Fintype s :=
  Subtype.fintype fun x => x ∈ s

theorem set_fintype_card_le_univ {α : Type _} [Fintype α] (s : Set α) [Fintype («expr↥ » s)] :
  Fintype.card («expr↥ » s) ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype s)

section 

variable (α)

/-- The `units α` type is equivalent to a subtype of `α × α`. -/
@[simps]
def _root_.units_equiv_prod_subtype [Monoidₓ α] : Units α ≃ { p : α × α // (p.1*p.2) = 1 ∧ (p.2*p.1) = 1 } :=
  { toFun := fun u => ⟨(u, «expr↑ » (u⁻¹)), u.val_inv, u.inv_val⟩,
    invFun := fun p => Units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2, left_inv := fun u => Units.ext rfl,
    right_inv := fun p => Subtype.ext$ Prod.extₓ rfl rfl }

/-- In a `group_with_zero` `α`, the unit group `units α` is equivalent to the subtype of nonzero
elements. -/
@[simps]
def _root_.units_equiv_ne_zero [GroupWithZeroₓ α] : Units α ≃ { a : α // a ≠ 0 } :=
  ⟨fun a => ⟨a, a.ne_zero⟩, fun a => Units.mk0 _ a.prop, fun _ => Units.ext rfl, fun _ => Subtype.ext rfl⟩

end 

instance [Monoidₓ α] [Fintype α] [DecidableEq α] : Fintype (Units α) :=
  Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem fintype.card_units
[group_with_zero α]
[fintype α]
[fintype (units α)] : «expr = »(fintype.card (units α), «expr - »(fintype.card α, 1)) :=
begin
  classical,
  rw ["[", expr eq_comm, ",", expr nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : α)⟩), ",", expr fintype.card_congr (units_equiv_ne_zero α), "]"] [],
  have [] [] [":=", expr fintype.card_congr (equiv.sum_compl ((«expr = » (0 : α)))).symm],
  rwa ["[", expr fintype.card_sum, ",", expr add_comm, ",", expr fintype.card_subtype_eq, "]"] ["at", ident this]
end

namespace Function.Embedding

/-- An embedding from a `fintype` to itself can be promoted to an equivalence. -/
noncomputable def equiv_of_fintype_self_embedding [Fintype α] (e : α ↪ α) : α ≃ α :=
  Equiv.ofBijective e (Fintype.injective_iff_bijective.1 e.2)

@[simp]
theorem equiv_of_fintype_self_embedding_to_embedding [Fintype α] (e : α ↪ α) :
  e.equiv_of_fintype_self_embedding.to_embedding = e :=
  by 
    ext 
    rfl

/-- If `‖β‖ < ‖α‖` there are no embeddings `α ↪ β`.
This is a formulation of the pigeonhole principle.

Note this cannot be an instance as it needs `h`. -/
@[simp]
theorem is_empty_of_card_lt [Fintype α] [Fintype β] (h : Fintype.card β < Fintype.card α) : IsEmpty (α ↪ β) :=
  ⟨fun f =>
      let ⟨x, y, Ne, feq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h 
      Ne$ f.injective feq⟩

/-- A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ card β`. -/
def trunc_of_card_le [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (h : Fintype.card α ≤ Fintype.card β) :
  Trunc (α ↪ β) :=
  (Fintype.truncEquivFin α).bind$
    fun ea =>
      (Fintype.truncEquivFin β).map$
        fun eb => ea.to_embedding.trans ((Finₓ.castLe h).toEmbedding.trans eb.symm.to_embedding)

theorem nonempty_of_card_le [Fintype α] [Fintype β] (h : Fintype.card α ≤ Fintype.card β) : Nonempty (α ↪ β) :=
  by 
    classical 
    exact (trunc_of_card_le h).Nonempty

theorem exists_of_card_le_finset [Fintype α] {s : Finset β} (h : Fintype.card α ≤ s.card) :
  ∃ f : α ↪ β, Set.Range f ⊆ s :=
  by 
    rw [←Fintype.card_coe] at h 
    rcases nonempty_of_card_le h with ⟨f⟩
    exact
      ⟨f.trans (embedding.subtype _),
        by 
          simp [Set.range_subset_iff]⟩

end Function.Embedding

@[simp]
theorem Finset.univ_map_embedding {α : Type _} [Fintype α] (e : α ↪ α) : univ.map e = univ :=
  by 
    rw [←e.equiv_of_fintype_self_embedding_to_embedding, univ_map_equiv_to_embedding]

namespace Fintype

theorem card_lt_of_surjective_not_injective [Fintype α] [Fintype β] (f : α → β) (h : Function.Surjective f)
  (h' : ¬Function.Injective f) : card β < card α :=
  card_lt_of_injective_not_surjective _ (Function.injective_surj_inv h)$
    fun hg =>
      have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surj_inv h, hg⟩
      h'$ (injective_iff_surjective_of_equiv (Equiv.ofBijective _ w).symm).mpr h

variable [DecidableEq α] [Fintype α] {δ : α → Type _}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `fintype.pi_finset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ finset.univ` in the `finset.pi` definition). -/
def pi_finset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map
    ⟨fun f a => f a (mem_univ a),
      fun _ _ =>
        by 
          simp [Function.funext_iffₓ]⟩

@[simp]
theorem mem_pi_finset {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a} : f ∈ pi_finset t ↔ ∀ a, f a ∈ t a :=
  by 
    split 
    ·
      simp only [pi_finset, mem_map, and_imp, forall_prop_of_true, exists_prop, mem_univ, exists_imp_distrib, mem_pi]
      rintro g hg hgf a 
      rw [←hgf]
      exact hg a
    ·
      simp only [pi_finset, mem_map, forall_prop_of_true, exists_prop, mem_univ, mem_pi]
      exact fun hf => ⟨fun a ha => f a, hf, rfl⟩

@[simp]
theorem coe_pi_finset (t : ∀ a, Finset (δ a)) : (pi_finset t : Set (∀ a, δ a)) = Set.Pi Set.Univ fun a => t a :=
  by 
    ext 
    simp 

theorem pi_finset_subset (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) : pi_finset t₁ ⊆ pi_finset t₂ :=
  fun g hg => mem_pi_finset.2$ fun a => h a$ mem_pi_finset.1 hg a

theorem pi_finset_disjoint_of_disjoint [∀ a, DecidableEq (δ a)] (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
  (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (pi_finset t₁) (pi_finset t₂) :=
  disjoint_iff_ne.2$
    fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
      disjoint_iff_ne.1 h (f₁ a) (mem_pi_finset.1 hf₁ a) (f₂ a) (mem_pi_finset.1 hf₂ a) (congr_funₓ eq₁₂ a)

end Fintype

/-! ### pi -/


/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance Pi.fintype {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
  Fintype (∀ a, β a) :=
  ⟨Fintype.piFinset fun _ => univ,
    by 
      simp ⟩

@[simp]
theorem Fintype.pi_finset_univ {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
  (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) = (Finset.univ : Finset (∀ a, β a)) :=
  rfl

instance DArray.fintype {n : ℕ} {α : Finₓ n → Type _} [∀ n, Fintype (α n)] : Fintype (DArray n α) :=
  Fintype.ofEquiv _ (Equiv.dArrayEquivFin _).symm

instance Arrayₓ.fintype {n : ℕ} {α : Type _} [Fintype α] : Fintype (Arrayₓ n α) :=
  DArray.fintype

instance Vector.fintype {α : Type _} [Fintype α] {n : ℕ} : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm

instance Quotientₓ.fintype [Fintype α] (s : Setoidₓ α) [DecidableRel (· ≈ · : α → α → Prop)] : Fintype (Quotientₓ s) :=
  Fintype.ofSurjective Quotientₓ.mk fun x => Quotientₓ.induction_on x fun x => ⟨x, rfl⟩

instance Finset.fintype [Fintype α] : Fintype (Finset α) :=
  ⟨univ.Powerset, fun x => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:927:38: unsupported irreducible non-definition
@[irreducible]
instance function.embedding.fintype
{α β}
[fintype α]
[fintype β]
[decidable_eq α]
[decidable_eq β] : fintype «expr ↪ »(α, β) :=
fintype.of_equiv _ (equiv.subtype_injective_equiv_embedding α β)

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) :=
  Quotientₓ.fintype _

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  Fintype.ofEquiv _ Sym.symEquivSym'.symm

@[simp]
theorem Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Finset.card_powerset Finset.univ

@[simp]
theorem Finset.univ_filter_card_eq (α : Type _) [Fintype α] (k : ℕ) :
  ((Finset.univ : Finset (Finset α)).filter fun s => s.card = k) = Finset.univ.powersetLen k :=
  by 
    ext 
    simp [Finset.mem_powerset_len]

@[simp]
theorem Fintype.card_finset_len [Fintype α] (k : ℕ) :
  Fintype.card { s : Finset α // s.card = k } = Nat.choose (Fintype.card α) k :=
  by 
    simp [Fintype.subtype_card, Finset.card_univ]

@[simp]
theorem Set.to_finset_univ [Fintype α] : (Set.Univ : Set α).toFinset = Finset.univ :=
  by 
    ext 
    simp only [Set.mem_univ, mem_univ, Set.mem_to_finset]

@[simp]
theorem Set.to_finset_eq_empty_iff {s : Set α} [Fintype s] : s.to_finset = ∅ ↔ s = ∅ :=
  by 
    simp [ext_iff, Set.ext_iff]

@[simp]
theorem Set.to_finset_empty : (∅ : Set α).toFinset = ∅ :=
  Set.to_finset_eq_empty_iff.mpr rfl

@[simp]
theorem Set.to_finset_range [DecidableEq α] [Fintype β] (f : β → α) [Fintype (Set.Range f)] :
  (Set.Range f).toFinset = Finset.univ.Image f :=
  by 
    simp [ext_iff]

theorem Fintype.card_subtype_le [Fintype α] (p : α → Prop) [DecidablePred p] :
  Fintype.card { x // p x } ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype _)

theorem Fintype.card_subtype_lt [Fintype α] {p : α → Prop} [DecidablePred p] {x : α} (hx : ¬p x) :
  Fintype.card { x // p x } < Fintype.card α :=
  Fintype.card_lt_of_injective_of_not_mem coeₓ Subtype.coe_injective$
    by 
      rwa [Subtype.range_coe_subtype]

theorem Fintype.card_subtype [Fintype α] (p : α → Prop) [DecidablePred p] :
  Fintype.card { x // p x } = ((Finset.univ : Finset α).filter p).card :=
  by 
    refine' Fintype.card_of_subtype _ _ 
    simp 

theorem Fintype.card_subtype_or (p q : α → Prop) [Fintype { x // p x }] [Fintype { x // q x }]
  [Fintype { x // p x ∨ q x }] :
  Fintype.card { x // p x ∨ q x } ≤ Fintype.card { x // p x }+Fintype.card { x // q x } :=
  by 
    classical 
    convert Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
    rw [Fintype.card_sum]

theorem Fintype.card_subtype_or_disjoint (p q : α → Prop) (h : Disjoint p q) [Fintype { x // p x }]
  [Fintype { x // q x }] [Fintype { x // p x ∨ q x }] :
  Fintype.card { x // p x ∨ q x } = Fintype.card { x // p x }+Fintype.card { x // q x } :=
  by 
    classical 
    convert Fintype.card_congr (subtypeOrEquiv p q h)
    simp 

theorem Fintype.card_quotient_le [Fintype α] (s : Setoidₓ α) [DecidableRel (· ≈ · : α → α → Prop)] :
  Fintype.card (Quotientₓ s) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective _ (surjective_quotient_mk _)

theorem Fintype.card_quotient_lt [Fintype α] {s : Setoidₓ α} [DecidableRel (· ≈ · : α → α → Prop)] {x y : α}
  (h1 : x ≠ y) (h2 : x ≈ y) : Fintype.card (Quotientₓ s) < Fintype.card α :=
  Fintype.card_lt_of_surjective_not_injective _ (surjective_quotient_mk _)$ fun w => h1 (w$ Quotientₓ.eq.mpr h2)

instance Psigma.fintype {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] : Fintype (Σ'a, β a) :=
  Fintype.ofEquiv _ (Equiv.psigmaEquivSigma _).symm

instance Psigma.fintypePropLeft {α : Prop} {β : α → Type _} [Decidable α] [∀ a, Fintype (β a)] : Fintype (Σ'a, β a) :=
  if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, Psigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩ else
    ⟨∅, fun x => h x.1⟩

instance Psigma.fintypePropRight {α : Type _} {β : α → Prop} [∀ a, Decidable (β a)] [Fintype α] : Fintype (Σ'a, β a) :=
  Fintype.ofEquiv { a // β a } ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => rfl, fun ⟨x, y⟩ => rfl⟩

instance Psigma.fintypePropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] : Fintype (Σ'a, β a) :=
  if h : ∃ a, β a then
    ⟨{⟨h.fst, h.snd⟩},
      fun ⟨_, _⟩ =>
        by 
          simp ⟩
  else ⟨∅, fun ⟨x, y⟩ => h ⟨x, y⟩⟩

instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ α _).Powerset.map ⟨coeₓ, coe_injective⟩,
    fun s =>
      by 
        classical 
        refine' mem_map.2 ⟨finset.univ.filter s, mem_powerset.2 (subset_univ _), _⟩
        apply (coe_filter _ _).trans 
        rw [coe_univ, Set.sep_univ]
        rfl⟩

@[simp]
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)

instance pfunFintype (p : Prop) [Decidable p] (α : p → Type _) [∀ hp, Fintype (α hp)] : Fintype (∀ hp : p, α hp) :=
  if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩ else
    ⟨singleton fun h => (hp h).elim,
      by 
        simp [hp, Function.funext_iffₓ]⟩

@[simp]
theorem Finset.univ_pi_univ {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
  (Finset.univ.pi fun a : α => (Finset.univ : Finset (β a))) = Finset.univ :=
  by 
    ext 
    simp 

theorem mem_image_univ_iff_mem_range {α β : Type _} [Fintype α] [DecidableEq β] {f : α → β} {b : β} :
  b ∈ univ.Image f ↔ b ∈ Set.Range f :=
  by 
    simp 

/-- An auxiliary function for `quotient.fin_choice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def Quotientₓ.finChoiceAux {ι : Type _} [DecidableEq ι] {α : ι → Type _} [S : ∀ i, Setoidₓ (α i)] :
  ∀ l : List ι,
    (∀ i _ : i ∈ l, Quotientₓ (S i)) →
      @Quotientₓ (∀ i _ : i ∈ l, α i)
        (by 
          infer_instance)
| [], f => «expr⟦ ⟧» fun i => False.elim
| i :: l, f =>
  by 
    refine'
      Quotientₓ.liftOn₂ (f i (List.mem_cons_selfₓ _ _))
        (Quotientₓ.finChoiceAux l fun j h => f j (List.mem_cons_of_memₓ _ h)) _ _ 
    exact
      fun a l =>
        «expr⟦ ⟧»
          fun j h =>
            if e : j = i then
              by 
                rw [e] <;> exact a
            else l _ (h.resolve_left e)
    refine' fun a₁ l₁ a₂ l₂ h₁ h₂ => Quotientₓ.sound fun j h => _ 
    byCases' e : j = i <;> simp [e]
    ·
      subst j 
      exact h₁
    ·
      exact h₂ _ _

theorem Quotientₓ.fin_choice_aux_eq {ι : Type _} [DecidableEq ι] {α : ι → Type _} [S : ∀ i, Setoidₓ (α i)] :
  ∀ l : List ι f : ∀ i _ : i ∈ l, α i, (Quotientₓ.finChoiceAux l fun i h => «expr⟦ ⟧» (f i h)) = «expr⟦ ⟧» f
| [], f => Quotientₓ.sound fun i h => h.elim
| i :: l, f =>
  by 
    simp [Quotientₓ.finChoiceAux, Quotientₓ.fin_choice_aux_eq l]
    refine' Quotientₓ.sound fun j h => _ 
    byCases' e : j = i <;> simp [e]
    subst j 
    rfl

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def quotient.fin_choice
{ι : Type*}
[decidable_eq ι]
[fintype ι]
{α : ι → Type*}
[S : ∀ i, setoid (α i)]
(f : ∀ i, quotient (S i)) : @quotient (∀ i, α i) (by apply_instance) :=
quotient.lift_on (@quotient.rec_on _ _ (λ
  l : multiset ι, @quotient (∀
   i «expr ∈ » l, α i) (by apply_instance)) finset.univ.1 (λ
  l, quotient.fin_choice_aux l (λ
   i
   _, f i)) (λ a b h, begin
    have [] [] [":=", expr λ a, quotient.fin_choice_aux_eq a (λ i h, quotient.out (f i))],
    simp [] [] [] ["[", expr quotient.out_eq, "]"] [] ["at", ident this],
    simp [] [] [] ["[", expr this, "]"] [] [],
    let [ident g] [] [":=", expr λ a : multiset ι, «expr⟦ ⟧»(λ (i : ι) (h : «expr ∈ »(i, a)), quotient.out (f i))],
    refine [expr eq_of_heq ((eq_rec_heq _ _).trans (_ : «expr == »(g a, g b)))],
    congr' [1] [],
    exact [expr quotient.sound h]
  end)) (λ f, «expr⟦ ⟧»(λ i, f i (finset.mem_univ _))) (λ a b h, «expr $ »(quotient.sound, λ i, h _ _))

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem quotient.fin_choice_eq
{ι : Type*}
[decidable_eq ι]
[fintype ι]
{α : ι → Type*}
[∀ i, setoid (α i)]
(f : ∀ i, α i) : «expr = »(quotient.fin_choice (λ i, «expr⟦ ⟧»(f i)), «expr⟦ ⟧»(f)) :=
begin
  let [ident q] [] [],
  swap,
  change [expr «expr = »(quotient.lift_on q _ _, _)] [] [],
  have [] [":", expr «expr = »(q, «expr⟦ ⟧»(λ i h, f i))] [],
  { dsimp [] ["[", expr q, "]"] [] [],
    exact [expr quotient.induction_on (@finset.univ ι _).1 (λ l, quotient.fin_choice_aux_eq _ _)] },
  simp [] [] [] ["[", expr this, "]"] [] [],
  exact [expr setoid.refl _]
end

section Equiv

open List Equiv Equiv.Perm

variable [DecidableEq α] [DecidableEq β]

/-- Given a list, produce a list of all permutations of its elements. -/
def permsOfList : List α → List (perm α)
| [] => [1]
| a :: l => permsOfList l ++ l.bind fun b => (permsOfList l).map fun f => swap a b*f

theorem length_perms_of_list : ∀ l : List α, length (permsOfList l) = l.length !
| [] => rfl
| a :: l =>
  by 
    rw [length_cons, Nat.factorial_succ]
    simp [permsOfList, length_bind, length_perms_of_list, Function.comp, Nat.succ_mul]
    cc

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mem_perms_of_list_of_mem
{l : list α}
{f : perm α}
(h : ∀ x, «expr ≠ »(f x, x) → «expr ∈ »(x, l)) : «expr ∈ »(f, perms_of_list l) :=
begin
  induction [expr l] [] ["with", ident a, ident l, ident IH] ["generalizing", ident f, ident h],
  { exact [expr list.mem_singleton.2 «expr $ »(equiv.ext, λ x, «expr $ »(decidable.by_contradiction, h _))] },
  by_cases [expr hfa, ":", expr «expr = »(f a, a)],
  { refine [expr mem_append_left _ (IH (λ x hx, mem_of_ne_of_mem _ (h x hx)))],
    rintro [ident rfl],
    exact [expr hx hfa] },
  have [ident hfa'] [":", expr «expr ≠ »(f (f a), f a)] [":=", expr mt (λ h, f.injective h) hfa],
  have [] [":", expr ∀ x : α, «expr ≠ »(«expr * »(swap a (f a), f) x, x) → «expr ∈ »(x, l)] [],
  { intros [ident x, ident hx],
    have [ident hxa] [":", expr «expr ≠ »(x, a)] [],
    { rintro [ident rfl],
      apply [expr hx],
      simp [] [] ["only"] ["[", expr mul_apply, ",", expr swap_apply_right, "]"] [] [] },
    refine [expr list.mem_of_ne_of_mem hxa (h x (λ h, _))],
    simp [] [] ["only"] ["[", expr h, ",", expr mul_apply, ",", expr swap_apply_def, ",", expr mul_apply, ",", expr ne.def, ",", expr apply_eq_iff_eq, "]"] [] ["at", ident hx]; split_ifs ["at", ident hx] [],
    exacts ["[", expr hxa (h.symm.trans h_1), ",", expr hx h, "]"] },
  suffices [] [":", expr «expr ∨ »(«expr ∈ »(f, perms_of_list l), «expr∃ , »((b «expr ∈ » l)
     (g «expr ∈ » perms_of_list l), «expr = »(«expr * »(swap a b, g), f)))],
  { simpa [] [] ["only"] ["[", expr perms_of_list, ",", expr exists_prop, ",", expr list.mem_map, ",", expr mem_append, ",", expr list.mem_bind, "]"] [] [] },
  refine [expr or_iff_not_imp_left.2 (λ hfl, ⟨f a, _, «expr * »(swap a (f a), f), IH this, _⟩)],
  { by_cases [expr hffa, ":", expr «expr = »(f (f a), a)],
    { exact [expr mem_of_ne_of_mem hfa (h _ (mt (λ h, f.injective h) hfa))] },
    { apply [expr this],
      simp [] [] ["only"] ["[", expr mul_apply, ",", expr swap_apply_def, ",", expr mul_apply, ",", expr ne.def, ",", expr apply_eq_iff_eq, "]"] [] [],
      split_ifs [] []; cc } },
  { rw ["[", "<-", expr mul_assoc, ",", expr mul_def (swap a (f a)) (swap a (f a)), ",", expr swap_swap, ",", "<-", expr perm.one_def, ",", expr one_mul, "]"] [] }
end

theorem mem_of_mem_perms_of_list : ∀ {l : List α} {f : perm α}, f ∈ permsOfList l → ∀ {x}, f x ≠ x → x ∈ l
| [], f, h =>
  have  : f = 1 :=
    by 
      simpa [permsOfList] using h 
  by 
    rw [this] <;> simp 
| a :: l, f, h =>
  (mem_append.1 h).elim (fun h x hx => mem_cons_of_mem _ (mem_of_mem_perms_of_list h hx))
    fun h x hx =>
      let ⟨y, hy, hy'⟩ := List.mem_bindₓ.1 h 
      let ⟨g, hg₁, hg₂⟩ := List.mem_mapₓ.1 hy' 
      if hxa : x = a then
        by 
          simp [hxa]
      else
        if hxy : x = y then
          mem_cons_of_mem _$
            by 
              rwa [hxy]
        else
          mem_cons_of_mem _$
            mem_of_mem_perms_of_list hg₁$
              by 
                rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def] <;> splitIfs <;> cc

theorem mem_perms_of_list_iff {l : List α} {f : perm α} : f ∈ permsOfList l ↔ ∀ {x}, f x ≠ x → x ∈ l :=
  ⟨mem_of_mem_perms_of_list, mem_perms_of_list_of_mem⟩

theorem nodup_perms_of_list : ∀ {l : List α} hl : l.nodup, (permsOfList l).Nodup
| [], hl =>
  by 
    simp [permsOfList]
| a :: l, hl =>
  have hl' : l.nodup := nodup_of_nodup_cons hl 
  have hln' : (permsOfList l).Nodup := nodup_perms_of_list hl' 
  have hmeml : ∀ {f : perm α}, f ∈ permsOfList l → f a = a :=
    fun f hf => not_not.1 (mt (mem_of_mem_perms_of_list hf) (nodup_cons.1 hl).1)
  by 
    rw [permsOfList, List.nodup_append, List.nodup_bind, pairwise_iff_nth_le] <;>
      exact
        ⟨hln',
          ⟨fun _ _ => nodup_map (fun _ _ => mul_left_cancelₓ) hln',
            fun i j hj hij x hx₁ hx₂ =>
              let ⟨f, hf⟩ := List.mem_mapₓ.1 hx₁ 
              let ⟨g, hg⟩ := List.mem_mapₓ.1 hx₂ 
              have hix : x a = nth_le l i (lt_transₓ hij hj) :=
                by 
                  rw [←hf.2, mul_apply, hmeml hf.1, swap_apply_left]
              have hiy : x a = nth_le l j hj :=
                by 
                  rw [←hg.2, mul_apply, hmeml hg.1, swap_apply_left]
              absurd (hf.2.trans hg.2.symm)$
                fun h =>
                  ne_of_ltₓ hij$
                    nodup_iff_nth_le_inj.1 hl' i j (lt_transₓ hij hj) hj$
                      by 
                        rw [←hix, hiy]⟩,
          fun f hf₁ hf₂ =>
            let ⟨x, hx, hx'⟩ := List.mem_bindₓ.1 hf₂ 
            let ⟨g, hg⟩ := List.mem_mapₓ.1 hx' 
            have hgxa : (g⁻¹) x = a :=
              f.injective$
                by 
                  rw [hmeml hf₁, ←hg.2] <;> simp 
            have hxa : x ≠ a := fun h => (List.nodup_cons.1 hl).1 (h ▸ hx)
            (List.nodup_cons.1 hl).1$
              hgxa ▸
                mem_of_mem_perms_of_list hg.1
                  (by 
                    rwa [apply_inv_self, hgxa])⟩

/-- Given a finset, produce the finset of all permutations of its elements. -/
def permsOfFinset (s : Finset α) : Finset (perm α) :=
  Quotientₓ.hrecOn s.1 (fun l hl => ⟨permsOfList l, nodup_perms_of_list hl⟩)
    (fun a b hab =>
      hfunext (congr_argₓ _ (Quotientₓ.sound hab))
        fun ha hb _ =>
          heq_of_eq$
            Finset.ext$
              by 
                simp [mem_perms_of_list_iff, hab.mem_iff])
    s.2

theorem mem_perms_of_finset_iff : ∀ {s : Finset α} {f : perm α}, f ∈ permsOfFinset s ↔ ∀ {x}, f x ≠ x → x ∈ s :=
  by 
    rintro ⟨⟨l⟩, hs⟩ f <;> exact mem_perms_of_list_iff

theorem card_perms_of_finset : ∀ s : Finset α, (permsOfFinset s).card = s.card ! :=
  by 
    rintro ⟨⟨l⟩, hs⟩ <;> exact length_perms_of_list l

/-- The collection of permutations of a fintype is a fintype. -/
def fintypePerm [Fintype α] : Fintype (perm α) :=
  ⟨permsOfFinset (@Finset.univ α _),
    by 
      simp [mem_perms_of_finset_iff]⟩

instance [Fintype α] [Fintype β] : Fintype (α ≃ β) :=
  if h : Fintype.card β = Fintype.card α then
    Trunc.recOnSubsingleton (Fintype.truncEquivFin α)
      fun eα =>
        Trunc.recOnSubsingleton (Fintype.truncEquivFin β)
          fun eβ =>
            @Fintype.ofEquiv _ (perm α) fintypePerm
              (equiv_congr (Equiv.refl α) (eα.trans (Eq.recOnₓ h eβ.symm)) : α ≃ α ≃ (α ≃ β))
  else ⟨∅, fun x => False.elim (h (Fintype.card_eq.2 ⟨x.symm⟩))⟩

theorem Fintype.card_perm [Fintype α] : Fintype.card (perm α) = (Fintype.card α)! :=
  Subsingleton.elimₓ (@fintypePerm α _ _) (@Equiv.fintype α α _ _ _ _) ▸ card_perms_of_finset _

theorem Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) : Fintype.card (α ≃ β) = (Fintype.card α)! :=
  Fintype.card_congr (equiv_congr (Equiv.refl α) e) ▸ Fintype.card_perm

theorem univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α = 1) : (univ : Finset α) = {x} :=
  by 
    symm 
    apply eq_of_subset_of_card_le (subset_univ {x})
    apply le_of_eqₓ 
    simp [h, Finset.card_univ]

end Equiv

namespace Fintype

section Choose

open Fintype Equiv

variable [Fintype α] (p : α → Prop) [DecidablePred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x (hp : ∃!a : α, p a) : { a // p a } :=
  ⟨Finset.choose p univ
      (by 
        simp  <;> exact hp),
    Finset.choose_property _ _ _⟩

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃!a, p a) : α :=
  choose_x p hp

theorem choose_spec (hp : ∃!a, p a) : p (choose p hp) :=
  (choose_x p hp).property

@[simp]
theorem choose_subtype_eq {α : Type _} (p : α → Prop) [Fintype { a : α // p a }] [DecidableEq α] (x : { a : α // p a })
  (h : ∃!a : { a // p a }, (a : α) = x :=
    ⟨x, rfl,
      fun y hy =>
        by 
          simpa [Subtype.ext_iff] using hy⟩) :
  Fintype.choose (fun y : { a : α // p a } => (y : α) = x) h = x :=
  by 
    rw [Subtype.ext_iff, Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]

end Choose

section BijectionInverse

open Function

variable [Fintype α] [DecidableEq β] {f : α → β}

/--
`bij_inv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `function.inv_fun`. -/
def bij_inv (f_bij : bijective f) (b : β) : α :=
  Fintype.choose (fun a => f a = b)
    (by 
      rcases f_bij.right b with ⟨a', fa_eq_b⟩
      rw [←fa_eq_b]
      exact ⟨a', ⟨rfl, fun a h => f_bij.left h⟩⟩)

theorem left_inverse_bij_inv (f_bij : bijective f) : left_inverse (bij_inv f_bij) f :=
  fun a => f_bij.left (choose_spec (fun a' => f a' = f a) _)

theorem right_inverse_bij_inv (f_bij : bijective f) : RightInverse (bij_inv f_bij) f :=
  fun b => choose_spec (fun a' => f a' = b) _

theorem bijective_bij_inv (f_bij : bijective f) : bijective (bij_inv f_bij) :=
  ⟨(right_inverse_bij_inv _).Injective, (left_inverse_bij_inv _).Surjective⟩

end BijectionInverse

theorem well_founded_of_trans_of_irrefl [Fintype α] (r : α → α → Prop) [IsTrans α r] [IsIrrefl α r] : WellFounded r :=
  by 
    classical <;>
      exact
        have  : ∀ x y, r x y → (univ.filter fun z => r z x).card < (univ.filter fun z => r z y).card :=
          fun x y hxy =>
            Finset.card_lt_card$
              by 
                simp only [finset.lt_iff_ssubset.symm, lt_iff_le_not_leₓ, Finset.le_iff_subset, Finset.subset_iff,
                    mem_filter, true_andₓ, mem_univ, hxy] <;>
                  exact ⟨fun z hzx => trans hzx hxy, not_forall_of_exists_not ⟨x, not_imp.2 ⟨hxy, irrefl x⟩⟩⟩
        Subrelation.wfₓ this (measure_wf _)

theorem preorder.well_founded [Fintype α] [Preorderₓ α] : WellFounded (· < · : α → α → Prop) :=
  well_founded_of_trans_of_irrefl _

@[instance]
theorem linear_order.is_well_order [Fintype α] [LinearOrderₓ α] : IsWellOrder α (· < ·) :=
  { wf := preorder.well_founded }

end Fintype

/-- A type is said to be infinite if it has no fintype instance.
  Note that `infinite α` is equivalent to `is_empty (fintype α)`. -/
class Infinite (α : Type _) : Prop where 
  not_fintype : Fintype α → False

theorem not_fintype (α : Type _) [h1 : Infinite α] [h2 : Fintype α] : False :=
  Infinite.not_fintype h2

protected theorem Fintype.false {α : Type _} [Infinite α] (h : Fintype α) : False :=
  not_fintype α

protected theorem Infinite.false {α : Type _} [Fintype α] (h : Infinite α) : False :=
  not_fintype α

@[simp]
theorem is_empty_fintype {α : Type _} : IsEmpty (Fintype α) ↔ Infinite α :=
  ⟨fun ⟨x⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨x⟩⟩

/-- A non-infinite type is a fintype. -/
noncomputable def fintypeOfNotInfinite {α : Type _} (h : ¬Infinite α) : Fintype α :=
  Nonempty.some$
    by 
      rwa [←not_is_empty_iff, is_empty_fintype]

section 

open_locale Classical

/--
Any type is (classically) either a `fintype`, or `infinite`.

One can obtain the relevant typeclasses via `cases fintype_or_infinite α; resetI`.
-/
noncomputable def fintypeOrInfinite (α : Type _) : Psum (Fintype α) (Infinite α) :=
  if h : Infinite α then Psum.inr h else Psum.inl (fintypeOfNotInfinite h)

end 

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finset.exists_minimal
{α : Type*}
[preorder α]
(s : finset α)
(h : s.nonempty) : «expr∃ , »((m «expr ∈ » s), ∀ x «expr ∈ » s, «expr¬ »(«expr < »(x, m))) :=
begin
  obtain ["⟨", ident c, ",", ident hcs, ":", expr «expr ∈ »(c, s), "⟩", ":=", expr h],
  have [] [":", expr well_founded (@has_lt.lt {x // «expr ∈ »(x, s)} _)] [":=", expr fintype.well_founded_of_trans_of_irrefl _],
  obtain ["⟨", "⟨", ident m, ",", ident hms, ":", expr «expr ∈ »(m, s), "⟩", ",", "-", ",", ident H, "⟩", ":=", expr this.has_min set.univ ⟨⟨c, hcs⟩, trivial⟩],
  exact [expr ⟨m, hms, λ x hx hxm, H ⟨x, hx⟩ trivial hxm⟩]
end

theorem Finset.exists_maximal {α : Type _} [Preorderₓ α] (s : Finset α) (h : s.nonempty) :
  ∃ (m : _)(_ : m ∈ s), ∀ x _ : x ∈ s, ¬m < x :=
  @Finset.exists_minimal (OrderDual α) _ s h

namespace Infinite

theorem exists_not_mem_finset [Infinite α] (s : Finset α) : ∃ x, x ∉ s :=
  not_forall.1$ fun h => Fintype.false ⟨s, h⟩

instance (priority := 100) (α : Type _) [H : Infinite α] : Nontrivial α :=
  ⟨let ⟨x, hx⟩ := exists_not_mem_finset (∅ : Finset α)
    let ⟨y, hy⟩ := exists_not_mem_finset ({x} : Finset α)
    ⟨y, x,
      by 
        simpa only [mem_singleton] using hy⟩⟩

protected theorem Nonempty (α : Type _) [Infinite α] : Nonempty α :=
  by 
    infer_instance

theorem of_injective [Infinite β] (f : β → α) (hf : injective f) : Infinite α :=
  ⟨fun I =>
      by 
        exact (Fintype.ofInjective f hf).False⟩

theorem of_surjective [Infinite β] (f : α → β) (hf : surjective f) : Infinite α :=
  ⟨fun I =>
      by 
        classical 
        exact (Fintype.ofSurjective f hf).False⟩

instance : Infinite ℕ :=
  ⟨fun ⟨s, hs⟩ => Finset.not_mem_range_self$ s.subset_range_sup_succ (hs _)⟩

instance : Infinite ℤ :=
  Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.injₓ

instance [Infinite α] : Infinite (Set α) :=
  of_injective singleton fun a b => Set.singleton_eq_singleton_iff.1

instance [Infinite α] : Infinite (Finset α) :=
  of_injective singleton Finset.singleton_injective

instance [Nonempty α] : Infinite (Multiset α) :=
  by 
    inhabit α 
    exact of_injective (Multiset.repeat (default α)) (Multiset.repeat_injective _)

instance [Nonempty α] : Infinite (List α) :=
  of_surjective (coeₓ : List α → Multiset α) (surjective_quot_mk _)

instance sum_of_left [Infinite α] : Infinite (Sum α β) :=
  of_injective Sum.inl Sum.inl_injective

instance sum_of_right [Infinite β] : Infinite (Sum α β) :=
  of_injective Sum.inr Sum.inr_injective

instance prod_of_right [Nonempty α] [Infinite β] : Infinite (α × β) :=
  of_surjective Prod.snd Prod.snd_surjective

instance prod_of_left [Infinite α] [Nonempty β] : Infinite (α × β) :=
  of_surjective Prod.fst Prod.fst_surjectiveₓ

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private noncomputable def nat_embedding_aux (α : Type*) [infinite α] : exprℕ() → α
| n := by letI [] [] [":=", expr classical.dec_eq α]; exact [expr classical.some (exists_not_mem_finset ((multiset.range n).pmap (λ
    (m)
    (hm : «expr < »(m, n)), nat_embedding_aux m) (λ _, multiset.mem_range.1)).to_finset)]

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
private theorem nat_embedding_aux_injective (α : Type*) [infinite α] : function.injective (nat_embedding_aux α) :=
begin
  rintro [ident m, ident n, ident h],
  letI [] [] [":=", expr classical.dec_eq α],
  wlog [ident hmlen] [":", expr «expr ≤ »(m, n)] [] ["using", ident m, ident n],
  by_contradiction [ident hmn],
  have [ident hmn] [":", expr «expr < »(m, n)] [],
  from [expr lt_of_le_of_ne hmlen hmn],
  refine [expr classical.some_spec (exists_not_mem_finset ((multiset.range n).pmap (λ
      (m)
      (hm : «expr < »(m, n)), nat_embedding_aux α m) (λ _, multiset.mem_range.1)).to_finset) _],
  refine [expr multiset.mem_to_finset.2 (multiset.mem_pmap.2 ⟨m, multiset.mem_range.2 hmn, _⟩)],
  rw ["[", expr h, ",", expr nat_embedding_aux, "]"] []
end

/-- Embedding of `ℕ` into an infinite type. -/
noncomputable def nat_embedding (α : Type _) [Infinite α] : ℕ ↪ α :=
  ⟨_, nat_embedding_aux_injective α⟩

theorem exists_subset_card_eq (α : Type _) [Infinite α] (n : ℕ) : ∃ s : Finset α, s.card = n :=
  ⟨(range n).map (nat_embedding α),
    by 
      rw [card_map, card_range]⟩

end Infinite

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem infinite_sum : «expr ↔ »(infinite «expr ⊕ »(α, β), «expr ∨ »(infinite α, infinite β)) :=
begin
  refine [expr ⟨λ H, _, λ H, H.elim (@infinite.sum_of_left α β) (@infinite.sum_of_right α β)⟩],
  contrapose ["!"] [ident H],
  haveI [] [] [":=", expr fintype_of_not_infinite H.1],
  haveI [] [] [":=", expr fintype_of_not_infinite H.2],
  exact [expr infinite.false]
end

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem infinite_prod : «expr ↔ »(infinite «expr × »(α, β), «expr ∨ »(«expr ∧ »(infinite α, nonempty β), «expr ∧ »(nonempty α, infinite β))) :=
begin
  refine [expr ⟨λ
    H, _, λ
    H, H.elim «expr $ »(and_imp.2, @infinite.prod_of_left α β) «expr $ »(and_imp.2, @infinite.prod_of_right α β)⟩],
  rw [expr and.comm] [],
  contrapose ["!"] [ident H],
  introI [ident H'],
  rcases [expr infinite.nonempty «expr × »(α, β), "with", "⟨", ident a, ",", ident b, "⟩"],
  haveI [] [] [":=", expr fintype_of_not_infinite (H.1 ⟨b⟩)],
  haveI [] [] [":=", expr fintype_of_not_infinite (H.2 ⟨a⟩)],
  exact [expr H'.false]
end

/-- If every finset in a type has bounded cardinality, that type is finite. -/
noncomputable def fintypeOfFinsetCardLe {ι : Type _} (n : ℕ) (w : ∀ s : Finset ι, s.card ≤ n) : Fintype ι :=
  by 
    apply fintypeOfNotInfinite 
    intro i 
    obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n+1)
    specialize w s 
    rw [c] at w 
    exact Nat.not_succ_le_selfₓ n w

theorem not_injective_infinite_fintype [Infinite α] [Fintype β] (f : α → β) : ¬injective f :=
  fun hf => (Fintype.ofInjective f hf).False

/--
The pigeonhole principle for infinitely many pigeons in finitely many pigeonholes. If there are
infinitely many pigeons in finitely many pigeonholes, then there are at least two pigeons in the
same pigeonhole.

See also: `fintype.exists_ne_map_eq_of_card_lt`, `fintype.exists_infinite_fiber`.
-/
theorem Fintype.exists_ne_map_eq_of_infinite [Infinite α] [Fintype β] (f : α → β) : ∃ x y : α, x ≠ y ∧ f x = f y :=
  by 
    classical 
    byContra hf 
    pushNeg  at hf 
    apply not_injective_infinite_fintype f 
    intro x y 
    contrapose 
    apply hf

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:927:38: unsupported irreducible non-definition
@[irreducible] instance function.embedding.is_empty {α β} [infinite α] [fintype β] : is_empty «expr ↪ »(α, β) :=
⟨λ f, let ⟨x, y, ne, feq⟩ := fintype.exists_ne_map_eq_of_infinite f in «expr $ »(ne, f.injective feq)⟩

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100]
noncomputable
instance function.embedding.fintype' {α β : Type*} [fintype β] : fintype «expr ↪ »(α, β) :=
begin
  by_cases [expr h, ":", expr infinite α],
  { resetI,
    apply_instance },
  { have [] [] [":=", expr fintype_of_not_infinite h],
    classical,
    apply_instance }
end

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `fintype.exists_ne_map_eq_of_infinite`
-/
theorem fintype.exists_infinite_fiber
[infinite α]
[fintype β]
(f : α → β) : «expr∃ , »((y : β), infinite «expr ⁻¹' »(f, {y})) :=
begin
  classical,
  by_contra [ident hf],
  push_neg ["at", ident hf],
  haveI [] [] [":=", expr λ y, «expr $ »(fintype_of_not_infinite, hf y)],
  let [ident key] [":", expr fintype α] [":=", expr { elems := univ.bUnion (λ y : β, «expr ⁻¹' »(f, {y}).to_finset),
     complete := by simp [] [] [] [] [] [] }],
  exact [expr key.false]
end

theorem not_surjective_fintype_infinite [Fintype α] [Infinite β] (f : α → β) : ¬surjective f :=
  fun hf : surjective f =>
    have H : Infinite α := Infinite.of_surjective f hf 
    by 
      exact not_fintype α

section Trunc

/--
For `s : multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `trunc α`.
-/
def truncOfMultisetExistsMem {α} (s : Multiset α) : (∃ x, x ∈ s) → Trunc α :=
  Quotientₓ.recOnSubsingleton s$
    fun l h =>
      match l, h with 
      | [], _ =>
        False.elim
          (by 
            tauto)
      | a :: _, _ => Trunc.mk a

/--
A `nonempty` `fintype` constructively contains an element.
-/
def truncOfNonemptyFintype α [Nonempty α] [Fintype α] : Trunc α :=
  truncOfMultisetExistsMem Finset.univ.val
    (by 
      simp )

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A `fintype` with positive cardinality constructively contains an element.
-/ def trunc_of_card_pos {α} [fintype α] (h : «expr < »(0, fintype.card α)) : trunc α :=
by { letI [] [] [":=", expr fintype.card_pos_iff.mp h],
  exact [expr trunc_of_nonempty_fintype α] }

/--
By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `trunc (Σ' a, P a)`, containing data.
-/
def truncSigmaOfExists {α} [Fintype α] {P : α → Prop} [DecidablePred P] (h : ∃ a, P a) : Trunc (Σ'a, P a) :=
  @truncOfNonemptyFintype (Σ'a, P a) (Exists.elim h$ fun a ha => ⟨⟨a, ha⟩⟩) _

end Trunc

namespace Multiset

variable [Fintype α] [DecidableEq α]

@[simp]
theorem count_univ (a : α) : count a Finset.univ.val = 1 :=
  count_eq_one_of_mem Finset.univ.Nodup (Finset.mem_univ _)

end Multiset

namespace Fintype

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A recursor principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
def trunc_rec_empty_option
{P : Type u → Sort v}
(of_equiv : ∀ {α β}, «expr ≃ »(α, β) → P α → P β)
(h_empty : P pempty)
(h_option : ∀ {α} [fintype α] [decidable_eq α], P α → P (option α))
(α : Type u)
[fintype α]
[decidable_eq α] : trunc (P α) :=
begin
  suffices [] [":", expr ∀ n : exprℕ(), trunc (P «expr $ »(ulift, fin n))],
  { apply [expr trunc.bind (this (fintype.card α))],
    intro [ident h],
    apply [expr trunc.map _ (fintype.trunc_equiv_fin α)],
    intro [ident e],
    exact [expr of_equiv (equiv.ulift.trans e.symm) h] },
  intro [ident n],
  induction [expr n] [] ["with", ident n, ident ih] [],
  { have [] [":", expr «expr = »(card pempty, card (ulift (fin 0)))] [],
    { simp [] [] ["only"] ["[", expr card_fin, ",", expr card_pempty, ",", expr card_ulift, "]"] [] [] },
    apply [expr trunc.bind (trunc_equiv_of_card_eq this)],
    intro [ident e],
    apply [expr trunc.mk],
    refine [expr of_equiv e h_empty] },
  { have [] [":", expr «expr = »(card (option (ulift (fin n))), card (ulift (fin n.succ)))] [],
    { simp [] [] ["only"] ["[", expr card_fin, ",", expr card_option, ",", expr card_ulift, "]"] [] [] },
    apply [expr trunc.bind (trunc_equiv_of_card_eq this)],
    intro [ident e],
    apply [expr trunc.map _ ih],
    intro [ident ih],
    refine [expr of_equiv e (h_option ih)] }
end

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
@[elab_as_eliminator]
theorem induction_empty_option' {P : ∀ α : Type u [Fintype α], Prop}
  (of_equiv : ∀ α β [Fintype β] e : α ≃ β, @P α (@Fintype.ofEquiv α β ‹_› e.symm) → @P β ‹_›) (h_empty : P Pempty)
  (h_option :
    ∀ α [Fintype α],
      by 
        exact P α → P (Option α))
  (α : Type u) [Fintype α] : P α :=
  by 
    obtain ⟨p⟩ :=
      @trunc_rec_empty_option (fun α => ∀ h, @P α h) (fun α β e hα hβ => @of_equiv α β hβ e (hα _))
        (fun _i =>
          by 
            convert h_empty)
        _ α _ (Classical.decEq α)
    ·
      exact p _
    ·
      rintro α hα - Pα hα' 
      skip 
      convert h_option α (Pα _)

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
theorem induction_empty_option {P : Type u → Prop} (of_equiv : ∀ {α β}, α ≃ β → P α → P β) (h_empty : P Pempty)
  (h_option : ∀ {α} [Fintype α], P α → P (Option α)) (α : Type u) [Fintype α] : P α :=
  by 
    refine' induction_empty_option' _ _ _ α 
    exacts[fun α β _ => of_equiv, h_empty, @h_option]

end Fintype

/-- Auxiliary definition to show `exists_seq_of_forall_finset_exists`. -/
noncomputable def seqOfForallFinsetExistsAux {α : Type _} [DecidableEq α] (P : α → Prop) (r : α → α → Prop)
  (h : ∀ s : Finset α, ∃ y, (∀ x _ : x ∈ s, P x) → P y ∧ ∀ x _ : x ∈ s, r x y) : ℕ → α
| n =>
  Classical.some (h (Finset.image (fun i : Finₓ n => seqOfForallFinsetExistsAux i) (Finset.univ : Finset (Finₓ n))))

-- error in Data.Fintype.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists
{α : Type*}
(P : α → exprProp())
(r : α → α → exprProp())
(h : ∀
 s : finset α, ∀
 x «expr ∈ » s, P x → «expr∃ , »((y), «expr ∧ »(P y, ∀
   x «expr ∈ » s, r x y))) : «expr∃ , »((f : exprℕ() → α), «expr ∧ »(∀
  n, P (f n), ∀ m n, «expr < »(m, n) → r (f m) (f n))) :=
begin
  classical,
  haveI [] [":", expr nonempty α] [],
  { rcases [expr h «expr∅»() (by simp [] [] [] [] [] []), "with", "⟨", ident y, ",", ident hy, "⟩"],
    exact [expr ⟨y⟩] },
  choose ["!"] [ident F] [ident hF] ["using", expr h],
  have [ident h'] [":", expr ∀
   s : finset α, «expr∃ , »((y), ∀
    x «expr ∈ » s, P x → «expr ∧ »(P y, ∀ x «expr ∈ » s, r x y))] [":=", expr λ s, ⟨F s, hF s⟩],
  set [] [ident f] [] [":="] [expr seq_of_forall_finset_exists_aux P r h'] ["with", ident hf],
  have [ident A] [":", expr ∀ n : exprℕ(), P (f n)] [],
  { assume [binders (n)],
    induction [expr n] ["using", ident nat.strong_induction_on] ["with", ident n, ident IH] [],
    have [ident IH'] [":", expr ∀ x : fin n, P (f x)] [":=", expr λ n, IH n.1 n.2],
    rw ["[", expr hf, ",", expr seq_of_forall_finset_exists_aux, "]"] [],
    exact [expr (classical.some_spec (h' (finset.image (λ
         i : fin n, f i) (finset.univ : finset (fin n)))) (by simp [] [] [] ["[", expr IH', "]"] [] [])).1] },
  refine [expr ⟨f, A, λ m n hmn, _⟩],
  nth_rewrite [1] [expr hf] [],
  rw [expr seq_of_forall_finset_exists_aux] [],
  apply [expr (classical.some_spec (h' (finset.image (λ
       i : fin n, f i) (finset.univ : finset (fin n)))) (by simp [] [] [] ["[", expr A, "]"] [] [])).2],
  exact [expr finset.mem_image.2 ⟨⟨m, hmn⟩, finset.mem_univ _, rfl⟩]
end

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists' {α : Type _} (P : α → Prop) (r : α → α → Prop) [IsSymm α r]
  (h : ∀ s : Finset α, (∀ x _ : x ∈ s, P x) → ∃ y, P y ∧ ∀ x _ : x ∈ s, r x y) :
  ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m ≠ n → r (f m) (f n) :=
  by 
    rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
    refine' ⟨f, hf, fun m n hmn => _⟩
    rcases lt_trichotomyₓ m n with (h | rfl | h)
    ·
      exact hf' m n h
    ·
      exact (hmn rfl).elim
    ·
      apply symm 
      exact hf' n m h

