/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import Mathbin.Algebra.BigOperators.Finsupp
import Mathbin.Data.Finset.Preimage
import Mathbin.Data.List.Alist

/-!
# Miscellaneous definitions, lemmas, and constructions using finsupp

## Main declarations

* `finsupp.graph`: the finset of input and output pairs with non-zero outputs.
* `alist.lookup_finsupp`: converts an association list into a finitely supported function
  via `alist.lookup`, sending absent keys to zero.
* `finsupp.map_range.equiv`: `finsupp.map_range` as an equiv.
* `finsupp.map_domain`: maps the domain of a `finsupp` by a function and by summing.
* `finsupp.comap_domain`: postcomposition of a `finsupp` with a function injective on the preimage
  of its support.
* `finsupp.some`: restrict a finitely supported function on `option α` to a finitely supported
  function on `α`.
* `finsupp.filter`: `filter p f` is the finitely supported function that is `f a` if `p a` is true
  and 0 otherwise.
* `finsupp.frange`: the image of a finitely supported function on its support.
* `finsupp.subtype_domain`: the restriction of a finitely supported function `f` to a subtype.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* This file is currently ~1600 lines long and is quite a miscellany of definitions and lemmas,
  so it should be divided into smaller pieces.

* Expand the list of definitions and important lemmas to the module docstring.

-/


noncomputable section

open Finset Function

open Classical BigOperators

variable {α β γ ι M M' N P G H R S : Type _}

namespace Finsupp

/-! ### Declarations about `graph` -/


section Graph

variable [Zero M]

/-- The graph of a finitely supported function over its support, i.e. the finset of input and output
pairs with non-zero outputs. -/
def graph (f : α →₀ M) : Finset (α × M) :=
  f.Support.map ⟨fun a => Prod.mk a (f a), fun x y h => (Prod.mk.inj h).1⟩

theorem mk_mem_graph_iff {a : α} {m : M} {f : α →₀ M} : (a, m) ∈ f.graph ↔ f a = m ∧ m ≠ 0 := by
  simp_rw [graph, mem_map, mem_support_iff]
  constructor
  · rintro ⟨b, ha, rfl, -⟩
    exact ⟨rfl, ha⟩
    
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩
    

@[simp]
theorem mem_graph_iff {c : α × M} {f : α →₀ M} : c ∈ f.graph ↔ f c.1 = c.2 ∧ c.2 ≠ 0 := by
  cases c
  exact mk_mem_graph_iff

theorem mk_mem_graph (f : α →₀ M) {a : α} (ha : a ∈ f.Support) : (a, f a) ∈ f.graph :=
  mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩

theorem apply_eq_of_mem_graph {a : α} {m : M} {f : α →₀ M} (h : (a, m) ∈ f.graph) : f a = m :=
  (mem_graph_iff.1 h).1

@[simp]
theorem not_mem_graph_snd_zero (a : α) (f : α →₀ M) : (a, (0 : M)) ∉ f.graph := fun h => (mem_graph_iff.1 h).2.irrefl

@[simp]
theorem image_fst_graph (f : α →₀ M) : f.graph.Image Prod.fst = f.Support := by
  simp only [graph, map_eq_image, image_image, embedding.coe_fn_mk, (· ∘ ·), image_id']

theorem graph_injective (α M) [Zero M] : Injective (@graph α M _) := by
  intro f g h
  have hsup : f.support = g.support := by
    rw [← image_fst_graph, h, image_fst_graph]
  refine' ext_iff'.2 ⟨hsup, fun x hx => apply_eq_of_mem_graph <| h.symm ▸ _⟩
  exact mk_mem_graph _ (hsup ▸ hx)

@[simp]
theorem graph_inj {f g : α →₀ M} : f.graph = g.graph ↔ f = g :=
  (graph_injective α M).eq_iff

@[simp]
theorem graph_zero : graph (0 : α →₀ M) = ∅ := by
  simp [graph]

@[simp]
theorem graph_eq_empty {f : α →₀ M} : f.graph = ∅ ↔ f = 0 :=
  (graph_injective α M).eq_iff' graph_zero

/-- Produce an association list for the finsupp over its support using choice. -/
@[simps]
def toAlist (f : α →₀ M) : Alist fun x : α => M :=
  ⟨f.graph.toList.map Prod.toSigma, by
    rw [List.Nodupkeys, List.keys, List.map_mapₓ, Prod.fst_comp_to_sigma, List.nodup_map_iff_inj_on]
    · rintro ⟨b, m⟩ hb ⟨c, n⟩ hc (rfl : b = c)
      rw [mem_to_list, Finsupp.mem_graph_iff] at hb hc
      dsimp'  at hb hc
      rw [← hc.1, hb.1]
      
    · apply nodup_to_list
      ⟩

@[simp]
theorem to_alist_keys_to_finset (f : α →₀ M) : f.toAlist.keys.toFinset = f.Support := by
  ext
  simp [to_alist, Alist.mem_keys, Alist.keys, List.keys]

@[simp]
theorem mem_to_alist {f : α →₀ M} {x : α} : x ∈ f.toAlist ↔ f x ≠ 0 := by
  rw [Alist.mem_keys, ← List.mem_to_finset, to_alist_keys_to_finset, mem_support_iff]

end Graph

end Finsupp

/-! ### Declarations about `alist.lookup_finsupp` -/


section LookupFinsupp

variable [Zero M]

namespace Alist

open List

/-- Converts an association list into a finitely supported function via `alist.lookup`, sending
absent keys to zero. -/
@[simps]
def lookupFinsupp (l : Alist fun x : α => M) : α →₀ M where
  Support := (l.1.filter fun x => Sigma.snd x ≠ 0).keys.toFinset
  toFun := fun a => (l.lookup a).getOrElse 0
  mem_support_to_fun := fun a => by
    simp_rw [mem_to_finset, List.mem_keys, List.mem_filterₓ, ← mem_lookup_iff]
    cases lookup a l <;> simp

alias lookup_finsupp_to_fun ← lookup_finsupp_apply

theorem lookup_finsupp_eq_iff_of_ne_zero {l : Alist fun x : α => M} {a : α} {x : M} (hx : x ≠ 0) :
    l.lookupFinsupp a = x ↔ x ∈ l.lookup a := by
  rw [lookup_finsupp_to_fun]
  cases' lookup a l with m <;> simp [hx.symm]

theorem lookup_finsupp_eq_zero_iff {l : Alist fun x : α => M} {a : α} :
    l.lookupFinsupp a = 0 ↔ a ∉ l ∨ (0 : M) ∈ l.lookup a := by
  rw [lookup_finsupp_to_fun, ← lookup_eq_none]
  cases' lookup a l with m <;> simp

@[simp]
theorem empty_lookup_finsupp : lookupFinsupp (∅ : Alist fun x : α => M) = 0 := by
  ext
  simp

@[simp]
theorem insert_lookup_finsupp (l : Alist fun x : α => M) (a : α) (m : M) :
    (l.insert a m).lookupFinsupp = l.lookupFinsupp.update a m := by
  ext b
  by_cases' h : b = a <;> simp [h]

@[simp]
theorem singleton_lookup_finsupp (a : α) (m : M) : (singleton a m).lookupFinsupp = Finsupp.single a m := by
  simp [← Alist.insert_empty]

@[simp]
theorem _root_.finsupp.to_alist_lookup_finsupp (f : α →₀ M) : f.toAlist.lookupFinsupp = f := by
  ext
  by_cases' h : f a = 0
  · suffices f.to_alist.lookup a = none by
      simp [h, this]
    · simp [lookup_eq_none, h]
      
    
  · suffices f.to_alist.lookup a = some (f a) by
      simp [h, this]
    · apply mem_lookup_iff.2
      simpa using h
      
    

theorem lookup_finsupp_surjective : Surjective (@lookupFinsupp α M _) := fun f => ⟨_, Finsupp.to_alist_lookup_finsupp f⟩

end Alist

end LookupFinsupp

/-! ### Declarations about `map_range` -/


section MapRange

namespace Finsupp

section Equivₓ

variable [Zero M] [Zero N] [Zero P]

/-- `finsupp.map_range` as an equiv. -/
@[simps apply]
def mapRange.equiv (f : M ≃ N) (hf : f 0 = 0) (hf' : f.symm 0 = 0) : (α →₀ M) ≃ (α →₀ N) where
  toFun := (mapRange f hf : (α →₀ M) → α →₀ N)
  invFun := (mapRange f.symm hf' : (α →₀ N) → α →₀ M)
  left_inv := fun x => by
    rw [← map_range_comp _ _ _ _] <;> simp_rw [Equivₓ.symm_comp_self]
    · exact map_range_id _
      
    · rfl
      
  right_inv := fun x => by
    rw [← map_range_comp _ _ _ _] <;> simp_rw [Equivₓ.self_comp_symm]
    · exact map_range_id _
      
    · rfl
      

@[simp]
theorem mapRange.equiv_refl : mapRange.equiv (Equivₓ.refl M) rfl rfl = Equivₓ.refl (α →₀ M) :=
  Equivₓ.ext map_range_id

theorem mapRange.equiv_trans (f : M ≃ N) (hf : f 0 = 0) (hf') (f₂ : N ≃ P) (hf₂ : f₂ 0 = 0) (hf₂') :
    (mapRange.equiv (f.trans f₂)
        (by
          rw [Equivₓ.trans_apply, hf, hf₂])
        (by
          rw [Equivₓ.symm_trans_apply, hf₂', hf']) :
        (α →₀ _) ≃ _) =
      (mapRange.equiv f hf hf').trans (mapRange.equiv f₂ hf₂ hf₂') :=
  Equivₓ.ext <| map_range_comp _ _ _ _ _

@[simp]
theorem mapRange.equiv_symm (f : M ≃ N) (hf hf') :
    ((mapRange.equiv f hf hf').symm : (α →₀ _) ≃ _) = mapRange.equiv f.symm hf' hf :=
  Equivₓ.ext fun x => rfl

end Equivₓ

section ZeroHom

variable [Zero M] [Zero N] [Zero P]

/-- Composition with a fixed zero-preserving homomorphism is itself an zero-preserving homomorphism
on functions. -/
@[simps]
def mapRange.zeroHom (f : ZeroHom M N) : ZeroHom (α →₀ M) (α →₀ N) where
  toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
  map_zero' := map_range_zero

@[simp]
theorem mapRange.zero_hom_id : mapRange.zeroHom (ZeroHom.id M) = ZeroHom.id (α →₀ M) :=
  ZeroHom.ext map_range_id

theorem mapRange.zero_hom_comp (f : ZeroHom N P) (f₂ : ZeroHom M N) :
    (mapRange.zeroHom (f.comp f₂) : ZeroHom (α →₀ _) _) = (mapRange.zeroHom f).comp (mapRange.zeroHom f₂) :=
  ZeroHom.ext <| map_range_comp _ _ _ _ _

end ZeroHom

section AddMonoidHom

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [AddCommMonoidₓ P]

/-- Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
def mapRange.addMonoidHom (f : M →+ N) : (α →₀ M) →+ α →₀ N where
  toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
  map_zero' := map_range_zero
  map_add' := fun a b => map_range_add f.map_add _ _

@[simp]
theorem mapRange.add_monoid_hom_id : mapRange.addMonoidHom (AddMonoidHom.id M) = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext map_range_id

theorem mapRange.add_monoid_hom_comp (f : N →+ P) (f₂ : M →+ N) :
    (mapRange.addMonoidHom (f.comp f₂) : (α →₀ _) →+ _) = (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) :=
  AddMonoidHom.ext <| map_range_comp _ _ _ _ _

@[simp]
theorem mapRange.add_monoid_hom_to_zero_hom (f : M →+ N) :
    (mapRange.addMonoidHom f).toZeroHom = (mapRange.zeroHom f.toZeroHom : ZeroHom (α →₀ _) _) :=
  ZeroHom.ext fun _ => rfl

theorem map_range_multiset_sum (f : M →+ N) (m : Multiset (α →₀ M)) :
    mapRange f f.map_zero m.Sum = (m.map fun x => mapRange f f.map_zero x).Sum :=
  (mapRange.addMonoidHom f : (α →₀ _) →+ _).map_multiset_sum _

theorem map_range_finset_sum (f : M →+ N) (s : Finset ι) (g : ι → α →₀ M) :
    mapRange f f.map_zero (∑ x in s, g x) = ∑ x in s, mapRange f f.map_zero (g x) :=
  (mapRange.addMonoidHom f : (α →₀ _) →+ _).map_sum _ _

/-- `finsupp.map_range.add_monoid_hom` as an equiv. -/
@[simps apply]
def mapRange.addEquiv (f : M ≃+ N) : (α →₀ M) ≃+ (α →₀ N) :=
  { mapRange.addMonoidHom f.toAddMonoidHom with toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N),
    invFun := (mapRange f.symm f.symm.map_zero : (α →₀ N) → α →₀ M),
    left_inv := fun x => by
      rw [← map_range_comp _ _ _ _] <;> simp_rw [AddEquiv.symm_comp_self]
      · exact map_range_id _
        
      · rfl
        ,
    right_inv := fun x => by
      rw [← map_range_comp _ _ _ _] <;> simp_rw [AddEquiv.self_comp_symm]
      · exact map_range_id _
        
      · rfl
         }

@[simp]
theorem mapRange.add_equiv_refl : mapRange.addEquiv (AddEquiv.refl M) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext map_range_id

theorem mapRange.add_equiv_trans (f : M ≃+ N) (f₂ : N ≃+ P) :
    (mapRange.addEquiv (f.trans f₂) : (α →₀ _) ≃+ _) = (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) :=
  AddEquiv.ext <| map_range_comp _ _ _ _ _

@[simp]
theorem mapRange.add_equiv_symm (f : M ≃+ N) :
    ((mapRange.addEquiv f).symm : (α →₀ _) ≃+ _) = mapRange.addEquiv f.symm :=
  AddEquiv.ext fun x => rfl

@[simp]
theorem mapRange.add_equiv_to_add_monoid_hom (f : M ≃+ N) :
    (mapRange.addEquiv f : (α →₀ _) ≃+ _).toAddMonoidHom = (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ _) →+ _) :=
  AddMonoidHom.ext fun _ => rfl

@[simp]
theorem mapRange.add_equiv_to_equiv (f : M ≃+ N) :
    (mapRange.addEquiv f).toEquiv = (mapRange.equiv f.toEquiv f.map_zero f.symm.map_zero : (α →₀ _) ≃ _) :=
  Equivₓ.ext fun _ => rfl

end AddMonoidHom

end Finsupp

end MapRange

/-! ### Declarations about `equiv_congr_left` -/


section EquivCongrLeft

variable [Zero M]

namespace Finsupp

/-- Given `f : α ≃ β`, we can map `l : α →₀ M` to  `equiv_map_domain f l : β →₀ M` (computably)
by mapping the support forwards and the function backwards. -/
def equivMapDomain (f : α ≃ β) (l : α →₀ M) : β →₀ M where
  Support := l.Support.map f.toEmbedding
  toFun := fun a => l (f.symm a)
  mem_support_to_fun := fun a => by
    simp only [Finset.mem_map_equiv, mem_support_to_fun] <;> rfl

@[simp]
theorem equiv_map_domain_apply (f : α ≃ β) (l : α →₀ M) (b : β) : equivMapDomain f l b = l (f.symm b) :=
  rfl

theorem equiv_map_domain_symm_apply (f : α ≃ β) (l : β →₀ M) (a : α) : equivMapDomain f.symm l a = l (f a) :=
  rfl

@[simp]
theorem equiv_map_domain_refl (l : α →₀ M) : equivMapDomain (Equivₓ.refl _) l = l := by
  ext x <;> rfl

theorem equiv_map_domain_refl' : equivMapDomain (Equivₓ.refl _) = @id (α →₀ M) := by
  ext x <;> rfl

theorem equiv_map_domain_trans (f : α ≃ β) (g : β ≃ γ) (l : α →₀ M) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by
  ext x <;> rfl

theorem equiv_map_domain_trans' (f : α ≃ β) (g : β ≃ γ) :
    @equivMapDomain _ _ M _ (f.trans g) = equivMapDomain g ∘ equivMapDomain f := by
  ext x <;> rfl

@[simp]
theorem equiv_map_domain_single (f : α ≃ β) (a : α) (b : M) : equivMapDomain f (single a b) = single (f a) b := by
  ext x <;> simp only [single_apply, Equivₓ.apply_eq_iff_eq_symm_apply, equiv_map_domain_apply] <;> congr

@[simp]
theorem equiv_map_domain_zero {f : α ≃ β} : equivMapDomain f (0 : α →₀ M) = (0 : β →₀ M) := by
  ext x <;> simp only [equiv_map_domain_apply, coe_zero, Pi.zero_apply]

/-- Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `equiv.Pi_congr_left`. -/
def equivCongrLeft (f : α ≃ β) : (α →₀ M) ≃ (β →₀ M) := by
  refine' ⟨equiv_map_domain f, equiv_map_domain f.symm, fun f => _, fun f => _⟩ <;>
    ext x <;> simp only [equiv_map_domain_apply, Equivₓ.symm_symm, Equivₓ.symm_apply_apply, Equivₓ.apply_symm_apply]

@[simp]
theorem equiv_congr_left_apply (f : α ≃ β) (l : α →₀ M) : equivCongrLeft f l = equivMapDomain f l :=
  rfl

@[simp]
theorem equiv_congr_left_symm (f : α ≃ β) : (@equivCongrLeft _ _ M _ f).symm = equivCongrLeft f.symm :=
  rfl

end Finsupp

end EquivCongrLeft

section CastFinsupp

variable [Zero M] (f : α →₀ M)

namespace Nat

@[simp, norm_cast]
theorem cast_finsupp_prod [CommSemiringₓ R] (g : α → M → ℕ) : (↑(f.Prod g) : R) = f.Prod fun a b => ↑(g a b) :=
  Nat.cast_prod _ _

@[simp, norm_cast]
theorem cast_finsupp_sum [CommSemiringₓ R] (g : α → M → ℕ) : (↑(f.Sum g) : R) = f.Sum fun a b => ↑(g a b) :=
  Nat.cast_sum _ _

end Nat

namespace Int

@[simp, norm_cast]
theorem cast_finsupp_prod [CommRingₓ R] (g : α → M → ℤ) : (↑(f.Prod g) : R) = f.Prod fun a b => ↑(g a b) :=
  Int.cast_prod _ _

@[simp, norm_cast]
theorem cast_finsupp_sum [CommRingₓ R] (g : α → M → ℤ) : (↑(f.Sum g) : R) = f.Sum fun a b => ↑(g a b) :=
  Int.cast_sum _ _

end Int

namespace Rat

@[simp, norm_cast]
theorem cast_finsupp_sum [DivisionRing R] [CharZero R] (g : α → M → ℚ) : (↑(f.Sum g) : R) = f.Sum fun a b => g a b :=
  cast_sum _ _

@[simp, norm_cast]
theorem cast_finsupp_prod [Field R] [CharZero R] (g : α → M → ℚ) : (↑(f.Prod g) : R) = f.Prod fun a b => g a b :=
  cast_prod _ _

end Rat

end CastFinsupp

/-! ### Declarations about `map_domain` -/


namespace Finsupp

section MapDomain

variable [AddCommMonoidₓ M] {v v₁ v₂ : α →₀ M}

/-- Given `f : α → β` and `v : α →₀ M`, `map_domain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def mapDomain (f : α → β) (v : α →₀ M) : β →₀ M :=
  v.Sum fun a => single (f a)

theorem map_domain_apply {f : α → β} (hf : Function.Injective f) (x : α →₀ M) (a : α) : mapDomain f x (f a) = x a := by
  rw [map_domain, sum_apply, Sum, Finset.sum_eq_single a, single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne (hf.ne hba)
    
  · intro h
    rw [not_mem_support_iff.1 h, single_zero, zero_apply]
    

theorem map_domain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ Set.Range f) : mapDomain f x a = 0 := by
  rw [map_domain, sum_apply, Sum]
  exact Finset.sum_eq_zero fun a' h' => single_eq_of_ne fun eq => h <| Eq ▸ Set.mem_range_self _

@[simp]
theorem map_domain_id : mapDomain id v = v :=
  sum_single _

theorem map_domain_comp {f : α → β} {g : β → γ} : mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) := by
  refine' ((sum_sum_index _ _).trans _).symm
  · intro
    exact single_zero _
    
  · intro
    exact single_add _
    
  refine' sum_congr fun _ _ => sum_single_index _
  · exact single_zero _
    

@[simp]
theorem map_domain_single {f : α → β} {a : α} {b : M} : mapDomain f (single a b) = single (f a) b :=
  sum_single_index <| single_zero _

@[simp]
theorem map_domain_zero {f : α → β} : mapDomain f (0 : α →₀ M) = (0 : β →₀ M) :=
  sum_zero_index

theorem map_domain_congr {f g : α → β} (h : ∀ x ∈ v.Support, f x = g x) : v.mapDomain f = v.mapDomain g :=
  (Finset.sum_congr rfl) fun _ H => by
    simp only [h _ H]

theorem map_domain_add {f : α → β} : mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂ :=
  sum_add_index' (fun _ => single_zero _) fun _ => single_add _

@[simp]
theorem map_domain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) : mapDomain f x a = x (f.symm a) := by
  conv_lhs => rw [← f.apply_symm_apply a]
  exact map_domain_apply f.injective _ _

/-- `finsupp.map_domain` is an `add_monoid_hom`. -/
@[simps]
def mapDomain.addMonoidHom (f : α → β) : (α →₀ M) →+ β →₀ M where
  toFun := mapDomain f
  map_zero' := map_domain_zero
  map_add' := fun _ _ => map_domain_add

@[simp]
theorem mapDomain.add_monoid_hom_id : mapDomain.addMonoidHom id = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext fun _ => map_domain_id

theorem mapDomain.add_monoid_hom_comp (f : β → γ) (g : α → β) :
    (mapDomain.addMonoidHom (f ∘ g) : (α →₀ M) →+ γ →₀ M) =
      (mapDomain.addMonoidHom f).comp (mapDomain.addMonoidHom g) :=
  AddMonoidHom.ext fun _ => map_domain_comp

theorem map_domain_finset_sum {f : α → β} {s : Finset ι} {v : ι → α →₀ M} :
    mapDomain f (∑ i in s, v i) = ∑ i in s, mapDomain f (v i) :=
  (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M).map_sum _ _

theorem map_domain_sum [Zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
    mapDomain f (s.Sum v) = s.Sum fun a b => mapDomain f (v a b) :=
  (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M).map_finsupp_sum _ _

theorem map_domain_support [DecidableEq β] {f : α → β} {s : α →₀ M} : (s.mapDomain f).Support ⊆ s.Support.Image f :=
  Finset.Subset.trans support_sum <|
    Finset.Subset.trans (Finset.bUnion_mono fun a ha => support_single_subset) <| by
      rw [Finset.bUnion_singleton] <;> exact subset.refl _

theorem map_domain_apply' (S : Set α) {f : α → β} (x : α →₀ M) (hS : (x.Support : Set α) ⊆ S) (hf : Set.InjOn f S)
    {a : α} (ha : a ∈ S) : mapDomain f x (f a) = x a := by
  rw [map_domain, sum_apply, Sum]
  simp_rw [single_apply]
  have : ∀ (b : α) (ha1 : b ∈ x.support), (if f b = f a then x b else 0) = if f b = f a then x a else 0 := by
    intro b hb
    refine' if_ctx_congr Iff.rfl (fun hh => _) fun _ => rfl
    rw [hf (hS hb) ha hh]
  conv in ite _ _ _ => rw [this _ H]
  by_cases' ha : a ∈ x.support
  · rw [← Finset.add_sum_erase _ _ ha, if_pos rfl]
    convert add_zeroₓ _
    have : ∀ i ∈ x.support.erase a, f i ≠ f a := by
      intro i hi
      exact Finset.ne_of_mem_erase hi ∘ hf (hS <| Finset.mem_of_mem_erase hi) (hS ha)
    conv in ite _ _ _ => rw [if_neg (this x H)]
    exact Finset.sum_const_zero
    
  · rw [mem_support_iff, not_not] at ha
    simp [ha]
    

theorem map_domain_support_of_inj_on [DecidableEq β] {f : α → β} (s : α →₀ M) (hf : Set.InjOn f s.Support) :
    (mapDomain f s).Support = Finset.image f s.Support :=
  Finset.Subset.antisymm map_domain_support <| by
    intro x hx
    simp only [mem_image, exists_prop, mem_support_iff, Ne.def] at hx
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩
    simp only [mem_support_iff, Ne.def]
    rw [map_domain_apply' (↑s.support : Set _) _ _ hf]
    · exact hx_h_left
      
    · simp only [mem_coe, mem_support_iff, Ne.def]
      exact hx_h_left
      
    · exact subset.refl _
      

theorem map_domain_support_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f) (s : α →₀ M) :
    (mapDomain f s).Support = Finset.image f s.Support :=
  map_domain_support_of_inj_on s (hf.InjOn _)

@[to_additive]
theorem prod_map_domain_index [CommMonoidₓ N] {f : α → β} {s : α →₀ M} {h : β → M → N} (h_zero : ∀ b, h b 0 = 1)
    (h_add : ∀ b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) : (mapDomain f s).Prod h = s.Prod fun a m => h (f a) m :=
  (prod_sum_index h_zero h_add).trans <| prod_congr fun _ _ => prod_single_index (h_zero _)

-- Note that in `prod_map_domain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `monoid_hom`.
/-- A version of `sum_map_domain_index` that takes a bundled `add_monoid_hom`,
rather than separate linearity hypotheses.
-/
@[simp]
theorem sum_map_domain_index_add_monoid_hom [AddCommMonoidₓ N] {f : α → β} {s : α →₀ M} (h : β → M →+ N) :
    ((mapDomain f s).Sum fun b m => h b m) = s.Sum fun a m => h (f a) m :=
  @sum_map_domain_index _ _ _ _ _ _ _ _ (fun b m => h b m) (fun b => (h b).map_zero) fun b m₁ m₂ => (h b).map_add _ _

theorem emb_domain_eq_map_domain (f : α ↪ β) (v : α →₀ M) : embDomain f v = mapDomain f v := by
  ext a
  by_cases' a ∈ Set.Range f
  · rcases h with ⟨a, rfl⟩
    rw [map_domain_apply f.injective, emb_domain_apply]
    
  · rw [map_domain_notin_range, emb_domain_notin_range] <;> assumption
    

@[to_additive]
theorem prod_map_domain_index_inj [CommMonoidₓ N] {f : α → β} {s : α →₀ M} {h : β → M → N} (hf : Function.Injective f) :
    (s.mapDomain f).Prod h = s.Prod fun a b => h (f a) b := by
  rw [← Function.Embedding.coe_fn_mk f hf, ← emb_domain_eq_map_domain, prod_emb_domain]

theorem map_domain_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (mapDomain f : (α →₀ M) → β →₀ M) := by
  intro v₁ v₂ eq
  ext a
  have : map_domain f v₁ (f a) = map_domain f v₂ (f a) := by
    rw [Eq]
  rwa [map_domain_apply hf, map_domain_apply hf] at this

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ)  ↪ (β →₀ ℕ)` given by `map_domain`. -/
@[simps]
def mapDomainEmbedding {α β : Type _} (f : α ↪ β) : (α →₀ ℕ) ↪ β →₀ ℕ :=
  ⟨Finsupp.mapDomain f, Finsupp.map_domain_injective f.Injective⟩

theorem mapDomain.add_monoid_hom_comp_map_range [AddCommMonoidₓ N] (f : α → β) (g : M →+ N) :
    (mapDomain.addMonoidHom f).comp (mapRange.addMonoidHom g) =
      (mapRange.addMonoidHom g).comp (mapDomain.addMonoidHom f) :=
  by
  ext
  simp

/-- When `g` preserves addition, `map_range` and `map_domain` commute. -/
theorem map_domain_map_range [AddCommMonoidₓ N] (f : α → β) (v : α →₀ M) (g : M → N) (h0 : g 0 = 0)
    (hadd : ∀ x y, g (x + y) = g x + g y) : mapDomain f (mapRange g h0 v) = mapRange g h0 (mapDomain f v) :=
  let g' : M →+ N := { toFun := g, map_zero' := h0, map_add' := hadd }
  AddMonoidHom.congr_fun (mapDomain.add_monoid_hom_comp_map_range f g') v

theorem sum_update_add [AddCommMonoidₓ α] [AddCommMonoidₓ β] (f : ι →₀ α) (i : ι) (a : α) (g : ι → α → β)
    (hg : ∀ i, g i 0 = 0) (hgg : ∀ (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
    (f.update i a).Sum g + g i (f i) = f.Sum g + g i a := by
  rw [update_eq_erase_add_single, sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single, sum_add_index' hg hgg, add_assocₓ, add_assocₓ]
  congr 1
  rw [add_commₓ, sum_single_index (hg _), sum_single_index (hg _)]

theorem map_domain_inj_on (S : Set α) {f : α → β} (hf : Set.InjOn f S) :
    Set.InjOn (mapDomain f : (α →₀ M) → β →₀ M) { w | (w.Support : Set α) ⊆ S } := by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  by_cases' h : a ∈ v₁.support ∪ v₂.support
  · rw [← map_domain_apply' S _ hv₁ hf _, ← map_domain_apply' S _ hv₂ hf _, Eq] <;>
      · apply Set.union_subset hv₁ hv₂
        exact_mod_cast h
        
    
  · simp only [Decidable.not_or_iff_and_not, mem_union, not_not, mem_support_iff] at h
    simp [h]
    

theorem equiv_map_domain_eq_map_domain {M} [AddCommMonoidₓ M] (f : α ≃ β) (l : α →₀ M) :
    equivMapDomain f l = mapDomain f l := by
  ext x <;> simp [map_domain_equiv_apply]

end MapDomain

/-! ### Declarations about `comap_domain` -/


section ComapDomain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comap_domain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
@[simps Support]
def comapDomain [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.Support)) : α →₀ M where
  Support := l.Support.Preimage f hf
  toFun := fun a => l (f a)
  mem_support_to_fun := by
    intro a
    simp only [finset.mem_def.symm, Finset.mem_preimage]
    exact l.mem_support_to_fun (f a)

@[simp]
theorem comap_domain_apply [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.Support)) (a : α) :
    comapDomain f l hf a = l (f a) :=
  rfl

theorem sum_comap_domain [Zero M] [AddCommMonoidₓ N] (f : α → β) (l : β →₀ M) (g : β → M → N)
    (hf : Set.BijOn f (f ⁻¹' ↑l.Support) ↑l.Support) : (comapDomain f l hf.InjOn).Sum (g ∘ f) = l.Sum g := by
  simp only [Sum, comap_domain_apply, (· ∘ ·)]
  simp [comap_domain, Finset.sum_preimage_of_bij f _ _ fun x => g x (l x)]

theorem eq_zero_of_comap_domain_eq_zero [AddCommMonoidₓ M] (f : α → β) (l : β →₀ M)
    (hf : Set.BijOn f (f ⁻¹' ↑l.Support) ↑l.Support) : comapDomain f l hf.InjOn = 0 → l = 0 := by
  rw [← support_eq_empty, ← support_eq_empty, comap_domain]
  simp only [Finset.ext_iff, Finset.not_mem_empty, iff_falseₓ, mem_preimage]
  intro h a ha
  cases' hf.2.2 ha with b hb
  exact h b (hb.2.symm ▸ ha)

section FInjective

section Zero

variable [Zero M]

/-- Note the `hif` argument is needed for this to work in `rw`. -/
@[simp]
theorem comap_domain_zero (f : α → β) (hif : Set.InjOn f (f ⁻¹' ↑(0 : β →₀ M).Support) := Set.inj_on_empty _) :
    comapDomain f (0 : β →₀ M) hif = (0 : α →₀ M) := by
  ext
  rfl

@[simp]
theorem comap_domain_single (f : α → β) (a : α) (m : M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).Support)) :
    comapDomain f (Finsupp.single (f a) m) hif = Finsupp.single a m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp only [single_zero, comap_domain_zero]
    
  · rw [eq_single_iff, comap_domain_apply, comap_domain_support, ← Finset.coe_subset, coe_preimage,
      support_single_ne_zero _ hm, coe_singleton, coe_singleton, single_eq_same]
    rw [support_single_ne_zero _ hm, coe_singleton] at hif
    exact ⟨fun x hx => hif hx rfl hx, rfl⟩
    

end Zero

section AddZeroClassₓ

variable [AddZeroClassₓ M] {f : α → β}

theorem comap_domain_add (v₁ v₂ : β →₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.Support))
    (hv₂ : Set.InjOn f (f ⁻¹' ↑v₂.Support)) (hv₁₂ : Set.InjOn f (f ⁻¹' ↑(v₁ + v₂).Support)) :
    comapDomain f (v₁ + v₂) hv₁₂ = comapDomain f v₁ hv₁ + comapDomain f v₂ hv₂ := by
  ext
  simp only [comap_domain_apply, coe_add, Pi.add_apply]

/-- A version of `finsupp.comap_domain_add` that's easier to use. -/
theorem comap_domain_add_of_injective (hf : Function.Injective f) (v₁ v₂ : β →₀ M) :
    comapDomain f (v₁ + v₂) (hf.InjOn _) = comapDomain f v₁ (hf.InjOn _) + comapDomain f v₂ (hf.InjOn _) :=
  comap_domain_add _ _ _ _ _

/-- `finsupp.comap_domain` is an `add_monoid_hom`. -/
@[simps]
def comapDomain.addMonoidHom (hf : Function.Injective f) : (β →₀ M) →+ α →₀ M where
  toFun := fun x => comapDomain f x (hf.InjOn _)
  map_zero' := comap_domain_zero f
  map_add' := comap_domain_add_of_injective hf

end AddZeroClassₓ

variable [AddCommMonoidₓ M] (f : α → β)

theorem map_domain_comap_domain (hf : Function.Injective f) (l : β →₀ M) (hl : ↑l.Support ⊆ Set.Range f) :
    mapDomain f (comapDomain f l (hf.InjOn _)) = l := by
  ext a
  by_cases' h_cases : a ∈ Set.Range f
  · rcases Set.mem_range.1 h_cases with ⟨b, hb⟩
    rw [hb.symm, map_domain_apply hf, comap_domain_apply]
    
  · rw [map_domain_notin_range _ _ h_cases]
    by_contra h_contr
    apply h_cases (hl <| Finset.mem_coe.2 <| mem_support_iff.2 fun h => h_contr h.symm)
    

end FInjective

end ComapDomain

/-! ### Declarations about finitely supported functions whose support is an `option` type -/


section Option

/-- Restrict a finitely supported function on `option α` to a finitely supported function on `α`. -/
def some [Zero M] (f : Option α →₀ M) : α →₀ M :=
  f.comapDomain Option.some fun _ => by
    simp

@[simp]
theorem some_apply [Zero M] (f : Option α →₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl

@[simp]
theorem some_zero [Zero M] : (0 : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_add [AddCommMonoidₓ M] (f g : Option α →₀ M) : (f + g).some = f.some + g.some := by
  ext
  simp

@[simp]
theorem some_single_none [Zero M] (m : M) : (single none m : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_single_some [Zero M] (a : α) (m : M) : (single (Option.some a) m : Option α →₀ M).some = single a m := by
  ext b
  simp [single_apply]

@[to_additive]
theorem prod_option_index [AddCommMonoidₓ M] [CommMonoidₓ N] (f : Option α →₀ M) (b : Option α → M → N)
    (h_zero : ∀ o, b o 0 = 1) (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
    f.Prod b = b none (f none) * f.some.Prod fun a => b (Option.some a) := by
  apply induction_linear f
  · simp [h_zero]
    
  · intro f₁ f₂ h₁ h₂
    rw [Finsupp.prod_add_index, h₁, h₂, some_add, Finsupp.prod_add_index]
    simp only [h_add, Pi.add_apply, Finsupp.coe_add]
    rw [mul_mul_mul_commₓ]
    all_goals
      simp [h_zero, h_add]
    
  · rintro (_ | a) m <;> simp [h_zero, h_add]
    

theorem sum_option_index_smul [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (f : Option α →₀ R) (b : Option α → M) :
    (f.Sum fun o r => r • b o) = f none • b none + f.some.Sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

end Option

/-! ### Declarations about `filter` -/


section Filter

section Zero

variable [Zero M] (p : α → Prop) (f : α →₀ M)

/-- `filter p f` is the finitely supported function that is `f a` if `p a` is true and 0 otherwise. -/
def filter (p : α → Prop) (f : α →₀ M) : α →₀ M where
  toFun := fun a => if p a then f a else 0
  Support := f.Support.filter fun a => p a
  mem_support_to_fun := fun a => by
    split_ifs <;>
      · simp only [h, mem_filter, mem_support_iff]
        tauto
        

theorem filter_apply (a : α) [D : Decidable (p a)] : f.filter p a = if p a then f a else 0 := by
  rw [Subsingleton.elimₓ D] <;> rfl

theorem filter_eq_indicator : ⇑(f.filter p) = Set.indicatorₓ { x | p x } f :=
  rfl

theorem filter_eq_zero_iff : f.filter p = 0 ↔ ∀ x, p x → f x = 0 := by
  simp only [FunLike.ext_iff, filter_eq_indicator, zero_apply, Set.indicator_apply_eq_zero, Set.mem_set_of_eq]

theorem filter_eq_self_iff : f.filter p = f ↔ ∀ x, f x ≠ 0 → p x := by
  simp only [FunLike.ext_iff, filter_eq_indicator, Set.indicator_apply_eq_self, Set.mem_set_of_eq, not_imp_comm]

@[simp]
theorem filter_apply_pos {a : α} (h : p a) : f.filter p a = f a :=
  if_pos h

@[simp]
theorem filter_apply_neg {a : α} (h : ¬p a) : f.filter p a = 0 :=
  if_neg h

@[simp]
theorem support_filter [D : DecidablePred p] : (f.filter p).Support = f.Support.filter p := by
  rw [Subsingleton.elimₓ D] <;> rfl

theorem filter_zero : (0 : α →₀ M).filter p = 0 := by
  rw [← support_eq_empty, support_filter, support_zero, Finset.filter_empty]

@[simp]
theorem filter_single_of_pos {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
  (filter_eq_self_iff _ _).2 fun x hx => (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp]
theorem filter_single_of_neg {a : α} {b : M} (h : ¬p a) : (single a b).filter p = 0 :=
  (filter_eq_zero_iff _ _).2 fun x hpx => single_apply_eq_zero.2 fun hxa => absurd hpx (hxa.symm ▸ h)

@[to_additive]
theorem prod_filter_index [CommMonoidₓ N] (g : α → M → N) :
    (f.filter p).Prod g = ∏ x in (f.filter p).Support, g x (f x) := by
  refine' Finset.prod_congr rfl fun x hx => _
  rw [support_filter, Finset.mem_filter] at hx
  rw [filter_apply_pos _ _ hx.2]

@[simp, to_additive]
theorem prod_filter_mul_prod_filter_not [CommMonoidₓ N] (g : α → M → N) :
    (f.filter p).Prod g * (f.filter fun a => ¬p a).Prod g = f.Prod g := by
  simp_rw [prod_filter_index, support_filter, prod_filter_mul_prod_filter_not, Finsupp.prod]

@[simp, to_additive]
theorem prod_div_prod_filter [CommGroupₓ G] (g : α → M → G) :
    f.Prod g / (f.filter p).Prod g = (f.filter fun a => ¬p a).Prod g :=
  div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

end Zero

theorem filter_pos_add_filter_neg [AddZeroClassₓ M] (f : α →₀ M) (p : α → Prop) :
    (f.filter p + f.filter fun a => ¬p a) = f :=
  coe_fn_injective <| Set.indicator_self_add_compl { x | p x } f

end Filter

/-! ### Declarations about `frange` -/


section Frange

variable [Zero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange (f : α →₀ M) : Finset M :=
  Finset.image f f.Support

theorem mem_frange {f : α →₀ M} {y : M} : y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y :=
  Finset.mem_image.trans
    ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩, fun ⟨hy, x, hx⟩ =>
      ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_not_mem_frange {f : α →₀ M} : (0 : M) ∉ f.frange := fun H => (mem_frange.1 H).1 rfl

theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} := fun r hr =>
  let ⟨t, ht1, ht2⟩ := mem_frange.1 hr
  ht2 ▸ by
    rw [single_apply] at ht2⊢ <;> split_ifs  at ht2⊢ <;> [exact Finset.mem_singleton_self _, cc]

end Frange

/-! ### Declarations about `subtype_domain` -/


section SubtypeDomain

section Zero

variable [Zero M] {p : α → Prop}

/-- `subtype_domain p f` is the restriction of the finitely supported function `f` to subtype `p`. -/
def subtypeDomain (p : α → Prop) (f : α →₀ M) : Subtype p →₀ M :=
  ⟨f.Support.Subtype p, f ∘ coe, fun a => by
    simp only [mem_subtype, mem_support_iff]⟩

@[simp]
theorem support_subtype_domain [D : DecidablePred p] {f : α →₀ M} : (subtypeDomain p f).Support = f.Support.Subtype p :=
  by
  rw [Subsingleton.elimₓ D] <;> rfl

@[simp]
theorem subtype_domain_apply {a : Subtype p} {v : α →₀ M} : (subtypeDomain p v) a = v a.val :=
  rfl

@[simp]
theorem subtype_domain_zero : subtypeDomain p (0 : α →₀ M) = 0 :=
  rfl

theorem subtype_domain_eq_zero_iff' {f : α →₀ M} : f.subtypeDomain p = 0 ↔ ∀ x, p x → f x = 0 := by
  simp_rw [← support_eq_empty, support_subtype_domain, subtype_eq_empty, not_mem_support_iff]

theorem subtype_domain_eq_zero_iff {f : α →₀ M} (hf : ∀ x ∈ f.Support, p x) : f.subtypeDomain p = 0 ↔ f = 0 :=
  subtype_domain_eq_zero_iff'.trans
    ⟨fun H => ext fun x => if hx : p x then H x hx else not_mem_support_iff.1 <| mt (hf x) hx, fun H x _ => by
      simp [H]⟩

@[to_additive]
theorem prod_subtype_domain_index [CommMonoidₓ N] {v : α →₀ M} {h : α → M → N} (hp : ∀ x ∈ v.Support, p x) :
    ((v.subtypeDomain p).Prod fun a b => h a b) = v.Prod h :=
  prod_bij (fun p _ => p.val) (fun _ => mem_subtype.1) (fun _ _ => rfl) (fun _ _ _ _ => Subtype.eq) fun b hb =>
    ⟨⟨b, hp b hb⟩, mem_subtype.2 hb, rfl⟩

end Zero

section AddZeroClassₓ

variable [AddZeroClassₓ M] {p : α → Prop} {v v' : α →₀ M}

@[simp]
theorem subtype_domain_add {v v' : α →₀ M} : (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  ext fun _ => rfl

/-- `subtype_domain` but as an `add_monoid_hom`. -/
def subtypeDomainAddMonoidHom : (α →₀ M) →+ Subtype p →₀ M where
  toFun := subtypeDomain p
  map_zero' := subtype_domain_zero
  map_add' := fun _ _ => subtype_domain_add

/-- `finsupp.filter` as an `add_monoid_hom`. -/
def filterAddHom (p : α → Prop) : (α →₀ M) →+ α →₀ M where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' := fun f g => coe_fn_injective <| Set.indicator_add { x | p x } f g

@[simp]
theorem filter_add {v v' : α →₀ M} : (v + v').filter p = v.filter p + v'.filter p :=
  (filterAddHom p).map_add v v'

end AddZeroClassₓ

section CommMonoidₓ

variable [AddCommMonoidₓ M] {p : α → Prop}

theorem subtype_domain_sum {s : Finset ι} {h : ι → α →₀ M} :
    (∑ c in s, h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p :=
  (subtypeDomainAddMonoidHom : _ →+ Subtype p →₀ M).map_sum _ s

theorem subtype_domain_finsupp_sum [Zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
    (s.Sum h).subtypeDomain p = s.Sum fun c d => (h c d).subtypeDomain p :=
  subtype_domain_sum

theorem filter_sum (s : Finset ι) (f : ι → α →₀ M) : (∑ a in s, f a).filter p = ∑ a in s, filter p (f a) :=
  (filterAddHom p : (α →₀ M) →+ _).map_sum f s

theorem filter_eq_sum (p : α → Prop) [D : DecidablePred p] (f : α →₀ M) :
    f.filter p = ∑ i in f.Support.filter p, single i (f i) :=
  (f.filter p).sum_single.symm.trans <|
    (Finset.sum_congr
        (by
          rw [Subsingleton.elimₓ D] <;> rfl))
      fun x hx => by
      rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end CommMonoidₓ

section Groupₓ

variable [AddGroupₓ G] {p : α → Prop} {v v' : α →₀ G}

@[simp]
theorem subtype_domain_neg : (-v).subtypeDomain p = -v.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
theorem subtype_domain_sub : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
theorem single_neg (a : α) (b : G) : single a (-b) = -single a b :=
  (singleAddHom a : G →+ _).map_neg b

@[simp]
theorem single_sub (a : α) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  (singleAddHom a : G →+ _).map_sub b₁ b₂

@[simp]
theorem erase_neg (a : α) (f : α →₀ G) : erase a (-f) = -erase a f :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_neg f

@[simp]
theorem erase_sub (a : α) (f₁ f₂ : α →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_sub f₁ f₂

@[simp]
theorem filter_neg (p : α → Prop) (f : α →₀ G) : filter p (-f) = -filter p f :=
  (filterAddHom p : (_ →₀ G) →+ _).map_neg f

@[simp]
theorem filter_sub (p : α → Prop) (f₁ f₂ : α →₀ G) : filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
  (filterAddHom p : (_ →₀ G) →+ _).map_sub f₁ f₂

end Groupₓ

end SubtypeDomain

theorem mem_support_multiset_sum [AddCommMonoidₓ M] {s : Multiset (α →₀ M)} (a : α) :
    a ∈ s.Sum.Support → ∃ f ∈ s, a ∈ (f : α →₀ M).Support :=
  Multiset.induction_on s False.elim
    (by
      intro f s ih ha
      by_cases' a ∈ f.support
      · exact ⟨f, Multiset.mem_cons_self _ _, h⟩
        
      · simp only [Multiset.sum_cons, mem_support_iff, add_apply, not_mem_support_iff.1 h, zero_addₓ] at ha
        rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩
        exact ⟨f', Multiset.mem_cons_of_mem h₀, h₁⟩
        )

theorem mem_support_finset_sum [AddCommMonoidₓ M] {s : Finset ι} {h : ι → α →₀ M} (a : α)
    (ha : a ∈ (∑ c in s, h c).Support) : ∃ c ∈ s, a ∈ (h c).Support :=
  let ⟨f, hf, hfa⟩ := mem_support_multiset_sum a ha
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩

/-! ### Declarations about `curry` and `uncurry` -/


section CurryUncurry

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N]

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry (f : α × β →₀ M) : α →₀ β →₀ M :=
  f.Sum fun p c => single p.1 (single p.2 c)

@[simp]
theorem curry_apply (f : α × β →₀ M) (x : α) (y : β) : f.curry x y = f (x, y) := by
  have : ∀ b : α × β, single b.fst (single b.snd (f b)) x y = if b = (x, y) then f b else 0 := by
    rintro ⟨b₁, b₂⟩
    simp [single_apply, ite_apply, Prod.ext_iff, ite_and]
    split_ifs <;> simp [single_apply, *]
  rw [Finsupp.curry, sum_apply, sum_apply, Finsupp.sum, Finset.sum_eq_single, this, if_pos rfl]
  · intro b hb b_ne
    rw [this b, if_neg b_ne]
    
  · intro hxy
    rw [this (x, y), if_pos rfl, not_mem_support_iff.mp hxy]
    

theorem sum_curry_index (f : α × β →₀ M) (g : α → β → M → N) (hg₀ : ∀ a b, g a b 0 = 0)
    (hg₁ : ∀ a b c₀ c₁, g a b (c₀ + c₁) = g a b c₀ + g a b c₁) :
    (f.curry.Sum fun a f => f.Sum (g a)) = f.Sum fun p c => g p.1 p.2 c := by
  rw [Finsupp.curry]
  trans
  · exact
      sum_sum_index (fun a => sum_zero_index) fun a b₀ b₁ =>
        sum_add_index' (fun a => hg₀ _ _) fun c d₀ d₁ => hg₁ _ _ _ _
    
  congr
  funext p c
  trans
  · exact sum_single_index sum_zero_index
    
  exact sum_single_index (hg₀ _ _)

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry (f : α →₀ β →₀ M) : α × β →₀ M :=
  f.Sum fun a g => g.Sum fun b c => single (a, b) c

/-- `finsupp_prod_equiv` defines the `equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
def finsuppProdEquiv : (α × β →₀ M) ≃ (α →₀ β →₀ M) := by
  refine' ⟨Finsupp.curry, Finsupp.uncurry, fun f => _, fun f => _⟩ <;>
    simp only [Finsupp.curry, Finsupp.uncurry, sum_sum_index, sum_zero_index, sum_add_index, sum_single_index,
      single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, Prod.mk.eta,
      (single_sum _ _ _).symm, sum_single]

theorem filter_curry (f : α × β →₀ M) (p : α → Prop) : (f.filter fun a : α × β => p a.1).curry = f.curry.filter p := by
  rw [Finsupp.curry, Finsupp.curry, Finsupp.sum, Finsupp.sum, filter_sum, support_filter, sum_filter]
  refine' Finset.sum_congr rfl _
  rintro ⟨a₁, a₂⟩ ha
  dsimp' only
  split_ifs
  · rw [filter_apply_pos, filter_single_of_pos] <;> exact h
    
  · rwa [filter_single_of_neg]
    

theorem support_curry [DecidableEq α] (f : α × β →₀ M) : f.curry.Support ⊆ f.Support.Image Prod.fst := by
  rw [← Finset.bUnion_singleton]
  refine' Finset.Subset.trans support_sum _
  refine' Finset.bUnion_mono fun a _ => support_single_subset

end CurryUncurry

/-! ### Declarations about finitely supported functions whose support is a `sum` type -/


section Sum

/-- `finsupp.sum_elim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
def sumElim {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) : Sum α β →₀ γ :=
  onFinset (f.Support.map ⟨_, Sum.inl_injective⟩ ∪ g.Support.map ⟨_, Sum.inr_injective⟩) (Sum.elim f g) fun ab h => by
    cases' ab with a b <;> simp only [Sum.elim_inl, Sum.elim_inr] at h <;> simpa

@[simp]
theorem coe_sum_elim {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) : ⇑(sumElim f g) = Sum.elim f g :=
  rfl

theorem sum_elim_apply {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : Sum α β) :
    sumElim f g x = Sum.elim f g x :=
  rfl

theorem sum_elim_inl {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : α) : sumElim f g (Sum.inl x) = f x :=
  rfl

theorem sum_elim_inr {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : β) : sumElim f g (Sum.inr x) = g x :=
  rfl

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symmApply]
def sumFinsuppEquivProdFinsupp {α β γ : Type _} [Zero γ] : (Sum α β →₀ γ) ≃ (α →₀ γ) × (β →₀ γ) where
  toFun := fun f =>
    ⟨f.comapDomain Sum.inl (Sum.inl_injective.InjOn _), f.comapDomain Sum.inr (Sum.inr_injective.InjOn _)⟩
  invFun := fun fg => sumElim fg.1 fg.2
  left_inv := fun f => by
    ext ab
    cases' ab with a b <;> simp
  right_inv := fun fg => by
    ext <;> simp

theorem fst_sum_finsupp_equiv_prod_finsupp {α β γ : Type _} [Zero γ] (f : Sum α β →₀ γ) (x : α) :
    (sumFinsuppEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sum_finsupp_equiv_prod_finsupp {α β γ : Type _} [Zero γ] (f : Sum α β →₀ γ) (y : β) :
    (sumFinsuppEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl

theorem sum_finsupp_equiv_prod_finsupp_symm_inl {α β γ : Type _} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ)) (x : α) :
    (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sum_finsupp_equiv_prod_finsupp_symm_inr {α β γ : Type _} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ)) (y : β) :
    (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

variable [AddMonoidₓ M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symmApply]
def sumFinsuppAddEquivProdFinsupp {α β : Type _} : (Sum α β →₀ M) ≃+ (α →₀ M) × (β →₀ M) :=
  { sumFinsuppEquivProdFinsupp with
    map_add' := by
      intros
      ext <;>
        simp only [Equivₓ.to_fun_as_coe, Prod.fst_add, Prod.snd_add, add_apply, snd_sum_finsupp_equiv_prod_finsupp,
          fst_sum_finsupp_equiv_prod_finsupp] }

theorem fst_sum_finsupp_add_equiv_prod_finsupp {α β : Type _} (f : Sum α β →₀ M) (x : α) :
    (sumFinsuppAddEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sum_finsupp_add_equiv_prod_finsupp {α β : Type _} (f : Sum α β →₀ M) (y : β) :
    (sumFinsuppAddEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl

theorem sum_finsupp_add_equiv_prod_finsupp_symm_inl {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sum_finsupp_add_equiv_prod_finsupp_symm_inr {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

/-! ### Declarations about scalar multiplication -/


section

variable [Zero M] [MonoidWithZeroₓ R] [MulActionWithZero R M]

@[simp]
theorem single_smul (a b : α) (f : α → M) (r : R) : single a r b • f a = single a (r • f b) b := by
  by_cases' a = b <;> simp [h]

end

section

variable [Monoidₓ G] [MulAction G α] [AddCommMonoidₓ M]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts. -/
def comapHasSmul : HasSmul G (α →₀ M) where smul := fun g => mapDomain ((· • ·) g)

attribute [local instance] comap_has_smul

theorem comap_smul_def (g : G) (f : α →₀ M) : g • f = mapDomain ((· • ·) g) f :=
  rfl

@[simp]
theorem comap_smul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  map_domain_single

/-- `finsupp.comap_has_smul` is multiplicative -/
def comapMulAction : MulAction G (α →₀ M) where
  one_smul := fun f => by
    rw [comap_smul_def, one_smul_eq_id, map_domain_id]
  mul_smul := fun g g' f => by
    rw [comap_smul_def, comap_smul_def, comap_smul_def, ← comp_smul_left, map_domain_comp]

attribute [local instance] comap_mul_action

/-- `finsupp.comap_has_smul` is distributive -/
def comapDistribMulAction : DistribMulAction G (α →₀ M) where
  smul_zero := fun g => by
    ext
    dsimp' [(· • ·)]
    simp
  smul_add := fun g f f' => by
    ext
    dsimp' [(· • ·)]
    simp [map_domain_add]

end

section

variable [Groupₓ G] [MulAction G α] [AddCommMonoidₓ M]

attribute [local instance] comap_has_smul comap_mul_action comap_distrib_mul_action

/-- When `G` is a group, `finsupp.comap_has_smul` acts by precomposition with the action of `g⁻¹`.
-/
@[simp]
theorem comap_smul_apply (g : G) (f : α →₀ M) (a : α) : (g • f) a = f (g⁻¹ • a) := by
  conv_lhs => rw [← smul_inv_smul g a]
  exact map_domain_apply (MulAction.injective g) _ (g⁻¹ • a)

end

section

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : HasSmul R (α →₀ M) :=
  ⟨fun a v => v.map_range ((· • ·) a) (smul_zero _)⟩

/-!
Throughout this section, some `monoid` and `semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/


@[simp]
theorem coe_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (b : R) (v : α →₀ M) : ⇑(b • v) = b • v :=
  rfl

theorem smul_apply {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (b : R) (v : α →₀ M) (a : α) :
    (b • v) a = b • v a :=
  rfl

theorem _root_.is_smul_regular.finsupp {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {k : R}
    (hk : IsSmulRegular M k) : IsSmulRegular (α →₀ M) k := fun _ _ h => ext fun i => hk (congr_fun h i)

instance [Monoidₓ R] [Nonempty α] [AddMonoidₓ M] [DistribMulAction R M] [HasFaithfulSmul R M] :
    HasFaithfulSmul R (α →₀ M) where eq_of_smul_eq_smul := fun r₁ r₂ h =>
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun m : M => by
      simpa using congr_fun (h (single a m)) a

variable (α M)

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction R (α →₀ M) where
  smul := (· • ·)
  smul_add := fun a x y => ext fun _ => smul_add _ _ _
  one_smul := fun x => ext fun _ => one_smul _ _
  mul_smul := fun r s x => ext fun _ => mul_smul _ _ _
  smul_zero := fun x => ext fun _ => smul_zero _

instance [Monoidₓ R] [Monoidₓ S] [AddMonoidₓ M] [DistribMulAction R M] [DistribMulAction S M] [HasSmul R S]
    [IsScalarTower R S M] : IsScalarTower R S (α →₀ M) where smul_assoc := fun r s a => ext fun _ => smul_assoc _ _ _

instance [Monoidₓ R] [Monoidₓ S] [AddMonoidₓ M] [DistribMulAction R M] [DistribMulAction S M] [SmulCommClass R S M] :
    SmulCommClass R S (α →₀ M) where smul_comm := fun r s a => ext fun _ => smul_comm _ _ _

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsCentralScalar R (α →₀ M) where op_smul_eq_smul := fun r a => ext fun _ => op_smul_eq_smul _ _

instance [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module R (α →₀ M) :=
  { Finsupp.distribMulAction α M with smul := (· • ·), zero_smul := fun x => ext fun _ => zero_smul _ _,
    add_smul := fun a x y => ext fun _ => add_smul _ _ _ }

variable {α M} {R}

theorem support_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {b : R} {g : α →₀ M} :
    (b • g).Support ⊆ g.Support := fun a => by
  simp only [smul_apply, mem_support_iff, Ne.def]
  exact mt fun h => h.symm ▸ smul_zero _

@[simp]
theorem support_smul_eq [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [NoZeroSmulDivisors R M] {b : R} (hb : b ≠ 0)
    {g : α →₀ M} : (b • g).Support = g.Support :=
  Finset.ext fun a => by
    simp [Finsupp.smul_apply, hb]

section

variable {p : α → Prop}

@[simp]
theorem filter_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {b : R} {v : α →₀ M} :
    (b • v).filter p = b • v.filter p :=
  coe_fn_injective <| Set.indicator_const_smul { x | p x } b v

end

theorem map_domain_smul {_ : Monoidₓ R} [AddCommMonoidₓ M] [DistribMulAction R M] {f : α → β} (b : R) (v : α →₀ M) :
    mapDomain f (b • v) = b • mapDomain f v :=
  map_domain_map_range _ _ _ _ (smul_add b)

@[simp]
theorem smul_single {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (c : R) (a : α) (b : M) :
    c • Finsupp.single a b = Finsupp.single a (c • b) :=
  map_range_single

@[simp]
theorem smul_single' {_ : Semiringₓ R} (c : R) (a : α) (b : R) : c • Finsupp.single a b = Finsupp.single a (c * b) :=
  smul_single _ _ _

theorem map_range_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] [AddMonoidₓ N] [DistribMulAction R N]
    {f : M → N} {hf : f 0 = 0} (c : R) (v : α →₀ M) (hsmul : ∀ x, f (c • x) = c • f x) :
    mapRange f hf (c • v) = c • mapRange f hf v := by
  erw [← map_range_comp]
  have : f ∘ (· • ·) c = (· • ·) c ∘ f := funext hsmul
  simp_rw [this]
  apply map_range_comp
  rw [Function.comp_applyₓ, smul_zero, hf]

theorem smul_single_one [Semiringₓ R] (a : α) (b : R) : b • single a 1 = single a b := by
  rw [smul_single, smul_eq_mul, mul_oneₓ]

theorem comap_domain_smul [AddMonoidₓ M] [Monoidₓ R] [DistribMulAction R M] {f : α → β} (r : R) (v : β →₀ M)
    (hfv : Set.InjOn f (f ⁻¹' ↑v.Support))
    (hfrv : Set.InjOn f (f ⁻¹' ↑(r • v).Support) :=
      hfv.mono <| Set.preimage_mono <| Finset.coe_subset.mpr support_smul) :
    comapDomain f (r • v) hfrv = r • comapDomain f v hfv := by
  ext
  rfl

/-- A version of `finsupp.comap_domain_smul` that's easier to use. -/
theorem comap_domain_smul_of_injective [AddMonoidₓ M] [Monoidₓ R] [DistribMulAction R M] {f : α → β}
    (hf : Function.Injective f) (r : R) (v : β →₀ M) :
    comapDomain f (r • v) (hf.InjOn _) = r • comapDomain f v (hf.InjOn _) :=
  comap_domain_smul _ _ _ _

end

theorem sum_smul_index [Semiringₓ R] [AddCommMonoidₓ M] {g : α →₀ R} {b : R} {h : α → R → M} (h0 : ∀ i, h i 0 = 0) :
    (b • g).Sum h = g.Sum fun i a => h i (b * a) :=
  Finsupp.sum_map_range_index h0

theorem sum_smul_index' [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] [AddCommMonoidₓ N] {g : α →₀ M} {b : R}
    {h : α → M → N} (h0 : ∀ i, h i 0 = 0) : (b • g).Sum h = g.Sum fun i c => h i (b • c) :=
  Finsupp.sum_map_range_index h0

/-- A version of `finsupp.sum_smul_index'` for bundled additive maps. -/
theorem sum_smul_index_add_monoid_hom [Monoidₓ R] [AddMonoidₓ M] [AddCommMonoidₓ N] [DistribMulAction R M] {g : α →₀ M}
    {b : R} {h : α → M →+ N} : ((b • g).Sum fun a => h a) = g.Sum fun i c => h i (b • c) :=
  sum_map_range_index fun i => (h i).map_zero

instance [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] {ι : Type _} [NoZeroSmulDivisors R M] :
    NoZeroSmulDivisors R (ι →₀ M) :=
  ⟨fun c f h =>
    or_iff_not_imp_left.mpr fun hc => Finsupp.ext fun i => (smul_eq_zero.mp (Finsupp.ext_iff.mp h i)).resolve_left hc⟩

section DistribMulActionHom

variable [Semiringₓ R]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [DistribMulAction R M] [DistribMulAction R N]

/-- `finsupp.single` as a `distrib_mul_action_hom`.

See also `finsupp.lsingle` for the version as a linear map. -/
def DistribMulActionHom.single (a : α) : M →+[R] α →₀ M :=
  { singleAddHom a with
    map_smul' := fun k m => by
      simp only [AddMonoidHom.to_fun_eq_coe, single_add_hom_apply, smul_single] }

theorem distrib_mul_action_hom_ext {f g : (α →₀ M) →+[R] N} (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) :
    f = g :=
  DistribMulActionHom.to_add_monoid_hom_injective <| add_hom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem distrib_mul_action_hom_ext' {f g : (α →₀ M) →+[R] N}
    (h : ∀ a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) : f = g :=
  distrib_mul_action_hom_ext fun a => DistribMulActionHom.congr_fun (h a)

end DistribMulActionHom

section

variable [Zero R]

/-- The `finsupp` version of `pi.unique`. -/
instance uniqueOfRight [Subsingleton R] : Unique (α →₀ R) :=
  FunLike.coe_injective.unique

/-- The `finsupp` version of `pi.unique_of_is_empty`. -/
instance uniqueOfLeft [IsEmpty α] : Unique (α →₀ R) :=
  FunLike.coe_injective.unique

end

/-- Given an `add_comm_monoid M` and `s : set α`, `restrict_support_equiv s M` is the `equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
def restrictSupportEquiv (s : Set α) (M : Type _) [AddCommMonoidₓ M] : { f : α →₀ M // ↑f.Support ⊆ s } ≃ (s →₀ M) := by
  refine' ⟨fun f => subtype_domain (fun x => x ∈ s) f.1, fun f => ⟨f.mapDomain Subtype.val, _⟩, _, _⟩
  · refine' Set.Subset.trans (Finset.coe_subset.2 map_domain_support) _
    rw [Finset.coe_image, Set.image_subset_iff]
    exact fun x hx => x.2
    
  · rintro ⟨f, hf⟩
    apply Subtype.eq
    ext a
    dsimp' only
    refine' Classical.by_cases (fun h : a ∈ Set.Range (Subtype.val : s → α) => _) fun h => _
    · rcases h with ⟨x, rfl⟩
      rw [map_domain_apply Subtype.val_injective, subtype_domain_apply]
      
    · convert map_domain_notin_range _ _ h
      rw [← not_mem_support_iff]
      refine' mt _ h
      exact fun ha => ⟨⟨a, hf ha⟩, rfl⟩
      
    
  · intro f
    ext ⟨a, ha⟩
    dsimp' only
    rw [subtype_domain_apply, map_domain_apply Subtype.val_injective]
    

/-- Given `add_comm_monoid M` and `e : α ≃ β`, `dom_congr e` is the corresponding `equiv` between
`α →₀ M` and `β →₀ M`.

This is `finsupp.equiv_congr_left` as an `add_equiv`. -/
@[simps apply]
protected def domCongr [AddCommMonoidₓ M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) where
  toFun := equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv := fun v => by
    simp only [← equiv_map_domain_trans, Equivₓ.self_trans_symm]
    exact equiv_map_domain_refl _
  right_inv := by
    intro v
    simp only [← equiv_map_domain_trans, Equivₓ.symm_trans_self]
    exact equiv_map_domain_refl _
  map_add' := fun a b => by
    simp only [equiv_map_domain_eq_map_domain] <;> exact map_domain_add

@[simp]
theorem dom_congr_refl [AddCommMonoidₓ M] : Finsupp.domCongr (Equivₓ.refl α) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext fun _ => equiv_map_domain_refl _

@[simp]
theorem dom_congr_symm [AddCommMonoidₓ M] (e : α ≃ β) :
    (Finsupp.domCongr e).symm = (Finsupp.domCongr e.symm : (β →₀ M) ≃+ (α →₀ M)) :=
  AddEquiv.ext fun _ => rfl

@[simp]
theorem dom_congr_trans [AddCommMonoidₓ M] (e : α ≃ β) (f : β ≃ γ) :
    (Finsupp.domCongr e).trans (Finsupp.domCongr f) = (Finsupp.domCongr (e.trans f) : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => (equiv_map_domain_trans _ _ _).symm

end Finsupp

namespace Finsupp

/-! ### Declarations about sigma types -/


section Sigma

variable {αs : ι → Type _} [Zero M] (l : (Σi, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `finsupp` version of `sigma.curry`.
-/
def split (i : ι) : αs i →₀ M :=
  l.comapDomain (Sigma.mk i) fun x1 x2 _ _ hx => heq_iff_eq.1 (Sigma.mk.inj hx).2

theorem split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ := by
  dunfold split
  rw [comap_domain_apply]

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def splitSupport : Finset ι :=
  l.Support.Image Sigma.fst

theorem mem_split_support_iff_nonzero (i : ι) : i ∈ splitSupport l ↔ split l i ≠ 0 := by
  rw [split_support, mem_image, Ne.def, ← support_eq_empty, ← Ne.def, ← Finset.nonempty_iff_ne_empty, split,
    comap_domain, Finset.Nonempty]
  simp only [exists_prop, Finset.mem_preimage, exists_and_distrib_right, exists_eq_right, mem_support_iff, Sigma.exists,
    Ne.def]

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
def splitComp [Zero N] (g : ∀ i, (αs i →₀ M) → N) (hg : ∀ i x, x = 0 ↔ g i x = 0) : ι →₀ N where
  Support := splitSupport l
  toFun := fun i => g i (split l i)
  mem_support_to_fun := by
    intro i
    rw [mem_split_support_iff_nonzero, not_iff_not, hg]

theorem sigma_support : l.Support = l.splitSupport.Sigma fun i => (l.split i).Support := by
  simp only [Finset.ext_iff, split_support, split, comap_domain, mem_image, mem_preimage, Sigma.forall, mem_sigma] <;>
    tauto

theorem sigma_sum [AddCommMonoidₓ N] (f : (Σi : ι, αs i) → M → N) :
    l.Sum f = ∑ i in splitSupport l, (split l i).Sum fun (a : αs i) b => f ⟨i, a⟩ b := by
  simp only [Sum, sigma_support, sum_sigma, split_apply]

variable {η : Type _} [Fintype η] {ιs : η → Type _} [Zero α]

/-- On a `fintype η`, `finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `finsupp` version of `equiv.Pi_curry`. -/
noncomputable def sigmaFinsuppEquivPiFinsupp : ((Σj, ιs j) →₀ α) ≃ ∀ j, ιs j →₀ α where
  toFun := split
  invFun := fun f =>
    onFinset (Finset.univ.Sigma fun j => (f j).Support) (fun ji => f ji.1 ji.2) fun g hg =>
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩
  left_inv := fun f => by
    ext
    simp [split]
  right_inv := fun f => by
    ext
    simp [split]

@[simp]
theorem sigma_finsupp_equiv_pi_finsupp_apply (f : (Σj, ιs j) →₀ α) (j i) :
    sigmaFinsuppEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

/-- On a `fintype η`, `finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `add_equiv` version of `finsupp.sigma_finsupp_equiv_pi_finsupp`.
-/
noncomputable def sigmaFinsuppAddEquivPiFinsupp {α : Type _} {ιs : η → Type _} [AddMonoidₓ α] :
    ((Σj, ιs j) →₀ α) ≃+ ∀ j, ιs j →₀ α :=
  { sigmaFinsuppEquivPiFinsupp with
    map_add' := fun f g => by
      ext
      simp }

@[simp]
theorem sigma_finsupp_add_equiv_pi_finsupp_apply {α : Type _} {ιs : η → Type _} [AddMonoidₓ α] (f : (Σj, ιs j) →₀ α)
    (j i) : sigmaFinsuppAddEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

end Sigma

end Finsupp

