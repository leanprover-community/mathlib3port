/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Data.List.Nodup

#align_import data.prod.tprod from "leanprover-community/mathlib"@"c227d107bbada5d0d9d20287e3282c0a7f1651a0"

/-!
# Finite products of types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the product of types over a list. For `l : list ι` and `α : ι → Type*` we define
`list.tprod α l = l.foldr (λ i β, α i × β) punit`.
This type should not be used if `Π i, α i` or `Π i ∈ l, α i` can be used instead
(in the last expression, we could also replace the list `l` by a set or a finset).
This type is used as an intermediary between binary products and finitary products.
The application of this type is finitary product measures, but it could be used in any
construction/theorem that is easier to define/prove on binary products than on finitary products.

* Once we have the construction on binary products (like binary product measures in
  `measure_theory.prod`), we can easily define a finitary version on the type `tprod l α`
  by iterating. Properties can also be easily extended from the binary case to the finitary case
  by iterating.
* Then we can use the equivalence `list.tprod.pi_equiv_tprod` below (or enhanced versions of it,
  like a `measurable_equiv` for product measures) to get the construction on `Π i : ι, α i`, at
  least when assuming `[fintype ι] [encodable ι]` (using `encodable.sorted_univ`).
  Using `local attribute [instance] fintype.to_encodable` we can get rid of the argument
  `[encodable ι]`.

## Main definitions

* We have the equivalence `tprod.pi_equiv_tprod : (Π i, α i) ≃ tprod α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `set.tprod : (Π i, set (α i)) → set (tprod α l)`.
-/


open List Function

variable {ι : Type _} {α : ι → Type _} {i j : ι} {l : List ι} {f : ∀ i, α i}

namespace List

variable (α)

#print List.TProd /-
/-- The product of a family of types over a list. -/
def TProd (l : List ι) : Type _ :=
  l.foldr (fun i β => α i × β) PUnit
#align list.tprod List.TProd
-/

variable {α}

namespace Tprod

open List

#print List.TProd.mk /-
/-- Turning a function `f : Π i, α i` into an element of the iterated product `tprod α l`. -/
protected def mk : ∀ (l : List ι) (f : ∀ i, α i), TProd α l
  | [] => fun f => PUnit.unit
  | i :: is => fun f => (f i, mk is f)
#align list.tprod.mk List.TProd.mk
-/

instance [∀ i, Inhabited (α i)] : Inhabited (TProd α l) :=
  ⟨TProd.mk l default⟩

#print List.TProd.fst_mk /-
@[simp]
theorem fst_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (TProd.mk (i :: l) f).1 = f i :=
  rfl
#align list.tprod.fst_mk List.TProd.fst_mk
-/

#print List.TProd.snd_mk /-
@[simp]
theorem snd_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (TProd.mk (i :: l) f).2 = TProd.mk l f :=
  rfl
#align list.tprod.snd_mk List.TProd.snd_mk
-/

variable [DecidableEq ι]

#print List.TProd.elim /-
/-- Given an element of the iterated product `l.prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
protected def elim : ∀ {l : List ι} (v : TProd α l) {i : ι} (hi : i ∈ l), α i
  | i :: is, v, j, hj =>
    if hji : j = i then by subst hji; exact v.1 else elim v.2 (hj.resolve_left hji)
#align list.tprod.elim List.TProd.elim
-/

#print List.TProd.elim_self /-
@[simp]
theorem elim_self (v : TProd α (i :: l)) : v.elim (l.mem_cons_self i) = v.1 := by simp [tprod.elim]
#align list.tprod.elim_self List.TProd.elim_self
-/

#print List.TProd.elim_of_ne /-
@[simp]
theorem elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : TProd α (i :: l)) :
    v.elim hj = TProd.elim v.2 (hj.resolve_left hji) := by simp [tprod.elim, hji]
#align list.tprod.elim_of_ne List.TProd.elim_of_ne
-/

#print List.TProd.elim_of_mem /-
@[simp]
theorem elim_of_mem (hl : (i :: l).Nodup) (hj : j ∈ l) (v : TProd α (i :: l)) :
    v.elim (mem_cons_of_mem _ hj) = TProd.elim v.2 hj := by apply elim_of_ne; rintro rfl;
  exact hl.not_mem hj
#align list.tprod.elim_of_mem List.TProd.elim_of_mem
-/

#print List.TProd.elim_mk /-
theorem elim_mk : ∀ (l : List ι) (f : ∀ i, α i) {i : ι} (hi : i ∈ l), (TProd.mk l f).elim hi = f i
  | i :: is, f, j, hj => by
    by_cases hji : j = i
    · subst hji; simp
    · rw [elim_of_ne _ hji, snd_mk, elim_mk]
#align list.tprod.elim_mk List.TProd.elim_mk
-/

#print List.TProd.ext /-
@[ext]
theorem ext :
    ∀ {l : List ι} (hl : l.Nodup) {v w : TProd α l}
      (hvw : ∀ (i) (hi : i ∈ l), v.elim hi = w.elim hi), v = w
  | [], hl, v, w, hvw => PUnit.ext
  | i :: is, hl, v, w, hvw => by
    ext; rw [← elim_self v, hvw, elim_self]
    refine' ext (nodup_cons.mp hl).2 fun j hj => _
    rw [← elim_of_mem hl, hvw, elim_of_mem hl]
#align list.tprod.ext List.TProd.ext
-/

#print List.TProd.elim' /-
/-- A version of `tprod.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp]
protected def elim' (h : ∀ i, i ∈ l) (v : TProd α l) (i : ι) : α i :=
  v.elim (h i)
#align list.tprod.elim' List.TProd.elim'
-/

#print List.TProd.mk_elim /-
theorem mk_elim (hnd : l.Nodup) (h : ∀ i, i ∈ l) (v : TProd α l) : TProd.mk l (v.elim' h) = v :=
  TProd.ext hnd fun i hi => by simp [elim_mk]
#align list.tprod.mk_elim List.TProd.mk_elim
-/

#print List.TProd.piEquivTProd /-
/-- Pi-types are equivalent to iterated products. -/
def piEquivTProd (hnd : l.Nodup) (h : ∀ i, i ∈ l) : (∀ i, α i) ≃ TProd α l :=
  ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩
#align list.tprod.pi_equiv_tprod List.TProd.piEquivTProd
-/

end Tprod

end List

namespace Set

open List

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.tprod /-
/-- A product of sets in `tprod α l`. -/
@[simp]
protected def tprod : ∀ (l : List ι) (t : ∀ i, Set (α i)), Set (TProd α l)
  | [], t => univ
  | i :: is, t => t i ×ˢ tprod is t
#align set.tprod Set.tprod
-/

#print Set.mk_preimage_tprod /-
theorem mk_preimage_tprod :
    ∀ (l : List ι) (t : ∀ i, Set (α i)), TProd.mk l ⁻¹' Set.tprod l t = {i | i ∈ l}.pi t
  | [], t => by simp [Set.tprod]
  | i :: l, t => by
    ext f
    have : f ∈ tprod.mk l ⁻¹' Set.tprod l t ↔ f ∈ {x | x ∈ l}.pi t := by rw [mk_preimage_tprod l t]
    change tprod.mk l f ∈ Set.tprod l t ↔ ∀ i : ι, i ∈ l → f i ∈ t i at this
    -- `simp [set.tprod, tprod.mk, this]` can close this goal but is slow.
    rw [Set.tprod, tprod.mk, mem_preimage, mem_pi, prod_mk_mem_set_prod_eq]
    simp_rw [mem_set_of_eq, mem_cons_iff]
    rw [forall_eq_or_imp, and_congr_right_iff]
    exact fun _ => this
#align set.mk_preimage_tprod Set.mk_preimage_tprod
-/

#print Set.elim_preimage_pi /-
theorem elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : ∀ i, i ∈ l)
    (t : ∀ i, Set (α i)) : TProd.elim' h ⁻¹' pi univ t = Set.tprod l t :=
  by
  have : {i | i ∈ l} = univ := by ext i; simp [h]
  rw [← this, ← mk_preimage_tprod, preimage_preimage]
  convert preimage_id; simp [tprod.mk_elim hnd h, id_def]
#align set.elim_preimage_pi Set.elim_preimage_pi
-/

end Set

