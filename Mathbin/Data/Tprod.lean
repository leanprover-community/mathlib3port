import Mathbin.Data.List.Nodup

/-!
# Finite products of types

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
  Using `local attribute [instance] fintype.encodable` we can get rid of the argument
  `[encodable ι]`.

## Main definitions

* We have the equivalence `tprod.pi_equiv_tprod : (Π i, α i) ≃ tprod α l`
  if `l` contains every element of `ι` exactly once.
* The product of sets is `set.tprod : (Π i, set (α i)) → set (tprod α l)`.
-/


open List Function

variable{ι : Type _}{α : ι → Type _}{i j : ι}{l : List ι}{f : ∀ i, α i}

namespace List

variable(α)

/-- The product of a family of types over a list. -/
def tprod (l : List ι) : Type _ :=
  l.foldr (fun i β => α i × β) PUnit

variable{α}

namespace Tprod

open List

/-- Turning a function `f : Π i, α i` into an element of the iterated product `tprod α l`. -/
protected def mk : ∀ (l : List ι) (f : ∀ i, α i), tprod α l
| [] => fun f => PUnit.unit
| i :: is => fun f => (f i, mk is f)

instance  [∀ i, Inhabited (α i)] : Inhabited (tprod α l) :=
  ⟨tprod.mk l fun i => default (α i)⟩

@[simp]
theorem fst_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (tprod.mk (i :: l) f).1 = f i :=
  rfl

@[simp]
theorem snd_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (tprod.mk (i :: l) f).2 = tprod.mk l f :=
  rfl

variable[DecidableEq ι]

/-- Given an element of the iterated product `l.prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
protected def elim : ∀ {l : List ι} (v : tprod α l) {i : ι} (hi : i ∈ l), α i
| i :: is, v, j, hj =>
  if hji : j = i then
    by 
      subst hji 
      exact v.1
  else elim v.2 (hj.resolve_left hji)

@[simp]
theorem elim_self (v : tprod α (i :: l)) : v.elim (l.mem_cons_self i) = v.1 :=
  by 
    simp [tprod.elim]

@[simp]
theorem elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : tprod α (i :: l)) :
  v.elim hj = tprod.elim v.2 (hj.resolve_left hji) :=
  by 
    simp [tprod.elim, hji]

@[simp]
theorem elim_of_mem (hl : (i :: l).Nodup) (hj : j ∈ l) (v : tprod α (i :: l)) :
  v.elim (mem_cons_of_mem _ hj) = tprod.elim v.2 hj :=
  by 
    apply elim_of_ne 
    rintro rfl 
    exact not_mem_of_nodup_cons hl hj

theorem elim_mk : ∀ (l : List ι) (f : ∀ i, α i) {i : ι} (hi : i ∈ l), (tprod.mk l f).elim hi = f i
| i :: is, f, j, hj =>
  by 
    byCases' hji : j = i
    ·
      subst hji 
      simp 
    ·
      rw [elim_of_ne _ hji, snd_mk, elim_mk]

@[ext]
theorem ext : ∀ {l : List ι} (hl : l.nodup) {v w : tprod α l} (hvw : ∀ i (hi : i ∈ l), v.elim hi = w.elim hi), v = w
| [], hl, v, w, hvw => PUnit.extₓ
| i :: is, hl, v, w, hvw =>
  by 
    ext 
    rw [←elim_self v, hvw, elim_self]
    refine' ext (nodup_cons.mp hl).2 fun j hj => _ 
    rw [←elim_of_mem hl, hvw, elim_of_mem hl]

/-- A version of `tprod.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp]
protected def elim' (h : ∀ i, i ∈ l) (v : tprod α l) (i : ι) : α i :=
  v.elim (h i)

theorem mk_elim (hnd : l.nodup) (h : ∀ i, i ∈ l) (v : tprod α l) : tprod.mk l (v.elim' h) = v :=
  tprod.ext hnd
    fun i hi =>
      by 
        simp [elim_mk]

/-- Pi-types are equivalent to iterated products. -/
def pi_equiv_tprod (hnd : l.nodup) (h : ∀ i, i ∈ l) : (∀ i, α i) ≃ tprod α l :=
  ⟨tprod.mk l, tprod.elim' h, fun f => funext$ fun i => elim_mk l f (h i), mk_elim hnd h⟩

end Tprod

end List

namespace Set

open List

/-- A product of sets in `tprod α l`. -/
@[simp]
protected def tprod : ∀ (l : List ι) (t : ∀ i, Set (α i)), Set (tprod α l)
| [], t => univ
| i :: is, t => (t i).Prod (tprod is t)

-- error in Data.Tprod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mk_preimage_tprod : ∀
(l : list ι)
(t : ∀ i, set (α i)), «expr = »(«expr ⁻¹' »(tprod.mk l, set.tprod l t), {i | «expr ∈ »(i, l)}.pi t)
| «expr[ , ]»([]), t := by simp [] [] [] ["[", expr set.tprod, "]"] [] []
| «expr :: »(i, l), t := begin
  ext [] [ident f] [],
  have [] [":", expr «expr ↔ »(«expr ∈ »(f, «expr ⁻¹' »(tprod.mk l, set.tprod l t)), «expr ∈ »(f, {x | «expr ∈ »(x, l)}.pi t))] [],
  { rw ["[", expr mk_preimage_tprod l t, "]"] [] },
  change [expr «expr ↔ »(«expr ∈ »(tprod.mk l f, set.tprod l t), ∀
    i : ι, «expr ∈ »(i, l) → «expr ∈ »(f i, t i))] [] ["at", ident this],
  rw ["[", expr set.tprod, ",", expr tprod.mk, ",", expr mem_preimage, ",", expr mem_pi, ",", expr prod_mk_mem_set_prod_eq, "]"] [],
  simp_rw ["[", expr mem_set_of_eq, ",", expr mem_cons_iff, "]"] [],
  rw ["[", expr forall_eq_or_imp, ",", expr and.congr_right_iff, "]"] [],
  exact [expr λ _, this]
end

-- error in Data.Tprod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem elim_preimage_pi
[decidable_eq ι]
{l : list ι}
(hnd : l.nodup)
(h : ∀ i, «expr ∈ »(i, l))
(t : ∀ i, set (α i)) : «expr = »(«expr ⁻¹' »(tprod.elim' h, pi univ t), set.tprod l t) :=
begin
  have [] [":", expr «expr = »({i | «expr ∈ »(i, l)}, univ)] [],
  { ext [] [ident i] [],
    simp [] [] [] ["[", expr h, "]"] [] [] },
  rw ["[", "<-", expr this, ",", "<-", expr mk_preimage_tprod, ",", expr preimage_preimage, "]"] [],
  convert [] [expr preimage_id] [],
  simp [] [] [] ["[", expr tprod.mk_elim hnd h, ",", expr id_def, "]"] [] []
end

end Set

