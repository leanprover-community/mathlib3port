/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module data.prod.tprod
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Nodup

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

/- warning: list.tprod -> List.TProd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}}, (ι -> Type.{u_2}) -> (List.{u_1} ι) -> Type.{max u_2 u_3}
but is expected to have type
  forall {ι : Type.{u}}, (ι -> Type.{v}) -> (List.{u} ι) -> Type.{v}
Case conversion may be inaccurate. Consider using '#align list.tprod List.TProdₓ'. -/
/-- The product of a family of types over a list. -/
def TProd (l : List ι) : Type _ :=
  l.foldr (fun i β => α i × β) PUnit
#align list.tprod List.TProd

variable {α}

namespace Tprod

open List

/- warning: list.tprod.mk -> List.TProd.mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} (l : List.{u_1} ι), (forall (i : ι), α i) -> (List.TProd.{u_1, u_2, u_3} ι α l)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} (l : List.{u} ι), (forall (i : ι), α i) -> (List.TProd.{u, v} ι α l)
Case conversion may be inaccurate. Consider using '#align list.tprod.mk List.TProd.mkₓ'. -/
/-- Turning a function `f : Π i, α i` into an element of the iterated product `tprod α l`. -/
protected def mk : ∀ (l : List ι) (f : ∀ i, α i), TProd α l
  | [] => fun f => PUnit.unit
  | i :: is => fun f => (f i, mk is f)
#align list.tprod.mk List.TProd.mk

instance [∀ i, Inhabited (α i)] : Inhabited (TProd α l) :=
  ⟨TProd.mk l default⟩

/- warning: list.tprod.fst_mk -> List.TProd.fst_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} (i : ι) (l : List.{u_1} ι) (f : forall (i : ι), α i), Eq.{succ u_2} (α i) (Prod.fst.{u_2, max u_2 u_3} (α i) (List.foldr.{u_1, succ (max u_2 u_3)} ι Type.{max u_2 u_3} (fun (i : ι) (β : Type.{max u_2 u_3}) => Prod.{u_2, max u_2 u_3} (α i) β) PUnit.{succ (max u_2 u_3)} l) (List.TProd.mk.{u_1, u_2, u_3} ι (fun (i : ι) => α i) (List.cons.{u_1} ι i l) f)) (f i)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} (i : ι) (l : List.{u} ι) (f : forall (i : ι), α i), Eq.{succ v} ((fun (i : ι) => α i) i) (Prod.fst.{v, v} ((fun (i : ι) => α i) i) (List.foldr.{u, succ v} ι Type.{v} (fun (i : ι) (β : Type.{v}) => Prod.{v, v} ((fun (i : ι) => α i) i) β) PUnit.{succ v} l) (List.TProd.mk.{u, v} ι (fun (i : ι) => α i) (List.cons.{u} ι i l) f)) (f i)
Case conversion may be inaccurate. Consider using '#align list.tprod.fst_mk List.TProd.fst_mkₓ'. -/
@[simp]
theorem fst_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (TProd.mk (i :: l) f).1 = f i :=
  rfl
#align list.tprod.fst_mk List.TProd.fst_mk

/- warning: list.tprod.snd_mk -> List.TProd.snd_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} (i : ι) (l : List.{u_1} ι) (f : forall (i : ι), α i), Eq.{succ (max u_2 u_3)} (List.foldr.{u_1, succ (max u_2 u_3)} ι Type.{max u_2 u_3} (fun (i : ι) (β : Type.{max u_2 u_3}) => Prod.{u_2, max u_2 u_3} (α i) β) PUnit.{succ (max u_2 u_3)} l) (Prod.snd.{u_2, max u_2 u_3} (α i) (List.foldr.{u_1, succ (max u_2 u_3)} ι Type.{max u_2 u_3} (fun (i : ι) (β : Type.{max u_2 u_3}) => Prod.{u_2, max u_2 u_3} (α i) β) PUnit.{succ (max u_2 u_3)} l) (List.TProd.mk.{u_1, u_2, u_3} ι (fun (i : ι) => α i) (List.cons.{u_1} ι i l) f)) (List.TProd.mk.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l f)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} (i : ι) (l : List.{u} ι) (f : forall (i : ι), α i), Eq.{succ v} (List.foldr.{u, succ v} ι Type.{v} (fun (i : ι) (β : Type.{v}) => Prod.{v, v} ((fun (i : ι) => α i) i) β) PUnit.{succ v} l) (Prod.snd.{v, v} ((fun (i : ι) => α i) i) (List.foldr.{u, succ v} ι Type.{v} (fun (i : ι) (β : Type.{v}) => Prod.{v, v} ((fun (i : ι) => α i) i) β) PUnit.{succ v} l) (List.TProd.mk.{u, v} ι (fun (i : ι) => α i) (List.cons.{u} ι i l) f)) (List.TProd.mk.{u, v} ι (fun (i : ι) => α i) l f)
Case conversion may be inaccurate. Consider using '#align list.tprod.snd_mk List.TProd.snd_mkₓ'. -/
@[simp]
theorem snd_mk (i : ι) (l : List ι) (f : ∀ i, α i) : (TProd.mk (i :: l) f).2 = TProd.mk l f :=
  rfl
#align list.tprod.snd_mk List.TProd.snd_mk

variable [DecidableEq ι]

/- warning: list.tprod.elim -> List.TProd.elim is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} [_inst_1 : DecidableEq.{succ u_1} ι] {l : List.{u_1} ι}, (List.TProd.{u_1, u_2, u_3} ι α l) -> (forall {i : ι}, (Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) i l) -> (α i))
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} [_inst_1 : DecidableEq.{succ u} ι] {l : List.{u} ι}, (List.TProd.{u, v} ι α l) -> (forall {i : ι}, (Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) i l) -> (α i))
Case conversion may be inaccurate. Consider using '#align list.tprod.elim List.TProd.elimₓ'. -/
/-- Given an element of the iterated product `l.prod α`, take a projection into direction `i`.
  If `i` appears multiple times in `l`, this chooses the first component in direction `i`. -/
protected def elim : ∀ {l : List ι} (v : TProd α l) {i : ι} (hi : i ∈ l), α i
  | i :: is, v, j, hj =>
    if hji : j = i then by
      subst hji
      exact v.1
    else elim v.2 (hj.resolve_left hji)
#align list.tprod.elim List.TProd.elim

/- warning: list.tprod.elim_self -> List.TProd.elim_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} {i : ι} {l : List.{u_1} ι} [_inst_1 : DecidableEq.{succ u_1} ι] (v : List.TProd.{u_1, u_2, u_3} ι α (List.cons.{u_1} ι i l)), Eq.{succ u_2} (α i) (List.TProd.elim.{u_1, u_2, u_3} ι α (fun (a : ι) (b : ι) => _inst_1 a b) (List.cons.{u_1} ι i l) v i (List.mem_cons_self.{u_1} ι i l)) (Prod.fst.{u_2, max u_2 u_3} (α i) (List.foldr.{u_1, succ (max u_2 u_3)} ι Type.{max u_2 u_3} (fun (i : ι) (β : Type.{max u_2 u_3}) => Prod.{u_2, max u_2 u_3} (α i) β) PUnit.{succ (max u_2 u_3)} l) v)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} {i : ι} {l : List.{u} ι} [_inst_1 : DecidableEq.{succ u} ι] (v : List.TProd.{u, v} ι α (List.cons.{u} ι i l)), Eq.{succ v} (α i) (List.TProd.elim.{u, v} ι α (fun (a : ι) (b : ι) => _inst_1 a b) (List.cons.{u} ι i l) v i (List.mem_cons_self.{u} ι i l)) (Prod.fst.{v, v} (α i) (List.foldr.{u, succ v} ι Type.{v} (fun (i : ι) (β : Type.{v}) => Prod.{v, v} (α i) β) PUnit.{succ v} l) v)
Case conversion may be inaccurate. Consider using '#align list.tprod.elim_self List.TProd.elim_selfₓ'. -/
@[simp]
theorem elim_self (v : TProd α (i :: l)) : v.elim (l.mem_cons_self i) = v.1 := by simp [tprod.elim]
#align list.tprod.elim_self List.TProd.elim_self

/- warning: list.tprod.elim_of_ne -> List.TProd.elim_of_ne is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} {i : ι} {j : ι} {l : List.{u_1} ι} [_inst_1 : DecidableEq.{succ u_1} ι] (hj : Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) j (List.cons.{u_1} ι i l)) (hji : Ne.{succ u_1} ι j i) (v : List.TProd.{u_1, u_2, u_3} ι α (List.cons.{u_1} ι i l)), Eq.{succ u_2} (α j) (List.TProd.elim.{u_1, u_2, u_3} ι α (fun (a : ι) (b : ι) => _inst_1 a b) (List.cons.{u_1} ι i l) v j hj) (List.TProd.elim.{u_1, u_2, u_3} ι α (fun (a : ι) (b : ι) => _inst_1 a b) l (Prod.snd.{u_2, max u_2 u_3} (α i) (List.foldr.{u_1, succ (max u_2 u_3)} ι Type.{max u_2 u_3} (fun (i : ι) (β : Type.{max u_2 u_3}) => Prod.{u_2, max u_2 u_3} (α i) β) PUnit.{succ (max u_2 u_3)} l) v) j (Or.resolve_left (Eq.{succ u_1} ι j i) (List.Mem.{u_1} ι j l) hj hji))
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} {i : ι} {j : ι} {l : List.{u} ι} [_inst_1 : DecidableEq.{succ u} ι] (hj : Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) j (List.cons.{u} ι i l)) (hji : Ne.{succ u} ι j i) (v : List.TProd.{u, v} ι α (List.cons.{u} ι i l)), Eq.{succ v} (α j) (List.TProd.elim.{u, v} ι α (fun (a : ι) (b : ι) => _inst_1 a b) (List.cons.{u} ι i l) v j hj) (List.TProd.elim.{u, v} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) l (Prod.snd.{v, v} (α i) (List.foldr.{u, succ v} ι Type.{v} (fun (i : ι) (β : Type.{v}) => Prod.{v, v} (α i) β) PUnit.{succ v} l) v) j (Or.resolve_left (Eq.{succ u} ι j i) (Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) j l) (Iff.mp (Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) j (List.cons.{u} ι i l)) (Or (Eq.{succ u} ι j i) (Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) j l)) (List.mem_cons.{u} ι j i l) hj) hji))
Case conversion may be inaccurate. Consider using '#align list.tprod.elim_of_ne List.TProd.elim_of_neₓ'. -/
@[simp]
theorem elim_of_ne (hj : j ∈ i :: l) (hji : j ≠ i) (v : TProd α (i :: l)) :
    v.elim hj = TProd.elim v.2 (hj.resolve_left hji) := by simp [tprod.elim, hji]
#align list.tprod.elim_of_ne List.TProd.elim_of_ne

/- warning: list.tprod.elim_of_mem -> List.TProd.elim_of_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} {i : ι} {j : ι} {l : List.{u_1} ι} [_inst_1 : DecidableEq.{succ u_1} ι], (List.Nodup.{u_1} ι (List.cons.{u_1} ι i l)) -> (forall (hj : Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) j l) (v : List.TProd.{u_1, u_2, u_3} ι α (List.cons.{u_1} ι i l)), Eq.{succ u_2} (α j) (List.TProd.elim.{u_1, u_2, u_3} ι α (fun (a : ι) (b : ι) => _inst_1 a b) (List.cons.{u_1} ι i l) v j (List.mem_cons_of_mem.{u_1} ι i j l hj)) (List.TProd.elim.{u_1, u_2, u_3} ι α (fun (a : ι) (b : ι) => _inst_1 a b) l (Prod.snd.{u_2, max u_2 u_3} (α i) (List.foldr.{u_1, succ (max u_2 u_3)} ι Type.{max u_2 u_3} (fun (i : ι) (β : Type.{max u_2 u_3}) => Prod.{u_2, max u_2 u_3} (α i) β) PUnit.{succ (max u_2 u_3)} l) v) j hj))
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} {i : ι} {j : ι} {l : List.{u} ι} [_inst_1 : DecidableEq.{succ u} ι], (List.Nodup.{u} ι (List.cons.{u} ι i l)) -> (forall (hj : Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) j l) (v : List.TProd.{u, v} ι α (List.cons.{u} ι i l)), Eq.{succ v} (α j) (List.TProd.elim.{u, v} ι α (fun (a : ι) (b : ι) => _inst_1 a b) (List.cons.{u} ι i l) v j (List.mem_cons_of_mem.{u} ι i j l hj)) (List.TProd.elim.{u, v} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) l (Prod.snd.{v, v} (α i) (List.foldr.{u, succ v} ι Type.{v} (fun (i : ι) (β : Type.{v}) => Prod.{v, v} (α i) β) PUnit.{succ v} l) v) j hj))
Case conversion may be inaccurate. Consider using '#align list.tprod.elim_of_mem List.TProd.elim_of_memₓ'. -/
@[simp]
theorem elim_of_mem (hl : (i :: l).Nodup) (hj : j ∈ l) (v : TProd α (i :: l)) :
    v.elim (mem_cons_of_mem _ hj) = TProd.elim v.2 hj :=
  by
  apply elim_of_ne
  rintro rfl
  exact hl.not_mem hj
#align list.tprod.elim_of_mem List.TProd.elim_of_mem

/- warning: list.tprod.elim_mk -> List.TProd.elim_mk is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} [_inst_1 : DecidableEq.{succ u_1} ι] (l : List.{u_1} ι) (f : forall (i : ι), α i) {i : ι} (hi : Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) i l), Eq.{succ u_2} (α i) (List.TProd.elim.{u_1, u_2, u_3} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) l (List.TProd.mk.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l f) i hi) (f i)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} [_inst_1 : DecidableEq.{succ u} ι] (l : List.{u} ι) (f : forall (i : ι), α i) {i : ι} (hi : Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) i l), Eq.{succ v} (α i) (List.TProd.elim.{u, v} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) l (List.TProd.mk.{u, v} ι (fun (i : ι) => α i) l f) i hi) (f i)
Case conversion may be inaccurate. Consider using '#align list.tprod.elim_mk List.TProd.elim_mkₓ'. -/
theorem elim_mk : ∀ (l : List ι) (f : ∀ i, α i) {i : ι} (hi : i ∈ l), (TProd.mk l f).elim hi = f i
  | i :: is, f, j, hj => by
    by_cases hji : j = i
    · subst hji
      simp
    · rw [elim_of_ne _ hji, snd_mk, elim_mk]
#align list.tprod.elim_mk List.TProd.elim_mk

/- warning: list.tprod.ext -> List.TProd.ext is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} [_inst_1 : DecidableEq.{succ u_1} ι] {l : List.{u_1} ι}, (List.Nodup.{u_1} ι l) -> (forall {v : List.TProd.{u_1, u_2, u_3} ι α l} {w : List.TProd.{u_1, u_2, u_3} ι α l}, (forall (i : ι) (hi : Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) i l), Eq.{succ u_2} (α i) (List.TProd.elim.{u_1, u_2, u_3} ι α (fun (a : ι) (b : ι) => _inst_1 a b) l v i hi) (List.TProd.elim.{u_1, u_2, u_3} ι α (fun (a : ι) (b : ι) => _inst_1 a b) l w i hi)) -> (Eq.{succ (max u_2 u_3)} (List.TProd.{u_1, u_2, u_3} ι α l) v w))
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} [_inst_1 : DecidableEq.{succ u} ι] {l : List.{u} ι}, (List.Nodup.{u} ι l) -> (forall {v : List.TProd.{u, v} ι α l} {w : List.TProd.{u, v} ι α l}, (forall (i : ι) (hi : Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) i l), Eq.{succ v} (α i) (List.TProd.elim.{u, v} ι α (fun (a : ι) (b : ι) => _inst_1 a b) l v i hi) (List.TProd.elim.{u, v} ι α (fun (a : ι) (b : ι) => _inst_1 a b) l w i hi)) -> (Eq.{succ v} (List.TProd.{u, v} ι α l) v w))
Case conversion may be inaccurate. Consider using '#align list.tprod.ext List.TProd.extₓ'. -/
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

/- warning: list.tprod.elim' -> List.TProd.elim' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} {l : List.{u_1} ι} [_inst_1 : DecidableEq.{succ u_1} ι], (forall (i : ι), Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) i l) -> (List.TProd.{u_1, u_2, u_3} ι α l) -> (forall (i : ι), α i)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} {l : List.{u} ι} [_inst_1 : DecidableEq.{succ u} ι], (forall (i : ι), Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) i l) -> (List.TProd.{u, v} ι α l) -> (forall (i : ι), α i)
Case conversion may be inaccurate. Consider using '#align list.tprod.elim' List.TProd.elim'ₓ'. -/
/-- A version of `tprod.elim` when `l` contains all elements. In this case we get a function into
  `Π i, α i`. -/
@[simp]
protected def elim' (h : ∀ i, i ∈ l) (v : TProd α l) (i : ι) : α i :=
  v.elim (h i)
#align list.tprod.elim' List.TProd.elim'

/- warning: list.tprod.mk_elim -> List.TProd.mk_elim is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} {l : List.{u_1} ι} [_inst_1 : DecidableEq.{succ u_1} ι], (List.Nodup.{u_1} ι l) -> (forall (h : forall (i : ι), Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) i l) (v : List.TProd.{u_1, u_2, u_3} ι α l), Eq.{succ (max u_2 u_3)} (List.TProd.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l) (List.TProd.mk.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l (List.TProd.elim'.{u_1, u_2, u_3} ι α l (fun (a : ι) (b : ι) => _inst_1 a b) h v)) v)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} {l : List.{u} ι} [_inst_1 : DecidableEq.{succ u} ι], (List.Nodup.{u} ι l) -> (forall (h : forall (i : ι), Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) i l) (v : List.TProd.{u, v} ι α l), Eq.{succ v} (List.TProd.{u, v} ι (fun (i : ι) => α i) l) (List.TProd.mk.{u, v} ι (fun (i : ι) => α i) l (List.TProd.elim'.{u, v} ι α l (fun (a : ι) (b : ι) => _inst_1 a b) h v)) v)
Case conversion may be inaccurate. Consider using '#align list.tprod.mk_elim List.TProd.mk_elimₓ'. -/
theorem mk_elim (hnd : l.Nodup) (h : ∀ i, i ∈ l) (v : TProd α l) : TProd.mk l (v.elim' h) = v :=
  TProd.ext hnd fun i hi => by simp [elim_mk]
#align list.tprod.mk_elim List.TProd.mk_elim

/- warning: list.tprod.pi_equiv_tprod -> List.TProd.piEquivTProd is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} {l : List.{u_1} ι} [_inst_1 : DecidableEq.{succ u_1} ι], (List.Nodup.{u_1} ι l) -> (forall (i : ι), Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) i l) -> (Equiv.{max (succ u_1) (succ u_2), succ (max u_2 u_3)} (forall (i : ι), α i) (List.TProd.{u_1, u_2, u_3} ι α l))
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} {l : List.{u} ι} [_inst_1 : DecidableEq.{succ u} ι], (List.Nodup.{u} ι l) -> (forall (i : ι), Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) i l) -> (Equiv.{max (succ u) (succ v), succ v} (forall (i : ι), α i) (List.TProd.{u, v} ι α l))
Case conversion may be inaccurate. Consider using '#align list.tprod.pi_equiv_tprod List.TProd.piEquivTProdₓ'. -/
/-- Pi-types are equivalent to iterated products. -/
def piEquivTProd (hnd : l.Nodup) (h : ∀ i, i ∈ l) : (∀ i, α i) ≃ TProd α l :=
  ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩
#align list.tprod.pi_equiv_tprod List.TProd.piEquivTProd

end Tprod

end List

namespace Set

open List

/- warning: set.tprod -> Set.tprod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} (l : List.{u_1} ι), (forall (i : ι), Set.{u_2} (α i)) -> (Set.{max u_2 u_3} (List.TProd.{u_1, u_2, u_3} ι α l))
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} (l : List.{u} ι), (forall (i : ι), Set.{v} (α i)) -> (Set.{v} (List.TProd.{u, v} ι α l))
Case conversion may be inaccurate. Consider using '#align set.tprod Set.tprodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A product of sets in `tprod α l`. -/
@[simp]
protected def tprod : ∀ (l : List ι) (t : ∀ i, Set (α i)), Set (TProd α l)
  | [], t => univ
  | i :: is, t => t i ×ˢ tprod is t
#align set.tprod Set.tprod

/- warning: set.mk_preimage_tprod -> Set.mk_preimage_tprod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} (l : List.{u_1} ι) (t : forall (i : ι), Set.{u_2} (α i)), Eq.{max (succ (max u_1 u_2)) 1} (Set.{max u_1 u_2} (forall (i : ι), α i)) (Set.preimage.{max u_1 u_2, max u_2 u_3} (forall (i : ι), α i) (List.TProd.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l) (List.TProd.mk.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l) (Set.tprod.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l t)) (Set.pi.{u_1, u_2} ι (fun (i : ι) => α i) (setOf.{u_1} ι (fun (i : ι) => Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) i l)) t)
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} (l : List.{u} ι) (t : forall (i : ι), Set.{v} (α i)), Eq.{max (succ u) (succ v)} (Set.{max u v} (forall (i : ι), α i)) (Set.preimage.{max u v, v} (forall (i : ι), α i) (List.TProd.{u, v} ι (fun (i : ι) => α i) l) (List.TProd.mk.{u, v} ι (fun (i : ι) => α i) l) (Set.tprod.{u, v} ι (fun (i : ι) => α i) l t)) (Set.pi.{u, v} ι (fun (i : ι) => α i) (setOf.{u} ι (fun (i : ι) => Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) i l)) t)
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_tprod Set.mk_preimage_tprodₓ'. -/
theorem mk_preimage_tprod :
    ∀ (l : List ι) (t : ∀ i, Set (α i)), TProd.mk l ⁻¹' Set.tprod l t = { i | i ∈ l }.pi t
  | [], t => by simp [Set.tprod]
  | i :: l, t => by
    ext f
    have : f ∈ tprod.mk l ⁻¹' Set.tprod l t ↔ f ∈ { x | x ∈ l }.pi t := by
      rw [mk_preimage_tprod l t]
    change tprod.mk l f ∈ Set.tprod l t ↔ ∀ i : ι, i ∈ l → f i ∈ t i at this
    -- `simp [set.tprod, tprod.mk, this]` can close this goal but is slow.
    rw [Set.tprod, tprod.mk, mem_preimage, mem_pi, prod_mk_mem_set_prod_eq]
    simp_rw [mem_set_of_eq, mem_cons_iff]
    rw [forall_eq_or_imp, and_congr_right_iff]
    exact fun _ => this
#align set.mk_preimage_tprod Set.mk_preimage_tprod

/- warning: set.elim_preimage_pi -> Set.elim_preimage_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u_1}} {α : ι -> Type.{u_2}} [_inst_1 : DecidableEq.{succ u_1} ι] {l : List.{u_1} ι}, (List.Nodup.{u_1} ι l) -> (forall (h : forall (i : ι), Membership.Mem.{u_1, u_1} ι (List.{u_1} ι) (List.hasMem.{u_1} ι) i l) (t : forall (i : ι), Set.{u_2} (α i)), Eq.{max (succ (max u_2 u_3)) 1} (Set.{max u_2 u_3} (List.TProd.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l)) (Set.preimage.{max u_2 u_3, max u_1 u_2} (List.TProd.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l) (forall (i : ι), α i) (List.TProd.elim'.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l (fun (a : ι) (b : ι) => _inst_1 a b) h) (Set.pi.{u_1, u_2} ι (fun (i : ι) => α i) (Set.univ.{u_1} ι) t)) (Set.tprod.{u_1, u_2, u_3} ι (fun (i : ι) => α i) l t))
but is expected to have type
  forall {ι : Type.{u}} {α : ι -> Type.{v}} [_inst_1 : DecidableEq.{succ u} ι] {l : List.{u} ι}, (List.Nodup.{u} ι l) -> (forall (h : forall (i : ι), Membership.mem.{u, u} ι (List.{u} ι) (List.instMembershipList.{u} ι) i l) (t : forall (i : ι), Set.{v} (α i)), Eq.{succ v} (Set.{v} (List.TProd.{u, v} ι (fun (i : ι) => α i) l)) (Set.preimage.{v, max v u} (List.TProd.{u, v} ι (fun (i : ι) => α i) l) (forall (i : ι), α i) (List.TProd.elim'.{u, v} ι (fun (i : ι) => α i) l (fun (a : ι) (b : ι) => _inst_1 a b) h) (Set.pi.{u, v} ι (fun (i : ι) => α i) (Set.univ.{u} ι) t)) (Set.tprod.{u, v} ι (fun (i : ι) => α i) l t))
Case conversion may be inaccurate. Consider using '#align set.elim_preimage_pi Set.elim_preimage_piₓ'. -/
theorem elim_preimage_pi [DecidableEq ι] {l : List ι} (hnd : l.Nodup) (h : ∀ i, i ∈ l)
    (t : ∀ i, Set (α i)) : TProd.elim' h ⁻¹' pi univ t = Set.tprod l t :=
  by
  have : { i | i ∈ l } = univ := by
    ext i
    simp [h]
  rw [← this, ← mk_preimage_tprod, preimage_preimage]
  convert preimage_id
  simp [tprod.mk_elim hnd h, id_def]
#align set.elim_preimage_pi Set.elim_preimage_pi

end Set

