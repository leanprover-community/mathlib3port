/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Algebra.NeZero
import Algebra.Order.WithZero
import Order.RelIso.Basic
import Algebra.Order.Group.Nat
import Order.Hom.Set

#align_import data.fin.basic from "leanprover-community/mathlib"@"3a2b5524a138b5d0b818b858b516d4ac8a484b03"

/-!
# The finite type with `n` elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`fin n` is the type whose elements are natural numbers smaller than `n`.
This file expands on the development in the core library.

## Main definitions

### Induction principles

* `fin_zero_elim` : Elimination principle for the empty set `fin 0`, generalizes `fin.elim0`.
* `fin.succ_rec` : Define `C n i` by induction on  `i : fin n` interpreted
  as `(0 : fin (n - i)).succ.succ…`. This function has two arguments: `H0 n` defines
  `0`-th element `C (n+1) 0` of an `(n+1)`-tuple, and `Hs n i` defines `(i+1)`-st element
  of `(n+1)`-tuple based on `n`, `i`, and `i`-th element of `n`-tuple.
* `fin.succ_rec_on` : same as `fin.succ_rec` but `i : fin n` is the first argument;
* `fin.induction` : Define `C i` by induction on `i : fin (n + 1)`, separating into the
  `nat`-like base cases of `C 0` and `C (i.succ)`.
* `fin.induction_on` : same as `fin.induction` but with `i : fin (n + 1)` as the first argument.
* `fin.cases` : define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
  `i = fin.succ j`, `j : fin n`, defined using `fin.induction`.
* `fin.reverse_induction`: reverse induction on `i : fin (n + 1)`; given `C (fin.last n)` and
  `∀ i : fin n, C (fin.succ i) → C (fin.cast_succ i)`, constructs all values `C i` by going down;
* `fin.last_cases`: define `f : Π i, fin (n + 1), C i` by separately handling the cases
  `i = fin.last n` and `i = fin.cast_succ j`, a special case of `fin.reverse_induction`;
* `fin.add_cases`: define a function on `fin (m + n)` by separately handling the cases
  `fin.cast_add n i` and `fin.nat_add m i`;
* `fin.succ_above_cases`: given `i : fin (n + 1)`, define a function on `fin (n + 1)` by separately
  handling the cases `j = i` and `j = fin.succ_above i k`, same as `fin.insert_nth` but marked
  as eliminator and works for `Sort*`.

### Order embeddings and an order isomorphism

* `fin.order_iso_subtype` : coercion to `{ i // i < n }` as an `order_iso`;
* `fin.coe_embedding` : coercion to natural numbers as an `embedding`;
* `fin.coe_order_embedding` : coercion to natural numbers as an `order_embedding`;
* `fin.succ_embedding` : `fin.succ` as an `order_embedding`;
* `fin.cast_le h` : embed `fin n` into `fin m`, `h : n ≤ m`;
* `fin.cast eq` : order isomorphism between `fin n` and fin m` provided that `n = m`,
  see also `equiv.fin_congr`;
* `fin.cast_add m` : embed `fin n` into `fin (n+m)`;
* `fin.cast_succ` : embed `fin n` into `fin (n+1)`;
* `fin.succ_above p` : embed `fin n` into `fin (n + 1)` with a hole around `p`;
* `fin.add_nat m i` : add `m` on `i` on the right, generalizes `fin.succ`;
* `fin.nat_add n i` adds `n` on `i` on the left;

### Other casts

* `fin.of_nat'`: given a positive number `n` (deduced from `[ne_zero n]`), `fin.of_nat' i` is
  `i % n` interpreted as an element of `fin n`;
* `fin.cast_lt i h` : embed `i` into a `fin` where `h` proves it belongs into;
* `fin.pred_above (p : fin n) i` : embed `i : fin (n+1)` into `fin n` by subtracting one if `p < i`;
* `fin.cast_pred` : embed `fin (n + 2)` into `fin (n + 1)` by mapping `fin.last (n + 1)` to
  `fin.last n`;
* `fin.sub_nat i h` : subtract `m` from `i ≥ m`, generalizes `fin.pred`;
* `fin.clamp n m` : `min n m` as an element of `fin (m + 1)`;
* `fin.div_nat i` : divides `i : fin (m * n)` by `n`;
* `fin.mod_nat i` : takes the mod of `i : fin (m * n)` by `n`;

### Misc definitions

* `fin.last n` : The greatest value of `fin (n+1)`.
* `fin.rev : fin n → fin n` : the antitone involution given by `i ↦ n-(i+1)`

-/


universe u v

open Fin Nat Function

#print finZeroElim /-
/-- Elimination principle for the empty set `fin 0`, dependent version. -/
def finZeroElim {α : Fin 0 → Sort u} (x : Fin 0) : α x :=
  x.elim0ₓ
#align fin_zero_elim finZeroElim
-/

namespace Fin

#print Fin.elim0 /-
/-- A non-dependent variant of `elim0`. -/
def elim0 {α : Sort _} (x : Fin 0) : α :=
  x.elim0ₓ
#align fin.elim0' Fin.elim0
-/

variable {n m : ℕ} {a b : Fin n}

#print Fin.coeToNat /-
instance coeToNat (n : ℕ) : Coe (Fin n) Nat :=
  ⟨Fin.val⟩
#align fin.fin_to_nat Fin.coeToNat
-/

#print Fin.val_injective /-
theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_veq n
#align fin.val_injective Fin.val_injective
-/

#print Fin.prop /-
protected theorem prop (a : Fin n) : a.val < n :=
  a.2
#align fin.prop Fin.prop
-/

#print Fin.is_lt /-
@[simp]
theorem is_lt (a : Fin n) : (a : ℕ) < n :=
  a.2
#align fin.is_lt Fin.is_lt
-/

#print Fin.pos /-
protected theorem pos (i : Fin n) : 0 < n :=
  lt_of_le_of_lt (Nat.zero_le _) i.is_lt
#align fin.pos Fin.pos
-/

#print Fin.pos_iff_nonempty /-
theorem pos_iff_nonempty {n : ℕ} : 0 < n ↔ Nonempty (Fin n) :=
  ⟨fun h => ⟨⟨0, h⟩⟩, fun ⟨i⟩ => i.Pos⟩
#align fin.pos_iff_nonempty Fin.pos_iff_nonempty
-/

#print Fin.equivSubtype /-
/-- Equivalence between `fin n` and `{ i // i < n }`. -/
@[simps apply symm_apply]
def equivSubtype : Fin n ≃ { i // i < n }
    where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
#align fin.equiv_subtype Fin.equivSubtype
-/

section coe

/-!
### coercions and constructions
-/


#print Fin.eta /-
@[simp]
protected theorem eta (a : Fin n) (h : (a : ℕ) < n) : (⟨(a : ℕ), h⟩ : Fin n) = a := by
  cases a <;> rfl
#align fin.eta Fin.eta
-/

#print Fin.ext /-
@[ext]
theorem ext {a b : Fin n} (h : (a : ℕ) = b) : a = b :=
  eq_of_veq h
#align fin.ext Fin.ext
-/

#print Fin.ext_iff /-
theorem ext_iff {a b : Fin n} : a = b ↔ (a : ℕ) = b :=
  Iff.intro (congr_arg _) Fin.eq_of_veq
#align fin.ext_iff Fin.ext_iff
-/

/- warning: fin.coe_injective clashes with fin.val_injective -> Fin.val_injective
Case conversion may be inaccurate. Consider using '#align fin.coe_injective Fin.val_injectiveₓ'. -/
#print Fin.val_injective /-
theorem val_injective {n : ℕ} : Injective (coe : Fin n → ℕ) :=
  Fin.val_injective
#align fin.coe_injective Fin.val_injective
-/

#print Fin.val_eq_val /-
theorem val_eq_val (a b : Fin n) : (a : ℕ) = b ↔ a = b :=
  ext_iff.symm
#align fin.coe_eq_coe Fin.val_eq_val
-/

#print Fin.eq_iff_veq /-
theorem eq_iff_veq (a b : Fin n) : a = b ↔ a.1 = b.1 :=
  ⟨veq_of_eq, eq_of_veq⟩
#align fin.eq_iff_veq Fin.eq_iff_veq
-/

#print Fin.ne_iff_vne /-
theorem ne_iff_vne (a b : Fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
  ⟨vne_of_ne, ne_of_vne⟩
#align fin.ne_iff_vne Fin.ne_iff_vne
-/

#print Fin.mk_eq_mk /-
-- built-in reduction doesn't always work
@[simp, nolint simp_nf]
theorem mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a' :=
  ext_iff
#align fin.mk_eq_mk Fin.mk_eq_mk
-/

#print Fin.mk.inj_iff /-
protected theorem mk.inj_iff {n a b : ℕ} {ha : a < n} {hb : b < n} :
    (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ ↔ a = b :=
  eq_iff_veq _ _
#align fin.mk.inj_iff Fin.mk.inj_iff
-/

#print Fin.val_mk /-
theorem val_mk {m n : ℕ} (h : m < n) : (⟨m, h⟩ : Fin n).val = m :=
  rfl
#align fin.mk_val Fin.val_mk
-/

#print Fin.eq_mk_iff_val_eq /-
theorem eq_mk_iff_val_eq {k : ℕ} {hk : k < n} : a = ⟨k, hk⟩ ↔ (a : ℕ) = k :=
  Fin.eq_iff_veq a ⟨k, hk⟩
#align fin.eq_mk_iff_coe_eq Fin.eq_mk_iff_val_eq
-/

/- warning: fin.coe_mk clashes with fin.mk_val -> Fin.val_mk
Case conversion may be inaccurate. Consider using '#align fin.coe_mk Fin.val_mkₓ'. -/
#print Fin.val_mk /-
@[simp, norm_cast]
theorem val_mk {m n : ℕ} (h : m < n) : ((⟨m, h⟩ : Fin n) : ℕ) = m :=
  rfl
#align fin.coe_mk Fin.val_mk
-/

#print Fin.mk_val /-
theorem mk_val (i : Fin n) : (⟨i, i.property⟩ : Fin n) = i :=
  Fin.eta _ _
#align fin.mk_coe Fin.mk_val
-/

theorem coe_eq_val (a : Fin n) : (a : ℕ) = a.val :=
  rfl
#align fin.coe_eq_val Fin.coe_eq_val

@[simp]
theorem val_eq_coe (a : Fin n) : a.val = a :=
  rfl
#align fin.val_eq_coe Fin.val_eq_coe

#print Fin.heq_fun_iff /-
/-- Assume `k = l`. If two functions defined on `fin k` and `fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected theorem heq_fun_iff {α : Sort _} {k l : ℕ} (h : k = l) {f : Fin k → α} {g : Fin l → α} :
    HEq f g ↔ ∀ i : Fin k, f i = g ⟨(i : ℕ), h ▸ i.2⟩ := by subst h; simp [Function.funext_iff]
#align fin.heq_fun_iff Fin.heq_fun_iff
-/

#print Fin.heq_ext_iff /-
protected theorem heq_ext_iff {k l : ℕ} (h : k = l) {i : Fin k} {j : Fin l} :
    HEq i j ↔ (i : ℕ) = (j : ℕ) := by subst h; simp [coe_eq_coe]
#align fin.heq_ext_iff Fin.heq_ext_iff
-/

#print Fin.exists_iff /-
theorem exists_iff {p : Fin n → Prop} : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
  ⟨fun h => Exists.elim h fun ⟨i, hi⟩ hpi => ⟨i, hi, hpi⟩, fun h =>
    Exists.elim h fun i hi => ⟨⟨i, hi.fst⟩, hi.snd⟩⟩
#align fin.exists_iff Fin.exists_iff
-/

#print Fin.forall_iff /-
theorem forall_iff {p : Fin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
  ⟨fun h i hi => h ⟨i, hi⟩, fun h ⟨i, hi⟩ => h i hi⟩
#align fin.forall_iff Fin.forall_iff
-/

end coe

section Order

/-!
### order
-/


#print Fin.is_le /-
theorem is_le (i : Fin (n + 1)) : (i : ℕ) ≤ n :=
  le_of_lt_succ i.is_lt
#align fin.is_le Fin.is_le
-/

#print Fin.is_le' /-
@[simp]
theorem is_le' : (a : ℕ) ≤ n :=
  le_of_lt a.is_lt
#align fin.is_le' Fin.is_le'
-/

#print Fin.lt_iff_val_lt_val /-
theorem lt_iff_val_lt_val : a < b ↔ (a : ℕ) < b :=
  Iff.rfl
#align fin.lt_iff_coe_lt_coe Fin.lt_iff_val_lt_val
-/

#print Fin.le_iff_val_le_val /-
theorem le_iff_val_le_val : a ≤ b ↔ (a : ℕ) ≤ b :=
  Iff.rfl
#align fin.le_iff_coe_le_coe Fin.le_iff_val_le_val
-/

#print Fin.mk_lt_of_lt_val /-
theorem mk_lt_of_lt_val {a : ℕ} (h : a < b) : (⟨a, h.trans b.is_lt⟩ : Fin n) < b :=
  h
#align fin.mk_lt_of_lt_coe Fin.mk_lt_of_lt_val
-/

#print Fin.mk_le_of_le_val /-
theorem mk_le_of_le_val {a : ℕ} (h : a ≤ b) : (⟨a, h.trans_lt b.is_lt⟩ : Fin n) ≤ b :=
  h
#align fin.mk_le_of_le_coe Fin.mk_le_of_le_val
-/

#print Fin.val_fin_lt /-
/-- `a < b` as natural numbers if and only if `a < b` in `fin n`. -/
@[norm_cast, simp]
theorem val_fin_lt {n : ℕ} {a b : Fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
  Iff.rfl
#align fin.coe_fin_lt Fin.val_fin_lt
-/

#print Fin.val_fin_le /-
/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `fin n`. -/
@[norm_cast, simp]
theorem val_fin_le {n : ℕ} {a b : Fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
  Iff.rfl
#align fin.coe_fin_le Fin.val_fin_le
-/

instance {n : ℕ} : LinearOrder (Fin n) :=
  @LinearOrder.lift (Fin n) _ _ ⟨fun x y => ⟨max x y, max_rec' (· < n) x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' (· < n) x.2 y.2⟩⟩ Fin.val Fin.val_injective (fun _ _ => rfl)
    fun _ _ => rfl

#print Fin.mk_le_mk /-
@[simp]
theorem mk_le_mk {x y : Nat} {hx} {hy} : (⟨x, hx⟩ : Fin n) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl
#align fin.mk_le_mk Fin.mk_le_mk
-/

#print Fin.mk_lt_mk /-
@[simp]
theorem mk_lt_mk {x y : Nat} {hx} {hy} : (⟨x, hx⟩ : Fin n) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl
#align fin.mk_lt_mk Fin.mk_lt_mk
-/

#print Fin.min_val /-
@[simp]
theorem min_val : min (a : ℕ) n = a := by simp
#align fin.min_coe Fin.min_val
-/

#print Fin.max_val /-
@[simp]
theorem max_val : max (a : ℕ) n = n := by simp
#align fin.max_coe Fin.max_val
-/

instance {n : ℕ} : PartialOrder (Fin n) := by infer_instance

#print Fin.val_strictMono /-
theorem val_strictMono : StrictMono (coe : Fin n → ℕ) := fun _ _ => id
#align fin.coe_strict_mono Fin.val_strictMono
-/

#print Fin.orderIsoSubtype /-
/-- The equivalence `fin n ≃ { i // i < n }` is an order isomorphism. -/
@[simps apply symm_apply]
def orderIsoSubtype : Fin n ≃o { i // i < n } :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])
#align fin.order_iso_subtype Fin.orderIsoSubtype
-/

#print Fin.valEmbedding /-
/-- The inclusion map `fin n → ℕ` is an embedding. -/
@[simps apply]
def valEmbedding : Fin n ↪ ℕ :=
  ⟨coe, val_injective⟩
#align fin.coe_embedding Fin.valEmbedding
-/

#print Fin.equivSubtype_symm_trans_valEmbedding /-
@[simp]
theorem equivSubtype_symm_trans_valEmbedding :
    equivSubtype.symm.toEmbedding.trans valEmbedding = Embedding.subtype (· < n) :=
  rfl
#align fin.equiv_subtype_symm_trans_val_embedding Fin.equivSubtype_symm_trans_valEmbedding
-/

#print Fin.valOrderEmb /-
/-- The inclusion map `fin n → ℕ` is an order embedding. -/
@[simps apply]
def valOrderEmb (n) : Fin n ↪o ℕ :=
  ⟨valEmbedding, fun a b => Iff.rfl⟩
#align fin.coe_order_embedding Fin.valOrderEmb
-/

#print Fin.Lt.isWellOrder /-
/-- The ordering on `fin n` is a well order. -/
instance Fin.Lt.isWellOrder (n) : IsWellOrder (Fin n) (· < ·) :=
  (valOrderEmb n).IsWellOrder
#align fin.fin.lt.is_well_order Fin.Lt.isWellOrder
-/

/-- Use the ordering on `fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker,
unless we declare the `has_well_founded` instance:
```lean
def factorial {n : ℕ} : fin n → ℕ
| ⟨0, _⟩ := 1
| ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : ℕ} : WellFoundedRelation (Fin n) :=
  ⟨_, measure_wf coe⟩

instance hasZeroOfNeZero [NeZero n] : Zero (Fin n) :=
  ⟨⟨0, NeZero.pos _⟩⟩
#align fin.has_zero_of_ne_zero Fin.hasZeroOfNeZero

/-- Given a positive `n`, `fin.of_nat' i` is `i % n` as an element of `fin n`. -/
def ofNat'' [NeZero n] (i : ℕ) : Fin n :=
  ⟨i % n, mod_lt _ <| NeZero.pos n⟩
#align fin.of_nat' Fin.ofNat''ₓ

instance hasOneOfNeZero [NeZero n] : One (Fin n) :=
  ⟨ofNat'' 1⟩
#align fin.has_one_of_ne_zero Fin.hasOneOfNeZero

#print Fin.val_zero /-
@[simp]
theorem val_zero (n : ℕ) [NeZero n] : ((0 : Fin n) : ℕ) = 0 :=
  rfl
#align fin.coe_zero Fin.val_zero
-/

attribute [simp] val_zero

#print Fin.val_zero' /-
@[simp]
theorem val_zero' (n) [NeZero n] : (0 : Fin n).val = 0 :=
  rfl
#align fin.val_zero' Fin.val_zero'
-/

#print Fin.mk_zero /-
@[simp]
theorem mk_zero [NeZero n] : (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n) = (0 : Fin _) :=
  rfl
#align fin.mk_zero Fin.mk_zero
-/

#print Fin.zero_le' /-
@[simp]
theorem zero_le' [NeZero n] (a : Fin n) : 0 ≤ a :=
  zero_le a.1
#align fin.zero_le Fin.zero_le'
-/

#print Fin.zero_lt_one /-
theorem zero_lt_one : (0 : Fin (n + 2)) < 1 :=
  Nat.zero_lt_one
#align fin.zero_lt_one Fin.zero_lt_one
-/

#print Fin.not_lt_zero /-
@[simp]
theorem not_lt_zero (a : Fin n.succ) : ¬a < 0 :=
  fun.
#align fin.not_lt_zero Fin.not_lt_zero
-/

#print Fin.pos_iff_ne_zero' /-
theorem pos_iff_ne_zero' [NeZero n] (a : Fin n) : 0 < a ↔ a ≠ 0 := by
  rw [← coe_fin_lt, coe_zero, pos_iff_ne_zero, Ne.def, Ne.def, ext_iff, coe_zero]
#align fin.pos_iff_ne_zero Fin.pos_iff_ne_zero'
-/

#print Fin.eq_zero_or_eq_succ /-
theorem eq_zero_or_eq_succ {n : ℕ} (i : Fin (n + 1)) : i = 0 ∨ ∃ j : Fin n, i = j.succ :=
  by
  rcases i with ⟨_ | j, h⟩
  · left; rfl
  · right; exact ⟨⟨j, Nat.lt_of_succ_lt_succ h⟩, rfl⟩
#align fin.eq_zero_or_eq_succ Fin.eq_zero_or_eq_succ
-/

#print Fin.eq_succ_of_ne_zero /-
theorem eq_succ_of_ne_zero {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ 0) : ∃ j : Fin n, i = j.succ :=
  (eq_zero_or_eq_succ i).resolve_left hi
#align fin.eq_succ_of_ne_zero Fin.eq_succ_of_ne_zero
-/

#print Fin.revPerm /-
/-- The antitone involution `fin n → fin n` given by `i ↦ n-(i+1)`. -/
def revPerm : Equiv.Perm (Fin n) :=
  Involutive.toPerm (fun i => ⟨n - (i + 1), tsub_lt_self i.Pos (Nat.succ_pos _)⟩) fun i =>
    ext <| by
      rw [coe_mk, coe_mk, ← tsub_tsub, tsub_tsub_cancel_of_le (Nat.add_one_le_iff.2 i.is_lt),
        add_tsub_cancel_right]
#align fin.rev Fin.revPerm
-/

@[simp]
theorem val_rev (i : Fin n) : (i.revPerm : ℕ) = n - (i + 1) :=
  rfl
#align fin.coe_rev Fin.val_revₓ

#print Fin.rev_involutive /-
theorem rev_involutive : Involutive (@revPerm n) :=
  Involutive.toPerm_involutive _
#align fin.rev_involutive Fin.rev_involutive
-/

#print Fin.rev_injective /-
theorem rev_injective : Injective (@revPerm n) :=
  rev_involutive.Injective
#align fin.rev_injective Fin.rev_injective
-/

#print Fin.rev_surjective /-
theorem rev_surjective : Surjective (@revPerm n) :=
  rev_involutive.Surjective
#align fin.rev_surjective Fin.rev_surjective
-/

#print Fin.rev_bijective /-
theorem rev_bijective : Bijective (@revPerm n) :=
  rev_involutive.Bijective
#align fin.rev_bijective Fin.rev_bijective
-/

@[simp]
theorem rev_inj {i j : Fin n} : i.revPerm = j.revPerm ↔ i = j :=
  rev_injective.eq_iff
#align fin.rev_inj Fin.rev_injₓ

@[simp]
theorem rev_rev (i : Fin n) : i.revPerm.revPerm = i :=
  rev_involutive _
#align fin.rev_rev Fin.rev_revₓ

#print Fin.revPerm_symm /-
@[simp]
theorem revPerm_symm : (@revPerm n).symm = revPerm :=
  rfl
#align fin.rev_symm Fin.revPerm_symm
-/

theorem rev_eq {n a : ℕ} (i : Fin (n + 1)) (h : n = a + i) :
    i.revPerm = ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro h.symm)⟩ :=
  by
  ext
  dsimp
  conv_lhs =>
    congr
    rw [h]
  rw [add_assoc, add_tsub_cancel_right]
#align fin.rev_eq Fin.rev_eqₓ

@[simp]
theorem rev_le_rev {i j : Fin n} : i.revPerm ≤ j.revPerm ↔ j ≤ i := by
  simp only [le_iff_coe_le_coe, coe_rev, tsub_le_tsub_iff_left (Nat.add_one_le_iff.2 j.is_lt),
    add_le_add_iff_right]
#align fin.rev_le_rev Fin.rev_le_revₓ

@[simp]
theorem rev_lt_rev {i j : Fin n} : i.revPerm < j.revPerm ↔ j < i :=
  lt_iff_lt_of_le_iff_le rev_le_rev
#align fin.rev_lt_rev Fin.rev_lt_revₓ

#print Fin.revOrderIso /-
/-- `fin.rev n` as an order-reversing isomorphism. -/
@[simps apply toEquiv]
def revOrderIso {n} : (Fin n)ᵒᵈ ≃o Fin n :=
  ⟨OrderDual.ofDual.trans revPerm, fun i j => rev_le_rev⟩
#align fin.rev_order_iso Fin.revOrderIso
-/

#print Fin.revOrderIso_symm_apply /-
@[simp]
theorem revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual i.revPerm :=
  rfl
#align fin.rev_order_iso_symm_apply Fin.revOrderIso_symm_apply
-/

#print Fin.last /-
/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : Fin (n + 1) :=
  ⟨_, n.lt_succ_self⟩
#align fin.last Fin.last
-/

#print Fin.val_last /-
@[simp, norm_cast]
theorem val_last (n : ℕ) : (last n : ℕ) = n :=
  rfl
#align fin.coe_last Fin.val_last
-/

/- warning: fin.last_val clashes with fin.coe_last -> Fin.val_last
Case conversion may be inaccurate. Consider using '#align fin.last_val Fin.val_lastₓ'. -/
#print Fin.val_last /-
theorem val_last (n : ℕ) : (last n).val = n :=
  rfl
#align fin.last_val Fin.val_last
-/

#print Fin.le_last /-
theorem le_last (i : Fin (n + 1)) : i ≤ last n :=
  le_of_lt_succ i.is_lt
#align fin.le_last Fin.le_last
-/

instance : BoundedOrder (Fin (n + 1)) where
  top := last n
  le_top := le_last
  bot := 0
  bot_le := zero_le'

instance : Lattice (Fin (n + 1)) :=
  LinearOrder.toLattice

#print Fin.last_pos /-
theorem last_pos : (0 : Fin (n + 2)) < last (n + 1) := by simp [lt_iff_coe_lt_coe]
#align fin.last_pos Fin.last_pos
-/

#print Fin.eq_last_of_not_lt /-
theorem eq_last_of_not_lt {i : Fin (n + 1)} (h : ¬(i : ℕ) < n) : i = last n :=
  le_antisymm (le_last i) (not_lt.1 h)
#align fin.eq_last_of_not_lt Fin.eq_last_of_not_lt
-/

#print Fin.top_eq_last /-
theorem top_eq_last (n : ℕ) : ⊤ = Fin.last n :=
  rfl
#align fin.top_eq_last Fin.top_eq_last
-/

#print Fin.bot_eq_zero /-
theorem bot_eq_zero (n : ℕ) : ⊥ = (0 : Fin (n + 1)) :=
  rfl
#align fin.bot_eq_zero Fin.bot_eq_zero
-/

section

variable {α : Type _} [Preorder α]

open Set

#print Fin.coe_orderIso_apply /-
/-- If `e` is an `order_iso` between `fin n` and `fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
@[simp]
theorem coe_orderIso_apply (e : Fin n ≃o Fin m) (i : Fin n) : (e i : ℕ) = i :=
  by
  rcases i with ⟨i, hi⟩
  rw [Fin.val_mk]
  induction' i using Nat.strong_induction_on with i h
  refine' le_antisymm (forall_lt_iff_le.1 fun j hj => _) (forall_lt_iff_le.1 fun j hj => _)
  · have := e.symm.lt_iff_lt.2 (mk_lt_of_lt_coe hj)
    rw [e.symm_apply_apply] at this
    convert this
    simpa using h _ this (e.symm _).is_lt
  · rwa [← h j hj (hj.trans hi), ← lt_iff_coe_lt_coe, e.lt_iff_lt]
#align fin.coe_order_iso_apply Fin.coe_orderIso_apply
-/

#print Fin.orderIso_subsingleton /-
instance orderIso_subsingleton : Subsingleton (Fin n ≃o α) :=
  ⟨fun e e' => by
    ext i
    rw [← e.symm.apply_eq_iff_eq, e.symm_apply_apply, ← e'.trans_apply, ext_iff,
      coe_order_iso_apply]⟩
#align fin.order_iso_subsingleton Fin.orderIso_subsingleton
-/

#print Fin.orderIso_subsingleton' /-
instance orderIso_subsingleton' : Subsingleton (α ≃o Fin n) :=
  OrderIso.symm_injective.Subsingleton
#align fin.order_iso_subsingleton' Fin.orderIso_subsingleton'
-/

#print Fin.orderIsoUnique /-
instance orderIsoUnique : Unique (Fin n ≃o Fin n) :=
  Unique.mk' _
#align fin.order_iso_unique Fin.orderIsoUnique
-/

#print Fin.strictMono_unique /-
/-- Two strictly monotone functions from `fin n` are equal provided that their ranges
are equal. -/
theorem strictMono_unique {f g : Fin n → α} (hf : StrictMono f) (hg : StrictMono g)
    (h : range f = range g) : f = g :=
  have : (hf.OrderIso f).trans (OrderIso.setCongr _ _ h) = hg.OrderIso g := Subsingleton.elim _ _
  congr_arg (Function.comp (coe : range g → α)) (funext <| RelIso.ext_iff.1 this)
#align fin.strict_mono_unique Fin.strictMono_unique
-/

#print Fin.orderEmbedding_eq /-
/-- Two order embeddings of `fin n` are equal provided that their ranges are equal. -/
theorem orderEmbedding_eq {f g : Fin n ↪o α} (h : range f = range g) : f = g :=
  RelEmbedding.ext <| funext_iff.1 <| strictMono_unique f.StrictMono g.StrictMono h
#align fin.order_embedding_eq Fin.orderEmbedding_eq
-/

end

end Order

section Add

/-!
### addition, numerals, and coercion from nat
-/


#print Fin.val_one'' /-
theorem val_one'' {n : ℕ} : (1 : Fin (n + 1)).val = 1 % (n + 1) :=
  rfl
#align fin.one_val Fin.val_one''
-/

#print Fin.val_one' /-
theorem val_one' (n : ℕ) [NeZero n] : ((1 : Fin n) : ℕ) = 1 % n :=
  rfl
#align fin.coe_one' Fin.val_one'
-/

#print Fin.val_one /-
@[simp]
theorem val_one (n : ℕ) : (1 : Fin (n + 2)).val = 1 :=
  rfl
#align fin.val_one Fin.val_one
-/

/- warning: fin.coe_one clashes with fin.val_one -> Fin.val_one
Case conversion may be inaccurate. Consider using '#align fin.coe_one Fin.val_oneₓ'. -/
#print Fin.val_one /-
@[simp]
theorem val_one (n : ℕ) : ((1 : Fin (n + 2)) : ℕ) = 1 :=
  rfl
#align fin.coe_one Fin.val_one
-/

#print Fin.mk_one /-
@[simp]
theorem mk_one : (⟨1, Nat.succ_lt_succ (Nat.succ_pos n)⟩ : Fin (n + 2)) = (1 : Fin _) :=
  rfl
#align fin.mk_one Fin.mk_one
-/

instance {n : ℕ} : Nontrivial (Fin (n + 2)) :=
  ⟨⟨0, 1, by decide⟩⟩

#print Fin.nontrivial_iff_two_le /-
theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  rcases n with (_ | _ | n) <;> simp [Fin.nontrivial, not_nontrivial, Nat.succ_le_iff]
#align fin.nontrivial_iff_two_le Fin.nontrivial_iff_two_le
-/

#print Fin.subsingleton_iff_le_one /-
theorem subsingleton_iff_le_one : Subsingleton (Fin n) ↔ n ≤ 1 := by
  rcases n with (_ | _ | n) <;> simp [IsEmpty.subsingleton, Unique.subsingleton, not_subsingleton]
#align fin.subsingleton_iff_le_one Fin.subsingleton_iff_le_one
-/

section Monoid

#print Fin.addCommSemigroup /-
instance addCommSemigroup (n : ℕ) : AddCommSemigroup (Fin n)
    where
  add := (· + ·)
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc]
  add_comm := by simp [eq_iff_veq, add_def, add_comm]
#align fin.add_comm_semigroup Fin.addCommSemigroup
-/

#print Fin.add_zero /-
@[simp]
protected theorem add_zero [NeZero n] (k : Fin n) : k + 0 = k := by
  simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]
#align fin.add_zero Fin.add_zero
-/

#print Fin.zero_add /-
@[simp]
protected theorem zero_add [NeZero n] (k : Fin n) : (0 : Fin n) + k = k := by
  simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]
#align fin.zero_add Fin.zero_add
-/

#print Fin.addCommMonoid /-
instance addCommMonoid (n : ℕ) [NeZero n] : AddCommMonoid (Fin n) :=
  { Fin.addCommSemigroup n with
    add := (· + ·)
    zero := 0
    zero_add := Fin.zero_add
    add_zero := Fin.add_zero }
#align fin.add_comm_monoid Fin.addCommMonoid
-/

instance [NeZero n] : AddMonoidWithOne (Fin n) :=
  { Fin.addCommMonoid n with
    one := 1
    natCast := Fin.ofNat''
    natCast_zero := rfl
    natCast_succ := fun i => eq_of_veq (add_mod _ _ _) }

end Monoid

#print Fin.val_add /-
theorem val_add {n : ℕ} : ∀ a b : Fin n, (a + b).val = (a.val + b.val) % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl
#align fin.val_add Fin.val_add
-/

/- warning: fin.coe_add clashes with fin.val_add -> Fin.val_add
Case conversion may be inaccurate. Consider using '#align fin.coe_add Fin.val_addₓ'. -/
#print Fin.val_add /-
theorem val_add {n : ℕ} : ∀ a b : Fin n, ((a + b : Fin n) : ℕ) = (a + b) % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl
#align fin.coe_add Fin.val_add
-/

#print Fin.val_add_eq_ite /-
theorem val_add_eq_ite {n : ℕ} (a b : Fin n) :
    (↑(a + b) : ℕ) = if n ≤ a + b then a + b - n else a + b := by
  rw [Fin.val_add, Nat.add_mod_eq_ite, Nat.mod_eq_of_lt (show ↑a < n from a.2),
    Nat.mod_eq_of_lt (show ↑b < n from b.2)]
#align fin.coe_add_eq_ite Fin.val_add_eq_ite
-/

#print Fin.val_bit0 /-
theorem val_bit0 {n : ℕ} (k : Fin n) : ((bit0 k : Fin n) : ℕ) = bit0 (k : ℕ) % n := by cases k; rfl
#align fin.coe_bit0 Fin.val_bit0
-/

#print Fin.val_bit1 /-
theorem val_bit1 {n : ℕ} [NeZero n] (k : Fin n) : ((bit1 k : Fin n) : ℕ) = bit1 (k : ℕ) % n := by
  simp [bit1, coe_add, coe_bit0, coe_one']
#align fin.coe_bit1 Fin.val_bit1
-/

#print Fin.val_add_one_of_lt /-
theorem val_add_one_of_lt {n : ℕ} {i : Fin n.succ} (h : i < last _) : (↑(i + 1) : ℕ) = i + 1 :=
  by
  -- First show that `((1 : fin n.succ) : ℕ) = 1`, because `n.succ` is at least 2.
  cases n
  · cases h
  -- Then just unfold the definitions.
  rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (Nat.succ_lt_succ _)]
  exact h
#align fin.coe_add_one_of_lt Fin.val_add_one_of_lt
-/

#print Fin.last_add_one /-
@[simp]
theorem last_add_one : ∀ n, last n + 1 = 0
  | 0 => Subsingleton.elim _ _
  | n + 1 => by ext; rw [coe_add, coe_zero, coe_last, coe_one, Nat.mod_self]
#align fin.last_add_one Fin.last_add_one
-/

#print Fin.val_add_one /-
theorem val_add_one {n : ℕ} (i : Fin (n + 1)) :
    ((i + 1 : Fin (n + 1)) : ℕ) = if i = last _ then 0 else i + 1 :=
  by
  rcases(le_last i).eq_or_lt with (rfl | h)
  · simp
  · simpa [h.ne] using coe_add_one_of_lt h
#align fin.coe_add_one Fin.val_add_one
-/

section Bit

#print Fin.mk_bit0 /-
@[simp]
theorem mk_bit0 {m n : ℕ} (h : bit0 m < n) :
    (⟨bit0 m, h⟩ : Fin n) = (bit0 ⟨m, (Nat.le_add_right m m).trans_lt h⟩ : Fin _) :=
  eq_of_veq (Nat.mod_eq_of_lt h).symm
#align fin.mk_bit0 Fin.mk_bit0
-/

#print Fin.mk_bit1 /-
@[simp]
theorem mk_bit1 {m n : ℕ} [NeZero n] (h : bit1 m < n) :
    (⟨bit1 m, h⟩ : Fin n) =
      (bit1 ⟨m, (Nat.le_add_right m m).trans_lt ((m + m).lt_succ_self.trans h)⟩ : Fin _) :=
  by
  ext
  simp only [bit1, bit0] at h
  simp only [bit1, bit0, coe_add, coe_one', coe_mk, ← Nat.add_mod, Nat.mod_eq_of_lt h]
#align fin.mk_bit1 Fin.mk_bit1
-/

end Bit

#print Fin.val_two /-
@[simp]
theorem val_two {n : ℕ} : (2 : Fin (n + 3)).val = 2 :=
  rfl
#align fin.val_two Fin.val_two
-/

/- warning: fin.coe_two clashes with fin.val_two -> Fin.val_two
Case conversion may be inaccurate. Consider using '#align fin.coe_two Fin.val_twoₓ'. -/
#print Fin.val_two /-
@[simp]
theorem val_two {n : ℕ} : ((2 : Fin (n + 3)) : ℕ) = 2 :=
  rfl
#align fin.coe_two Fin.val_two
-/

section OfNatCoe

#print Fin.ofNat''_eq_cast /-
@[simp]
theorem ofNat''_eq_cast (n : ℕ) (a : ℕ) : (ofNat a : Fin (n + 1)) = a :=
  rfl
#align fin.of_nat_eq_coe Fin.ofNat''_eq_cast
-/

@[simp]
theorem ofNat''_eq_coe (n : ℕ) [NeZero n] (a : ℕ) : (ofNat'' a : Fin n) = a :=
  rfl
#align fin.of_nat'_eq_coe Fin.ofNat''ₓ_eq_coe

#print Fin.val_cast_of_lt /-
/-- Converting an in-range number to `fin n` produces a result
whose value is the original number.  -/
theorem val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) : (a : Fin n).val = a :=
  by
  rw [← of_nat'_eq_coe]
  exact Nat.mod_eq_of_lt h
#align fin.coe_val_of_lt Fin.val_cast_of_lt
-/

#print Fin.cast_val_eq_self /-
/-- Converting the value of a `fin n` to `fin n` results
in the same value.  -/
theorem cast_val_eq_self {n : ℕ} [NeZero n] (a : Fin n) : (a.val : Fin n) = a :=
  by
  rw [Fin.eq_iff_veq]
  exact coe_val_of_lt a.property
#align fin.coe_val_eq_self Fin.cast_val_eq_self
-/

/- warning: fin.coe_coe_of_lt clashes with fin.coe_val_of_lt -> Fin.val_cast_of_lt
Case conversion may be inaccurate. Consider using '#align fin.coe_coe_of_lt Fin.val_cast_of_ltₓ'. -/
#print Fin.val_cast_of_lt /-
/-- Coercing an in-range number to `fin n`, and converting back
to `ℕ`, results in that number. -/
theorem val_cast_of_lt {n : ℕ} [NeZero n] {a : ℕ} (h : a < n) : ((a : Fin n) : ℕ) = a :=
  val_cast_of_lt h
#align fin.coe_coe_of_lt Fin.val_cast_of_lt
-/

/- warning: fin.coe_coe_eq_self clashes with fin.coe_val_eq_self -> Fin.cast_val_eq_self
Case conversion may be inaccurate. Consider using '#align fin.coe_coe_eq_self Fin.cast_val_eq_selfₓ'. -/
#print Fin.cast_val_eq_self /-
/-- Converting a `fin n` to `ℕ` and back results in the same
value. -/
@[simp]
theorem cast_val_eq_self {n : ℕ} [NeZero n] (a : Fin n) : ((a : ℕ) : Fin n) = a :=
  cast_val_eq_self a
#align fin.coe_coe_eq_self Fin.cast_val_eq_self
-/

#print Fin.natCast_eq_last /-
theorem natCast_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by
  rw [← Fin.ofNat''_eq_cast, Fin.ofNat, Fin.last]; simp only [Nat.mod_eq_of_lt n.lt_succ_self]
#align fin.coe_nat_eq_last Fin.natCast_eq_last
-/

#print Fin.le_val_last /-
theorem le_val_last (i : Fin (n + 1)) : i ≤ n := by rw [Fin.natCast_eq_last]; exact Fin.le_last i
#align fin.le_coe_last Fin.le_val_last
-/

end OfNatCoe

#print Fin.add_one_pos /-
theorem add_one_pos (i : Fin (n + 1)) (h : i < Fin.last n) : (0 : Fin (n + 1)) < i + 1 :=
  by
  cases n
  · exact absurd h (Nat.not_lt_zero _)
  · rw [lt_iff_coe_lt_coe, coe_last, ← add_lt_add_iff_right 1] at h
    rw [lt_iff_coe_lt_coe, coe_add, coe_zero, coe_one, Nat.mod_eq_of_lt h]
    exact Nat.zero_lt_succ _
#align fin.add_one_pos Fin.add_one_pos
-/

#print Fin.one_pos /-
theorem one_pos : (0 : Fin (n + 2)) < 1 :=
  succ_pos 0
#align fin.one_pos Fin.one_pos
-/

#print Fin.zero_ne_one /-
theorem zero_ne_one : (0 : Fin (n + 2)) ≠ 1 :=
  ne_of_lt one_pos
#align fin.zero_ne_one Fin.zero_ne_one
-/

#print Fin.zero_eq_one_iff /-
@[simp]
theorem zero_eq_one_iff [NeZero n] : (0 : Fin n) = 1 ↔ n = 1 :=
  by
  constructor
  · intro h
    have := congr_arg (coe : Fin n → ℕ) h
    simp only [Fin.val_zero, ← Nat.dvd_iff_mod_eq_zero, Fin.val_one', @eq_comm _ 0] at this
    exact eq_one_of_dvd_one this
  · rintro rfl; rfl
#align fin.zero_eq_one_iff Fin.zero_eq_one_iff
-/

#print Fin.one_eq_zero_iff /-
@[simp]
theorem one_eq_zero_iff [NeZero n] : (1 : Fin n) = 0 ↔ n = 1 := by rw [eq_comm, zero_eq_one_iff]
#align fin.one_eq_zero_iff Fin.one_eq_zero_iff
-/

end Add

section Succ

/-!
### succ and casts into larger fin types
-/


#print Fin.val_succ /-
@[simp]
theorem val_succ (j : Fin n) : (j.succ : ℕ) = j + 1 := by cases j <;> simp [Fin.succ]
#align fin.coe_succ Fin.val_succ
-/

#print Fin.succ_pos /-
@[simp]
theorem succ_pos (a : Fin n) : (0 : Fin (n + 1)) < a.succ := by simp [lt_iff_coe_lt_coe]
#align fin.succ_pos Fin.succ_pos
-/

#print Fin.succEmb /-
/-- `fin.succ` as an `order_embedding` -/
def succEmb (n : ℕ) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono Fin.succ fun ⟨i, hi⟩ ⟨j, hj⟩ h => succ_lt_succ h
#align fin.succ_embedding Fin.succEmb
-/

#print Fin.coe_succOrderEmb /-
@[simp]
theorem coe_succOrderEmb : ⇑(succEmb n) = Fin.succ :=
  rfl
#align fin.coe_succ_embedding Fin.coe_succOrderEmb
-/

#print Fin.succ_le_succ_iff /-
@[simp]
theorem succ_le_succ_iff : a.succ ≤ b.succ ↔ a ≤ b :=
  (succEmb n).le_iff_le
#align fin.succ_le_succ_iff Fin.succ_le_succ_iff
-/

#print Fin.succ_lt_succ_iff /-
@[simp]
theorem succ_lt_succ_iff : a.succ < b.succ ↔ a < b :=
  (succEmb n).lt_iff_lt
#align fin.succ_lt_succ_iff Fin.succ_lt_succ_iff
-/

#print Fin.succ_injective /-
theorem succ_injective (n : ℕ) : Injective (@Fin.succ n) :=
  (succEmb n).Injective
#align fin.succ_injective Fin.succ_injective
-/

#print Fin.succ_inj /-
@[simp]
theorem succ_inj {a b : Fin n} : a.succ = b.succ ↔ a = b :=
  (succ_injective n).eq_iff
#align fin.succ_inj Fin.succ_inj
-/

#print Fin.succ_ne_zero /-
theorem succ_ne_zero {n} : ∀ k : Fin n, Fin.succ k ≠ 0
  | ⟨k, hk⟩, HEq => Nat.succ_ne_zero k <| ext_iff.1 HEq
#align fin.succ_ne_zero Fin.succ_ne_zero
-/

#print Fin.succ_zero_eq_one' /-
@[simp]
theorem succ_zero_eq_one' [NeZero n] : Fin.succ (0 : Fin n) = 1 :=
  by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl
#align fin.succ_zero_eq_one Fin.succ_zero_eq_one'
-/

#print Fin.succ_zero_eq_one /-
/-- Version of `succ_zero_eq_one` to be used by `dsimp` -/
@[simp]
theorem succ_zero_eq_one : Fin.succ (0 : Fin (n + 1)) = 1 :=
  rfl
#align fin.succ_zero_eq_one' Fin.succ_zero_eq_one
-/

#print Fin.succ_one_eq_two' /-
@[simp]
theorem succ_one_eq_two' [NeZero n] : Fin.succ (1 : Fin (n + 1)) = 2 :=
  by
  cases n
  · exact (NeZero.ne 0 rfl).elim
  · rfl
#align fin.succ_one_eq_two Fin.succ_one_eq_two'
-/

#print Fin.succ_one_eq_two /-
/-- Version of `succ_one_eq_two` to be used by `dsimp` -/
@[simp]
theorem succ_one_eq_two : Fin.succ (1 : Fin (n + 2)) = 2 :=
  rfl
#align fin.succ_one_eq_two' Fin.succ_one_eq_two
-/

#print Fin.succ_mk /-
@[simp]
theorem succ_mk (n i : ℕ) (h : i < n) : Fin.succ ⟨i, h⟩ = ⟨i + 1, Nat.succ_lt_succ h⟩ :=
  rfl
#align fin.succ_mk Fin.succ_mk
-/

#print Fin.mk_succ_pos /-
theorem mk_succ_pos (i : ℕ) (h : i < n) : (0 : Fin (n + 1)) < ⟨i.succ, add_lt_add_right h 1⟩ := by
  rw [lt_iff_coe_lt_coe, coe_zero]; exact Nat.succ_pos i
#align fin.mk_succ_pos Fin.mk_succ_pos
-/

#print Fin.one_lt_succ_succ /-
theorem one_lt_succ_succ (a : Fin n) : (1 : Fin (n + 2)) < a.succ.succ :=
  by
  cases n
  · exact finZeroElim a
  · rw [← succ_zero_eq_one, succ_lt_succ_iff]; exact succ_pos a
#align fin.one_lt_succ_succ Fin.one_lt_succ_succ
-/

#print Fin.add_one_lt_iff /-
@[simp]
theorem add_one_lt_iff {n : ℕ} {k : Fin (n + 2)} : k + 1 < k ↔ k = last _ :=
  by
  simp only [lt_iff_coe_lt_coe, coe_add, coe_last, ext_iff]
  cases' k with k hk
  rcases(le_of_lt_succ hk).eq_or_lt with (rfl | hk')
  · simp
  · simp [hk'.ne, mod_eq_of_lt (succ_lt_succ hk'), le_succ _]
#align fin.add_one_lt_iff Fin.add_one_lt_iff
-/

#print Fin.add_one_le_iff /-
@[simp]
theorem add_one_le_iff {n : ℕ} {k : Fin (n + 1)} : k + 1 ≤ k ↔ k = last _ :=
  by
  cases n
  · simp [Subsingleton.elim (k + 1) k, Subsingleton.elim (Fin.last _) k]
  rw [← not_iff_not, ← add_one_lt_iff, lt_iff_le_and_ne, not_and']
  refine' ⟨fun h _ => h, fun h => h _⟩
  rw [Ne.def, ext_iff, coe_add_one]
  split_ifs with hk hk <;> simp [hk, eq_comm]
#align fin.add_one_le_iff Fin.add_one_le_iff
-/

#print Fin.last_le_iff /-
@[simp]
theorem last_le_iff {n : ℕ} {k : Fin (n + 1)} : last n ≤ k ↔ k = last n :=
  top_le_iff
#align fin.last_le_iff Fin.last_le_iff
-/

#print Fin.lt_add_one_iff /-
@[simp]
theorem lt_add_one_iff {n : ℕ} {k : Fin (n + 1)} : k < k + 1 ↔ k < last n :=
  by
  rw [← not_iff_not]
  simp
#align fin.lt_add_one_iff Fin.lt_add_one_iff
-/

#print Fin.le_zero_iff' /-
@[simp]
theorem le_zero_iff' {n : ℕ} [NeZero n] {k : Fin n} : k ≤ 0 ↔ k = 0 :=
  ⟨fun h => Fin.eq_of_veq <| by rw [Nat.eq_zero_of_le_zero h] <;> rfl, by rintro rfl <;> rfl⟩
#align fin.le_zero_iff Fin.le_zero_iff'
-/

#print Fin.succ_succ_ne_one /-
theorem succ_succ_ne_one (a : Fin n) : Fin.succ (Fin.succ a) ≠ 1 :=
  ne_of_gt (one_lt_succ_succ a)
#align fin.succ_succ_ne_one Fin.succ_succ_ne_one
-/

#print Fin.castLT /-
/-- `cast_lt i h` embeds `i` into a `fin` where `h` proves it belongs into.  -/
def castLT (i : Fin m) (h : i.1 < n) : Fin n :=
  ⟨i.1, h⟩
#align fin.cast_lt Fin.castLT
-/

#print Fin.coe_castLT /-
@[simp]
theorem coe_castLT (i : Fin m) (h : i.1 < n) : (castLT i h : ℕ) = i :=
  rfl
#align fin.coe_cast_lt Fin.coe_castLT
-/

#print Fin.castLT_mk /-
@[simp]
theorem castLT_mk (i n m : ℕ) (hn : i < n) (hm : i < m) : castLT ⟨i, hn⟩ hm = ⟨i, hm⟩ :=
  rfl
#align fin.cast_lt_mk Fin.castLT_mk
-/

#print Fin.castLEOrderEmb /-
/-- `cast_le h i` embeds `i` into a larger `fin` type.  -/
def castLEOrderEmb (h : n ≤ m) : Fin n ↪o Fin m :=
  OrderEmbedding.ofStrictMono (fun a => castLT a (lt_of_lt_of_le a.2 h)) fun a b h => h
#align fin.cast_le Fin.castLEOrderEmb
-/

#print Fin.coe_castLE /-
@[simp]
theorem coe_castLE (h : n ≤ m) (i : Fin n) : (castLEOrderEmb h i : ℕ) = i :=
  rfl
#align fin.coe_cast_le Fin.coe_castLE
-/

#print Fin.castLE_mk /-
@[simp]
theorem castLE_mk (i n m : ℕ) (hn : i < n) (h : n ≤ m) :
    castLEOrderEmb h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h⟩ :=
  rfl
#align fin.cast_le_mk Fin.castLE_mk
-/

#print Fin.castLE_zero /-
@[simp]
theorem castLE_zero {n m : ℕ} (h : n.succ ≤ m.succ) : castLEOrderEmb h 0 = 0 := by simp [eq_iff_veq]
#align fin.cast_le_zero Fin.castLE_zero
-/

#print Fin.range_castLE /-
@[simp]
theorem range_castLE {n k : ℕ} (h : n ≤ k) : Set.range (castLEOrderEmb h) = {i | (i : ℕ) < n} :=
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, Fin.ext rfl⟩⟩
#align fin.range_cast_le Fin.range_castLE
-/

#print Fin.coe_of_injective_castLE_symm /-
@[simp]
theorem coe_of_injective_castLE_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLEOrderEmb h).Injective).symm ⟨i, hi⟩ : ℕ) = i :=
  by
  rw [← coe_cast_le]
  exact congr_arg coe (Equiv.apply_ofInjective_symm _ _)
#align fin.coe_of_injective_cast_le_symm Fin.coe_of_injective_castLE_symm
-/

#print Fin.castLE_succ /-
@[simp]
theorem castLE_succ {m n : ℕ} (h : m + 1 ≤ n + 1) (i : Fin m) :
    castLEOrderEmb h i.succ = (castLEOrderEmb (Nat.succ_le_succ_iff.mp h) i).succ := by
  simp [Fin.eq_iff_veq]
#align fin.cast_le_succ Fin.castLE_succ
-/

#print Fin.castLE_castLE /-
@[simp]
theorem castLE_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLEOrderEmb mn (Fin.castLEOrderEmb km i) = Fin.castLEOrderEmb (km.trans mn) i :=
  Fin.ext (by simp only [coe_cast_le])
#align fin.cast_le_cast_le Fin.castLE_castLE
-/

#print Fin.castLE_comp_castLE /-
@[simp]
theorem castLE_comp_castLE {k m n} (km : k ≤ m) (mn : m ≤ n) :
    Fin.castLEOrderEmb mn ∘ Fin.castLEOrderEmb km = Fin.castLEOrderEmb (km.trans mn) :=
  funext (castLE_castLE km mn)
#align fin.cast_le_comp_cast_le Fin.castLE_comp_castLE
-/

#print Fin.castOrderIso /-
/-- `cast eq i` embeds `i` into a equal `fin` type, see also `equiv.fin_congr`. -/
def castOrderIso (eq : n = m) : Fin n ≃o Fin m
    where
  toEquiv :=
    ⟨castLEOrderEmb Eq.le, castLEOrderEmb Eq.symm.le, fun a => eq_of_veq rfl, fun a =>
      eq_of_veq rfl⟩
  map_rel_iff' a b := Iff.rfl
#align fin.cast Fin.castOrderIso
-/

#print Fin.symm_castOrderIso /-
@[simp]
theorem symm_castOrderIso (h : n = m) : (castOrderIso h).symm = castOrderIso h.symm :=
  rfl
#align fin.symm_cast Fin.symm_castOrderIso
-/

/-- While `fin.coe_order_iso_apply` is a more general case of this, we mark this `simp` anyway
as it is eligible for `dsimp`. -/
@[simp]
theorem coe_cast (h : n = m) (i : Fin n) : (castOrderIso h i : ℕ) = i :=
  rfl
#align fin.coe_cast Fin.coe_castₓ

#print Fin.cast_zero /-
@[simp]
theorem cast_zero {n' : ℕ} [NeZero n] {h : n = n'} :
    castOrderIso h (0 : Fin n) =
      haveI : NeZero n' := by rw [← h] <;> infer_instance
      0 :=
  ext rfl
#align fin.cast_zero Fin.cast_zero
-/

@[simp]
theorem cast_last {n' : ℕ} {h : n + 1 = n' + 1} : castOrderIso h (last n) = last n' :=
  ext (by rw [coe_cast, coe_last, coe_last, Nat.succ_injective h])
#align fin.cast_last Fin.cast_lastₓ

@[simp]
theorem cast_mk (h : n = m) (i : ℕ) (hn : i < n) :
    castOrderIso h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h.le⟩ :=
  rfl
#align fin.cast_mk Fin.cast_mkₓ

@[simp]
theorem cast_trans {k : ℕ} (h : n = m) (h' : m = k) {i : Fin n} :
    castOrderIso h' (castOrderIso h i) = castOrderIso (Eq.trans h h') i :=
  rfl
#align fin.cast_trans Fin.cast_transₓ

#print Fin.castOrderIso_refl /-
@[simp]
theorem castOrderIso_refl (h : n = n := rfl) : castOrderIso h = OrderIso.refl (Fin n) := by ext; rfl
#align fin.cast_refl Fin.castOrderIso_refl
-/

#print Fin.castLE_of_eq /-
theorem castLE_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} :
    (castLEOrderEmb h' : Fin m → Fin n) = Fin.castOrderIso h :=
  funext fun _ => rfl
#align fin.cast_le_of_eq Fin.castLE_of_eq
-/

#print Fin.castOrderIso_toEquiv /-
/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem castOrderIso_toEquiv (h : n = m) : (castOrderIso h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h; simp
#align fin.cast_to_equiv Fin.castOrderIso_toEquiv
-/

#print Fin.cast_eq_cast /-
/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_eq_cast (h : n = m) : (castOrderIso h : Fin n → Fin m) = cast (h ▸ rfl) := by subst h;
  ext; simp
#align fin.cast_eq_cast Fin.cast_eq_cast
-/

#print Fin.castAddOrderEmb /-
/-- `cast_add m i` embeds `i : fin n` in `fin (n+m)`. See also `fin.nat_add` and `fin.add_nat`. -/
def castAddOrderEmb (m) : Fin n ↪o Fin (n + m) :=
  castLEOrderEmb <| Nat.le_add_right n m
#align fin.cast_add Fin.castAddOrderEmb
-/

#print Fin.coe_castAdd /-
@[simp]
theorem coe_castAdd (m : ℕ) (i : Fin n) : (castAddOrderEmb m i : ℕ) = i :=
  rfl
#align fin.coe_cast_add Fin.coe_castAdd
-/

@[simp]
theorem castAdd_zero : (castAddOrderEmb 0 : Fin n → Fin (n + 0)) = castOrderIso rfl :=
  rfl
#align fin.cast_add_zero Fin.castAdd_zeroₓ

#print Fin.castAdd_lt /-
theorem castAdd_lt {m : ℕ} (n : ℕ) (i : Fin m) : (castAddOrderEmb n i : ℕ) < m :=
  i.2
#align fin.cast_add_lt Fin.castAdd_lt
-/

#print Fin.castAdd_mk /-
@[simp]
theorem castAdd_mk (m : ℕ) (i : ℕ) (h : i < n) :
    castAddOrderEmb m ⟨i, h⟩ = ⟨i, lt_add_right i n m h⟩ :=
  rfl
#align fin.cast_add_mk Fin.castAdd_mk
-/

#print Fin.castAdd_castLT /-
@[simp]
theorem castAdd_castLT (m : ℕ) (i : Fin (n + m)) (hi : i.val < n) :
    castAddOrderEmb m (castLT i hi) = i :=
  ext rfl
#align fin.cast_add_cast_lt Fin.castAdd_castLT
-/

#print Fin.castLT_castAdd /-
@[simp]
theorem castLT_castAdd (m : ℕ) (i : Fin n) : castLT (castAddOrderEmb m i) (castAdd_lt m i) = i :=
  ext rfl
#align fin.cast_lt_cast_add Fin.castLT_castAdd
-/

/-- For rewriting in the reverse direction, see `fin.cast_cast_add_left`. -/
theorem castAdd_cast {n n' : ℕ} (m : ℕ) (i : Fin n') (h : n' = n) :
    castAddOrderEmb m (Fin.castOrderIso h i) =
      Fin.castOrderIso (congr_arg _ h) (castAddOrderEmb m i) :=
  ext rfl
#align fin.cast_add_cast Fin.castAdd_castₓ

theorem cast_castAdd_left {n n' m : ℕ} (i : Fin n') (h : n' + m = n + m) :
    castOrderIso h (castAddOrderEmb m i) =
      castAddOrderEmb m (castOrderIso (add_right_cancel h) i) :=
  ext rfl
#align fin.cast_cast_add_left Fin.cast_castAdd_leftₓ

@[simp]
theorem cast_castAdd_right {n m m' : ℕ} (i : Fin n) (h : n + m' = n + m) :
    castOrderIso h (castAddOrderEmb m' i) = castAddOrderEmb m i :=
  ext rfl
#align fin.cast_cast_add_right Fin.cast_castAdd_rightₓ

#print Fin.castAdd_castAdd /-
theorem castAdd_castAdd {m n p : ℕ} (i : Fin m) :
    castAddOrderEmb p (castAddOrderEmb n i) =
      castOrderIso (add_assoc _ _ _).symm (castAddOrderEmb (n + p) i) :=
  ext rfl
#align fin.cast_add_cast_add Fin.castAdd_castAdd
-/

/-- The cast of the successor is the succesor of the cast. See `fin.succ_cast_eq` for rewriting in
the reverse direction. -/
@[simp]
theorem cast_succ_eq {n' : ℕ} (i : Fin n) (h : n.succ = n'.succ) :
    castOrderIso h i.succ = (castOrderIso (Nat.succ.inj h) i).succ :=
  ext <| by simp
#align fin.cast_succ_eq Fin.cast_succ_eqₓ

theorem succ_cast_eq {n' : ℕ} (i : Fin n) (h : n = n') :
    (castOrderIso h i).succ = castOrderIso (by rw [h]) i.succ :=
  ext <| by simp
#align fin.succ_cast_eq Fin.succ_cast_eqₓ

#print Fin.castSuccEmb /-
/-- `cast_succ i` embeds `i : fin n` in `fin (n+1)`. -/
def castSuccEmb : Fin n ↪o Fin (n + 1) :=
  castAddOrderEmb 1
#align fin.cast_succ Fin.castSuccEmb
-/

#print Fin.coe_castSucc /-
@[simp]
theorem coe_castSucc (i : Fin n) : (i.cast_succ : ℕ) = i :=
  rfl
#align fin.coe_cast_succ Fin.coe_castSucc
-/

#print Fin.castSucc_mk /-
@[simp]
theorem castSucc_mk (n i : ℕ) (h : i < n) : castSuccEmb ⟨i, h⟩ = ⟨i, Nat.lt.step h⟩ :=
  rfl
#align fin.cast_succ_mk Fin.castSucc_mk
-/

@[simp]
theorem cast_castSucc {n' : ℕ} {h : n + 1 = n' + 1} {i : Fin n} :
    castOrderIso h (castSuccEmb i) = castSuccEmb (castOrderIso (Nat.succ_injective h) i) := by ext;
  simp only [coe_cast, coe_cast_succ]
#align fin.cast_cast_succ Fin.cast_castSuccₓ

#print Fin.castSucc_lt_succ /-
theorem castSucc_lt_succ (i : Fin n) : i.cast_succ < i.succ :=
  lt_iff_val_lt_val.2 <| by simp only [coe_cast_succ, coe_succ, Nat.lt_succ_self]
#align fin.cast_succ_lt_succ Fin.castSucc_lt_succ
-/

#print Fin.le_castSucc_iff /-
theorem le_castSucc_iff {i : Fin (n + 1)} {j : Fin n} : i ≤ j.cast_succ ↔ i < j.succ := by
  simpa [lt_iff_coe_lt_coe, le_iff_coe_le_coe] using nat.succ_le_succ_iff.symm
#align fin.le_cast_succ_iff Fin.le_castSucc_iff
-/

#print Fin.castSucc_lt_iff_succ_le /-
theorem castSucc_lt_iff_succ_le {n : ℕ} {i : Fin n} {j : Fin (n + 1)} :
    i.cast_succ < j ↔ i.succ ≤ j := by
  simpa only [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc] using
    Nat.lt_iff_add_one_le
#align fin.cast_succ_lt_iff_succ_le Fin.castSucc_lt_iff_succ_le
-/

#print Fin.succ_last /-
@[simp]
theorem succ_last (n : ℕ) : (last n).succ = last n.succ :=
  rfl
#align fin.succ_last Fin.succ_last
-/

#print Fin.succ_eq_last_succ /-
@[simp]
theorem succ_eq_last_succ {n : ℕ} (i : Fin n.succ) : i.succ = last (n + 1) ↔ i = last n := by
  rw [← succ_last, (succ_injective _).eq_iff]
#align fin.succ_eq_last_succ Fin.succ_eq_last_succ
-/

#print Fin.castSucc_castLT /-
@[simp]
theorem castSucc_castLT (i : Fin (n + 1)) (h : (i : ℕ) < n) : castSuccEmb (castLT i h) = i :=
  Fin.eq_of_veq rfl
#align fin.cast_succ_cast_lt Fin.castSucc_castLT
-/

#print Fin.castLT_castSucc /-
@[simp]
theorem castLT_castSucc {n : ℕ} (a : Fin n) (h : (a : ℕ) < n) : castLT (castSuccEmb a) h = a := by
  cases a <;> rfl
#align fin.cast_lt_cast_succ Fin.castLT_castSucc
-/

#print Fin.castSucc_lt_castSucc_iff /-
@[simp]
theorem castSucc_lt_castSucc_iff : a.cast_succ < b.cast_succ ↔ a < b :=
  (@castSuccEmb n).lt_iff_lt
#align fin.cast_succ_lt_cast_succ_iff Fin.castSucc_lt_castSucc_iff
-/

#print Fin.castSucc_injective /-
theorem castSucc_injective (n : ℕ) : Injective (@Fin.castSuccEmb n) :=
  (castSuccEmb : Fin n ↪o _).Injective
#align fin.cast_succ_injective Fin.castSucc_injective
-/

#print Fin.castSucc_inj /-
theorem castSucc_inj {a b : Fin n} : a.cast_succ = b.cast_succ ↔ a = b :=
  (castSucc_injective n).eq_iff
#align fin.cast_succ_inj Fin.castSucc_inj
-/

#print Fin.castSucc_lt_last /-
theorem castSucc_lt_last (a : Fin n) : castSuccEmb a < last n :=
  lt_iff_val_lt_val.mpr a.is_lt
#align fin.cast_succ_lt_last Fin.castSucc_lt_last
-/

#print Fin.castSucc_zero' /-
@[simp]
theorem castSucc_zero' [NeZero n] : castSuccEmb (0 : Fin n) = 0 :=
  rfl
#align fin.cast_succ_zero Fin.castSucc_zero'
-/

#print Fin.castSucc_one /-
@[simp]
theorem castSucc_one {n : ℕ} : Fin.castSuccEmb (1 : Fin (n + 2)) = 1 :=
  rfl
#align fin.cast_succ_one Fin.castSucc_one
-/

#print Fin.castSucc_pos' /-
/-- `cast_succ i` is positive when `i` is positive -/
theorem castSucc_pos' [NeZero n] {i : Fin n} (h : 0 < i) : 0 < castSuccEmb i := by
  simpa [lt_iff_coe_lt_coe] using h
#align fin.cast_succ_pos Fin.castSucc_pos'
-/

#print Fin.castSucc_eq_zero_iff' /-
@[simp]
theorem castSucc_eq_zero_iff' [NeZero n] (a : Fin n) : a.cast_succ = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| Iff.rfl).symm
#align fin.cast_succ_eq_zero_iff Fin.castSucc_eq_zero_iff'
-/

#print Fin.castSucc_ne_zero_iff /-
theorem castSucc_ne_zero_iff [NeZero n] (a : Fin n) : a.cast_succ ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| castSucc_eq_zero_iff' a
#align fin.cast_succ_ne_zero_iff Fin.castSucc_ne_zero_iff
-/

#print Fin.castSucc_fin_succ /-
theorem castSucc_fin_succ (n : ℕ) (j : Fin n) :
    castSuccEmb (Fin.succ j) = Fin.succ (castSuccEmb j) := by simp [Fin.ext_iff]
#align fin.cast_succ_fin_succ Fin.castSucc_fin_succ
-/

#print Fin.coe_eq_castSucc /-
@[norm_cast, simp]
theorem coe_eq_castSucc : (a : Fin (n + 1)) = a.cast_succ :=
  by
  ext
  exact coe_val_of_lt (Nat.lt.step a.is_lt)
#align fin.coe_eq_cast_succ Fin.coe_eq_castSucc
-/

#print Fin.coeSucc_eq_succ /-
@[simp]
theorem coeSucc_eq_succ : a.cast_succ + 1 = a.succ :=
  by
  cases n
  · exact finZeroElim a
  · simp [a.is_lt, eq_iff_veq, add_def, Nat.mod_eq_of_lt]
#align fin.coe_succ_eq_succ Fin.coeSucc_eq_succ
-/

#print Fin.lt_succ /-
theorem lt_succ : a.cast_succ < a.succ := by
  rw [cast_succ, lt_iff_coe_lt_coe, coe_cast_add, coe_succ]; exact lt_add_one a.val
#align fin.lt_succ Fin.lt_succ
-/

#print Fin.range_castSucc /-
@[simp]
theorem range_castSucc {n : ℕ} : Set.range (castSuccEmb : Fin n → Fin n.succ) = {i | (i : ℕ) < n} :=
  range_castLE _
#align fin.range_cast_succ Fin.range_castSucc
-/

#print Fin.coe_of_injective_castSucc_symm /-
@[simp]
theorem coe_of_injective_castSucc_symm {n : ℕ} (i : Fin (n + 1)) (hi) :
    ((Equiv.ofInjective castSuccEmb (castSucc_injective _)).symm ⟨i, hi⟩ : ℕ) = i :=
  by
  rw [← coe_cast_succ]
  exact congr_arg coe (Equiv.apply_ofInjective_symm _ _)
#align fin.coe_of_injective_cast_succ_symm Fin.coe_of_injective_castSucc_symm
-/

#print Fin.succ_castSucc /-
theorem succ_castSucc {n : ℕ} (i : Fin n) : i.cast_succ.succ = i.succ.cast_succ :=
  Fin.ext (by simp)
#align fin.succ_cast_succ Fin.succ_castSucc
-/

#print Fin.addNatOrderEmb /-
/-- `add_nat m i` adds `m` to `i`, generalizes `fin.succ`. -/
def addNatOrderEmb (m) : Fin n ↪o Fin (n + m) :=
  OrderEmbedding.ofStrictMono (fun i => ⟨(i : ℕ) + m, add_lt_add_right i.2 _⟩) fun i j h =>
    lt_iff_val_lt_val.2 <| add_lt_add_right h _
#align fin.add_nat Fin.addNatOrderEmb
-/

#print Fin.coe_addNat /-
@[simp]
theorem coe_addNat (m : ℕ) (i : Fin n) : (addNatOrderEmb m i : ℕ) = i + m :=
  rfl
#align fin.coe_add_nat Fin.coe_addNat
-/

#print Fin.addNat_one /-
@[simp]
theorem addNat_one {i : Fin n} : addNatOrderEmb 1 i = i.succ := by ext; rw [coe_add_nat, coe_succ]
#align fin.add_nat_one Fin.addNat_one
-/

#print Fin.le_coe_addNat /-
theorem le_coe_addNat (m : ℕ) (i : Fin n) : m ≤ addNatOrderEmb m i :=
  Nat.le_add_left _ _
#align fin.le_coe_add_nat Fin.le_coe_addNat
-/

#print Fin.addNat_mk /-
@[simp]
theorem addNat_mk (n i : ℕ) (hi : i < m) :
    addNatOrderEmb n ⟨i, hi⟩ = ⟨i + n, add_lt_add_right hi n⟩ :=
  rfl
#align fin.add_nat_mk Fin.addNat_mk
-/

@[simp]
theorem cast_addNat_zero {n n' : ℕ} (i : Fin n) (h : n + 0 = n') :
    castOrderIso h (addNatOrderEmb 0 i) = castOrderIso ((add_zero _).symm.trans h) i :=
  ext <| add_zero _
#align fin.cast_add_nat_zero Fin.cast_addNat_zeroₓ

/-- For rewriting in the reverse direction, see `fin.cast_add_nat_left`. -/
theorem addNat_cast {n n' m : ℕ} (i : Fin n') (h : n' = n) :
    addNatOrderEmb m (castOrderIso h i) = castOrderIso (congr_arg _ h) (addNatOrderEmb m i) :=
  ext rfl
#align fin.add_nat_cast Fin.addNat_castₓ

theorem cast_addNat_left {n n' m : ℕ} (i : Fin n') (h : n' + m = n + m) :
    castOrderIso h (addNatOrderEmb m i) = addNatOrderEmb m (castOrderIso (add_right_cancel h) i) :=
  ext rfl
#align fin.cast_add_nat_left Fin.cast_addNat_leftₓ

@[simp]
theorem cast_addNat_right {n m m' : ℕ} (i : Fin n) (h : n + m' = n + m) :
    castOrderIso h (addNatOrderEmb m' i) = addNatOrderEmb m i :=
  ext <| (congr_arg ((· + ·) (i : ℕ)) (add_left_cancel h) : _)
#align fin.cast_add_nat_right Fin.cast_addNat_rightₓ

#print Fin.natAddOrderEmb /-
/-- `nat_add n i` adds `n` to `i` "on the left". -/
def natAddOrderEmb (n) {m} : Fin m ↪o Fin (n + m) :=
  OrderEmbedding.ofStrictMono (fun i => ⟨n + (i : ℕ), add_lt_add_left i.2 _⟩) fun i j h =>
    lt_iff_val_lt_val.2 <| add_lt_add_left h _
#align fin.nat_add Fin.natAddOrderEmb
-/

#print Fin.coe_natAdd /-
@[simp]
theorem coe_natAdd (n : ℕ) {m : ℕ} (i : Fin m) : (natAddOrderEmb n i : ℕ) = n + i :=
  rfl
#align fin.coe_nat_add Fin.coe_natAdd
-/

#print Fin.natAdd_mk /-
@[simp]
theorem natAdd_mk (n i : ℕ) (hi : i < m) :
    natAddOrderEmb n ⟨i, hi⟩ = ⟨n + i, add_lt_add_left hi n⟩ :=
  rfl
#align fin.nat_add_mk Fin.natAdd_mk
-/

#print Fin.le_coe_natAdd /-
theorem le_coe_natAdd (m : ℕ) (i : Fin n) : m ≤ natAddOrderEmb m i :=
  Nat.le_add_right _ _
#align fin.le_coe_nat_add Fin.le_coe_natAdd
-/

theorem natAdd_zero {n : ℕ} :
    Fin.natAddOrderEmb 0 = (Fin.castOrderIso (zero_add n).symm).toRelEmbedding := by ext;
  apply zero_add
#align fin.nat_add_zero Fin.natAdd_zeroₓ

/-- For rewriting in the reverse direction, see `fin.cast_nat_add_right`. -/
theorem natAdd_cast {n n' : ℕ} (m : ℕ) (i : Fin n') (h : n' = n) :
    natAddOrderEmb m (castOrderIso h i) = castOrderIso (congr_arg _ h) (natAddOrderEmb m i) :=
  ext rfl
#align fin.nat_add_cast Fin.natAdd_castₓ

theorem cast_natAdd_right {n n' m : ℕ} (i : Fin n') (h : m + n' = m + n) :
    castOrderIso h (natAddOrderEmb m i) = natAddOrderEmb m (castOrderIso (add_left_cancel h) i) :=
  ext rfl
#align fin.cast_nat_add_right Fin.cast_natAdd_rightₓ

@[simp]
theorem cast_natAdd_left {n m m' : ℕ} (i : Fin n) (h : m' + n = m + n) :
    castOrderIso h (natAddOrderEmb m' i) = natAddOrderEmb m i :=
  ext <| (congr_arg (· + (i : ℕ)) (add_right_cancel h) : _)
#align fin.cast_nat_add_left Fin.cast_natAdd_leftₓ

theorem castAdd_natAdd (p m : ℕ) {n : ℕ} (i : Fin n) :
    castAddOrderEmb p (natAddOrderEmb m i) =
      castOrderIso (add_assoc _ _ _).symm (natAddOrderEmb m (castAddOrderEmb p i)) :=
  ext rfl
#align fin.cast_add_nat_add Fin.castAdd_natAddₓ

theorem natAdd_castAdd (p m : ℕ) {n : ℕ} (i : Fin n) :
    natAddOrderEmb m (castAddOrderEmb p i) =
      castOrderIso (add_assoc _ _ _) (castAddOrderEmb p (natAddOrderEmb m i)) :=
  ext rfl
#align fin.nat_add_cast_add Fin.natAdd_castAddₓ

theorem natAdd_natAdd (m n : ℕ) {p : ℕ} (i : Fin p) :
    natAddOrderEmb m (natAddOrderEmb n i) =
      castOrderIso (add_assoc _ _ _) (natAddOrderEmb (m + n) i) :=
  ext <| (add_assoc _ _ _).symm
#align fin.nat_add_nat_add Fin.natAdd_natAddₓ

@[simp]
theorem cast_natAdd_zero {n n' : ℕ} (i : Fin n) (h : 0 + n = n') :
    castOrderIso h (natAddOrderEmb 0 i) = castOrderIso ((zero_add _).symm.trans h) i :=
  ext <| zero_add _
#align fin.cast_nat_add_zero Fin.cast_natAdd_zeroₓ

@[simp]
theorem cast_natAdd (n : ℕ) {m : ℕ} (i : Fin m) :
    castOrderIso (add_comm _ _) (natAddOrderEmb n i) = addNatOrderEmb n i :=
  ext <| add_comm _ _
#align fin.cast_nat_add Fin.cast_natAddₓ

@[simp]
theorem cast_addNat {n : ℕ} (m : ℕ) (i : Fin n) :
    castOrderIso (add_comm _ _) (addNatOrderEmb m i) = natAddOrderEmb m i :=
  ext <| add_comm _ _
#align fin.cast_add_nat Fin.cast_addNatₓ

#print Fin.natAdd_last /-
@[simp]
theorem natAdd_last {m n : ℕ} : natAddOrderEmb n (last m) = last (n + m) :=
  rfl
#align fin.nat_add_last Fin.natAdd_last
-/

#print Fin.natAdd_castSucc /-
theorem natAdd_castSucc {m n : ℕ} {i : Fin m} :
    natAddOrderEmb n (castSuccEmb i) = castSuccEmb (natAddOrderEmb n i) :=
  rfl
#align fin.nat_add_cast_succ Fin.natAdd_castSucc
-/

end Succ

section Pred

/-!
### pred
-/


#print Fin.coe_pred /-
@[simp]
theorem coe_pred (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : ℕ) = j - 1 := by cases j; rfl
#align fin.coe_pred Fin.coe_pred
-/

#print Fin.succ_pred /-
@[simp]
theorem succ_pred : ∀ (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ = i
  | ⟨0, h⟩, hi => by contradiction
  | ⟨n + 1, h⟩, hi => rfl
#align fin.succ_pred Fin.succ_pred
-/

#print Fin.pred_succ /-
@[simp]
theorem pred_succ (i : Fin n) {h : i.succ ≠ 0} : i.succ.pred h = i := by cases i; rfl
#align fin.pred_succ Fin.pred_succ
-/

#print Fin.pred_eq_iff_eq_succ /-
theorem pred_eq_iff_eq_succ {n : ℕ} (i : Fin (n + 1)) (hi : i ≠ 0) (j : Fin n) :
    i.pred hi = j ↔ i = j.succ :=
  ⟨fun h => by simp only [← h, Fin.succ_pred], fun h => by simp only [h, Fin.pred_succ]⟩
#align fin.pred_eq_iff_eq_succ Fin.pred_eq_iff_eq_succ
-/

#print Fin.pred_mk_succ /-
@[simp]
theorem pred_mk_succ (i : ℕ) (h : i < n + 1) :
    Fin.pred ⟨i + 1, add_lt_add_right h 1⟩ (ne_of_vne (ne_of_gt (mk_succ_pos i h))) = ⟨i, h⟩ := by
  simp only [ext_iff, coe_pred, coe_mk, add_tsub_cancel_right]
#align fin.pred_mk_succ Fin.pred_mk_succ
-/

#print Fin.pred_mk /-
-- This is not a simp lemma by default, because `pred_mk_succ` is nicer when it applies.
theorem pred_mk {n : ℕ} (i : ℕ) (h : i < n + 1) (w) :
    Fin.pred ⟨i, h⟩ w =
      ⟨i - 1, by
        rwa [tsub_lt_iff_right (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero (Fin.vne_of_ne w))]⟩ :=
  rfl
#align fin.pred_mk Fin.pred_mk
-/

#print Fin.pred_le_pred_iff /-
@[simp]
theorem pred_le_pred_iff {n : ℕ} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha ≤ b.pred hb ↔ a ≤ b := by rw [← succ_le_succ_iff, succ_pred, succ_pred]
#align fin.pred_le_pred_iff Fin.pred_le_pred_iff
-/

#print Fin.pred_lt_pred_iff /-
@[simp]
theorem pred_lt_pred_iff {n : ℕ} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} :
    a.pred ha < b.pred hb ↔ a < b := by rw [← succ_lt_succ_iff, succ_pred, succ_pred]
#align fin.pred_lt_pred_iff Fin.pred_lt_pred_iff
-/

#print Fin.pred_inj /-
@[simp]
theorem pred_inj : ∀ {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
  | ⟨0, _⟩, b, ha, hb => by contradiction
  | ⟨i + 1, _⟩, ⟨0, _⟩, ha, hb => by contradiction
  | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, ha, hb => by simp [Fin.eq_iff_veq]
#align fin.pred_inj Fin.pred_inj
-/

#print Fin.pred_one /-
@[simp]
theorem pred_one {n : ℕ} : Fin.pred (1 : Fin (n + 2)) (Ne.symm (ne_of_lt one_pos)) = 0 :=
  rfl
#align fin.pred_one Fin.pred_one
-/

#print Fin.pred_add_one /-
theorem pred_add_one (i : Fin (n + 2)) (h : (i : ℕ) < n + 1) :
    pred (i + 1) (ne_of_gt (add_one_pos _ (lt_iff_val_lt_val.mpr h))) = castLT i h :=
  by
  rw [ext_iff, coe_pred, coe_cast_lt, coe_add, coe_one, mod_eq_of_lt, add_tsub_cancel_right]
  exact add_lt_add_right h 1
#align fin.pred_add_one Fin.pred_add_one
-/

#print Fin.subNat /-
/-- `sub_nat i h` subtracts `m` from `i`, generalizes `fin.pred`. -/
def subNat (m) (i : Fin (n + m)) (h : m ≤ (i : ℕ)) : Fin n :=
  ⟨(i : ℕ) - m, by rw [tsub_lt_iff_right h]; exact i.is_lt⟩
#align fin.sub_nat Fin.subNat
-/

#print Fin.coe_subNat /-
@[simp]
theorem coe_subNat (i : Fin (n + m)) (h : m ≤ i) : (i.subNat m h : ℕ) = i - m :=
  rfl
#align fin.coe_sub_nat Fin.coe_subNat
-/

#print Fin.subNat_mk /-
@[simp]
theorem subNat_mk {i : ℕ} (h₁ : i < n + m) (h₂ : m ≤ i) :
    subNat m ⟨i, h₁⟩ h₂ = ⟨i - m, (tsub_lt_iff_right h₂).2 h₁⟩ :=
  rfl
#align fin.sub_nat_mk Fin.subNat_mk
-/

#print Fin.pred_castSucc_succ /-
@[simp]
theorem pred_castSucc_succ (i : Fin n) :
    pred (castSuccEmb i.succ) (ne_of_gt (castSucc_pos' i.succ_pos)) = i.cast_succ := by
  simp [eq_iff_veq]
#align fin.pred_cast_succ_succ Fin.pred_castSucc_succ
-/

#print Fin.addNat_subNat /-
@[simp]
theorem addNat_subNat {i : Fin (n + m)} (h : m ≤ i) : addNatOrderEmb m (subNat m i h) = i :=
  ext <| tsub_add_cancel_of_le h
#align fin.add_nat_sub_nat Fin.addNat_subNat
-/

#print Fin.subNat_addNat /-
@[simp]
theorem subNat_addNat (i : Fin n) (m : ℕ) (h : m ≤ addNatOrderEmb m i := le_coe_addNat m i) :
    subNat m (addNatOrderEmb m i) h = i :=
  ext <| add_tsub_cancel_right i m
#align fin.sub_nat_add_nat Fin.subNat_addNat
-/

@[simp]
theorem natAdd_subNat_cast {i : Fin (n + m)} (h : n ≤ i) :
    natAddOrderEmb n (subNat n (castOrderIso (add_comm _ _) i) h) = i := by simp [← cast_add_nat]
#align fin.nat_add_sub_nat_cast Fin.natAdd_subNat_castₓ

end Pred

section DivMod

#print Fin.divNat /-
/-- Compute `i / n`, where `n` is a `nat` and inferred the type of `i`. -/
def divNat (i : Fin (m * n)) : Fin m :=
  ⟨i / n, Nat.div_lt_of_lt_mul <| mul_comm m n ▸ i.IProp⟩
#align fin.div_nat Fin.divNat
-/

#print Fin.coe_divNat /-
@[simp]
theorem coe_divNat (i : Fin (m * n)) : (i.divNat : ℕ) = i / n :=
  rfl
#align fin.coe_div_nat Fin.coe_divNat
-/

#print Fin.modNat /-
/-- Compute `i % n`, where `n` is a `nat` and inferred the type of `i`. -/
def modNat (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ <| pos_of_mul_pos_right i.Pos m.zero_le⟩
#align fin.mod_nat Fin.modNat
-/

#print Fin.coe_modNat /-
@[simp]
theorem coe_modNat (i : Fin (m * n)) : (i.modNat : ℕ) = i % n :=
  rfl
#align fin.coe_mod_nat Fin.coe_modNat
-/

end DivMod

section Rec

/-!
### recursion and induction principles
-/


#print Fin.succRec /-
/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple. -/
@[elab_as_elim]
def succRec {C : ∀ n, Fin n → Sort _} (H0 : ∀ n, C (succ n) 0)
    (Hs : ∀ n i, C n i → C (succ n) i.succ) : ∀ {n : ℕ} (i : Fin n), C n i
  | 0, i => i.elim0ₓ
  | succ n, ⟨0, _⟩ => H0 _
  | succ n, ⟨succ i, h⟩ => Hs _ _ (succ_rec ⟨i, lt_of_succ_lt_succ h⟩)
#align fin.succ_rec Fin.succRec
-/

#print Fin.succRecOn /-
/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple.

A version of `fin.succ_rec` taking `i : fin n` as the first argument. -/
@[elab_as_elim]
def succRecOn {n : ℕ} (i : Fin n) {C : ∀ n, Fin n → Sort _} (H0 : ∀ n, C (succ n) 0)
    (Hs : ∀ n i, C n i → C (succ n) i.succ) : C n i :=
  i.succRec H0 Hs
#align fin.succ_rec_on Fin.succRecOn
-/

#print Fin.succRecOn_zero /-
@[simp]
theorem succRecOn_zero {C : ∀ n, Fin n → Sort _} {H0 Hs} (n) :
    @Fin.succRecOn (succ n) 0 C H0 Hs = H0 n :=
  rfl
#align fin.succ_rec_on_zero Fin.succRecOn_zero
-/

#print Fin.succRecOn_succ /-
@[simp]
theorem succRecOn_succ {C : ∀ n, Fin n → Sort _} {H0 Hs} {n} (i : Fin n) :
    @Fin.succRecOn (succ n) i.succ C H0 Hs = Hs n i (Fin.succRecOn i H0 Hs) := by cases i <;> rfl
#align fin.succ_rec_on_succ Fin.succRecOn_succ
-/

#print Fin.induction /-
/-- Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.
-/
@[elab_as_elim]
def induction {C : Fin (n + 1) → Sort _} (h0 : C 0) (hs : ∀ i : Fin n, C i.cast_succ → C i.succ) :
    ∀ i : Fin (n + 1), C i := by
  rintro ⟨i, hi⟩
  induction' i with i IH
  · rwa [Fin.mk_zero]
  · refine' hs ⟨i, lt_of_succ_lt_succ hi⟩ _
    exact IH (lt_of_succ_lt hi)
#align fin.induction Fin.induction
-/

#print Fin.induction_zero /-
@[simp]
theorem induction_zero {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C i.cast_succ → C i.succ) : (induction h0 hs : _) 0 = h0 :=
  rfl
#align fin.induction_zero Fin.induction_zero
-/

#print Fin.induction_succ /-
@[simp]
theorem induction_succ {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C i.cast_succ → C i.succ) (i : Fin n) :
    (induction h0 hs : _) i.succ = hs i (induction h0 hs i.cast_succ) := by cases i <;> rfl
#align fin.induction_succ Fin.induction_succ
-/

#print Fin.inductionOn /-
/-- Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.

A version of `fin.induction` taking `i : fin (n + 1)` as the first argument.
-/
@[elab_as_elim]
def inductionOn (i : Fin (n + 1)) {C : Fin (n + 1) → Sort _} (h0 : C 0)
    (hs : ∀ i : Fin n, C i.cast_succ → C i.succ) : C i :=
  induction h0 hs i
#align fin.induction_on Fin.inductionOn
-/

#print Fin.cases /-
/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
`i = j.succ`, `j : fin n`. -/
@[elab_as_elim]
def cases {C : Fin (succ n) → Sort _} (H0 : C 0) (Hs : ∀ i : Fin n, C i.succ) :
    ∀ i : Fin (succ n), C i :=
  induction H0 fun i _ => Hs i
#align fin.cases Fin.cases
-/

#print Fin.cases_zero /-
@[simp]
theorem cases_zero {n} {C : Fin (succ n) → Sort _} {H0 Hs} : @Fin.cases n C H0 Hs 0 = H0 :=
  rfl
#align fin.cases_zero Fin.cases_zero
-/

#print Fin.cases_succ /-
@[simp]
theorem cases_succ {n} {C : Fin (succ n) → Sort _} {H0 Hs} (i : Fin n) :
    @Fin.cases n C H0 Hs i.succ = Hs i := by cases i <;> rfl
#align fin.cases_succ Fin.cases_succ
-/

#print Fin.cases_succ' /-
@[simp]
theorem cases_succ' {n} {C : Fin (succ n) → Sort _} {H0 Hs} {i : ℕ} (h : i + 1 < n + 1) :
    @Fin.cases n C H0 Hs ⟨i.succ, h⟩ = Hs ⟨i, lt_of_succ_lt_succ h⟩ := by cases i <;> rfl
#align fin.cases_succ' Fin.cases_succ'
-/

#print Fin.forall_fin_succ /-
theorem forall_fin_succ {P : Fin (n + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin n, P i.succ :=
  ⟨fun H => ⟨H 0, fun i => H _⟩, fun ⟨H0, H1⟩ i => Fin.cases H0 H1 i⟩
#align fin.forall_fin_succ Fin.forall_fin_succ
-/

#print Fin.exists_fin_succ /-
theorem exists_fin_succ {P : Fin (n + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin n, P i.succ :=
  ⟨fun ⟨i, h⟩ => Fin.cases Or.inl (fun i hi => Or.inr ⟨i, hi⟩) i h, fun h =>
    h.elim (fun h => ⟨0, h⟩) fun ⟨i, hi⟩ => ⟨i.succ, hi⟩⟩
#align fin.exists_fin_succ Fin.exists_fin_succ
-/

#print Fin.forall_fin_one /-
theorem forall_fin_one {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 :=
  @Unique.forall_iff (Fin 1) _ p
#align fin.forall_fin_one Fin.forall_fin_one
-/

#print Fin.exists_fin_one /-
theorem exists_fin_one {p : Fin 1 → Prop} : (∃ i, p i) ↔ p 0 :=
  @Unique.exists_iff (Fin 1) _ p
#align fin.exists_fin_one Fin.exists_fin_one
-/

#print Fin.forall_fin_two /-
theorem forall_fin_two {p : Fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 :=
  forall_fin_succ.trans <| and_congr_right fun _ => forall_fin_one
#align fin.forall_fin_two Fin.forall_fin_two
-/

#print Fin.exists_fin_two /-
theorem exists_fin_two {p : Fin 2 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 :=
  exists_fin_succ.trans <| or_congr_right exists_fin_one
#align fin.exists_fin_two Fin.exists_fin_two
-/

#print Fin.fin_two_eq_of_eq_zero_iff /-
theorem fin_two_eq_of_eq_zero_iff {a b : Fin 2} (h : a = 0 ↔ b = 0) : a = b := by revert a b;
  simp [forall_fin_two]
#align fin.fin_two_eq_of_eq_zero_iff Fin.fin_two_eq_of_eq_zero_iff
-/

/- ././././Mathport/Syntax/Translate/Command.lean:299:8: warning: using_well_founded used, estimated equivalent -/
#print Fin.reverseInduction /-
/--
Define `C i` by reverse induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `hlast` handles the base case on `C (fin.last n)`,
and `hs` defines the inductive step using `C i.succ`, inducting downwards.
-/
@[elab_as_elim]
def reverseInduction {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C i.cast_succ) : ∀ i : Fin (n + 1), C i
  | i =>
    if hi : i = Fin.last n then cast (by rw [hi]) hlast
    else
      let j : Fin n := ⟨i, lt_of_le_of_ne (Nat.le_of_lt_succ i.2) fun h => hi (Fin.ext h)⟩
      have wf : n + 1 - j.succ < n + 1 - i := by
        cases i
        rw [tsub_lt_tsub_iff_left_of_le] <;> simp [*, Nat.succ_le_iff]
      have hi : i = Fin.castSuccEmb j := Fin.ext rfl
      cast (by rw [hi]) (hs _ (reverse_induction j.succ))
termination_by x => WellFounded.wrap (measure_wf fun i : Fin (n + 1) => n + 1 - i) x
#align fin.reverse_induction Fin.reverseInduction
-/

#print Fin.reverseInduction_last /-
@[simp]
theorem reverseInduction_last {n : ℕ} {C : Fin (n + 1) → Sort _} (h0 : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C i.cast_succ) :
    (reverseInduction h0 hs (Fin.last n) : C (Fin.last n)) = h0 := by
  rw [reverse_induction] <;> simp
#align fin.reverse_induction_last Fin.reverseInduction_last
-/

#print Fin.reverseInduction_castSucc /-
@[simp]
theorem reverseInduction_castSucc {n : ℕ} {C : Fin (n + 1) → Sort _} (h0 : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C i.cast_succ) (i : Fin n) :
    (reverseInduction h0 hs i.cast_succ : C i.cast_succ) = hs i (reverseInduction h0 hs i.succ) :=
  by
  rw [reverse_induction, dif_neg (ne_of_lt (Fin.castSucc_lt_last i))]
  cases i
  rfl
#align fin.reverse_induction_cast_succ Fin.reverseInduction_castSucc
-/

#print Fin.lastCases /-
/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = fin.last n` and
`i = j.cast_succ`, `j : fin n`. -/
@[elab_as_elim]
def lastCases {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C i.cast_succ) (i : Fin (n + 1)) : C i :=
  reverseInduction hlast (fun i _ => hcast i) i
#align fin.last_cases Fin.lastCases
-/

#print Fin.lastCases_last /-
@[simp]
theorem lastCases_last {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C i.cast_succ) :
    (Fin.lastCases hlast hcast (Fin.last n) : C (Fin.last n)) = hlast :=
  reverseInduction_last _ _
#align fin.last_cases_last Fin.lastCases_last
-/

#print Fin.lastCases_castSucc /-
@[simp]
theorem lastCases_castSucc {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C i.cast_succ) (i : Fin n) :
    (Fin.lastCases hlast hcast (Fin.castSuccEmb i) : C (Fin.castSuccEmb i)) = hcast i :=
  reverseInduction_castSucc _ _ _
#align fin.last_cases_cast_succ Fin.lastCases_castSucc
-/

#print Fin.addCases /-
/-- Define `f : Π i : fin (m + n), C i` by separately handling the cases `i = cast_add n i`,
`j : fin m` and `i = nat_add m j`, `j : fin n`. -/
@[elab_as_elim]
def addCases {m n : ℕ} {C : Fin (m + n) → Sort u} (hleft : ∀ i, C (castAddOrderEmb n i))
    (hright : ∀ i, C (natAddOrderEmb m i)) (i : Fin (m + n)) : C i :=
  if hi : (i : ℕ) < m then Eq.recOn (castAdd_castLT n i hi) (hleft (castLT i hi))
  else Eq.recOn (natAdd_subNat_cast (le_of_not_lt hi)) (hright _)
#align fin.add_cases Fin.addCases
-/

#print Fin.addCases_left /-
@[simp]
theorem addCases_left {m n : ℕ} {C : Fin (m + n) → Sort _} (hleft : ∀ i, C (castAddOrderEmb n i))
    (hright : ∀ i, C (natAddOrderEmb m i)) (i : Fin m) :
    @addCases _ _ C hleft hright (Fin.castAddOrderEmb n i) = hleft i :=
  by
  cases' i with i hi
  rw [add_cases, dif_pos (cast_add_lt _ _)]
  rfl
#align fin.add_cases_left Fin.addCases_left
-/

#print Fin.addCases_right /-
@[simp]
theorem addCases_right {m n : ℕ} {C : Fin (m + n) → Sort _} (hleft : ∀ i, C (castAddOrderEmb n i))
    (hright : ∀ i, C (natAddOrderEmb m i)) (i : Fin n) :
    @addCases _ _ C hleft hright (natAddOrderEmb m i) = hright i :=
  by
  have : ¬(nat_add m i : ℕ) < m := (le_coe_nat_add _ _).not_lt
  rw [add_cases, dif_neg this]
  refine' eq_of_hEq ((eq_rec_hEq _ _).trans _); congr 1
  simp
#align fin.add_cases_right Fin.addCases_right
-/

end Rec

#print Fin.liftFun_iff_succ /-
theorem liftFun_iff_succ {α : Type _} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} :
    ((· < ·) ⇒ r) f f ↔ ∀ i : Fin n, r (f i.cast_succ) (f i.succ) :=
  by
  constructor
  · intro H i
    exact H i.cast_succ_lt_succ
  · refine' fun H i => Fin.induction _ _
    · exact fun h => (h.not_le (zero_le i)).elim
    · intro j ihj hij
      rw [← le_cast_succ_iff] at hij
      rcases hij.eq_or_lt with (rfl | hlt)
      exacts [H j, trans (ihj hlt) (H j)]
#align fin.lift_fun_iff_succ Fin.liftFun_iff_succ
-/

#print Fin.strictMono_iff_lt_succ /-
/-- A function `f` on `fin (n + 1)` is strictly monotone if and only if `f i < f (i + 1)`
for all `i`. -/
theorem strictMono_iff_lt_succ {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    StrictMono f ↔ ∀ i : Fin n, f i.cast_succ < f i.succ :=
  liftFun_iff_succ (· < ·)
#align fin.strict_mono_iff_lt_succ Fin.strictMono_iff_lt_succ
-/

#print Fin.monotone_iff_le_succ /-
/-- A function `f` on `fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for all `i`. -/
theorem monotone_iff_le_succ {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    Monotone f ↔ ∀ i : Fin n, f i.cast_succ ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| liftFun_iff_succ (· ≤ ·)
#align fin.monotone_iff_le_succ Fin.monotone_iff_le_succ
-/

#print Fin.strictAnti_iff_succ_lt /-
/-- A function `f` on `fin (n + 1)` is strictly antitone if and only if `f (i + 1) < f i`
for all `i`. -/
theorem strictAnti_iff_succ_lt {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    StrictAnti f ↔ ∀ i : Fin n, f i.succ < f i.cast_succ :=
  liftFun_iff_succ (· > ·)
#align fin.strict_anti_iff_succ_lt Fin.strictAnti_iff_succ_lt
-/

#print Fin.antitone_iff_succ_le /-
/-- A function `f` on `fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for all `i`. -/
theorem antitone_iff_succ_le {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f i.cast_succ :=
  antitone_iff_forall_lt.trans <| liftFun_iff_succ (· ≥ ·)
#align fin.antitone_iff_succ_le Fin.antitone_iff_succ_le
-/

section AddGroup

open Nat Int

/-- Negation on `fin n` -/
instance (n : ℕ) : Neg (Fin n) :=
  ⟨fun a => ⟨(n - a) % n, Nat.mod_lt _ a.Pos⟩⟩

/-- Abelian group structure on `fin n`. -/
instance (n : ℕ) [NeZero n] : AddCommGroup (Fin n) :=
  { Fin.addCommMonoid n,
    Fin.hasNeg
      n with
    add_left_neg := fun ⟨a, ha⟩ =>
      Fin.ext <|
        trans (Nat.mod_add_mod _ _ _) <| by
          rw [Fin.val_mk, Fin.val_zero, tsub_add_cancel_of_le, Nat.mod_self]; exact le_of_lt ha
    sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
      Fin.ext <| show (a + (n - b)) % n = (a + (n - b) % n) % n by simp
    sub := Fin.sub }

/-- Note this is more general than `fin.add_comm_group` as it applies (vacuously) to `fin 0` too. -/
instance (n : ℕ) : InvolutiveNeg (Fin n)
    where
  neg := Neg.neg
  neg_neg := Nat.casesOn n finZeroElim fun i => neg_neg

/-- Note this is more general than `fin.add_comm_group` as it applies (vacuously) to `fin 0` too. -/
instance (n : ℕ) : IsCancelAdd (Fin n)
    where
  add_left_cancel := Nat.casesOn n finZeroElim fun i _ _ _ => add_left_cancel
  add_right_cancel := Nat.casesOn n finZeroElim fun i _ _ _ => add_right_cancel

/-- Note this is more general than `fin.add_comm_group` as it applies (vacuously) to `fin 0` too. -/
instance (n : ℕ) : AddLeftCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

/-- Note this is more general than `fin.add_comm_group` as it applies (vacuously) to `fin 0` too. -/
instance (n : ℕ) : AddRightCancelSemigroup (Fin n) :=
  { Fin.addCommSemigroup n, Fin.instIsCancelAdd n with }

#print Fin.coe_neg /-
protected theorem coe_neg (a : Fin n) : ((-a : Fin n) : ℕ) = (n - a) % n :=
  rfl
#align fin.coe_neg Fin.coe_neg
-/

#print Fin.coe_sub /-
protected theorem coe_sub (a b : Fin n) : ((a - b : Fin n) : ℕ) = (a + (n - b)) % n := by
  cases a <;> cases b <;> rfl
#align fin.coe_sub Fin.coe_sub
-/

#print Fin.coe_fin_one /-
@[simp]
theorem coe_fin_one (a : Fin 1) : ↑a = 0 := by rw [Subsingleton.elim a 0, Fin.val_zero]
#align fin.coe_fin_one Fin.coe_fin_one
-/

#print Fin.coe_neg_one /-
@[simp]
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n :=
  by
  cases n
  · simp
  rw [Fin.coe_neg, Fin.val_one, Nat.add_one_sub_one, Nat.mod_eq_of_lt]
  constructor
#align fin.coe_neg_one Fin.coe_neg_one
-/

#print Fin.coe_sub_one /-
theorem coe_sub_one {n} (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 :=
  by
  cases n
  · simp
  split_ifs
  · simp [h]
  rw [sub_eq_add_neg, coe_add_eq_ite, coe_neg_one, if_pos, add_comm, add_tsub_add_eq_tsub_left]
  rw [add_comm ↑a, add_le_add_iff_left, Nat.one_le_iff_ne_zero]
  rwa [Fin.ext_iff] at h
#align fin.coe_sub_one Fin.coe_sub_one
-/

#print Fin.coe_sub_iff_le /-
theorem coe_sub_iff_le {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = a - b ↔ b ≤ a :=
  by
  cases n; · exact finZeroElim a
  rw [le_iff_coe_le_coe, Fin.coe_sub, ← add_tsub_assoc_of_le b.is_lt.le a]
  cases' le_or_lt (b : ℕ) a with h h
  · simp [← tsub_add_eq_add_tsub h, h, Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt a.is_lt)]
  · rw [Nat.mod_eq_of_lt, tsub_eq_zero_of_le h.le, tsub_eq_zero_iff_le, ← not_iff_not]
    · simpa [b.is_lt.trans_le le_add_self] using h
    · rwa [tsub_lt_iff_left (b.is_lt.le.trans le_add_self), add_lt_add_iff_right]
#align fin.coe_sub_iff_le Fin.coe_sub_iff_le
-/

#print Fin.coe_sub_iff_lt /-
theorem coe_sub_iff_lt {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = n + a - b ↔ a < b :=
  by
  cases n; · exact finZeroElim a
  rw [lt_iff_coe_lt_coe, Fin.coe_sub, add_comm]
  cases' le_or_lt (b : ℕ) a with h h
  ·
    simpa [add_tsub_assoc_of_le h, ← not_le, h] using
      ((Nat.mod_lt _ (Nat.succ_pos _)).trans_le le_self_add).Ne
  ·
    simp [← tsub_tsub_assoc b.is_lt.le h.le, ← tsub_add_eq_add_tsub b.is_lt.le,
      Nat.mod_eq_of_lt (tsub_lt_self (Nat.succ_pos _) (tsub_pos_of_lt h)), h]
#align fin.coe_sub_iff_lt Fin.coe_sub_iff_lt
-/

#print Fin.lt_sub_one_iff /-
@[simp]
theorem lt_sub_one_iff {n : ℕ} {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 :=
  by
  rcases k with ⟨_ | k, hk⟩
  simp [lt_iff_coe_lt_coe]
  have : (k + 1 + (n + 1)) % (n + 2) = k % (n + 2) := by
    rw [add_right_comm, add_assoc, add_mod_right]
  simp [lt_iff_coe_lt_coe, ext_iff, Fin.coe_sub, succ_eq_add_one, this,
    mod_eq_of_lt ((lt_succ_self _).trans hk)]
#align fin.lt_sub_one_iff Fin.lt_sub_one_iff
-/

#print Fin.le_sub_one_iff /-
@[simp]
theorem le_sub_one_iff {n : ℕ} {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 :=
  by
  cases n
  · simp [Subsingleton.elim (k - 1) k, Subsingleton.elim 0 k]
  rw [← lt_sub_one_iff, le_iff_lt_or_eq, lt_sub_one_iff, or_iff_left_iff_imp, eq_comm,
    sub_eq_iff_eq_add]
  simp
#align fin.le_sub_one_iff Fin.le_sub_one_iff
-/

#print Fin.sub_one_lt_iff /-
@[simp]
theorem sub_one_lt_iff {n : ℕ} {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
  not_iff_not.1 <| by simp only [not_lt, le_sub_one_iff, le_zero_iff]
#align fin.sub_one_lt_iff Fin.sub_one_lt_iff
-/

#print Fin.last_sub /-
theorem last_sub (i : Fin (n + 1)) : last n - i = i.revPerm :=
  ext <| by rw [coe_sub_iff_le.2 i.le_last, coe_last, coe_rev, Nat.succ_sub_succ_eq_sub]
#align fin.last_sub Fin.last_sub
-/

end AddGroup

section SuccAbove

#print Fin.strictMono_succAbove /-
theorem strictMono_succAbove (p : Fin (n + 1)) :
    StrictMono fun i : Fin n => if i.cast_succ < p then i.cast_succ else i.succ :=
  (castSuccEmb : Fin n ↪o _).StrictMono.ite (succEmb n).StrictMono
    (fun i j hij hj => lt_trans ((castSuccEmb : Fin n ↪o _).lt_iff_lt.2 hij) hj) fun i =>
    (castSucc_lt_succ i).le
#align fin.succ_above_aux Fin.strictMono_succAbove
-/

#print Fin.succAboveOrderEmb /-
/-- `succ_above p i` embeds `fin n` into `fin (n + 1)` with a hole around `p`. -/
def succAboveOrderEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono _ p.strictMono_succAbove
#align fin.succ_above Fin.succAboveOrderEmb
-/

#print Fin.succAbove_of_castSucc_lt /-
/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `cast_succ` when the resulting `i.cast_succ < p`. -/
theorem succAbove_of_castSucc_lt (p : Fin (n + 1)) (i : Fin n) (h : i.cast_succ < p) :
    p.succAboveOrderEmb i = i.cast_succ := by rw [succ_above]; exact if_pos h
#align fin.succ_above_below Fin.succAbove_of_castSucc_lt
-/

#print Fin.succAbove_ne_zero_zero /-
@[simp]
theorem succAbove_ne_zero_zero [NeZero n] {a : Fin (n + 1)} (ha : a ≠ 0) :
    a.succAboveOrderEmb 0 = 0 := by
  rw [Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact bot_lt_iff_ne_bot.mpr ha
#align fin.succ_above_ne_zero_zero Fin.succAbove_ne_zero_zero
-/

#print Fin.succAbove_eq_zero_iff /-
theorem succAbove_eq_zero_iff [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) :
    a.succAboveOrderEmb b = 0 ↔ b = 0 := by
  simp only [← succ_above_ne_zero_zero ha, OrderEmbedding.eq_iff_eq]
#align fin.succ_above_eq_zero_iff Fin.succAbove_eq_zero_iff
-/

#print Fin.succAbove_ne_zero /-
theorem succAbove_ne_zero [NeZero n] {a : Fin (n + 1)} {b : Fin n} (ha : a ≠ 0) (hb : b ≠ 0) :
    a.succAboveOrderEmb b ≠ 0 :=
  mt (succAbove_eq_zero_iff ha).mp hb
#align fin.succ_above_ne_zero Fin.succAbove_ne_zero
-/

#print Fin.succAbove_zero /-
/-- Embedding `fin n` into `fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp]
theorem succAbove_zero : ⇑(succAboveOrderEmb (0 : Fin (n + 1))) = Fin.succ :=
  rfl
#align fin.succ_above_zero Fin.succAbove_zero
-/

#print Fin.succAbove_last /-
/-- Embedding `fin n` into `fin (n + 1)` with a hole around `last n` embeds by `cast_succ`. -/
@[simp]
theorem succAbove_last : succAboveOrderEmb (Fin.last n) = castSuccEmb := by ext;
  simp only [succ_above_below, cast_succ_lt_last]
#align fin.succ_above_last Fin.succAbove_last
-/

#print Fin.succAbove_last_apply /-
theorem succAbove_last_apply (i : Fin n) : succAboveOrderEmb (Fin.last n) i = i.cast_succ := by
  rw [succ_above_last]
#align fin.succ_above_last_apply Fin.succAbove_last_apply
-/

#print Fin.succAbove_of_le_castSucc /-
/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
theorem succAbove_of_le_castSucc (p : Fin (n + 1)) (i : Fin n) (h : p ≤ i.cast_succ) :
    p.succAboveOrderEmb i = i.succ := by simp [succ_above, h.not_lt]
#align fin.succ_above_above Fin.succAbove_of_le_castSucc
-/

#print Fin.succAbove_lt_ge /-
/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
theorem succAbove_lt_ge (p : Fin (n + 1)) (i : Fin n) : i.cast_succ < p ∨ p ≤ i.cast_succ :=
  lt_or_ge (castSuccEmb i) p
#align fin.succ_above_lt_ge Fin.succAbove_lt_ge
-/

#print Fin.castSucc_lt_or_lt_succ /-
/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
theorem castSucc_lt_or_lt_succ (p : Fin (n + 1)) (i : Fin n) : i.cast_succ < p ∨ p < i.succ :=
  Or.cases_on (succAbove_lt_ge p i) (fun h => Or.inl h) fun h =>
    Or.inr (lt_of_le_of_lt h (castSucc_lt_succ i))
#align fin.succ_above_lt_gt Fin.castSucc_lt_or_lt_succ
-/

#print Fin.succAbove_lt_iff_castSucc_lt /-
/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp]
theorem succAbove_lt_iff_castSucc_lt (p : Fin (n + 1)) (i : Fin n) :
    p.succAboveOrderEmb i < p ↔ i.cast_succ < p :=
  by
  refine' Iff.intro _ _
  · intro h
    cases' succ_above_lt_ge p i with H H
    · exact H
    · rw [succ_above_above _ _ H] at h
      exact lt_trans (cast_succ_lt_succ i) h
  · intro h
    rw [succ_above_below _ _ h]
    exact h
#align fin.succ_above_lt_iff Fin.succAbove_lt_iff_castSucc_lt
-/

#print Fin.lt_succAbove_iff_le_castSucc /-
/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
theorem lt_succAbove_iff_le_castSucc (p : Fin (n + 1)) (i : Fin n) :
    p < p.succAboveOrderEmb i ↔ p ≤ i.cast_succ :=
  by
  refine' Iff.intro _ _
  · intro h
    cases' succ_above_lt_ge p i with H H
    · rw [succ_above_below _ _ H] at h
      exact le_of_lt h
    · exact H
  · intro h
    rw [succ_above_above _ _ h]
    exact lt_of_le_of_lt h (cast_succ_lt_succ i)
#align fin.lt_succ_above_iff Fin.lt_succAbove_iff_le_castSucc
-/

#print Fin.succAbove_ne /-
/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
never results in `p` itself -/
theorem succAbove_ne (p : Fin (n + 1)) (i : Fin n) : p.succAboveOrderEmb i ≠ p :=
  by
  intro eq
  by_cases H : i.cast_succ < p
  · simpa [lt_irrefl, ← succ_above_below _ _ H, Eq] using H
  · simpa [← succ_above_above _ _ (le_of_not_lt H), Eq] using cast_succ_lt_succ i
#align fin.succ_above_ne Fin.succAbove_ne
-/

#print Fin.succAbove_pos /-
/-- Embedding a positive `fin n` results in a positive fin (n + 1)` -/
theorem succAbove_pos [NeZero n] (p : Fin (n + 1)) (i : Fin n) (h : 0 < i) :
    0 < p.succAboveOrderEmb i := by
  by_cases H : i.cast_succ < p
  · simpa [succ_above_below _ _ H] using cast_succ_pos h
  · simp [succ_above_above _ _ (le_of_not_lt H)]
#align fin.succ_above_pos Fin.succAbove_pos
-/

@[simp]
theorem succAboveOrderEmb_castLT {x y : Fin (n + 1)} (h : x < y)
    (hx : x.1 < n := lt_of_lt_of_le h y.le_last) : y.succAboveOrderEmb (x.castLT hx) = x := by
  rw [succ_above_below, cast_succ_cast_lt]; exact h
#align fin.succ_above_cast_lt Fin.succAboveOrderEmb_castLT

@[simp]
theorem succAboveOrderEmb_pred {x y : Fin (n + 1)} (h : x < y)
    (hy : y ≠ 0 := (x.zero_le.trans_lt h).ne') : x.succAboveOrderEmb (y.pred hy) = y := by
  rw [succ_above_above, succ_pred]; simpa [le_iff_coe_le_coe] using Nat.le_pred_of_lt h
#align fin.succ_above_pred Fin.succAboveOrderEmb_pred

#print Fin.castPred_succAbove /-
theorem castPred_succAbove {x : Fin n} {y : Fin (n + 1)} (h : castSuccEmb x < y)
    (h' : (y.succAboveOrderEmb x).1 < n :=
      lt_of_lt_of_le ((succAbove_lt_iff_castSucc_lt _ _).2 h) (le_last y)) :
    (y.succAboveOrderEmb x).castLT h' = x := by
  simp only [succ_above_below _ _ h, cast_lt_cast_succ]
#align fin.cast_lt_succ_above Fin.castPred_succAbove
-/

#print Fin.pred_succAbove /-
theorem pred_succAbove {x : Fin n} {y : Fin (n + 1)} (h : y ≤ castSuccEmb x)
    (h' : y.succAboveOrderEmb x ≠ 0 :=
      (y.zero_le.trans_lt <| (lt_succAbove_iff_le_castSucc _ _).2 h).ne') :
    (y.succAboveOrderEmb x).pred h' = x := by simp only [succ_above_above _ _ h, pred_succ]
#align fin.pred_succ_above Fin.pred_succAbove
-/

#print Fin.exists_succAbove_eq /-
theorem exists_succAbove_eq {x y : Fin (n + 1)} (h : x ≠ y) : ∃ z, y.succAboveOrderEmb z = x :=
  by
  cases' h.lt_or_lt with hlt hlt
  exacts [⟨_, succ_above_cast_lt hlt⟩, ⟨_, succ_above_pred hlt⟩]
#align fin.exists_succ_above_eq Fin.exists_succAbove_eq
-/

#print Fin.exists_succAbove_eq_iff /-
@[simp]
theorem exists_succAbove_eq_iff {x y : Fin (n + 1)} : (∃ z, x.succAboveOrderEmb z = y) ↔ y ≠ x :=
  by
  refine' ⟨_, exists_succ_above_eq⟩
  rintro ⟨y, rfl⟩
  exact succ_above_ne _ _
#align fin.exists_succ_above_eq_iff Fin.exists_succAbove_eq_iff
-/

#print Fin.range_succAbove /-
/-- The range of `p.succ_above` is everything except `p`. -/
@[simp]
theorem range_succAbove (p : Fin (n + 1)) : Set.range p.succAboveOrderEmb = {p}ᶜ :=
  Set.ext fun _ => exists_succAbove_eq_iff
#align fin.range_succ_above Fin.range_succAbove
-/

#print Fin.range_succ /-
@[simp]
theorem range_succ (n : ℕ) : Set.range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ :=
  range_succAbove 0
#align fin.range_succ Fin.range_succ
-/

#print Fin.exists_succ_eq /-
@[simp]
theorem exists_succ_eq {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 :=
  @exists_succAbove_eq_iff n 0 x
#align fin.exists_succ_eq_iff Fin.exists_succ_eq
-/

#print Fin.succAbove_right_injective /-
/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
theorem succAbove_right_injective {x : Fin (n + 1)} : Injective (succAboveOrderEmb x) :=
  (succAboveOrderEmb x).Injective
#align fin.succ_above_right_injective Fin.succAbove_right_injective
-/

#print Fin.succAbove_right_inj /-
/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
theorem succAbove_right_inj {x : Fin (n + 1)} :
    x.succAboveOrderEmb a = x.succAboveOrderEmb b ↔ a = b :=
  succAbove_right_injective.eq_iff
#align fin.succ_above_right_inj Fin.succAbove_right_inj
-/

#print Fin.succAbove_left_injective /-
/-- `succ_above` is injective at the pivot -/
theorem succAbove_left_injective : Injective (@succAboveOrderEmb n) := fun _ _ h => by
  simpa [range_succ_above] using congr_arg (fun f : Fin n ↪o Fin (n + 1) => Set.range fᶜ) h
#align fin.succ_above_left_injective Fin.succAbove_left_injective
-/

#print Fin.succAbove_left_inj /-
/-- `succ_above` is injective at the pivot -/
@[simp]
theorem succAbove_left_inj {x y : Fin (n + 1)} :
    x.succAboveOrderEmb = y.succAboveOrderEmb ↔ x = y :=
  succAbove_left_injective.eq_iff
#align fin.succ_above_left_inj Fin.succAbove_left_inj
-/

#print Fin.zero_succAbove /-
@[simp]
theorem zero_succAbove {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)).succAboveOrderEmb i = i.succ :=
  rfl
#align fin.zero_succ_above Fin.zero_succAbove
-/

#print Fin.succ_succAbove_zero /-
@[simp]
theorem succ_succAbove_zero {n : ℕ} [NeZero n] (i : Fin n) : i.succ.succAboveOrderEmb 0 = 0 :=
  succAbove_of_castSucc_lt _ _ (succ_pos _)
#align fin.succ_succ_above_zero Fin.succ_succAbove_zero
-/

#print Fin.succ_succAbove_succ /-
@[simp]
theorem succ_succAbove_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    i.succ.succAboveOrderEmb j.succ = (i.succAboveOrderEmb j).succ :=
  (lt_or_ge j.cast_succ i).elim
    (fun h => by
      have h' : j.succ.cast_succ < i.succ := by simpa [lt_iff_coe_lt_coe] using h
      ext
      simp [succ_above_below _ _ h, succ_above_below _ _ h'])
    fun h => by
    have h' : i.succ ≤ j.succ.cast_succ := by simpa [le_iff_coe_le_coe] using h
    ext
    simp [succ_above_above _ _ h, succ_above_above _ _ h']
#align fin.succ_succ_above_succ Fin.succ_succAbove_succ
-/

#print Fin.one_succAbove_zero /-
@[simp]
theorem one_succAbove_zero {n : ℕ} : (1 : Fin (n + 2)).succAboveOrderEmb 0 = 0 :=
  succ_succAbove_zero 0
#align fin.one_succ_above_zero Fin.one_succAbove_zero
-/

#print Fin.succ_succAbove_one /-
/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succ_above_zero` or `succ_succ_above_zero`. -/
@[simp]
theorem succ_succAbove_one {n : ℕ} [NeZero n] (i : Fin (n + 1)) :
    i.succ.succAboveOrderEmb 1 = (i.succAboveOrderEmb 0).succ := by
  rw [← succ_succ_above_succ i 0, succ_zero_eq_one]
#align fin.succ_succ_above_one Fin.succ_succAbove_one
-/

#print Fin.one_succAbove_succ /-
@[simp]
theorem one_succAbove_succ {n : ℕ} (j : Fin n) :
    (1 : Fin (n + 2)).succAboveOrderEmb j.succ = j.succ.succ :=
  succ_succAbove_succ 0 j
#align fin.one_succ_above_succ Fin.one_succAbove_succ
-/

#print Fin.one_succAbove_one /-
@[simp]
theorem one_succAbove_one {n : ℕ} : (1 : Fin (n + 3)).succAboveOrderEmb 1 = 2 :=
  succ_succAbove_succ 0 0
#align fin.one_succ_above_one Fin.one_succAbove_one
-/

end SuccAbove

section PredAbove

#print Fin.predAbove /-
/-- `pred_above p i` embeds `i : fin (n+1)` into `fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : p.cast_succ < i then i.pred (ne_of_lt (lt_of_le_of_lt (zero_le' p.cast_succ) h)).symm
  else i.castLT (lt_of_le_of_lt (le_of_not_lt h) p.2)
#align fin.pred_above Fin.predAbove
-/

#print Fin.predAbove_right_monotone /-
theorem predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H =>
  by
  dsimp [pred_above]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_coe_le_coe, coe_pred]
  · exact pred_le_pred H
  ·
    calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · simp at ha; exact le_pred_of_lt (lt_of_le_of_lt ha hb)
  · exact H
#align fin.pred_above_right_monotone Fin.predAbove_right_monotone
-/

#print Fin.predAbove_left_monotone /-
theorem predAbove_left_monotone (i : Fin (n + 1)) : Monotone fun p => predAbove p i := fun a b H =>
  by
  dsimp [pred_above]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_coe_le_coe, coe_pred]
  · exact pred_le _
  · have : b < a := cast_succ_lt_cast_succ_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_le
#align fin.pred_above_left_monotone Fin.predAbove_left_monotone
-/

#print Fin.castPred /-
/-- `cast_pred` embeds `i : fin (n + 2)` into `fin (n + 1)`
by lowering just `last (n + 1)` to `last n`. -/
def castPred (i : Fin (n + 2)) : Fin (n + 1) :=
  predAbove (last n) i
#align fin.cast_pred Fin.castPred
-/

#print Fin.castPred_zero /-
@[simp]
theorem castPred_zero : castPred (0 : Fin (n + 2)) = 0 :=
  rfl
#align fin.cast_pred_zero Fin.castPred_zero
-/

#print Fin.castPred_one /-
@[simp]
theorem castPred_one : castPred (1 : Fin (n + 2)) = 1 := by cases n; apply Subsingleton.elim; rfl
#align fin.cast_pred_one Fin.castPred_one
-/

#print Fin.predAbove_zero_of_ne_zero /-
@[simp]
theorem predAbove_zero_of_ne_zero {i : Fin (n + 2)} (hi : i ≠ 0) : predAbove 0 i = i.pred hi :=
  by
  dsimp [pred_above]
  rw [dif_pos]
  exact (pos_iff_ne_zero _).mpr hi
#align fin.pred_above_zero Fin.predAbove_zero_of_ne_zero
-/

@[simp]
theorem castPred_last : castPred (last (n + 1)) = last n :=
  eq_of_veq (by simp [cast_pred, pred_above, cast_succ_lt_last])
#align fin.cast_pred_last Fin.castPred_last

#print Fin.castPred_mk /-
@[simp]
theorem castPred_mk (n i : ℕ) (h : i < n + 1) : castPred ⟨i, lt_succ_of_lt h⟩ = ⟨i, h⟩ :=
  by
  have : ¬cast_succ (last n) < ⟨i, lt_succ_of_lt h⟩ := by
    simpa [lt_iff_coe_lt_coe] using le_of_lt_succ h
  simp [cast_pred, pred_above, this]
#align fin.cast_pred_mk Fin.castPred_mk
-/

#print Fin.coe_castPred /-
theorem coe_castPred {n : ℕ} (a : Fin (n + 2)) (hx : a < Fin.last _) : (a.cast_pred : ℕ) = a :=
  by
  rcases a with ⟨a, ha⟩
  rw [cast_pred_mk]
  exacts [rfl, hx]
#align fin.coe_cast_pred Fin.coe_castPred
-/

#print Fin.predAbove_of_le_castSucc /-
theorem predAbove_of_le_castSucc (p : Fin (n + 1)) (i : Fin (n + 2)) (h : i ≤ p.cast_succ) :
    p.predAbove i = i.cast_pred :=
  by
  have : i ≤ (last n).cast_succ := h.trans p.le_last
  simp [pred_above, cast_pred, h.not_lt, this.not_lt]
#align fin.pred_above_below Fin.predAbove_of_le_castSucc
-/

@[simp]
theorem predAbove_last : predAbove (Fin.last n) = castPred :=
  rfl
#align fin.pred_above_last Fin.predAbove_last

#print Fin.predAbove_last_apply /-
theorem predAbove_last_apply (i : Fin n) : predAbove (Fin.last n) i = i.cast_pred := by
  rw [pred_above_last]
#align fin.pred_above_last_apply Fin.predAbove_last_apply
-/

#print Fin.predAbove_of_castSucc_lt /-
theorem predAbove_of_castSucc_lt (p : Fin n) (i : Fin (n + 1)) (h : p.cast_succ < i) :
    p.predAbove i = i.pred (p.cast_succ.zero_le.trans_lt h).Ne.symm := by simp [pred_above, h]
#align fin.pred_above_above Fin.predAbove_of_castSucc_lt
-/

theorem castPred_monotone : Monotone (@castPred n) :=
  predAbove_right_monotone (last _)
#align fin.cast_pred_monotone Fin.castPred_monotone

#print Fin.succAbove_predAbove /-
/-- Sending `fin (n+1)` to `fin n` by subtracting one from anything above `p`
then back to `fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
theorem succAbove_predAbove {p : Fin n} {i : Fin (n + 1)} (h : i ≠ p.cast_succ) :
    p.cast_succ.succAboveOrderEmb (p.predAbove i) = i :=
  by
  dsimp [pred_above, succ_above]
  rcases p with ⟨p, _⟩
  rcases i with ⟨i, _⟩
  cases' lt_or_le i p with H H
  · rw [dif_neg]; rw [if_pos]; rfl; exact H; simp; apply le_of_lt H
  · rw [dif_pos]; rw [if_neg]
    pick_goal 3
    -- For some reason `simp` doesn't fire fully unless we discharge the third goal.
    · exact lt_of_le_of_ne H (Ne.symm h)
    · simp
    · simp only [Fin.mk_eq_mk, Ne.def, Fin.castSucc_mk] at h
      simp only [pred, Fin.mk_lt_mk, not_lt]
      exact Nat.le_pred_of_lt (Nat.lt_of_le_of_ne H (Ne.symm h))
#align fin.succ_above_pred_above Fin.succAbove_predAbove
-/

#print Fin.predAbove_succAbove /-
/-- Sending `fin n` into `fin (n + 1)` with a gap at `p`
then back to `fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
theorem predAbove_succAbove (p : Fin n) (i : Fin n) :
    p.predAbove (p.cast_succ.succAboveOrderEmb i) = i :=
  by
  dsimp [pred_above, succ_above]
  rcases p with ⟨p, _⟩
  rcases i with ⟨i, _⟩
  split_ifs
  · rw [dif_neg]
    · rfl
    · simp_rw [if_pos h]
      simp only [Subtype.mk_lt_mk, not_lt]
      exact le_of_lt h
  · rw [dif_pos]
    · rfl
    · simp_rw [if_neg h]
      exact lt_succ_iff.mpr (not_lt.mp h)
#align fin.pred_above_succ_above Fin.predAbove_succAbove
-/

#print Fin.castSucc_pred_eq_pred_castSucc /-
theorem castSucc_pred_eq_pred_castSucc {a : Fin (n + 1)} (ha : a ≠ 0)
    (ha' := a.castSucc_ne_zero_iff.mpr ha) : (a.pred ha).cast_succ = a.cast_succ.pred ha' := by
  cases a; rfl
#align fin.cast_succ_pred_eq_pred_cast_succ Fin.castSucc_pred_eq_pred_castSucc
-/

#print Fin.pred_succAbove_pred /-
/-- `pred` commutes with `succ_above`. -/
theorem pred_succAbove_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succAbove_ne_zero ha hb) :
    (a.pred ha).succAboveOrderEmb (b.pred hb) = (a.succAboveOrderEmb b).pred hk :=
  by
  obtain hbelow | habove := lt_or_le b.cast_succ a
  -- `rwa` uses them
  · rw [Fin.succAbove_of_castSucc_lt]
    · rwa [cast_succ_pred_eq_pred_cast_succ, Fin.pred_inj, Fin.succAbove_of_castSucc_lt]
    · rwa [cast_succ_pred_eq_pred_cast_succ, pred_lt_pred_iff]
  · rw [Fin.succAbove_of_le_castSucc]
    have : (b.pred hb).succ = b.succ.pred (Fin.succ_ne_zero _) := by rw [succ_pred, pred_succ]
    · rwa [this, Fin.pred_inj, Fin.succAbove_of_le_castSucc]
    · rwa [cast_succ_pred_eq_pred_cast_succ, Fin.pred_le_pred_iff]
#align fin.pred_succ_above_pred Fin.pred_succAbove_pred
-/

#print Fin.succ_predAbove_succ /-
/-- `succ` commutes with `pred_above`. -/
@[simp]
theorem succ_predAbove_succ (a : Fin n) (b : Fin (n + 1)) :
    a.succ.predAbove b.succ = (a.predAbove b).succ :=
  by
  obtain h₁ | h₂ := lt_or_le a.cast_succ b
  · rw [Fin.predAbove_of_castSucc_lt _ _ h₁, Fin.succ_pred, Fin.predAbove_of_castSucc_lt,
      Fin.pred_succ]
    simpa only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ, add_lt_add_iff_right] using
      h₁
  · cases n
    · exfalso
      exact not_lt_zero' a.is_lt
    · rw [Fin.predAbove_of_le_castSucc a b h₂,
        Fin.predAbove_of_le_castSucc a.succ b.succ
          (by
            simpa only [le_iff_coe_le_coe, coe_succ, coe_cast_succ, add_le_add_iff_right] using h₂)]
      ext
      have h₀ : (b : ℕ) < n + 1 :=
        by
        simp only [le_iff_coe_le_coe, coe_cast_succ] at h₂
        simpa only [lt_succ_iff] using h₂.trans a.is_le
      have h₁ : (b.succ : ℕ) < n + 2 :=
        by
        rw [← Nat.succ_lt_succ_iff] at h₀
        simpa only [coe_succ] using h₀
      simp only [coe_cast_pred b h₀, coe_cast_pred b.succ h₁, coe_succ]
#align fin.succ_pred_above_succ Fin.succ_predAbove_succ
-/

#print Fin.castPred_castSucc /-
@[simp]
theorem castPred_castSucc (i : Fin (n + 1)) : castPred i.cast_succ = i := by
  simp [cast_pred, pred_above, le_last]
#align fin.cast_pred_cast_succ Fin.castPred_castSucc
-/

#print Fin.castSucc_castPred /-
theorem castSucc_castPred {i : Fin (n + 2)} (h : i < last _) : castSuccEmb i.cast_pred = i :=
  by
  rw [cast_pred, pred_above, dif_neg]
  · simp [Fin.eq_iff_veq]
  · exact h.not_le
#align fin.cast_succ_cast_pred Fin.castSucc_castPred
-/

theorem coe_castPred_le_self (i : Fin (n + 2)) : (i.cast_pred : ℕ) ≤ i :=
  by
  rcases i.le_last.eq_or_lt with (rfl | h)
  · simp
  · rw [cast_pred, pred_above, dif_neg]
    · simp
    · simpa [lt_iff_coe_lt_coe, le_iff_coe_le_coe, lt_succ_iff] using h
#align fin.coe_cast_pred_le_self Fin.coe_castPred_le_self

theorem coe_castPred_lt_iff {i : Fin (n + 2)} : (i.cast_pred : ℕ) < i ↔ i = Fin.last _ :=
  by
  rcases i.le_last.eq_or_lt with (rfl | H)
  · simp
  · simp only [ne_of_lt H]
    rw [← cast_succ_cast_pred H]
    simp
#align fin.coe_cast_pred_lt_iff Fin.coe_castPred_lt_iff

theorem lt_last_iff_coe_castPred {i : Fin (n + 2)} : i < Fin.last _ ↔ (i.cast_pred : ℕ) = i :=
  by
  rcases i.le_last.eq_or_lt with (rfl | H)
  · simp
  · simp only [H]
    rw [← cast_succ_cast_pred H]
    simp
#align fin.lt_last_iff_coe_cast_pred Fin.lt_last_iff_coe_castPred

end PredAbove

#print Fin.clamp /-
/-- `min n m` as an element of `fin (m + 1)` -/
def clamp (n m : ℕ) : Fin (m + 1) :=
  ofNat <| min n m
#align fin.clamp Fin.clamp
-/

#print Fin.coe_clamp /-
@[simp]
theorem coe_clamp (n m : ℕ) : (clamp n m : ℕ) = min n m :=
  Nat.mod_eq_of_lt <| Nat.lt_succ_iff.mpr <| min_le_right _ _
#align fin.coe_clamp Fin.coe_clamp
-/

#print Fin.coe_ofNat_eq_mod /-
@[simp]
theorem coe_ofNat_eq_mod (m n : ℕ) [NeZero m] : ((n : Fin m) : ℕ) = n % m :=
  rfl
#align fin.coe_of_nat_eq_mod Fin.coe_ofNat_eq_mod
-/

section Mul

/-!
### mul
-/


#print Fin.val_mul /-
theorem val_mul {n : ℕ} : ∀ a b : Fin n, (a * b).val = a.val * b.val % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl
#align fin.val_mul Fin.val_mul
-/

#print Fin.coe_mul /-
theorem coe_mul {n : ℕ} : ∀ a b : Fin n, ((a * b : Fin n) : ℕ) = a * b % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl
#align fin.coe_mul Fin.coe_mul
-/

#print Fin.mul_one' /-
@[simp]
protected theorem mul_one' [NeZero n] (k : Fin n) : k * 1 = k :=
  by
  cases n
  · simp
  cases n
  · simp
  simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)]
#align fin.mul_one Fin.mul_one'
-/

#print Fin.mul_comm /-
protected theorem mul_comm (a b : Fin n) : a * b = b * a :=
  Fin.eq_of_veq <| by rw [mul_def, mul_def, mul_comm]
#align fin.mul_comm Fin.mul_comm
-/

#print Fin.one_mul' /-
@[simp]
protected theorem one_mul' [NeZero n] (k : Fin n) : (1 : Fin n) * k = k := by
  rw [Fin.mul_comm, Fin.mul_one']
#align fin.one_mul Fin.one_mul'
-/

#print Fin.mul_zero' /-
@[simp]
protected theorem mul_zero' [NeZero n] (k : Fin n) : k * 0 = 0 := by simp [eq_iff_veq, mul_def]
#align fin.mul_zero Fin.mul_zero'
-/

#print Fin.zero_mul' /-
@[simp]
protected theorem zero_mul' [NeZero n] (k : Fin n) : (0 : Fin n) * k = 0 := by
  simp [eq_iff_veq, mul_def]
#align fin.zero_mul Fin.zero_mul'
-/

end Mul

section

-- Note that here we are disabling the "safety" of reflected, to allow us to reuse `nat.mk_numeral`.
-- The usual way to provide the required `reflected` instance would be via rewriting to prove that
-- the expression we use here is equivalent.
attribute [local semireducible] reflected

unsafe instance toExpr : ∀ n, has_reflect (Fin n)
  | 0 => finZeroElim
  | n + 1 =>
    nat.mk_numeral q(Fin n.succ) q((by infer_instance : Zero (Fin n.succ)))
        q((by infer_instance : One (Fin n.succ))) q((by infer_instance : Add (Fin n.succ))) ∘
      Fin.val
#align fin.reflect Fin.toExprₓ

end

end Fin

