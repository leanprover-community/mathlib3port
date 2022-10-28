/-
Copyright (c) 2017 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Keeley Hoek
-/
import Mathbin.Algebra.NeZero
import Mathbin.Data.Nat.Cast
import Mathbin.Order.RelIso
import Mathbin.Tactic.ApplyFun
import Mathbin.Tactic.Localized

/-!
# The finite type with `n` elements

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

/-- Elimination principle for the empty set `fin 0`, dependent version. -/
def finZeroElim {α : Fin 0 → Sort u} (x : Fin 0) : α x :=
  x.elim0

namespace Fin

/-- A non-dependent variant of `elim0`. -/
def elim0' {α : Sort _} (x : Fin 0) : α :=
  x.elim0

variable {n m : ℕ} {a b : Fin n}

instance finToNat (n : ℕ) : Coe (Fin n) Nat :=
  ⟨Fin.val⟩

theorem val_injective : Function.Injective (@Fin.val n) :=
  @Fin.eq_of_veq n

protected theorem prop (a : Fin n) : a.val < n :=
  a.2

@[simp]
theorem is_lt (a : Fin n) : (a : ℕ) < n :=
  a.2

protected theorem pos (i : Fin n) : 0 < n :=
  lt_of_le_of_lt (Nat.zero_le _) i.is_lt

theorem pos_iff_nonempty {n : ℕ} : 0 < n ↔ Nonempty (Fin n) :=
  ⟨fun h => ⟨⟨0, h⟩⟩, fun ⟨i⟩ => i.Pos⟩

/-- Equivalence between `fin n` and `{ i // i < n }`. -/
@[simps apply symmApply]
def equivSubtype : Fin n ≃ { i // i < n } where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

section coe

/-!
### coercions and constructions
-/


@[simp]
protected theorem eta (a : Fin n) (h : (a : ℕ) < n) : (⟨(a : ℕ), h⟩ : Fin n) = a := by cases a <;> rfl

@[ext]
theorem ext {a b : Fin n} (h : (a : ℕ) = b) : a = b :=
  eq_of_veq h

theorem ext_iff {a b : Fin n} : a = b ↔ (a : ℕ) = b :=
  Iff.intro (congr_arg _) Fin.eq_of_veq

theorem coe_injective {n : ℕ} : Injective (coe : Fin n → ℕ) :=
  Fin.val_injective

theorem coe_eq_coe (a b : Fin n) : (a : ℕ) = b ↔ a = b :=
  ext_iff.symm

theorem eq_iff_veq (a b : Fin n) : a = b ↔ a.1 = b.1 :=
  ⟨veq_of_eq, eq_of_veq⟩

theorem ne_iff_vne (a b : Fin n) : a ≠ b ↔ a.1 ≠ b.1 :=
  ⟨vne_of_ne, ne_of_vne⟩

-- built-in reduction doesn't always work
@[simp, nolint simp_nf]
theorem mk_eq_mk {a h a' h'} : @mk n a h = @mk n a' h' ↔ a = a' :=
  ext_iff

protected theorem mk.inj_iff {n a b : ℕ} {ha : a < n} {hb : b < n} : (⟨a, ha⟩ : Fin n) = ⟨b, hb⟩ ↔ a = b :=
  eq_iff_veq _ _

theorem mk_val {m n : ℕ} (h : m < n) : (⟨m, h⟩ : Fin n).val = m :=
  rfl

theorem eq_mk_iff_coe_eq {k : ℕ} {hk : k < n} : a = ⟨k, hk⟩ ↔ (a : ℕ) = k :=
  Fin.eq_iff_veq a ⟨k, hk⟩

@[simp, norm_cast]
theorem coe_mk {m n : ℕ} (h : m < n) : ((⟨m, h⟩ : Fin n) : ℕ) = m :=
  rfl

theorem mk_coe (i : Fin n) : (⟨i, i.property⟩ : Fin n) = i :=
  Fin.eta _ _

theorem coe_eq_val (a : Fin n) : (a : ℕ) = a.val :=
  rfl

@[simp]
theorem val_eq_coe (a : Fin n) : a.val = a :=
  rfl

/-- Assume `k = l`. If two functions defined on `fin k` and `fin l` are equal on each element,
then they coincide (in the heq sense). -/
protected theorem heq_fun_iff {α : Sort _} {k l : ℕ} (h : k = l) {f : Fin k → α} {g : Fin l → α} :
    HEq f g ↔ ∀ i : Fin k, f i = g ⟨(i : ℕ), h ▸ i.2⟩ := by
  subst h
  simp [Function.funext_iff]

protected theorem heq_ext_iff {k l : ℕ} (h : k = l) {i : Fin k} {j : Fin l} : HEq i j ↔ (i : ℕ) = (j : ℕ) := by
  subst h
  simp [coe_eq_coe]

theorem exists_iff {p : Fin n → Prop} : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
  ⟨fun h => Exists.elim h fun ⟨i, hi⟩ hpi => ⟨i, hi, hpi⟩, fun h => Exists.elim h fun i hi => ⟨⟨i, hi.fst⟩, hi.snd⟩⟩

theorem forall_iff {p : Fin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
  ⟨fun h i hi => h ⟨i, hi⟩, fun h ⟨i, hi⟩ => h i hi⟩

end coe

section Order

/-!
### order
-/


theorem is_le (i : Fin (n + 1)) : (i : ℕ) ≤ n :=
  le_of_lt_succ i.is_lt

@[simp]
theorem is_le' : (a : ℕ) ≤ n :=
  le_of_lt a.is_lt

theorem lt_iff_coe_lt_coe : a < b ↔ (a : ℕ) < b :=
  Iff.rfl

theorem le_iff_coe_le_coe : a ≤ b ↔ (a : ℕ) ≤ b :=
  Iff.rfl

theorem mk_lt_of_lt_coe {a : ℕ} (h : a < b) : (⟨a, h.trans b.is_lt⟩ : Fin n) < b :=
  h

theorem mk_le_of_le_coe {a : ℕ} (h : a ≤ b) : (⟨a, h.trans_lt b.is_lt⟩ : Fin n) ≤ b :=
  h

/-- `a < b` as natural numbers if and only if `a < b` in `fin n`. -/
@[norm_cast, simp]
theorem coe_fin_lt {n : ℕ} {a b : Fin n} : (a : ℕ) < (b : ℕ) ↔ a < b :=
  Iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `fin n`. -/
@[norm_cast, simp]
theorem coe_fin_le {n : ℕ} {a b : Fin n} : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
  Iff.rfl

instance {n : ℕ} : LinearOrder (Fin n) :=
  @LinearOrder.lift (Fin n) _ _ ⟨fun x y => ⟨max x y, max_rec' (· < n) x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' (· < n) x.2 y.2⟩⟩ Fin.val Fin.val_injective (fun _ _ => rfl) fun _ _ => rfl

@[simp]
theorem mk_le_mk {x y : Nat} {hx} {hy} : (⟨x, hx⟩ : Fin n) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
  Iff.rfl

@[simp]
theorem mk_lt_mk {x y : Nat} {hx} {hy} : (⟨x, hx⟩ : Fin n) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl

@[simp]
theorem min_coe : min (a : ℕ) n = a := by simp

@[simp]
theorem max_coe : max (a : ℕ) n = n := by simp

instance {n : ℕ} : PartialOrder (Fin n) := by infer_instance

theorem coe_strict_mono : StrictMono (coe : Fin n → ℕ) := fun _ _ => id

/-- The equivalence `fin n ≃ { i // i < n }` is an order isomorphism. -/
@[simps apply symmApply]
def orderIsoSubtype : Fin n ≃o { i // i < n } :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])

/-- The inclusion map `fin n → ℕ` is an embedding. -/
@[simps apply]
def coeEmbedding : Fin n ↪ ℕ :=
  ⟨coe, coe_injective⟩

@[simp]
theorem equiv_subtype_symm_trans_val_embedding :
    equivSubtype.symm.toEmbedding.trans coeEmbedding = Embedding.subtype (· < n) :=
  rfl

/-- The inclusion map `fin n → ℕ` is an order embedding. -/
@[simps apply]
def coeOrderEmbedding (n) : Fin n ↪o ℕ :=
  ⟨coeEmbedding, fun a b => Iff.rfl⟩

/-- The ordering on `fin n` is a well order. -/
instance Fin.Lt.is_well_order (n) : IsWellOrder (Fin n) (· < ·) :=
  (coeOrderEmbedding n).IsWellOrder

/-- Use the ordering on `fin n` for checking recursive definitions.

For example, the following definition is not accepted by the termination checker,
unless we declare the `has_well_founded` instance:
```lean
def factorial {n : ℕ} : fin n → ℕ
| ⟨0, _⟩ := 1
| ⟨i + 1, hi⟩ := (i + 1) * factorial ⟨i, i.lt_succ_self.trans hi⟩
```
-/
instance {n : ℕ} : HasWellFounded (Fin n) :=
  ⟨_, measure_wf coe⟩

@[simp]
theorem coe_zero {n : ℕ} : ((0 : Fin (n + 1)) : ℕ) = 0 :=
  rfl

attribute [simp] val_zero

@[simp]
theorem val_zero' (n) : (0 : Fin (n + 1)).val = 0 :=
  rfl

@[simp]
theorem mk_zero : (⟨0, Nat.succ_pos'⟩ : Fin (n + 1)) = (0 : Fin _) :=
  rfl

@[simp]
theorem zero_le (a : Fin (n + 1)) : 0 ≤ a :=
  zero_le a.1

theorem zero_lt_one : (0 : Fin (n + 2)) < 1 :=
  Nat.zero_lt_one

@[simp]
theorem not_lt_zero (a : Fin n.succ) : ¬a < 0 :=
  fun.

theorem pos_iff_ne_zero (a : Fin (n + 1)) : 0 < a ↔ a ≠ 0 := by
  rw [← coe_fin_lt, coe_zero, pos_iff_ne_zero, Ne.def, Ne.def, ext_iff, coe_zero]

theorem eq_zero_or_eq_succ {n : ℕ} (i : Fin (n + 1)) : i = 0 ∨ ∃ j : Fin n, i = j.succ := by
  rcases i with ⟨_ | j, h⟩
  · left
    rfl
    
  · right
    exact ⟨⟨j, Nat.lt_of_succ_lt_succ h⟩, rfl⟩
    

theorem eq_succ_of_ne_zero {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ 0) : ∃ j : Fin n, i = j.succ :=
  (eq_zero_or_eq_succ i).resolve_left hi

/-- The antitone involution `fin n → fin n` given by `i ↦ n-(i+1)`. -/
def rev : Equiv.Perm (Fin n) :=
  (Involutive.toPerm fun i => ⟨n - (i + 1), tsub_lt_self i.Pos (Nat.succ_pos _)⟩) fun i =>
    ext <| by
      rw [coe_mk, coe_mk, ← tsub_tsub, tsub_tsub_cancel_of_le (Nat.add_one_le_iff.2 i.is_lt), add_tsub_cancel_right]

@[simp]
theorem coe_rev (i : Fin n) : (i.rev : ℕ) = n - (i + 1) :=
  rfl

theorem rev_involutive : Involutive (@rev n) :=
  Involutive.to_perm_involutive _

theorem rev_injective : Injective (@rev n) :=
  rev_involutive.Injective

theorem rev_surjective : Surjective (@rev n) :=
  rev_involutive.Surjective

theorem rev_bijective : Bijective (@rev n) :=
  rev_involutive.Bijective

@[simp]
theorem rev_inj {i j : Fin n} : i.rev = j.rev ↔ i = j :=
  rev_injective.eq_iff

@[simp]
theorem rev_rev (i : Fin n) : i.rev.rev = i :=
  rev_involutive _

@[simp]
theorem rev_symm : (@rev n).symm = rev :=
  rfl

theorem rev_eq {n a : ℕ} (i : Fin (n + 1)) (h : n = a + i) : i.rev = ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro h.symm)⟩ :=
  by
  ext
  dsimp
  conv_lhs =>
  congr
  rw [h]
  rw [add_assoc, add_tsub_cancel_right]

@[simp]
theorem rev_le_rev {i j : Fin n} : i.rev ≤ j.rev ↔ j ≤ i := by
  simp only [le_iff_coe_le_coe, coe_rev, tsub_le_tsub_iff_left (Nat.add_one_le_iff.2 j.is_lt), add_le_add_iff_right]

@[simp]
theorem rev_lt_rev {i j : Fin n} : i.rev < j.rev ↔ j < i :=
  lt_iff_lt_of_le_iff_le rev_le_rev

/-- `fin.rev n` as an order-reversing isomorphism. -/
@[simps apply toEquiv]
def revOrderIso {n} : (Fin n)ᵒᵈ ≃o Fin n :=
  ⟨OrderDual.ofDual.trans rev, fun i j => rev_le_rev⟩

@[simp]
theorem rev_order_iso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual i.rev :=
  rfl

/-- The greatest value of `fin (n+1)` -/
def last (n : ℕ) : Fin (n + 1) :=
  ⟨_, n.lt_succ_self⟩

@[simp, norm_cast]
theorem coe_last (n : ℕ) : (last n : ℕ) = n :=
  rfl

theorem last_val (n : ℕ) : (last n).val = n :=
  rfl

theorem le_last (i : Fin (n + 1)) : i ≤ last n :=
  le_of_lt_succ i.is_lt

instance : BoundedOrder (Fin (n + 1)) where
  top := last n
  le_top := le_last
  bot := 0
  bot_le := zero_le

instance : Lattice (Fin (n + 1)) :=
  LinearOrder.toLattice

theorem last_pos : (0 : Fin (n + 2)) < last (n + 1) := by simp [lt_iff_coe_lt_coe]

theorem eq_last_of_not_lt {i : Fin (n + 1)} (h : ¬(i : ℕ) < n) : i = last n :=
  le_antisymm (le_last i) (not_lt.1 h)

theorem top_eq_last (n : ℕ) : ⊤ = Fin.last n :=
  rfl

theorem bot_eq_zero (n : ℕ) : ⊥ = (0 : Fin (n + 1)) :=
  rfl

section

variable {α : Type _} [Preorder α]

open Set

/-- If `e` is an `order_iso` between `fin n` and `fin m`, then `n = m` and `e` is the identity
map. In this lemma we state that for each `i : fin n` we have `(e i : ℕ) = (i : ℕ)`. -/
@[simp]
theorem coe_order_iso_apply (e : Fin n ≃o Fin m) (i : Fin n) : (e i : ℕ) = i := by
  rcases i with ⟨i, hi⟩
  rw [Fin.coe_mk]
  induction' i using Nat.strong_induction_on with i h
  refine' le_antisymm (forall_lt_iff_le.1 fun j hj => _) (forall_lt_iff_le.1 fun j hj => _)
  · have := e.symm.lt_iff_lt.2 (mk_lt_of_lt_coe hj)
    rw [e.symm_apply_apply] at this
    convert this
    simpa using h _ this (e.symm _).is_lt
    
  · rwa [← h j hj (hj.trans hi), ← lt_iff_coe_lt_coe, e.lt_iff_lt]
    

instance order_iso_subsingleton : Subsingleton (Fin n ≃o α) :=
  ⟨fun e e' => by
    ext i
    rw [← e.symm.apply_eq_iff_eq, e.symm_apply_apply, ← e'.trans_apply, ext_iff, coe_order_iso_apply]⟩

instance order_iso_subsingleton' : Subsingleton (α ≃o Fin n) :=
  OrderIso.symm_injective.Subsingleton

instance orderIsoUnique : Unique (Fin n ≃o Fin n) :=
  Unique.mk' _

/-- Two strictly monotone functions from `fin n` are equal provided that their ranges
are equal. -/
theorem strict_mono_unique {f g : Fin n → α} (hf : StrictMono f) (hg : StrictMono g) (h : Range f = Range g) : f = g :=
  have : (hf.OrderIso f).trans (OrderIso.setCongr _ _ h) = hg.OrderIso g := Subsingleton.elim _ _
  congr_arg (Function.comp (coe : Range g → α)) (funext <| RelIso.ext_iff.1 this)

/-- Two order embeddings of `fin n` are equal provided that their ranges are equal. -/
theorem order_embedding_eq {f g : Fin n ↪o α} (h : Range f = Range g) : f = g :=
  RelEmbedding.ext <| funext_iff.1 <| strict_mono_unique f.StrictMono g.StrictMono h

end

end Order

section Add

/-!
### addition, numerals, and coercion from nat
-/


/- warning: fin.of_nat' -> Fin.ofNat' is a dubious translation:
lean 3 declaration is
  forall {n : Nat} [_inst_1 : NeZero.{0} Nat Nat.hasZero n], Nat -> (Fin n)
but is expected to have type
  forall {n : Nat}, Nat -> (GT.gt.{0} Nat instLTNat n (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Fin n)
Case conversion may be inaccurate. Consider using '#align fin.of_nat' Fin.ofNat'ₓ'. -/
/-- Given a positive `n`, `fin.of_nat' i` is `i % n` as an element of `fin n`. -/
def ofNat' [NeZero n] (i : ℕ) : Fin n :=
  ⟨i % n, mod_lt _ <| NeZero.pos n⟩

/- warning: fin.one_val -> Fin.one_val is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} Nat (Fin.val (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)) (One.one.{0} (Fin (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne))) (Fin.hasOne n))) (HMod.hMod.{0 0 0} Nat Nat Nat (instHMod.{0} Nat Nat.hasMod) (One.one.{0} Nat Nat.hasOne) (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall {n : Nat}, Eq.{1} Nat (Fin.val (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (OfNat.ofNat.{0} (Fin (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) 1 (Fin.instOfNatFinHAddNatInstHAddInstAddNatOfNat (HAdd.hAdd.{0 0 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) 1))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align fin.one_val Fin.one_valₓ'. -/
theorem one_val {n : ℕ} : (1 : Fin (n + 1)).val = 1 % (n + 1) :=
  rfl

theorem coe_one' {n : ℕ} : ((1 : Fin (n + 1)) : ℕ) = 1 % (n + 1) :=
  rfl

@[simp]
theorem val_one {n : ℕ} : (1 : Fin (n + 2)).val = 1 :=
  rfl

@[simp]
theorem coe_one {n : ℕ} : ((1 : Fin (n + 2)) : ℕ) = 1 :=
  rfl

@[simp]
theorem mk_one : (⟨1, Nat.succ_lt_succ (Nat.succ_pos n)⟩ : Fin (n + 2)) = (1 : Fin _) :=
  rfl

instance {n : ℕ} : Nontrivial (Fin (n + 2)) :=
  ⟨⟨0, 1, by decide⟩⟩

theorem nontrivial_iff_two_le : Nontrivial (Fin n) ↔ 2 ≤ n := by
  rcases n with (_ | _ | n) <;> simp [Fin.nontrivial, not_nontrivial, Nat.succ_le_iff]

theorem subsingleton_iff_le_one : Subsingleton (Fin n) ↔ n ≤ 1 := by
  rcases n with (_ | _ | n) <;> simp [IsEmpty.subsingleton, Unique.subsingleton, not_subsingleton]

section Monoid

@[simp]
protected theorem add_zero (k : Fin (n + 1)) : k + 0 = k := by simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]

@[simp]
protected theorem zero_add (k : Fin (n + 1)) : (0 : Fin (n + 1)) + k = k := by
  simp [eq_iff_veq, add_def, mod_eq_of_lt (is_lt k)]

instance addCommMonoid (n : ℕ) : AddCommMonoid (Fin (n + 1)) where
  add := (· + ·)
  add_assoc := by simp [eq_iff_veq, add_def, add_assoc]
  zero := 0
  zero_add := Fin.zero_add
  add_zero := Fin.add_zero
  add_comm := by simp [eq_iff_veq, add_def, add_comm]

instance : AddMonoidWithOne (Fin (n + 1)) :=
  { Fin.addCommMonoid n with one := 1, natCast := Fin.ofNat, nat_cast_zero := rfl,
    nat_cast_succ := fun i => eq_of_veq (add_mod _ _ _) }

end Monoid

theorem val_add {n : ℕ} : ∀ a b : Fin n, (a + b).val = (a.val + b.val) % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

theorem coe_add {n : ℕ} : ∀ a b : Fin n, ((a + b : Fin n) : ℕ) = (a + b) % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

theorem coe_add_eq_ite {n : ℕ} (a b : Fin n) : (↑(a + b) : ℕ) = if n ≤ a + b then a + b - n else a + b := by
  rw [Fin.coe_add, Nat.add_mod_eq_ite, Nat.mod_eq_of_lt (show ↑a < n from a.2), Nat.mod_eq_of_lt (show ↑b < n from b.2)]

theorem coe_bit0 {n : ℕ} (k : Fin n) : ((bit0 k : Fin n) : ℕ) = bit0 (k : ℕ) % n := by
  cases k
  rfl

theorem coe_bit1 {n : ℕ} (k : Fin (n + 1)) : ((bit1 k : Fin (n + 1)) : ℕ) = bit1 (k : ℕ) % (n + 1) := by
  cases n
  · cases' k with k h
    cases k
    · show _ % _ = _
      simp
      
    cases' h with _ h
    cases h
    
  simp [bit1, Fin.coe_bit0, Fin.coe_add, Fin.coe_one]

theorem coe_add_one_of_lt {n : ℕ} {i : Fin n.succ} (h : i < last _) : (↑(i + 1) : ℕ) = i + 1 := by
  -- First show that `((1 : fin n.succ) : ℕ) = 1`, because `n.succ` is at least 2.
  cases n
  · cases h
    
  -- Then just unfold the definitions.
  rw [Fin.coe_add, Fin.coe_one, Nat.mod_eq_of_lt (Nat.succ_lt_succ _)]
  exact h

@[simp]
theorem last_add_one : ∀ n, last n + 1 = 0
  | 0 => Subsingleton.elim _ _
  | n + 1 => by
    ext
    rw [coe_add, coe_zero, coe_last, coe_one, Nat.mod_self]

theorem coe_add_one {n : ℕ} (i : Fin (n + 1)) : ((i + 1 : Fin (n + 1)) : ℕ) = if i = last _ then 0 else i + 1 := by
  rcases(le_last i).eq_or_lt with (rfl | h)
  · simp
    
  · simpa [h.ne] using coe_add_one_of_lt h
    

section Bit

@[simp]
theorem mk_bit0 {m n : ℕ} (h : bit0 m < n) :
    (⟨bit0 m, h⟩ : Fin n) = (bit0 ⟨m, (Nat.le_add_right m m).trans_lt h⟩ : Fin _) :=
  eq_of_veq (Nat.mod_eq_of_lt h).symm

@[simp]
theorem mk_bit1 {m n : ℕ} (h : bit1 m < n + 1) :
    (⟨bit1 m, h⟩ : Fin (n + 1)) = (bit1 ⟨m, (Nat.le_add_right m m).trans_lt ((m + m).lt_succ_self.trans h)⟩ : Fin _) :=
  by
  ext
  simp only [bit1, bit0] at h
  simp only [bit1, bit0, coe_add, coe_one', coe_mk, ← Nat.add_mod, Nat.mod_eq_of_lt h]

end Bit

@[simp]
theorem val_two {n : ℕ} : (2 : Fin (n + 3)).val = 2 :=
  rfl

@[simp]
theorem coe_two {n : ℕ} : ((2 : Fin (n + 3)) : ℕ) = 2 :=
  rfl

section OfNatCoe

@[simp]
theorem of_nat_eq_coe (n : ℕ) (a : ℕ) : (ofNat a : Fin (n + 1)) = a :=
  rfl

/-- Converting an in-range number to `fin (n + 1)` produces a result
whose value is the original number.  -/
theorem coe_val_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) : (a : Fin (n + 1)).val = a := by
  rw [← of_nat_eq_coe]
  exact Nat.mod_eq_of_lt h

/-- Converting the value of a `fin (n + 1)` to `fin (n + 1)` results
in the same value.  -/
theorem coe_val_eq_self {n : ℕ} (a : Fin (n + 1)) : (a.val : Fin (n + 1)) = a := by
  rw [Fin.eq_iff_veq]
  exact coe_val_of_lt a.property

/-- Coercing an in-range number to `fin (n + 1)`, and converting back
to `ℕ`, results in that number. -/
theorem coe_coe_of_lt {n : ℕ} {a : ℕ} (h : a < n + 1) : ((a : Fin (n + 1)) : ℕ) = a :=
  coe_val_of_lt h

/-- Converting a `fin (n + 1)` to `ℕ` and back results in the same
value. -/
@[simp]
theorem coe_coe_eq_self {n : ℕ} (a : Fin (n + 1)) : ((a : ℕ) : Fin (n + 1)) = a :=
  coe_val_eq_self a

theorem coe_nat_eq_last (n) : (n : Fin (n + 1)) = Fin.last n := by
  rw [← Fin.of_nat_eq_coe, Fin.ofNat, Fin.last]
  simp only [Nat.mod_eq_of_lt n.lt_succ_self]

theorem le_coe_last (i : Fin (n + 1)) : i ≤ n := by
  rw [Fin.coe_nat_eq_last]
  exact Fin.le_last i

end OfNatCoe

theorem add_one_pos (i : Fin (n + 1)) (h : i < Fin.last n) : (0 : Fin (n + 1)) < i + 1 := by
  cases n
  · exact absurd h (Nat.not_lt_zero _)
    
  · rw [lt_iff_coe_lt_coe, coe_last, ← add_lt_add_iff_right 1] at h
    rw [lt_iff_coe_lt_coe, coe_add, coe_zero, coe_one, Nat.mod_eq_of_lt h]
    exact Nat.zero_lt_succ _
    

theorem one_pos : (0 : Fin (n + 2)) < 1 :=
  succ_pos 0

theorem zero_ne_one : (0 : Fin (n + 2)) ≠ 1 :=
  ne_of_lt one_pos

@[simp]
theorem zero_eq_one_iff : (0 : Fin (n + 1)) = 1 ↔ n = 0 := by
  constructor
  · cases n <;> intro h
    · rfl
      
    · have := zero_ne_one
      contradiction
      
    
  · rintro rfl
    rfl
    

@[simp]
theorem one_eq_zero_iff : (1 : Fin (n + 1)) = 0 ↔ n = 0 := by rw [eq_comm, zero_eq_one_iff]

end Add

section Succ

/-!
### succ and casts into larger fin types
-/


@[simp]
theorem coe_succ (j : Fin n) : (j.succ : ℕ) = j + 1 := by cases j <;> simp [Fin.succ]

@[simp]
theorem succ_pos (a : Fin n) : (0 : Fin (n + 1)) < a.succ := by simp [lt_iff_coe_lt_coe]

/-- `fin.succ` as an `order_embedding` -/
def succEmbedding (n : ℕ) : Fin n ↪o Fin (n + 1) :=
  (OrderEmbedding.ofStrictMono Fin.succ) fun ⟨i, hi⟩ ⟨j, hj⟩ h => succ_lt_succ h

@[simp]
theorem coe_succ_embedding : ⇑(succEmbedding n) = Fin.succ :=
  rfl

@[simp]
theorem succ_le_succ_iff : a.succ ≤ b.succ ↔ a ≤ b :=
  (succEmbedding n).le_iff_le

@[simp]
theorem succ_lt_succ_iff : a.succ < b.succ ↔ a < b :=
  (succEmbedding n).lt_iff_lt

theorem succ_injective (n : ℕ) : Injective (@Fin.succ n) :=
  (succEmbedding n).Injective

@[simp]
theorem succ_inj {a b : Fin n} : a.succ = b.succ ↔ a = b :=
  (succ_injective n).eq_iff

theorem succ_ne_zero {n} : ∀ k : Fin n, Fin.succ k ≠ 0
  | ⟨k, hk⟩, HEq => Nat.succ_ne_zero k <| ext_iff.1 HEq

@[simp]
theorem succ_zero_eq_one : Fin.succ (0 : Fin (n + 1)) = 1 :=
  rfl

@[simp]
theorem succ_one_eq_two : Fin.succ (1 : Fin (n + 2)) = 2 :=
  rfl

@[simp]
theorem succ_mk (n i : ℕ) (h : i < n) : Fin.succ ⟨i, h⟩ = ⟨i + 1, Nat.succ_lt_succ h⟩ :=
  rfl

theorem mk_succ_pos (i : ℕ) (h : i < n) : (0 : Fin (n + 1)) < ⟨i.succ, add_lt_add_right h 1⟩ := by
  rw [lt_iff_coe_lt_coe, coe_zero]
  exact Nat.succ_pos i

theorem one_lt_succ_succ (a : Fin n) : (1 : Fin (n + 2)) < a.succ.succ := by
  cases n
  · exact finZeroElim a
    
  · rw [← succ_zero_eq_one, succ_lt_succ_iff]
    exact succ_pos a
    

@[simp]
theorem add_one_lt_iff {n : ℕ} {k : Fin (n + 2)} : k + 1 < k ↔ k = last _ := by
  simp only [lt_iff_coe_lt_coe, coe_add, coe_last, ext_iff]
  cases' k with k hk
  rcases(le_of_lt_succ hk).eq_or_lt with (rfl | hk')
  · simp
    
  · simp [hk'.ne, mod_eq_of_lt (succ_lt_succ hk'), le_succ _]
    

@[simp]
theorem add_one_le_iff {n : ℕ} {k : Fin (n + 1)} : k + 1 ≤ k ↔ k = last _ := by
  cases n
  · simp [Subsingleton.elim (k + 1) k, Subsingleton.elim (Fin.last _) k]
    
  rw [← not_iff_not, ← add_one_lt_iff, lt_iff_le_and_ne, not_and']
  refine' ⟨fun h _ => h, fun h => h _⟩
  rw [Ne.def, ext_iff, coe_add_one]
  split_ifs with hk hk <;> simp [hk, eq_comm]

@[simp]
theorem last_le_iff {n : ℕ} {k : Fin (n + 1)} : last n ≤ k ↔ k = last n :=
  top_le_iff

@[simp]
theorem lt_add_one_iff {n : ℕ} {k : Fin (n + 1)} : k < k + 1 ↔ k < last n := by
  rw [← not_iff_not]
  simp

@[simp]
theorem le_zero_iff {n : ℕ} {k : Fin (n + 1)} : k ≤ 0 ↔ k = 0 :=
  le_bot_iff

theorem succ_succ_ne_one (a : Fin n) : Fin.succ (Fin.succ a) ≠ 1 :=
  ne_of_gt (one_lt_succ_succ a)

/-- `cast_lt i h` embeds `i` into a `fin` where `h` proves it belongs into.  -/
def castLt (i : Fin m) (h : i.1 < n) : Fin n :=
  ⟨i.1, h⟩

@[simp]
theorem coe_cast_lt (i : Fin m) (h : i.1 < n) : (castLt i h : ℕ) = i :=
  rfl

@[simp]
theorem cast_lt_mk (i n m : ℕ) (hn : i < n) (hm : i < m) : castLt ⟨i, hn⟩ hm = ⟨i, hm⟩ :=
  rfl

/-- `cast_le h i` embeds `i` into a larger `fin` type.  -/
def castLe (h : n ≤ m) : Fin n ↪o Fin m :=
  (OrderEmbedding.ofStrictMono fun a => castLt a (lt_of_lt_of_le a.2 h)) fun a b h => h

@[simp]
theorem coe_cast_le (h : n ≤ m) (i : Fin n) : (castLe h i : ℕ) = i :=
  rfl

@[simp]
theorem cast_le_mk (i n m : ℕ) (hn : i < n) (h : n ≤ m) : castLe h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h⟩ :=
  rfl

@[simp]
theorem cast_le_zero {n m : ℕ} (h : n.succ ≤ m.succ) : castLe h 0 = 0 := by simp [eq_iff_veq]

@[simp]
theorem range_cast_le {n k : ℕ} (h : n ≤ k) : Set.Range (castLe h) = { i | (i : ℕ) < n } :=
  Set.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, Fin.ext rfl⟩⟩

@[simp]
theorem coe_of_injective_cast_le_symm {n k : ℕ} (h : n ≤ k) (i : Fin k) (hi) :
    ((Equiv.ofInjective _ (castLe h).Injective).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_cast_le]
  exact congr_arg coe (Equiv.apply_of_injective_symm _ _)

@[simp]
theorem cast_le_succ {m n : ℕ} (h : m + 1 ≤ n + 1) (i : Fin m) :
    castLe h i.succ = (castLe (Nat.succ_le_succ_iff.mp h) i).succ := by simp [Fin.eq_iff_veq]

@[simp]
theorem cast_le_cast_le {k m n} (km : k ≤ m) (mn : m ≤ n) (i : Fin k) :
    Fin.castLe mn (Fin.castLe km i) = Fin.castLe (km.trans mn) i :=
  Fin.ext (by simp only [coe_cast_le])

@[simp]
theorem cast_le_comp_cast_le {k m n} (km : k ≤ m) (mn : m ≤ n) :
    Fin.castLe mn ∘ Fin.castLe km = Fin.castLe (km.trans mn) :=
  funext (cast_le_cast_le km mn)

/-- `cast eq i` embeds `i` into a equal `fin` type, see also `equiv.fin_congr`. -/
def cast (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨castLe Eq.le, castLe Eq.symm.le, fun a => eq_of_veq rfl, fun a => eq_of_veq rfl⟩
  map_rel_iff' a b := Iff.rfl

@[simp]
theorem symm_cast (h : n = m) : (cast h).symm = cast h.symm :=
  rfl

/-- While `fin.coe_order_iso_apply` is a more general case of this, we mark this `simp` anyway
as it is eligible for `dsimp`. -/
@[simp]
theorem coe_cast (h : n = m) (i : Fin n) : (cast h i : ℕ) = i :=
  rfl

@[simp]
theorem cast_zero {n' : ℕ} {h : n + 1 = n' + 1} : cast h (0 : Fin (n + 1)) = 0 :=
  ext rfl

@[simp]
theorem cast_last {n' : ℕ} {h : n + 1 = n' + 1} : cast h (last n) = last n' :=
  ext (by rw [coe_cast, coe_last, coe_last, Nat.succ_injective h])

@[simp]
theorem cast_mk (h : n = m) (i : ℕ) (hn : i < n) : cast h ⟨i, hn⟩ = ⟨i, lt_of_lt_of_le hn h.le⟩ :=
  rfl

@[simp]
theorem cast_trans {k : ℕ} (h : n = m) (h' : m = k) {i : Fin n} : cast h' (cast h i) = cast (Eq.trans h h') i :=
  rfl

@[simp]
theorem cast_refl (h : n = n := rfl) : cast h = OrderIso.refl (Fin n) := by
  ext
  rfl

theorem cast_le_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} : (castLe h' : Fin m → Fin n) = Fin.cast h :=
  funext fun _ => rfl

/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_to_equiv (h : n = m) : (cast h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h
  simp

/-- While in many cases `fin.cast` is better than `equiv.cast`/`cast`, sometimes we want to apply
a generic theorem about `cast`. -/
theorem cast_eq_cast (h : n = m) : (cast h : Fin n → Fin m) = cast (h ▸ rfl) := by
  subst h
  ext
  simp

/-- `cast_add m i` embeds `i : fin n` in `fin (n+m)`. See also `fin.nat_add` and `fin.add_nat`. -/
def castAdd (m) : Fin n ↪o Fin (n + m) :=
  cast_le <| Nat.le_add_right n m

@[simp]
theorem coe_cast_add (m : ℕ) (i : Fin n) : (castAdd m i : ℕ) = i :=
  rfl

@[simp]
theorem cast_add_zero : (castAdd 0 : Fin n → Fin (n + 0)) = cast rfl :=
  rfl

theorem cast_add_lt {m : ℕ} (n : ℕ) (i : Fin m) : (castAdd n i : ℕ) < m :=
  i.2

@[simp]
theorem cast_add_mk (m : ℕ) (i : ℕ) (h : i < n) : castAdd m ⟨i, h⟩ = ⟨i, lt_add_right i n m h⟩ :=
  rfl

@[simp]
theorem cast_add_cast_lt (m : ℕ) (i : Fin (n + m)) (hi : i.val < n) : castAdd m (castLt i hi) = i :=
  ext rfl

@[simp]
theorem cast_lt_cast_add (m : ℕ) (i : Fin n) : castLt (castAdd m i) (cast_add_lt m i) = i :=
  ext rfl

/-- For rewriting in the reverse direction, see `fin.cast_cast_add_left`. -/
theorem cast_add_cast {n n' : ℕ} (m : ℕ) (i : Fin n') (h : n' = n) :
    castAdd m (Fin.cast h i) = Fin.cast (congr_arg _ h) (castAdd m i) :=
  ext rfl

theorem cast_cast_add_left {n n' m : ℕ} (i : Fin n') (h : n' + m = n + m) :
    cast h (castAdd m i) = castAdd m (cast (add_right_cancel h) i) :=
  ext rfl

@[simp]
theorem cast_cast_add_right {n m m' : ℕ} (i : Fin n) (h : n + m' = n + m) : cast h (castAdd m' i) = castAdd m i :=
  ext rfl

/-- The cast of the successor is the succesor of the cast. See `fin.succ_cast_eq` for rewriting in
the reverse direction. -/
@[simp]
theorem cast_succ_eq {n' : ℕ} (i : Fin n) (h : n.succ = n'.succ) : cast h i.succ = (cast (Nat.succ.inj h) i).succ :=
  ext <| by simp

theorem succ_cast_eq {n' : ℕ} (i : Fin n) (h : n = n') : (cast h i).succ = cast (by rw [h]) i.succ :=
  ext <| by simp

/-- `cast_succ i` embeds `i : fin n` in `fin (n+1)`. -/
def castSucc : Fin n ↪o Fin (n + 1) :=
  castAdd 1

@[simp]
theorem coe_cast_succ (i : Fin n) : (i.cast_succ : ℕ) = i :=
  rfl

@[simp]
theorem cast_succ_mk (n i : ℕ) (h : i < n) : castSucc ⟨i, h⟩ = ⟨i, Nat.lt.step h⟩ :=
  rfl

@[simp]
theorem cast_cast_succ {n' : ℕ} {h : n + 1 = n' + 1} {i : Fin n} :
    cast h (castSucc i) = castSucc (cast (Nat.succ_injective h) i) := by
  ext
  simp only [coe_cast, coe_cast_succ]

theorem cast_succ_lt_succ (i : Fin n) : i.cast_succ < i.succ :=
  lt_iff_coe_lt_coe.2 <| by simp only [coe_cast_succ, coe_succ, Nat.lt_succ_self]

theorem le_cast_succ_iff {i : Fin (n + 1)} {j : Fin n} : i ≤ j.cast_succ ↔ i < j.succ := by
  simpa [lt_iff_coe_lt_coe, le_iff_coe_le_coe] using nat.succ_le_succ_iff.symm

theorem cast_succ_lt_iff_succ_le {n : ℕ} {i : Fin n} {j : Fin (n + 1)} : i.cast_succ < j ↔ i.succ ≤ j := by
  simpa only [Fin.lt_iff_coe_lt_coe, Fin.le_iff_coe_le_coe, Fin.coe_succ, Fin.coe_cast_succ] using Nat.lt_iff_add_one_le

@[simp]
theorem succ_last (n : ℕ) : (last n).succ = last n.succ :=
  rfl

@[simp]
theorem succ_eq_last_succ {n : ℕ} (i : Fin n.succ) : i.succ = last (n + 1) ↔ i = last n := by
  rw [← succ_last, (succ_injective _).eq_iff]

@[simp]
theorem cast_succ_cast_lt (i : Fin (n + 1)) (h : (i : ℕ) < n) : castSucc (castLt i h) = i :=
  Fin.eq_of_veq rfl

@[simp]
theorem cast_lt_cast_succ {n : ℕ} (a : Fin n) (h : (a : ℕ) < n) : castLt (castSucc a) h = a := by cases a <;> rfl

@[simp]
theorem cast_succ_lt_cast_succ_iff : a.cast_succ < b.cast_succ ↔ a < b :=
  (@castSucc n).lt_iff_lt

theorem cast_succ_injective (n : ℕ) : Injective (@Fin.castSucc n) :=
  (castSucc : Fin n ↪o _).Injective

theorem cast_succ_inj {a b : Fin n} : a.cast_succ = b.cast_succ ↔ a = b :=
  (cast_succ_injective n).eq_iff

theorem cast_succ_lt_last (a : Fin n) : castSucc a < last n :=
  lt_iff_coe_lt_coe.mpr a.is_lt

@[simp]
theorem cast_succ_zero : castSucc (0 : Fin (n + 1)) = 0 :=
  rfl

@[simp]
theorem cast_succ_one {n : ℕ} : Fin.castSucc (1 : Fin (n + 2)) = 1 :=
  rfl

/-- `cast_succ i` is positive when `i` is positive -/
theorem cast_succ_pos {i : Fin (n + 1)} (h : 0 < i) : 0 < castSucc i := by simpa [lt_iff_coe_lt_coe] using h

@[simp]
theorem cast_succ_eq_zero_iff (a : Fin (n + 1)) : a.cast_succ = 0 ↔ a = 0 :=
  Fin.ext_iff.trans <| (Fin.ext_iff.trans <| Iff.rfl).symm

theorem cast_succ_ne_zero_iff (a : Fin (n + 1)) : a.cast_succ ≠ 0 ↔ a ≠ 0 :=
  not_iff_not.mpr <| cast_succ_eq_zero_iff a

theorem cast_succ_fin_succ (n : ℕ) (j : Fin n) : castSucc (Fin.succ j) = Fin.succ (castSucc j) := by simp [Fin.ext_iff]

@[norm_cast, simp]
theorem coe_eq_cast_succ : (a : Fin (n + 1)) = a.cast_succ := by
  ext
  exact coe_val_of_lt (Nat.lt.step a.is_lt)

@[simp]
theorem coe_succ_eq_succ : a.cast_succ + 1 = a.succ := by
  cases n
  · exact finZeroElim a
    
  · simp [a.is_lt, eq_iff_veq, add_def, Nat.mod_eq_of_lt]
    

theorem lt_succ : a.cast_succ < a.succ := by
  rw [cast_succ, lt_iff_coe_lt_coe, coe_cast_add, coe_succ]
  exact lt_add_one a.val

@[simp]
theorem range_cast_succ {n : ℕ} : Set.Range (castSucc : Fin n → Fin n.succ) = { i | (i : ℕ) < n } :=
  range_cast_le _

@[simp]
theorem coe_of_injective_cast_succ_symm {n : ℕ} (i : Fin n.succ) (hi) :
    ((Equiv.ofInjective castSucc (cast_succ_injective _)).symm ⟨i, hi⟩ : ℕ) = i := by
  rw [← coe_cast_succ]
  exact congr_arg coe (Equiv.apply_of_injective_symm _ _)

theorem succ_cast_succ {n : ℕ} (i : Fin n) : i.cast_succ.succ = i.succ.cast_succ :=
  Fin.ext (by simp)

/-- `add_nat m i` adds `m` to `i`, generalizes `fin.succ`. -/
def addNat (m) : Fin n ↪o Fin (n + m) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨(i : ℕ) + m, add_lt_add_right i.2 _⟩) fun i j h =>
    lt_iff_coe_lt_coe.2 <| add_lt_add_right h _

@[simp]
theorem coe_add_nat (m : ℕ) (i : Fin n) : (addNat m i : ℕ) = i + m :=
  rfl

@[simp]
theorem add_nat_one {i : Fin n} : addNat 1 i = i.succ := by
  ext
  rw [coe_add_nat, coe_succ]

theorem le_coe_add_nat (m : ℕ) (i : Fin n) : m ≤ addNat m i :=
  Nat.le_add_left _ _

@[simp]
theorem add_nat_mk (n i : ℕ) (hi : i < m) : addNat n ⟨i, hi⟩ = ⟨i + n, add_lt_add_right hi n⟩ :=
  rfl

@[simp]
theorem cast_add_nat_zero {n n' : ℕ} (i : Fin n) (h : n + 0 = n') :
    cast h (addNat 0 i) = cast ((add_zero _).symm.trans h) i :=
  ext <| add_zero _

/-- For rewriting in the reverse direction, see `fin.cast_add_nat_left`. -/
theorem add_nat_cast {n n' m : ℕ} (i : Fin n') (h : n' = n) : addNat m (cast h i) = cast (congr_arg _ h) (addNat m i) :=
  ext rfl

theorem cast_add_nat_left {n n' m : ℕ} (i : Fin n') (h : n' + m = n + m) :
    cast h (addNat m i) = addNat m (cast (add_right_cancel h) i) :=
  ext rfl

@[simp]
theorem cast_add_nat_right {n m m' : ℕ} (i : Fin n) (h : n + m' = n + m) : cast h (addNat m' i) = addNat m i :=
  ext <| (congr_arg ((· + ·) (i : ℕ)) (add_left_cancel h) : _)

/-- `nat_add n i` adds `n` to `i` "on the left". -/
def natAdd (n) {m} : Fin m ↪o Fin (n + m) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨n + (i : ℕ), add_lt_add_left i.2 _⟩) fun i j h =>
    lt_iff_coe_lt_coe.2 <| add_lt_add_left h _

@[simp]
theorem coe_nat_add (n : ℕ) {m : ℕ} (i : Fin m) : (natAdd n i : ℕ) = n + i :=
  rfl

@[simp]
theorem nat_add_mk (n i : ℕ) (hi : i < m) : natAdd n ⟨i, hi⟩ = ⟨n + i, add_lt_add_left hi n⟩ :=
  rfl

theorem le_coe_nat_add (m : ℕ) (i : Fin n) : m ≤ natAdd m i :=
  Nat.le_add_right _ _

theorem nat_add_zero {n : ℕ} : Fin.natAdd 0 = (Fin.cast (zero_add n).symm).toRelEmbedding := by
  ext
  apply zero_add

/-- For rewriting in the reverse direction, see `fin.cast_nat_add_right`. -/
theorem nat_add_cast {n n' : ℕ} (m : ℕ) (i : Fin n') (h : n' = n) :
    natAdd m (cast h i) = cast (congr_arg _ h) (natAdd m i) :=
  ext rfl

theorem cast_nat_add_right {n n' m : ℕ} (i : Fin n') (h : m + n' = m + n) :
    cast h (natAdd m i) = natAdd m (cast (add_left_cancel h) i) :=
  ext rfl

@[simp]
theorem cast_nat_add_left {n m m' : ℕ} (i : Fin n) (h : m' + n = m + n) : cast h (natAdd m' i) = natAdd m i :=
  ext <| (congr_arg (· + (i : ℕ)) (add_right_cancel h) : _)

@[simp]
theorem cast_nat_add_zero {n n' : ℕ} (i : Fin n) (h : 0 + n = n') :
    cast h (natAdd 0 i) = cast ((zero_add _).symm.trans h) i :=
  ext <| zero_add _

@[simp]
theorem cast_nat_add (n : ℕ) {m : ℕ} (i : Fin m) : cast (add_comm _ _) (natAdd n i) = addNat n i :=
  ext <| add_comm _ _

@[simp]
theorem cast_add_nat {n : ℕ} (m : ℕ) (i : Fin n) : cast (add_comm _ _) (addNat m i) = natAdd m i :=
  ext <| add_comm _ _

@[simp]
theorem nat_add_last {m n : ℕ} : natAdd n (last m) = last (n + m) :=
  rfl

theorem nat_add_cast_succ {m n : ℕ} {i : Fin m} : natAdd n (castSucc i) = castSucc (natAdd n i) :=
  rfl

end Succ

section Pred

/-!
### pred
-/


@[simp]
theorem coe_pred (j : Fin (n + 1)) (h : j ≠ 0) : (j.pred h : ℕ) = j - 1 := by
  cases j
  rfl

@[simp]
theorem succ_pred : ∀ (i : Fin (n + 1)) (h : i ≠ 0), (i.pred h).succ = i
  | ⟨0, h⟩, hi => by contradiction
  | ⟨n + 1, h⟩, hi => rfl

@[simp]
theorem pred_succ (i : Fin n) {h : i.succ ≠ 0} : i.succ.pred h = i := by
  cases i
  rfl

@[simp]
theorem pred_mk_succ (i : ℕ) (h : i < n + 1) :
    Fin.pred ⟨i + 1, add_lt_add_right h 1⟩ (ne_of_vne (ne_of_gt (mk_succ_pos i h))) = ⟨i, h⟩ := by
  simp only [ext_iff, coe_pred, coe_mk, add_tsub_cancel_right]

-- This is not a simp lemma by default, because `pred_mk_succ` is nicer when it applies.
theorem pred_mk {n : ℕ} (i : ℕ) (h : i < n + 1) (w) :
    Fin.pred ⟨i, h⟩ w =
      ⟨i - 1, by rwa [tsub_lt_iff_right (Nat.succ_le_of_lt <| Nat.pos_of_ne_zero (Fin.vne_of_ne w))]⟩ :=
  rfl

@[simp]
theorem pred_le_pred_iff {n : ℕ} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} : a.pred ha ≤ b.pred hb ↔ a ≤ b := by
  rw [← succ_le_succ_iff, succ_pred, succ_pred]

@[simp]
theorem pred_lt_pred_iff {n : ℕ} {a b : Fin n.succ} {ha : a ≠ 0} {hb : b ≠ 0} : a.pred ha < b.pred hb ↔ a < b := by
  rw [← succ_lt_succ_iff, succ_pred, succ_pred]

@[simp]
theorem pred_inj : ∀ {a b : Fin (n + 1)} {ha : a ≠ 0} {hb : b ≠ 0}, a.pred ha = b.pred hb ↔ a = b
  | ⟨0, _⟩, b, ha, hb => by contradiction
  | ⟨i + 1, _⟩, ⟨0, _⟩, ha, hb => by contradiction
  | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, ha, hb => by simp [Fin.eq_iff_veq]

@[simp]
theorem pred_one {n : ℕ} : Fin.pred (1 : Fin (n + 2)) (Ne.symm (ne_of_lt one_pos)) = 0 :=
  rfl

theorem pred_add_one (i : Fin (n + 2)) (h : (i : ℕ) < n + 1) :
    pred (i + 1) (ne_of_gt (add_one_pos _ (lt_iff_coe_lt_coe.mpr h))) = castLt i h := by
  rw [ext_iff, coe_pred, coe_cast_lt, coe_add, coe_one, mod_eq_of_lt, add_tsub_cancel_right]
  exact add_lt_add_right h 1

/-- `sub_nat i h` subtracts `m` from `i`, generalizes `fin.pred`. -/
def subNat (m) (i : Fin (n + m)) (h : m ≤ (i : ℕ)) : Fin n :=
  ⟨(i : ℕ) - m, by
    rw [tsub_lt_iff_right h]
    exact i.is_lt⟩

@[simp]
theorem coe_sub_nat (i : Fin (n + m)) (h : m ≤ i) : (i.subNat m h : ℕ) = i - m :=
  rfl

@[simp]
theorem sub_nat_mk {i : ℕ} (h₁ : i < n + m) (h₂ : m ≤ i) : subNat m ⟨i, h₁⟩ h₂ = ⟨i - m, (tsub_lt_iff_right h₂).2 h₁⟩ :=
  rfl

@[simp]
theorem pred_cast_succ_succ (i : Fin n) : pred (castSucc i.succ) (ne_of_gt (cast_succ_pos i.succ_pos)) = i.cast_succ :=
  by simp [eq_iff_veq]

@[simp]
theorem add_nat_sub_nat {i : Fin (n + m)} (h : m ≤ i) : addNat m (subNat m i h) = i :=
  ext <| tsub_add_cancel_of_le h

@[simp]
theorem sub_nat_add_nat (i : Fin n) (m : ℕ) (h : m ≤ addNat m i := le_coe_add_nat m i) : subNat m (addNat m i) h = i :=
  ext <| add_tsub_cancel_right i m

@[simp]
theorem nat_add_sub_nat_cast {i : Fin (n + m)} (h : n ≤ i) : natAdd n (subNat n (cast (add_comm _ _) i) h) = i := by
  simp [← cast_add_nat]

end Pred

section DivMod

/-- Compute `i / n`, where `n` is a `nat` and inferred the type of `i`. -/
def divNat (i : Fin (m * n)) : Fin m :=
  ⟨i / n, Nat.div_lt_of_lt_mul <| mul_comm m n ▸ i.Prop⟩

@[simp]
theorem coe_div_nat (i : Fin (m * n)) : (i.divNat : ℕ) = i / n :=
  rfl

/-- Compute `i % n`, where `n` is a `nat` and inferred the type of `i`. -/
def modNat (i : Fin (m * n)) : Fin n :=
  ⟨i % n, Nat.mod_lt _ <| pos_of_mul_pos_right i.Pos m.zero_le⟩

@[simp]
theorem coe_mod_nat (i : Fin (m * n)) : (i.modNat : ℕ) = i % n :=
  rfl

end DivMod

section Rec

/-!
### recursion and induction principles
-/


/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple. -/
@[elab_as_elim]
def succRec {C : ∀ n, Fin n → Sort _} (H0 : ∀ n, C (succ n) 0) (Hs : ∀ n i, C n i → C (succ n) i.succ) :
    ∀ {n : ℕ} (i : Fin n), C n i
  | 0, i => i.elim0
  | succ n, ⟨0, _⟩ => H0 _
  | succ n, ⟨succ i, h⟩ => Hs _ _ (succ_rec ⟨i, lt_of_succ_lt_succ h⟩)

/-- Define `C n i` by induction on `i : fin n` interpreted as `(0 : fin (n - i)).succ.succ…`.
This function has two arguments: `H0 n` defines `0`-th element `C (n+1) 0` of an `(n+1)`-tuple,
and `Hs n i` defines `(i+1)`-st element of `(n+1)`-tuple based on `n`, `i`, and `i`-th element
of `n`-tuple.

A version of `fin.succ_rec` taking `i : fin n` as the first argument. -/
@[elab_as_elim]
def succRecOn {n : ℕ} (i : Fin n) {C : ∀ n, Fin n → Sort _} (H0 : ∀ n, C (succ n) 0)
    (Hs : ∀ n i, C n i → C (succ n) i.succ) : C n i :=
  i.succRec H0 Hs

@[simp]
theorem succ_rec_on_zero {C : ∀ n, Fin n → Sort _} {H0 Hs} (n) : @Fin.succRecOn (succ n) 0 C H0 Hs = H0 n :=
  rfl

@[simp]
theorem succ_rec_on_succ {C : ∀ n, Fin n → Sort _} {H0 Hs} {n} (i : Fin n) :
    @Fin.succRecOn (succ n) i.succ C H0 Hs = Hs n i (Fin.succRecOn i H0 Hs) := by cases i <;> rfl

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
    

@[simp]
theorem induction_zero {C : Fin (n + 1) → Sort _} (h0 : C 0) (hs : ∀ i : Fin n, C i.cast_succ → C i.succ) :
    (induction h0 hs : _) 0 = h0 :=
  rfl

@[simp]
theorem induction_succ {C : Fin (n + 1) → Sort _} (h0 : C 0) (hs : ∀ i : Fin n, C i.cast_succ → C i.succ) (i : Fin n) :
    (induction h0 hs : _) i.succ = hs i (induction h0 hs i.cast_succ) := by cases i <;> rfl

/-- Define `C i` by induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
This function has two arguments: `h0` handles the base case on `C 0`,
and `hs` defines the inductive step using `C i.cast_succ`.

A version of `fin.induction` taking `i : fin (n + 1)` as the first argument.
-/
@[elab_as_elim]
def inductionOn (i : Fin (n + 1)) {C : Fin (n + 1) → Sort _} (h0 : C 0) (hs : ∀ i : Fin n, C i.cast_succ → C i.succ) :
    C i :=
  induction h0 hs i

/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = 0` and
`i = j.succ`, `j : fin n`. -/
@[elab_as_elim]
def cases {C : Fin (succ n) → Sort _} (H0 : C 0) (Hs : ∀ i : Fin n, C i.succ) : ∀ i : Fin (succ n), C i :=
  induction H0 fun i _ => Hs i

@[simp]
theorem cases_zero {n} {C : Fin (succ n) → Sort _} {H0 Hs} : @Fin.cases n C H0 Hs 0 = H0 :=
  rfl

@[simp]
theorem cases_succ {n} {C : Fin (succ n) → Sort _} {H0 Hs} (i : Fin n) : @Fin.cases n C H0 Hs i.succ = Hs i := by
  cases i <;> rfl

@[simp]
theorem cases_succ' {n} {C : Fin (succ n) → Sort _} {H0 Hs} {i : ℕ} (h : i + 1 < n + 1) :
    @Fin.cases n C H0 Hs ⟨i.succ, h⟩ = Hs ⟨i, lt_of_succ_lt_succ h⟩ := by cases i <;> rfl

theorem forall_fin_succ {P : Fin (n + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin n, P i.succ :=
  ⟨fun H => ⟨H 0, fun i => H _⟩, fun ⟨H0, H1⟩ i => Fin.cases H0 H1 i⟩

theorem exists_fin_succ {P : Fin (n + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin n, P i.succ :=
  ⟨fun ⟨i, h⟩ => Fin.cases Or.inl (fun i hi => Or.inr ⟨i, hi⟩) i h, fun h =>
    (h.elim fun h => ⟨0, h⟩) fun ⟨i, hi⟩ => ⟨i.succ, hi⟩⟩

theorem forall_fin_one {p : Fin 1 → Prop} : (∀ i, p i) ↔ p 0 :=
  @Unique.forall_iff (Fin 1) _ p

theorem exists_fin_one {p : Fin 1 → Prop} : (∃ i, p i) ↔ p 0 :=
  @Unique.exists_iff (Fin 1) _ p

theorem forall_fin_two {p : Fin 2 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 :=
  forall_fin_succ.trans <| and_congr_right fun _ => forall_fin_one

theorem exists_fin_two {p : Fin 2 → Prop} : (∃ i, p i) ↔ p 0 ∨ p 1 :=
  exists_fin_succ.trans <| or_congr_right' exists_fin_one

theorem fin_two_eq_of_eq_zero_iff {a b : Fin 2} (h : a = 0 ↔ b = 0) : a = b := by
  revert a b
  simp [forall_fin_two]

/-- Define `C i` by reverse induction on `i : fin (n + 1)` via induction on the underlying `nat` value.
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
      have hi : i = Fin.castSucc j := Fin.ext rfl
      cast (by rw [hi]) (hs _ (reverse_induction j.succ))

@[simp]
theorem reverse_induction_last {n : ℕ} {C : Fin (n + 1) → Sort _} (h0 : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C i.cast_succ) : (reverseInduction h0 hs (Fin.last n) : C (Fin.last n)) = h0 := by
  rw [reverse_induction] <;> simp

@[simp]
theorem reverse_induction_cast_succ {n : ℕ} {C : Fin (n + 1) → Sort _} (h0 : C (Fin.last n))
    (hs : ∀ i : Fin n, C i.succ → C i.cast_succ) (i : Fin n) :
    (reverseInduction h0 hs i.cast_succ : C i.cast_succ) = hs i (reverseInduction h0 hs i.succ) := by
  rw [reverse_induction, dif_neg (ne_of_lt (Fin.cast_succ_lt_last i))]
  cases i
  rfl

/-- Define `f : Π i : fin n.succ, C i` by separately handling the cases `i = fin.last n` and
`i = j.cast_succ`, `j : fin n`. -/
@[elab_as_elim, elab_strategy]
def lastCases {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n)) (hcast : ∀ i : Fin n, C i.cast_succ)
    (i : Fin (n + 1)) : C i :=
  reverseInduction hlast (fun i _ => hcast i) i

@[simp]
theorem last_cases_last {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C i.cast_succ) : (Fin.lastCases hlast hcast (Fin.last n) : C (Fin.last n)) = hlast :=
  reverse_induction_last _ _

@[simp]
theorem last_cases_cast_succ {n : ℕ} {C : Fin (n + 1) → Sort _} (hlast : C (Fin.last n))
    (hcast : ∀ i : Fin n, C i.cast_succ) (i : Fin n) :
    (Fin.lastCases hlast hcast (Fin.castSucc i) : C (Fin.castSucc i)) = hcast i :=
  reverse_induction_cast_succ _ _ _

/-- Define `f : Π i : fin (m + n), C i` by separately handling the cases `i = cast_add n i`,
`j : fin m` and `i = nat_add m j`, `j : fin n`. -/
@[elab_as_elim, elab_strategy]
def addCases {m n : ℕ} {C : Fin (m + n) → Sort u} (hleft : ∀ i, C (castAdd n i)) (hright : ∀ i, C (natAdd m i))
    (i : Fin (m + n)) : C i :=
  if hi : (i : ℕ) < m then Eq.recOn (cast_add_cast_lt n i hi) (hleft (castLt i hi))
  else Eq.recOn (nat_add_sub_nat_cast (le_of_not_lt hi)) (hright _)

@[simp]
theorem add_cases_left {m n : ℕ} {C : Fin (m + n) → Sort _} (hleft : ∀ i, C (castAdd n i))
    (hright : ∀ i, C (natAdd m i)) (i : Fin m) : addCases hleft hright (Fin.castAdd n i) = hleft i := by
  cases' i with i hi
  rw [add_cases, dif_pos (cast_add_lt _ _)]
  rfl

@[simp]
theorem add_cases_right {m n : ℕ} {C : Fin (m + n) → Sort _} (hleft : ∀ i, C (castAdd n i))
    (hright : ∀ i, C (natAdd m i)) (i : Fin n) : addCases hleft hright (natAdd m i) = hright i := by
  have : ¬(nat_add m i : ℕ) < m := (le_coe_nat_add _ _).not_lt
  rw [add_cases, dif_neg this]
  refine' eq_of_heq ((eq_rec_heq _ _).trans _)
  congr 1
  simp

end Rec

theorem lift_fun_iff_succ {α : Type _} (r : α → α → Prop) [IsTrans α r] {f : Fin (n + 1) → α} :
    ((· < ·) ⇒ r) f f ↔ ∀ i : Fin n, r (f i.cast_succ) (f i.succ) := by
  constructor
  · intro H i
    exact H i.cast_succ_lt_succ
    
  · refine' fun H i => Fin.induction _ _
    · exact fun h => (h.not_le (zero_le i)).elim
      
    · intro j ihj hij
      rw [← le_cast_succ_iff] at hij
      rcases hij.eq_or_lt with (rfl | hlt)
      exacts[H j, trans (ihj hlt) (H j)]
      
    

/-- A function `f` on `fin (n + 1)` is strictly monotone if and only if `f i < f (i + 1)`
for all `i`. -/
theorem strict_mono_iff_lt_succ {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    StrictMono f ↔ ∀ i : Fin n, f i.cast_succ < f i.succ :=
  lift_fun_iff_succ (· < ·)

/-- A function `f` on `fin (n + 1)` is monotone if and only if `f i ≤ f (i + 1)` for all `i`. -/
theorem monotone_iff_le_succ {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    Monotone f ↔ ∀ i : Fin n, f i.cast_succ ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| lift_fun_iff_succ (· ≤ ·)

/-- A function `f` on `fin (n + 1)` is strictly antitone if and only if `f (i + 1) < f i`
for all `i`. -/
theorem strict_anti_iff_succ_lt {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    StrictAnti f ↔ ∀ i : Fin n, f i.succ < f i.cast_succ :=
  lift_fun_iff_succ (· > ·)

/-- A function `f` on `fin (n + 1)` is antitone if and only if `f (i + 1) ≤ f i` for all `i`. -/
theorem antitone_iff_succ_le {α : Type _} [Preorder α] {f : Fin (n + 1) → α} :
    Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f i.cast_succ :=
  antitone_iff_forall_lt.trans <| lift_fun_iff_succ (· ≥ ·)

section AddGroup

open Nat Int

/-- Negation on `fin n` -/
instance (n : ℕ) : Neg (Fin n) :=
  ⟨fun a => ⟨(n - a) % n, Nat.mod_lt _ a.Pos⟩⟩

/-- Abelian group structure on `fin (n+1)`. -/
instance (n : ℕ) : AddCommGroup (Fin (n + 1)) :=
  { Fin.addCommMonoid n, Fin.hasNeg n.succ with
    add_left_neg := fun ⟨a, ha⟩ =>
      Fin.ext <|
        trans (Nat.mod_add_mod _ _ _) <| by
          rw [Fin.coe_mk, Fin.coe_zero, tsub_add_cancel_of_le, Nat.mod_self]
          exact le_of_lt ha,
    sub_eq_add_neg := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
      Fin.ext <| show (a + (n + 1 - b)) % (n + 1) = (a + (n + 1 - b) % (n + 1)) % (n + 1) by simp,
    sub := Fin.sub }

protected theorem coe_neg (a : Fin n) : ((-a : Fin n) : ℕ) = (n - a) % n :=
  rfl

protected theorem coe_sub (a b : Fin n) : ((a - b : Fin n) : ℕ) = (a + (n - b)) % n := by cases a <;> cases b <;> rfl

@[simp]
theorem coe_fin_one (a : Fin 1) : ↑a = 0 := by rw [Subsingleton.elim a 0, Fin.coe_zero]

@[simp]
theorem coe_neg_one : ↑(-1 : Fin (n + 1)) = n := by
  cases n
  · simp
    
  rw [Fin.coe_neg, Fin.coe_one, Nat.succ_sub_one, Nat.mod_eq_of_lt]
  constructor

theorem coe_sub_one {n} (a : Fin (n + 1)) : ↑(a - 1) = if a = 0 then n else a - 1 := by
  cases n
  · simp
    
  split_ifs
  · simp [h]
    
  rw [sub_eq_add_neg, coe_add_eq_ite, coe_neg_one, if_pos, add_comm, add_tsub_add_eq_tsub_left]
  rw [add_comm ↑a, add_le_add_iff_left, Nat.one_le_iff_ne_zero]
  rwa [Fin.ext_iff] at h

theorem coe_sub_iff_le {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = a - b ↔ b ≤ a := by
  cases n
  · exact finZeroElim a
    
  rw [le_iff_coe_le_coe, Fin.coe_sub, ← add_tsub_assoc_of_le b.is_lt.le a]
  cases' le_or_lt (b : ℕ) a with h h
  · simp [← tsub_add_eq_add_tsub h, h, Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt a.is_lt)]
    
  · rw [Nat.mod_eq_of_lt, tsub_eq_zero_of_le h.le, tsub_eq_zero_iff_le, ← not_iff_not]
    · simpa [b.is_lt.trans_le le_add_self] using h
      
    · rwa [tsub_lt_iff_left (b.is_lt.le.trans le_add_self), add_lt_add_iff_right]
      
    

theorem coe_sub_iff_lt {n : ℕ} {a b : Fin n} : (↑(a - b) : ℕ) = n + a - b ↔ a < b := by
  cases n
  · exact finZeroElim a
    
  rw [lt_iff_coe_lt_coe, Fin.coe_sub, add_comm]
  cases' le_or_lt (b : ℕ) a with h h
  · simpa [add_tsub_assoc_of_le h, ← not_le, h] using ((Nat.mod_lt _ (Nat.succ_pos _)).trans_le le_self_add).Ne
    
  · simp [← tsub_tsub_assoc b.is_lt.le h.le, ← tsub_add_eq_add_tsub b.is_lt.le,
      Nat.mod_eq_of_lt (tsub_lt_self (Nat.succ_pos _) (tsub_pos_of_lt h)), h]
    

@[simp]
theorem lt_sub_one_iff {n : ℕ} {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  rcases k with ⟨_ | k, hk⟩
  simp [lt_iff_coe_lt_coe]
  have : (k + 1 + (n + 1)) % (n + 2) = k % (n + 2) := by rw [add_right_comm, add_assoc, add_mod_right]
  simp [lt_iff_coe_lt_coe, ext_iff, Fin.coe_sub, succ_eq_add_one, this, mod_eq_of_lt ((lt_succ_self _).trans hk)]

@[simp]
theorem le_sub_one_iff {n : ℕ} {k : Fin (n + 1)} : k ≤ k - 1 ↔ k = 0 := by
  cases n
  · simp [Subsingleton.elim (k - 1) k, Subsingleton.elim 0 k]
    
  rw [← lt_sub_one_iff, le_iff_lt_or_eq, lt_sub_one_iff, or_iff_left_iff_imp, eq_comm, sub_eq_iff_eq_add]
  simp

@[simp]
theorem sub_one_lt_iff {n : ℕ} {k : Fin (n + 1)} : k - 1 < k ↔ 0 < k :=
  not_iff_not.1 <| by simp only [not_lt, le_sub_one_iff, le_zero_iff]

theorem last_sub (i : Fin (n + 1)) : last n - i = i.rev :=
  ext <| by rw [coe_sub_iff_le.2 i.le_last, coe_last, coe_rev, Nat.succ_sub_succ_eq_sub]

end AddGroup

section SuccAbove

theorem succ_above_aux (p : Fin (n + 1)) :
    StrictMono fun i : Fin n => if i.cast_succ < p then i.cast_succ else i.succ :=
  (castSucc : Fin n ↪o _).StrictMono.ite (succEmbedding n).StrictMono
    (fun i j hij hj => lt_trans ((castSucc : Fin n ↪o _).lt_iff_lt.2 hij) hj) fun i => (cast_succ_lt_succ i).le

/-- `succ_above p i` embeds `fin n` into `fin (n + 1)` with a hole around `p`. -/
def succAbove (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono _ p.succ_above_aux

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `cast_succ` when the resulting `i.cast_succ < p`. -/
theorem succ_above_below (p : Fin (n + 1)) (i : Fin n) (h : i.cast_succ < p) : p.succAbove i = i.cast_succ := by
  rw [succ_above]
  exact if_pos h

@[simp]
theorem succ_above_ne_zero_zero {a : Fin (n + 2)} (ha : a ≠ 0) : a.succAbove 0 = 0 := by
  rw [Fin.succ_above_below]
  · rfl
    
  · exact bot_lt_iff_ne_bot.mpr ha
    

theorem succ_above_eq_zero_iff {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) : a.succAbove b = 0 ↔ b = 0 := by
  simp only [← succ_above_ne_zero_zero ha, OrderEmbedding.eq_iff_eq]

theorem succ_above_ne_zero {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0) : a.succAbove b ≠ 0 :=
  mt (succ_above_eq_zero_iff ha).mp hb

/-- Embedding `fin n` into `fin (n + 1)` with a hole around zero embeds by `succ`. -/
@[simp]
theorem succ_above_zero : ⇑(succAbove (0 : Fin (n + 1))) = Fin.succ :=
  rfl

/-- Embedding `fin n` into `fin (n + 1)` with a hole around `last n` embeds by `cast_succ`. -/
@[simp]
theorem succ_above_last : succAbove (Fin.last n) = cast_succ := by
  ext
  simp only [succ_above_below, cast_succ_lt_last]

theorem succ_above_last_apply (i : Fin n) : succAbove (Fin.last n) i = i.cast_succ := by rw [succ_above_last]

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
embeds `i` by `succ` when the resulting `p < i.succ`. -/
theorem succ_above_above (p : Fin (n + 1)) (i : Fin n) (h : p ≤ i.cast_succ) : p.succAbove i = i.succ := by
  simp [succ_above, h.not_lt]

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
theorem succ_above_lt_ge (p : Fin (n + 1)) (i : Fin n) : i.cast_succ < p ∨ p ≤ i.cast_succ :=
  lt_or_ge (castSucc i) p

/-- Embedding `i : fin n` into `fin (n + 1)` is always about some hole `p`. -/
theorem succ_above_lt_gt (p : Fin (n + 1)) (i : Fin n) : i.cast_succ < p ∨ p < i.succ :=
  Or.cases_on (succ_above_lt_ge p i) (fun h => Or.inl h) fun h => Or.inr (lt_of_le_of_lt h (cast_succ_lt_succ i))

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is greater
results in a value that is less than `p`. -/
@[simp]
theorem succ_above_lt_iff (p : Fin (n + 1)) (i : Fin n) : p.succAbove i < p ↔ i.cast_succ < p := by
  refine' Iff.intro _ _
  · intro h
    cases' succ_above_lt_ge p i with H H
    · exact H
      
    · rw [succ_above_above _ _ H] at h
      exact lt_trans (cast_succ_lt_succ i) h
      
    
  · intro h
    rw [succ_above_below _ _ h]
    exact h
    

/-- Embedding `i : fin n` into `fin (n + 1)` using a pivot `p` that is lesser
results in a value that is greater than `p`. -/
theorem lt_succ_above_iff (p : Fin (n + 1)) (i : Fin n) : p < p.succAbove i ↔ p ≤ i.cast_succ := by
  refine' Iff.intro _ _
  · intro h
    cases' succ_above_lt_ge p i with H H
    · rw [succ_above_below _ _ H] at h
      exact le_of_lt h
      
    · exact H
      
    
  · intro h
    rw [succ_above_above _ _ h]
    exact lt_of_le_of_lt h (cast_succ_lt_succ i)
    

/-- Embedding `i : fin n` into `fin (n + 1)` with a hole around `p : fin (n + 1)`
never results in `p` itself -/
theorem succ_above_ne (p : Fin (n + 1)) (i : Fin n) : p.succAbove i ≠ p := by
  intro eq
  by_cases H:i.cast_succ < p
  · simpa [lt_irrefl, ← succ_above_below _ _ H, Eq] using H
    
  · simpa [← succ_above_above _ _ (le_of_not_lt H), Eq] using cast_succ_lt_succ i
    

/-- Embedding a positive `fin n` results in a positive fin (n + 1)` -/
theorem succ_above_pos (p : Fin (n + 2)) (i : Fin (n + 1)) (h : 0 < i) : 0 < p.succAbove i := by
  by_cases H:i.cast_succ < p
  · simpa [succ_above_below _ _ H] using cast_succ_pos h
    
  · simp [succ_above_above _ _ (le_of_not_lt H)]
    

@[simp]
theorem succ_above_cast_lt {x y : Fin (n + 1)} (h : x < y) (hx : x.1 < n := lt_of_lt_of_le h y.le_last) :
    y.succAbove (x.cast_lt hx) = x := by
  rw [succ_above_below, cast_succ_cast_lt]
  exact h

@[simp]
theorem succ_above_pred {x y : Fin (n + 1)} (h : x < y) (hy : y ≠ 0 := (x.zero_le.trans_lt h).ne') :
    x.succAbove (y.pred hy) = y := by
  rw [succ_above_above, succ_pred]
  simpa [le_iff_coe_le_coe] using Nat.le_pred_of_lt h

theorem cast_lt_succ_above {x : Fin n} {y : Fin (n + 1)} (h : castSucc x < y)
    (h' : (y.succAbove x).1 < n := lt_of_lt_of_le ((succ_above_lt_iff _ _).2 h) (le_last y)) :
    (y.succAbove x).cast_lt h' = x := by simp only [succ_above_below _ _ h, cast_lt_cast_succ]

theorem pred_succ_above {x : Fin n} {y : Fin (n + 1)} (h : y ≤ castSucc x)
    (h' : y.succAbove x ≠ 0 := (y.zero_le.trans_lt <| (lt_succ_above_iff _ _).2 h).ne') : (y.succAbove x).pred h' = x :=
  by simp only [succ_above_above _ _ h, pred_succ]

theorem exists_succ_above_eq {x y : Fin (n + 1)} (h : x ≠ y) : ∃ z, y.succAbove z = x := by
  cases' h.lt_or_lt with hlt hlt
  exacts[⟨_, succ_above_cast_lt hlt⟩, ⟨_, succ_above_pred hlt⟩]

@[simp]
theorem exists_succ_above_eq_iff {x y : Fin (n + 1)} : (∃ z, x.succAbove z = y) ↔ y ≠ x := by
  refine' ⟨_, exists_succ_above_eq⟩
  rintro ⟨y, rfl⟩
  exact succ_above_ne _ _

/-- The range of `p.succ_above` is everything except `p`. -/
@[simp]
theorem range_succ_above (p : Fin (n + 1)) : Set.Range p.succAbove = {p}ᶜ :=
  Set.ext fun _ => exists_succ_above_eq_iff

@[simp]
theorem range_succ (n : ℕ) : Set.Range (Fin.succ : Fin n → Fin (n + 1)) = {0}ᶜ :=
  range_succ_above 0

@[simp]
theorem exists_succ_eq_iff {x : Fin (n + 1)} : (∃ y, Fin.succ y = x) ↔ x ≠ 0 :=
  @exists_succ_above_eq_iff n 0 x

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
theorem succ_above_right_injective {x : Fin (n + 1)} : Injective (succAbove x) :=
  (succAbove x).Injective

/-- Given a fixed pivot `x : fin (n + 1)`, `x.succ_above` is injective -/
theorem succ_above_right_inj {x : Fin (n + 1)} : x.succAbove a = x.succAbove b ↔ a = b :=
  succ_above_right_injective.eq_iff

/-- `succ_above` is injective at the pivot -/
theorem succ_above_left_injective : Injective (@succAbove n) := fun _ _ h => by
  simpa [range_succ_above] using congr_arg (fun f : Fin n ↪o Fin (n + 1) => Set.Range fᶜ) h

/-- `succ_above` is injective at the pivot -/
@[simp]
theorem succ_above_left_inj {x y : Fin (n + 1)} : x.succAbove = y.succAbove ↔ x = y :=
  succ_above_left_injective.eq_iff

@[simp]
theorem zero_succ_above {n : ℕ} (i : Fin n) : (0 : Fin (n + 1)).succAbove i = i.succ :=
  rfl

@[simp]
theorem succ_succ_above_zero {n : ℕ} (i : Fin (n + 1)) : i.succ.succAbove 0 = 0 :=
  succ_above_below _ _ (succ_pos _)

@[simp]
theorem succ_succ_above_succ {n : ℕ} (i : Fin (n + 1)) (j : Fin n) : i.succ.succAbove j.succ = (i.succAbove j).succ :=
  (lt_or_ge j.cast_succ i).elim
    (fun h => by
      have h' : j.succ.cast_succ < i.succ := by simpa [lt_iff_coe_lt_coe] using h
      ext
      simp [succ_above_below _ _ h, succ_above_below _ _ h'])
    fun h => by
    have h' : i.succ ≤ j.succ.cast_succ := by simpa [le_iff_coe_le_coe] using h
    ext
    simp [succ_above_above _ _ h, succ_above_above _ _ h']

@[simp]
theorem one_succ_above_zero {n : ℕ} : (1 : Fin (n + 2)).succAbove 0 = 0 :=
  succ_succ_above_zero 0

/-- By moving `succ` to the outside of this expression, we create opportunities for further
simplification using `succ_above_zero` or `succ_succ_above_zero`. -/
@[simp]
theorem succ_succ_above_one {n : ℕ} (i : Fin (n + 2)) : i.succ.succAbove 1 = (i.succAbove 0).succ :=
  succ_succ_above_succ i 0

@[simp]
theorem one_succ_above_succ {n : ℕ} (j : Fin n) : (1 : Fin (n + 2)).succAbove j.succ = j.succ.succ :=
  succ_succ_above_succ 0 j

@[simp]
theorem one_succ_above_one {n : ℕ} : (1 : Fin (n + 3)).succAbove 1 = 2 :=
  succ_succ_above_succ 0 0

end SuccAbove

section PredAbove

/-- `pred_above p i` embeds `i : fin (n+1)` into `fin n` by subtracting one if `p < i`. -/
def predAbove (p : Fin n) (i : Fin (n + 1)) : Fin n :=
  if h : p.cast_succ < i then i.pred (ne_of_lt (lt_of_le_of_lt (zero_le p.cast_succ) h)).symm
  else i.cast_lt (lt_of_le_of_lt (le_of_not_lt h) p.2)

theorem pred_above_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [pred_above]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_coe_le_coe, coe_pred]
  · exact pred_le_pred H
    
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
      
    
  · simp at ha
    exact le_pred_of_lt (lt_of_le_of_lt ha hb)
    
  · exact H
    

theorem pred_above_left_monotone (i : Fin (n + 1)) : Monotone fun p => predAbove p i := fun a b H => by
  dsimp [pred_above]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_coe_le_coe, coe_pred]
  · exact pred_le _
    
  · have : b < a := cast_succ_lt_cast_succ_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_le
    

/-- `cast_pred` embeds `i : fin (n + 2)` into `fin (n + 1)`
by lowering just `last (n + 1)` to `last n`. -/
def castPred (i : Fin (n + 2)) : Fin (n + 1) :=
  predAbove (last n) i

@[simp]
theorem cast_pred_zero : castPred (0 : Fin (n + 2)) = 0 :=
  rfl

@[simp]
theorem cast_pred_one : castPred (1 : Fin (n + 2)) = 1 := by
  cases n
  apply Subsingleton.elim
  rfl

@[simp]
theorem pred_above_zero {i : Fin (n + 2)} (hi : i ≠ 0) : predAbove 0 i = i.pred hi := by
  dsimp [pred_above]
  rw [dif_pos]
  exact (pos_iff_ne_zero _).mpr hi

@[simp]
theorem cast_pred_last : castPred (last (n + 1)) = last n :=
  eq_of_veq (by simp [cast_pred, pred_above, cast_succ_lt_last])

@[simp]
theorem cast_pred_mk (n i : ℕ) (h : i < n + 1) : castPred ⟨i, lt_succ_of_lt h⟩ = ⟨i, h⟩ := by
  have : ¬cast_succ (last n) < ⟨i, lt_succ_of_lt h⟩ := by simpa [lt_iff_coe_lt_coe] using le_of_lt_succ h
  simp [cast_pred, pred_above, this]

theorem coe_cast_pred {n : ℕ} (a : Fin (n + 2)) (hx : a < Fin.last _) : (a.cast_pred : ℕ) = a := by
  rcases a with ⟨a, ha⟩
  rw [cast_pred_mk]
  exacts[rfl, hx]

theorem pred_above_below (p : Fin (n + 1)) (i : Fin (n + 2)) (h : i ≤ p.cast_succ) : p.predAbove i = i.cast_pred := by
  have : i ≤ (last n).cast_succ := h.trans p.le_last
  simp [pred_above, cast_pred, h.not_lt, this.not_lt]

@[simp]
theorem pred_above_last : predAbove (Fin.last n) = cast_pred :=
  rfl

theorem pred_above_last_apply (i : Fin n) : predAbove (Fin.last n) i = i.cast_pred := by rw [pred_above_last]

theorem pred_above_above (p : Fin n) (i : Fin (n + 1)) (h : p.cast_succ < i) :
    p.predAbove i = i.pred (p.cast_succ.zero_le.trans_lt h).Ne.symm := by simp [pred_above, h]

theorem cast_pred_monotone : Monotone (@castPred n) :=
  pred_above_right_monotone (last _)

/-- Sending `fin (n+1)` to `fin n` by subtracting one from anything above `p`
then back to `fin (n+1)` with a gap around `p` is the identity away from `p`. -/
@[simp]
theorem succ_above_pred_above {p : Fin n} {i : Fin (n + 1)} (h : i ≠ p.cast_succ) :
    p.cast_succ.succAbove (p.predAbove i) = i := by
  dsimp [pred_above, succ_above]
  rcases p with ⟨p, _⟩
  rcases i with ⟨i, _⟩
  cases' lt_or_le i p with H H
  · rw [dif_neg]
    rw [if_pos]
    rfl
    exact H
    simp
    apply le_of_lt H
    
  · rw [dif_pos]
    rw [if_neg]
    pick_goal 3
    -- For some reason `simp` doesn't fire fully unless we discharge the third goal.
    · exact lt_of_le_of_ne H (Ne.symm h)
      
    · simp
      
    · simp only [Fin.mk_eq_mk, Ne.def, Fin.cast_succ_mk] at h
      simp only [pred, Fin.mk_lt_mk, not_lt]
      exact Nat.le_pred_of_lt (Nat.lt_of_le_and_ne H (Ne.symm h))
      
    

/-- Sending `fin n` into `fin (n + 1)` with a gap at `p`
then back to `fin n` by subtracting one from anything above `p` is the identity. -/
@[simp]
theorem pred_above_succ_above (p : Fin n) (i : Fin n) : p.predAbove (p.cast_succ.succAbove i) = i := by
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
      
    

theorem cast_succ_pred_eq_pred_cast_succ {a : Fin (n + 1)} (ha : a ≠ 0) (ha' := a.cast_succ_ne_zero_iff.mpr ha) :
    (a.pred ha).cast_succ = a.cast_succ.pred ha' := by
  cases a
  rfl

/-- `pred` commutes with `succ_above`. -/
theorem pred_succ_above_pred {a : Fin (n + 2)} {b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (hk := succ_above_ne_zero ha hb) : (a.pred ha).succAbove (b.pred hb) = (a.succAbove b).pred hk := by
  obtain hbelow | habove := lt_or_le b.cast_succ a
  -- `rwa` uses them
  · rw [Fin.succ_above_below]
    · rwa [cast_succ_pred_eq_pred_cast_succ, Fin.pred_inj, Fin.succ_above_below]
      
    · rwa [cast_succ_pred_eq_pred_cast_succ, pred_lt_pred_iff]
      
    
  · rw [Fin.succ_above_above]
    have : (b.pred hb).succ = b.succ.pred (Fin.succ_ne_zero _) := by rw [succ_pred, pred_succ]
    · rwa [this, Fin.pred_inj, Fin.succ_above_above]
      
    · rwa [cast_succ_pred_eq_pred_cast_succ, Fin.pred_le_pred_iff]
      
    

/-- `succ` commutes with `pred_above`. -/
@[simp]
theorem succ_pred_above_succ (a : Fin n) (b : Fin (n + 1)) : a.succ.predAbove b.succ = (a.predAbove b).succ := by
  obtain h₁ | h₂ := lt_or_le a.cast_succ b
  · rw [Fin.pred_above_above _ _ h₁, Fin.succ_pred, Fin.pred_above_above, Fin.pred_succ]
    simpa only [Fin.lt_iff_coe_lt_coe, Fin.coe_cast_succ, Fin.coe_succ, add_lt_add_iff_right] using h₁
    
  · cases n
    · exfalso
      exact not_lt_zero' a.is_lt
      
    · rw [Fin.pred_above_below a b h₂,
        Fin.pred_above_below a.succ b.succ
          (by simpa only [le_iff_coe_le_coe, coe_succ, coe_cast_succ, add_le_add_iff_right] using h₂)]
      ext
      have h₀ : (b : ℕ) < n + 1 := by
        simp only [le_iff_coe_le_coe, coe_cast_succ] at h₂
        simpa only [lt_succ_iff] using h₂.trans a.is_le
      have h₁ : (b.succ : ℕ) < n + 2 := by
        rw [← Nat.succ_lt_succ_iff] at h₀
        simpa only [coe_succ] using h₀
      simp only [coe_cast_pred b h₀, coe_cast_pred b.succ h₁, coe_succ]
      
    

@[simp]
theorem cast_pred_cast_succ (i : Fin (n + 1)) : castPred i.cast_succ = i := by simp [cast_pred, pred_above, le_last]

theorem cast_succ_cast_pred {i : Fin (n + 2)} (h : i < last _) : castSucc i.cast_pred = i := by
  rw [cast_pred, pred_above, dif_neg]
  · simp [Fin.eq_iff_veq]
    
  · exact h.not_le
    

theorem coe_cast_pred_le_self (i : Fin (n + 2)) : (i.cast_pred : ℕ) ≤ i := by
  rcases i.le_last.eq_or_lt with (rfl | h)
  · simp
    
  · rw [cast_pred, pred_above, dif_neg]
    · simp
      
    · simpa [lt_iff_coe_lt_coe, le_iff_coe_le_coe, lt_succ_iff] using h
      
    

theorem coe_cast_pred_lt_iff {i : Fin (n + 2)} : (i.cast_pred : ℕ) < i ↔ i = Fin.last _ := by
  rcases i.le_last.eq_or_lt with (rfl | H)
  · simp
    
  · simp only [ne_of_lt H]
    rw [← cast_succ_cast_pred H]
    simp
    

theorem lt_last_iff_coe_cast_pred {i : Fin (n + 2)} : i < Fin.last _ ↔ (i.cast_pred : ℕ) = i := by
  rcases i.le_last.eq_or_lt with (rfl | H)
  · simp
    
  · simp only [H]
    rw [← cast_succ_cast_pred H]
    simp
    

end PredAbove

/-- `min n m` as an element of `fin (m + 1)` -/
def clamp (n m : ℕ) : Fin (m + 1) :=
  of_nat <| min n m

@[simp]
theorem coe_clamp (n m : ℕ) : (clamp n m : ℕ) = min n m :=
  Nat.mod_eq_of_lt <| Nat.lt_succ_iff.mpr <| min_le_right _ _

@[simp]
theorem coe_of_nat_eq_mod (m n : ℕ) : ((n : Fin (succ m)) : ℕ) = n % succ m := by rw [← of_nat_eq_coe] <;> rfl

@[simp]
theorem coe_of_nat_eq_mod' (m n : ℕ) [I : NeZero m] : (@Fin.ofNat' _ I n : ℕ) = n % m :=
  rfl

section Mul

/-!
### mul
-/


theorem val_mul {n : ℕ} : ∀ a b : Fin n, (a * b).val = a.val * b.val % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

theorem coe_mul {n : ℕ} : ∀ a b : Fin n, ((a * b : Fin n) : ℕ) = a * b % n
  | ⟨_, _⟩, ⟨_, _⟩ => rfl

@[simp]
protected theorem mul_one (k : Fin (n + 1)) : k * 1 = k := by
  cases n
  simp
  simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)]

@[simp]
protected theorem one_mul (k : Fin (n + 1)) : (1 : Fin (n + 1)) * k = k := by
  cases n
  simp
  simp [eq_iff_veq, mul_def, mod_eq_of_lt (is_lt k)]

@[simp]
protected theorem mul_zero (k : Fin (n + 1)) : k * 0 = 0 := by simp [eq_iff_veq, mul_def]

@[simp]
protected theorem zero_mul (k : Fin (n + 1)) : (0 : Fin (n + 1)) * k = 0 := by simp [eq_iff_veq, mul_def]

end Mul

section

-- Note that here we are disabling the "safety" of reflected, to allow us to reuse `nat.mk_numeral`.
-- The usual way to provide the required `reflected` instance would be via rewriting to prove that
-- the expression we use here is equivalent.
attribute [local semireducible] reflected

unsafe instance reflect : ∀ n, has_reflect (Fin n)
  | 0 => finZeroElim
  | n + 1 =>
    nat.mk_numeral (quote.1 (Fin n.succ)) (quote.1 (by infer_instance : Zero (Fin n.succ)))
        (quote.1 (by infer_instance : One (Fin n.succ))) (quote.1 (by infer_instance : Add (Fin n.succ))) ∘
      Fin.val

end

end Fin

