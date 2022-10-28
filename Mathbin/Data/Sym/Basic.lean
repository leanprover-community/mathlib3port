/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Multiset.Basic
import Mathbin.Data.Vector.Basic
import Mathbin.Data.Setoid.Basic
import Mathbin.Tactic.ApplyFun

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `data.sym.sym2`.

TODO: This was created as supporting material for `sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/


open Function

/-- The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def Sym (α : Type _) (n : ℕ) :=
  { s : Multiset α // s.card = n }

instance Sym.hasCoe (α : Type _) (n : ℕ) : Coe (Sym α n) (Multiset α) :=
  coeSubtype

/-- This is the `list.perm` setoid lifted to `vector`.

See note [reducible non-instances].
-/
@[reducible]
def Vector.Perm.isSetoid (α : Type _) (n : ℕ) : Setoid (Vector α n) :=
  (List.isSetoid α).comap Subtype.val

attribute [local instance] Vector.Perm.isSetoid

namespace Sym

variable {α β : Type _} {n n' m : ℕ} {s : Sym α n} {a b : α}

theorem coe_injective : Injective (coe : Sym α n → Multiset α) :=
  Subtype.coe_injective

@[simp, norm_cast]
theorem coe_inj {s₁ s₂ : Sym α n} : (s₁ : Multiset α) = s₂ ↔ s₁ = s₂ :=
  coe_injective.eq_iff

/-- Construct an element of the `n`th symmetric power from a multiset of cardinality `n`.
-/
@[simps, match_pattern]
abbrev mk (m : Multiset α) (h : m.card = n) : Sym α n :=
  ⟨m, h⟩

/-- The unique element in `sym α 0`.
-/
@[match_pattern]
def nil : Sym α 0 :=
  ⟨0, Multiset.card_zero⟩

@[simp]
theorem coe_nil : coe (@Sym.nil α) = (0 : Multiset α) :=
  rfl

/-- Inserts an element into the term of `sym α n`, increasing the length by one.
-/
@[match_pattern]
def cons (a : α) (s : Sym α n) : Sym α n.succ :=
  ⟨a ::ₘ s.1, by rw [Multiset.card_cons, s.2]⟩

-- mathport name: «expr ::ₛ »
infixr:67 " ::ₛ " => cons

@[simp]
theorem cons_inj_right (a : α) (s s' : Sym α n) : a ::ₛ s = a ::ₛ s' ↔ s = s' :=
  Subtype.ext_iff.trans <| (Multiset.cons_inj_right _).trans Subtype.ext_iff.symm

@[simp]
theorem cons_inj_left (a a' : α) (s : Sym α n) : a ::ₛ s = a' ::ₛ s ↔ a = a' :=
  Subtype.ext_iff.trans <| Multiset.cons_inj_left _

theorem cons_swap (a b : α) (s : Sym α n) : a ::ₛ b ::ₛ s = b ::ₛ a ::ₛ s :=
  Subtype.ext <| Multiset.cons_swap a b s.1

theorem coe_cons (s : Sym α n) (a : α) : (a ::ₛ s : Multiset α) = a ::ₘ s :=
  rfl

/-- This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
instance : HasLift (Vector α n) (Sym α n) where lift x := ⟨↑x.val, (Multiset.coe_card _).trans x.2⟩

@[simp]
theorem of_vector_nil : ↑(Vector.nil : Vector α 0) = (Sym.nil : Sym α 0) :=
  rfl

@[simp]
theorem of_vector_cons (a : α) (v : Vector α n) : ↑(Vector.cons a v) = a ::ₛ (↑v : Sym α n) := by
  cases v
  rfl

/-- `α ∈ s` means that `a` appears as one of the factors in `s`.
-/
instance : Membership α (Sym α n) :=
  ⟨fun a s => a ∈ s.1⟩

instance decidableMem [DecidableEq α] (a : α) (s : Sym α n) : Decidable (a ∈ s) :=
  s.1.decidableMem _

@[simp]
theorem mem_mk (a : α) (s : Multiset α) (h : s.card = n) : a ∈ mk s h ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem mem_cons : a ∈ b ::ₛ s ↔ a = b ∨ a ∈ s :=
  Multiset.mem_cons

@[simp]
theorem mem_coe : a ∈ (s : Multiset α) ↔ a ∈ s :=
  Iff.rfl

theorem mem_cons_of_mem (h : a ∈ s) : a ∈ b ::ₛ s :=
  Multiset.mem_cons_of_mem h

@[simp]
theorem mem_cons_self (a : α) (s : Sym α n) : a ∈ a ::ₛ s :=
  Multiset.mem_cons_self a s.1

theorem cons_of_coe_eq (a : α) (v : Vector α n) : a ::ₛ (↑v : Sym α n) = ↑(a ::ᵥ v) :=
  Subtype.ext <| by
    cases v
    rfl

theorem sound {a b : Vector α n} (h : a.val ~ b.val) : (↑a : Sym α n) = ↑b :=
  Subtype.ext <| Quotient.sound h

/-- `erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if a is present in the sym. -/
def erase [DecidableEq α] (s : Sym α (n + 1)) (a : α) (h : a ∈ s) : Sym α n :=
  ⟨s.val.erase a, (Multiset.card_erase_of_mem h).trans <| s.property.symm ▸ n.pred_succ⟩

@[simp]
theorem erase_mk [DecidableEq α] (m : Multiset α) (hc : m.card = n + 1) (a : α) (h : a ∈ m) :
    (mk m hc).erase a h =
      mk (m.erase a)
        (by
          rw [Multiset.card_erase_of_mem h, hc]
          rfl) :=
  rfl

@[simp]
theorem coe_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a ∈ s) :
    (s.erase a h : Multiset α) = Multiset.erase s a :=
  rfl

@[simp]
theorem cons_erase [DecidableEq α] {s : Sym α n.succ} {a : α} (h : a ∈ s) : a ::ₛ s.erase a h = s :=
  coe_injective <| Multiset.cons_erase h

@[simp]
theorem erase_cons_head [DecidableEq α] (s : Sym α n) (a : α) (h : a ∈ a ::ₛ s := mem_cons_self a s) :
    (a ::ₛ s).erase a h = s :=
  coe_injective <| Multiset.erase_cons_head a s.1

/-- Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def Sym' (α : Type _) (n : ℕ) :=
  Quotient (Vector.Perm.isSetoid α n)

/-- This is `cons` but for the alternative `sym'` definition.
-/
def cons' {α : Type _} {n : ℕ} : α → Sym' α n → Sym' α (Nat.succ n) := fun a =>
  Quotient.map (Vector.cons a) fun ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h => List.Perm.cons _ h

-- mathport name: sym.cons'
notation a "::" b => cons' a b

/-- Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def symEquivSym' {α : Type _} {n : ℕ} : Sym α n ≃ Sym' α n :=
  Equiv.subtypeQuotientEquivQuotientSubtype _ _ (fun _ => by rfl) fun _ _ => by rfl

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem cons_equiv_eq_equiv_cons (α : Type _) (n : ℕ) (a : α) (s : Sym α n) :
    (a::symEquivSym' s) = symEquivSym' (a ::ₛ s) := by
  rcases s with ⟨⟨l⟩, _⟩
  rfl

instance : Zero (Sym α 0) :=
  ⟨⟨0, rfl⟩⟩

instance : EmptyCollection (Sym α 0) :=
  ⟨0⟩

theorem eq_nil_of_card_zero (s : Sym α 0) : s = nil :=
  Subtype.ext <| Multiset.card_eq_zero.1 s.2

instance uniqueZero : Unique (Sym α 0) :=
  ⟨⟨nil⟩, eq_nil_of_card_zero⟩

/-- `repeat a n` is the sym containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : Sym α n :=
  ⟨Multiset.repeat a n, Multiset.card_repeat _ _⟩

theorem repeat_succ {a : α} {n : ℕ} : repeat a n.succ = a ::ₛ repeat a n :=
  rfl

theorem coe_repeat : (repeat a n : Multiset α) = Multiset.repeat a n :=
  rfl

@[simp]
theorem mem_repeat : b ∈ repeat a n ↔ n ≠ 0 ∧ b = a :=
  Multiset.mem_repeat

theorem eq_repeat_iff : s = repeat a n ↔ ∀ b ∈ s, b = a := by
  rw [Subtype.ext_iff, coe_repeat]
  convert Multiset.eq_repeat'
  exact s.2.symm

theorem exists_mem (s : Sym α n.succ) : ∃ a, a ∈ s :=
  Multiset.card_pos_iff_exists_mem.1 <| s.2.symm ▸ n.succ_pos

theorem exists_eq_cons_of_succ (s : Sym α n.succ) : ∃ (a : α)(s' : Sym α n), s = a ::ₛ s' := by
  obtain ⟨a, ha⟩ := exists_mem s
  classical
  exact ⟨a, s.erase a ha, (cons_erase ha).symm⟩

theorem eq_repeat {a : α} {n : ℕ} {s : Sym α n} : s = repeat a n ↔ ∀ b ∈ s, b = a :=
  Subtype.ext_iff.trans <| Multiset.eq_repeat.trans <| and_iff_right s.Prop

theorem eq_repeat_of_subsingleton [Subsingleton α] (a : α) {n : ℕ} (s : Sym α n) : s = repeat a n :=
  eq_repeat.2 fun b hb => Subsingleton.elim _ _

instance [Subsingleton α] (n : ℕ) : Subsingleton (Sym α n) :=
  ⟨by
    cases n
    · simp
      
    · intro s s'
      obtain ⟨b, -⟩ := exists_mem s
      rw [eq_repeat_of_subsingleton b s', eq_repeat_of_subsingleton b s]
      ⟩

instance inhabitedSym [Inhabited α] (n : ℕ) : Inhabited (Sym α n) :=
  ⟨repeat default n⟩

instance inhabitedSym' [Inhabited α] (n : ℕ) : Inhabited (Sym' α n) :=
  ⟨Quotient.mk' (Vector.repeat default n)⟩

instance (n : ℕ) [IsEmpty α] : IsEmpty (Sym α n.succ) :=
  ⟨fun s => by
    obtain ⟨a, -⟩ := exists_mem s
    exact isEmptyElim a⟩

instance (n : ℕ) [Unique α] : Unique (Sym α n) :=
  Unique.mk' _

theorem repeat_left_inj {a b : α} {n : ℕ} (h : n ≠ 0) : repeat a n = repeat b n ↔ a = b :=
  Subtype.ext_iff.trans (Multiset.repeat_left_inj h)

theorem repeat_left_injective {n : ℕ} (h : n ≠ 0) : Function.Injective fun x : α => repeat x n := fun a b =>
  (repeat_left_inj h).1

instance (n : ℕ) [Nontrivial α] : Nontrivial (Sym α (n + 1)) :=
  (repeat_left_injective n.succ_ne_zero).Nontrivial

/-- A function `α → β` induces a function `sym α n → sym β n` by applying it to every element of
the underlying `n`-tuple. -/
def map {n : ℕ} (f : α → β) (x : Sym α n) : Sym β n :=
  ⟨x.val.map f, by simpa [Multiset.card_map] using x.property⟩

@[simp]
theorem mem_map {n : ℕ} {f : α → β} {b : β} {l : Sym α n} : b ∈ Sym.map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
  Multiset.mem_map

/-- Note: `sym.map_id` is not simp-normal, as simp ends up unfolding `id` with `sym.map_congr` -/
@[simp]
theorem map_id' {α : Type _} {n : ℕ} (s : Sym α n) : Sym.map (fun x : α => x) s = s := by simp [Sym.map]

theorem map_id {α : Type _} {n : ℕ} (s : Sym α n) : Sym.map id s = s := by simp [Sym.map]

@[simp]
theorem map_map {α β γ : Type _} {n : ℕ} (g : β → γ) (f : α → β) (s : Sym α n) :
    Sym.map g (Sym.map f s) = Sym.map (g ∘ f) s := by simp [Sym.map]

@[simp]
theorem map_zero (f : α → β) : Sym.map f (0 : Sym α 0) = (0 : Sym β 0) :=
  rfl

@[simp]
theorem map_cons {n : ℕ} (f : α → β) (a : α) (s : Sym α n) : (a ::ₛ s).map f = f a ::ₛ s.map f := by simp [map, cons]

@[congr]
theorem map_congr {f g : α → β} {s : Sym α n} (h : ∀ x ∈ s, f x = g x) : map f s = map g s :=
  Subtype.ext <| Multiset.map_congr rfl h

@[simp]
theorem map_mk {f : α → β} {m : Multiset α} {hc : m.card = n} : map f (mk m hc) = mk (m.map f) (by simp [hc]) :=
  rfl

@[simp]
theorem coe_map (s : Sym α n) (f : α → β) : ↑(s.map f) = Multiset.map f s :=
  rfl

theorem map_injective {f : α → β} (hf : Injective f) (n : ℕ) : Injective (map f : Sym α n → Sym β n) := fun s t h =>
  coe_injective <| Multiset.map_injective hf <| coe_inj.2 h

/-- Mapping an equivalence `α ≃ β` using `sym.map` gives an equivalence between `sym α n` and
`sym β n`. -/
@[simps]
def equivCongr (e : α ≃ β) : Sym α n ≃ Sym β n where
  toFun := map e
  invFun := map e.symm
  left_inv x := by rw [map_map, Equiv.symm_comp_self, map_id]
  right_inv x := by rw [map_map, Equiv.self_comp_symm, map_id]

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
an element of the symmetric power on `{x // x ∈ s}`. -/
def attach (s : Sym α n) : Sym { x // x ∈ s } n :=
  ⟨s.val.attach, by rw [Multiset.card_attach, s.2]⟩

@[simp]
theorem attach_mk {m : Multiset α} {hc : m.card = n} : attach (mk m hc) = mk m.attach (Multiset.card_attach.trans hc) :=
  rfl

@[simp]
theorem coe_attach (s : Sym α n) : (s.attach : Multiset { a // a ∈ s }) = Multiset.attach s :=
  rfl

theorem attach_map_coe (s : Sym α n) : s.attach.map coe = s :=
  coe_injective <| Multiset.attach_map_val _

@[simp]
theorem mem_attach (s : Sym α n) (x : { x // x ∈ s }) : x ∈ s.attach :=
  Multiset.mem_attach _ _

@[simp]
theorem attach_nil : (nil : Sym α 0).attach = nil :=
  rfl

@[simp]
theorem attach_cons (x : α) (s : Sym α n) :
    (cons x s).attach = cons ⟨x, mem_cons_self _ _⟩ (s.attach.map fun x => ⟨x, mem_cons_of_mem x.Prop⟩) :=
  coe_injective <| Multiset.attach_cons _ _

/-- Change the length of a `sym` using an equality.
The simp-normal form is for the `cast` to be pushed outward. -/
protected def cast {n m : ℕ} (h : n = m) : Sym α n ≃ Sym α m where
  toFun s := ⟨s.val, s.2.trans h⟩
  invFun s := ⟨s.val, s.2.trans h.symm⟩
  left_inv s := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

@[simp]
theorem cast_rfl : Sym.cast rfl s = s :=
  Subtype.ext rfl

@[simp]
theorem cast_cast {n'' : ℕ} (h : n = n') (h' : n' = n'') : Sym.cast h' (Sym.cast h s) = Sym.cast (h.trans h') s :=
  rfl

@[simp]
theorem coe_cast (h : n = m) : (Sym.cast h s : Multiset α) = s :=
  rfl

@[simp]
theorem mem_cast (h : n = m) : a ∈ Sym.cast h s ↔ a ∈ s :=
  Iff.rfl

/-- Append a pair of `sym` terms. -/
def append (s : Sym α n) (s' : Sym α n') : Sym α (n + n') :=
  ⟨s.1 + s'.1, by simp_rw [← s.2, ← s'.2, map_add]⟩

@[simp]
theorem append_inj_right (s : Sym α n) {t t' : Sym α n'} : s.append t = s.append t' ↔ t = t' :=
  Subtype.ext_iff.trans <| (add_right_inj _).trans Subtype.ext_iff.symm

@[simp]
theorem append_inj_left {s s' : Sym α n} (t : Sym α n') : s.append t = s'.append t ↔ s = s' :=
  Subtype.ext_iff.trans <| (add_left_inj _).trans Subtype.ext_iff.symm

theorem append_comm (s : Sym α n') (s' : Sym α n') : s.append s' = Sym.cast (add_comm _ _) (s'.append s) := by
  ext
  simp [append, add_comm]

@[simp, norm_cast]
theorem coe_append (s : Sym α n) (s' : Sym α n') : (s.append s' : Multiset α) = s + s' :=
  rfl

theorem mem_append_iff {s' : Sym α m} : a ∈ s.append s' ↔ a ∈ s ∨ a ∈ s' :=
  Multiset.mem_add

/-- Fill a term `m : sym α (n - i)` with `i` copies of `a` to obtain a term of `sym α n`.
This is a convenience wrapper for `m.append (repeat a i)` that adjusts the term using `sym.cast`. -/
def fill (a : α) (i : Fin (n + 1)) (m : Sym α (n - i)) : Sym α n :=
  Sym.cast (Nat.sub_add_cancel i.is_le) (m.append (repeat a i))

theorem coe_fill {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)} : (fill a i m : Multiset α) = m + repeat a i :=
  rfl

theorem mem_fill_iff {a b : α} {i : Fin (n + 1)} {s : Sym α (n - i)} :
    a ∈ Sym.fill b i s ↔ (i : ℕ) ≠ 0 ∧ a = b ∨ a ∈ s := by rw [fill, mem_cast, mem_append_iff, or_comm', mem_repeat]

open Multiset

/-- Remove every `a` from a given `sym α n`.
Yields the number of copies `i` and a term of `sym α (n - i)`. -/
def filterNe [DecidableEq α] (a : α) (m : Sym α n) : Σi : Fin (n + 1), Sym α (n - i) :=
  ⟨⟨m.1.count a, (count_le_card _ _).trans_lt <| by rw [m.2, Nat.lt_succ_iff]⟩, m.1.filter ((· ≠ ·) a),
    eq_tsub_of_add_eq <|
      Eq.trans
        (by
          rw [← countp_eq_card_filter, add_comm]
          exact (card_eq_countp_add_countp _ _).symm)
        m.2⟩

theorem sigma_sub_ext {m₁ m₂ : Σi : Fin (n + 1), Sym α (n - i)} (h : (m₁.2 : Multiset α) = m₂.2) : m₁ = m₂ :=
  Sigma.subtype_ext
    (Fin.ext <| by
      rw [← Nat.sub_sub_self m₁.1.is_le, ← Nat.sub_sub_self m₂.1.is_le, ← m₁.2.2, ← m₂.2.2, Subtype.val_eq_coe,
        Subtype.val_eq_coe, h])
    h

theorem fill_filter_ne [DecidableEq α] (a : α) (m : Sym α n) : (m.filterNe a).2.fill a (m.filterNe a).1 = m :=
  Subtype.ext
    (by
      dsimp only [coe_fill, filter_ne, Subtype.coe_mk, Fin.coe_mk]
      ext b
      rw [count_add, count_filter, Sym.coe_repeat, count_repeat]
      obtain rfl | h := eq_or_ne a b
      · rw [if_pos rfl, if_neg (not_not.2 rfl), zero_add]
        rfl
        
      · rw [if_pos h, if_neg h.symm, add_zero]
        rfl
        )

theorem filter_ne_fill [DecidableEq α] (a : α) (m : Σi : Fin (n + 1), Sym α (n - i)) (h : a ∉ m.2) :
    (m.2.fill a m.1).filterNe a = m :=
  sigma_sub_ext
    (by
      dsimp only [filter_ne, Subtype.coe_mk, Subtype.val_eq_coe, coe_fill]
      rw [filter_add, filter_eq_self.2, add_right_eq_self, eq_zero_iff_forall_not_mem]
      · intro b hb
        rw [mem_filter, Sym.mem_coe, mem_repeat] at hb
        exact hb.2 hb.1.2.symm
        
      · exact fun b hb => (hb.ne_of_not_mem h).symm
        )

end Sym

section Equiv

/-! ### Combinatorial equivalences -/


variable {α : Type _} {n : ℕ}

open Sym

namespace symOptionSuccEquiv

/-- Function from the symmetric product over `option` splitting on whether or not
it contains a `none`. -/
def encode [DecidableEq α] (s : Sym (Option α) n.succ) : Sum (Sym (Option α) n) (Sym α n.succ) :=
  if h : none ∈ s then Sum.inl (s.erase none h)
  else Sum.inr (s.attach.map fun o => Option.get <| Option.ne_none_iff_is_some.1 <| ne_of_mem_of_not_mem o.2 h)

@[simp]
theorem encode_of_none_mem [DecidableEq α] (s : Sym (Option α) n.succ) (h : none ∈ s) :
    encode s = Sum.inl (s.erase none h) :=
  dif_pos h

@[simp]
theorem encode_of_not_none_mem [DecidableEq α] (s : Sym (Option α) n.succ) (h : ¬none ∈ s) :
    encode s =
      Sum.inr (s.attach.map fun o => Option.get <| Option.ne_none_iff_is_some.1 <| ne_of_mem_of_not_mem o.2 h) :=
  dif_neg h

/-- Inverse of `sym_option_succ_equiv.decode`. -/
@[simp]
def decode : Sum (Sym (Option α) n) (Sym α n.succ) → Sym (Option α) n.succ
  | Sum.inl s => none ::ₛ s
  | Sum.inr s => s.map Embedding.coeOption

@[simp]
theorem decode_encode [DecidableEq α] (s : Sym (Option α) n.succ) : decode (encode s) = s := by
  by_cases h:none ∈ s
  · simp [h]
    
  · simp only [h, decode, not_false_iff, Subtype.val_eq_coe, encode_of_not_none_mem, embedding.coe_option_apply,
      map_map, comp_app, Option.coe_get]
    convert s.attach_map_coe
    

@[simp]
theorem encode_decode [DecidableEq α] (s : Sum (Sym (Option α) n) (Sym α n.succ)) : encode (decode s) = s := by
  obtain s | s := s
  · simp
    
  · unfold SymOptionSuccEquiv.encode
    split_ifs
    · obtain ⟨a, _, ha⟩ := multiset.mem_map.mp h
      exact Option.some_ne_none _ ha
      
    · refine' map_injective (Option.some_injective _) _ _
      convert Eq.trans _ (SymOptionSuccEquiv.decode (Sum.inr s)).attach_map_coe
      simp
      
    

end symOptionSuccEquiv

/-- The symmetric product over `option` is a disjoint union over simpler symmetric products. -/
@[simps]
def symOptionSuccEquiv [DecidableEq α] : Sym (Option α) n.succ ≃ Sum (Sym (Option α) n) (Sym α n.succ) where
  toFun := SymOptionSuccEquiv.encode
  invFun := SymOptionSuccEquiv.decode
  left_inv := SymOptionSuccEquiv.decode_encode
  right_inv := SymOptionSuccEquiv.encode_decode

end Equiv

