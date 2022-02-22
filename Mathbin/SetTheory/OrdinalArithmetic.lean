/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathbin.Logic.Small
import Mathbin.SetTheory.Ordinal
import Mathbin.Tactic.ByContra

/-!
# Ordinal arithmetic

Ordinals have an addition (corresponding to disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define correspondingly a subtraction, a division, a successor
function, a power function and a logarithm function.

We also define limit ordinals and prove the basic induction principle on ordinals separating
successor ordinals and limit ordinals, in `limit_rec_on`.

## Main definitions and results

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
* `o₁ - o₂` is the unique ordinal `o` such that `o₂ + o = o₁`, when `o₂ ≤ o₁`.
* `o₁ * o₂` is the lexicographic order on `o₂ × o₁`.
* `o₁ / o₂` is the ordinal `o` such that `o₁ = o₂ * o + o'` with `o' < o₂`. We also define the
  divisibility predicate, and a modulo operation.
* `succ o = o + 1` is the successor of `o`.
* `pred o` if the predecessor of `o`. If `o` is not a successor, we set `pred o = o`.

We also define the power function and the logarithm function on ordinals, and discuss the properties
of casts of natural numbers of and of `omega` with respect to these operations.

Some properties of the operations are also used to discuss general tools on ordinals:

* `is_limit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `limit_rec_on` is the main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals.
* `is_normal`: a function `f : ordinal → ordinal` satisfies `is_normal` if it is strictly increasing
  and order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.
* `enum_ord`: enumerates an unbounded set of ordinals by the ordinals themselves.
* `nfp f a`: the next fixed point of a function `f` on ordinals, above `a`. It behaves well
  for normal functions.
* `CNF b o` is the Cantor normal form of the ordinal `o` in base `b`.
* `sup`, `lsub`: the supremum / least strict upper bound of an indexed family of ordinals in
  `Type u`, as an ordinal in `Type u`.
* `bsup`, `blsub`: the supremum / least strict upper bound of a set of ordinals indexed by ordinals
  less than a given ordinal `o`.
-/


noncomputable section

open Function Cardinal Set Equivₓ

open_locale Classical Cardinal

universe u v w

variable {α : Type _} {β : Type _} {γ : Type _} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

namespace Ordinal

/-! ### Further properties of addition on ordinals -/


@[simp]
theorem lift_add a b : lift (a + b) = lift a + lift b :=
  (Quotientₓ.induction_on₂ a b) fun ⟨α, r, _⟩ ⟨β, s, _⟩ =>
    Quotientₓ.sound
      ⟨(RelIso.preimage Equivₓ.ulift _).trans
          (RelIso.sumLexCongr (RelIso.preimage Equivₓ.ulift _) (RelIso.preimage Equivₓ.ulift _)).symm⟩

@[simp]
theorem lift_succ a : lift (succ a) = succ (lift a) := by
  unfold succ <;> simp only [lift_add, lift_one]

instance hasLe.Le.add_contravariant_class : ContravariantClass Ordinal.{u} Ordinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun a b c =>
    (induction_on a) fun α r hr =>
      (induction_on b) fun β₁ s₁ hs₁ =>
        (induction_on c) fun β₂ s₂ hs₂ ⟨f⟩ =>
          ⟨have fl : ∀ a, f (Sum.inl a) = Sum.inl a := fun a => by
              simpa only [InitialSeg.trans_apply, InitialSeg.le_add_apply] using
                @InitialSeg.eq _ _ _ _ (@Sum.Lex.is_well_order _ _ _ _ hr hs₂) ((InitialSeg.leAdd r s₁).trans f)
                  (InitialSeg.leAdd r s₂) a
            have : ∀ b, { b' // f (Sum.inr b) = Sum.inr b' } := by
              intro b
              cases e : f (Sum.inr b)
              · rw [← fl] at e
                have := f.inj' e
                contradiction
                
              · exact ⟨_, rfl⟩
                
            let g b := (this b).1
            have fr : ∀ b, f (Sum.inr b) = Sum.inr (g b) := fun b => (this b).2
            ⟨⟨⟨g, fun x y h => by
                  injection
                    f.inj'
                      (by
                        rw [fr, fr, h] : f (Sum.inr x) = f (Sum.inr y))⟩,
                fun a b => by
                simpa only [Sum.lex_inr_inr, fr, RelEmbedding.coe_fn_to_embedding, InitialSeg.coe_fn_to_rel_embedding,
                  Function.Embedding.coe_fn_mk] using
                  @RelEmbedding.map_rel_iff _ _ _ _ f.to_rel_embedding (Sum.inr a) (Sum.inr b)⟩,
              fun a b H => by
              rcases f.init'
                  (by
                    rw [fr] <;> exact Sum.lex_inr_inr.2 H) with
                ⟨a' | a', h⟩
              · rw [fl] at h
                cases h
                
              · rw [fr] at h
                exact ⟨a', Sum.inr.injₓ h⟩
                ⟩⟩⟩

theorem add_succ (o₁ o₂ : Ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
  (add_assocₓ _ _ _).symm

@[simp]
theorem succ_zero : succ 0 = 1 :=
  zero_addₓ _

theorem one_le_iff_pos {o : Ordinal} : 1 ≤ o ↔ 0 < o := by
  rw [← succ_zero, succ_le]

theorem one_le_iff_ne_zero {o : Ordinal} : 1 ≤ o ↔ o ≠ 0 := by
  rw [one_le_iff_pos, Ordinal.pos_iff_ne_zero]

theorem succ_pos (o : Ordinal) : 0 < succ o :=
  lt_of_le_of_ltₓ (Ordinal.zero_le _) (lt_succ_self _)

theorem succ_ne_zero (o : Ordinal) : succ o ≠ 0 :=
  ne_of_gtₓ <| succ_pos o

@[simp]
theorem card_succ (o : Ordinal) : card (succ o) = card o + 1 := by
  simp only [succ, card_add, card_one]

theorem nat_cast_succ (n : ℕ) : (succ n : Ordinal) = n.succ :=
  rfl

theorem add_left_cancel a {b c : Ordinal} : a + b = a + c ↔ b = c := by
  simp only [le_antisymm_iffₓ, add_le_add_iff_left]

theorem lt_succ {a b : Ordinal} : a < succ b ↔ a ≤ b := by
  rw [← not_leₓ, succ_le, not_ltₓ]

theorem lt_one_iff_zero {a : Ordinal} : a < 1 ↔ a = 0 := by
  rw [← succ_zero, lt_succ, Ordinal.le_zero]

private theorem add_lt_add_iff_left' a {b c : Ordinal} : a + b < a + c ↔ b < c := by
  rw [← not_leₓ, ← not_leₓ, add_le_add_iff_left]

instance : CovariantClass Ordinal.{u} Ordinal.{u} (· + ·) (· < ·) :=
  ⟨fun a b c => (add_lt_add_iff_left' a).2⟩

instance : ContravariantClass Ordinal.{u} Ordinal.{u} (· + ·) (· < ·) :=
  ⟨fun a b c => (add_lt_add_iff_left' a).1⟩

theorem lt_of_add_lt_add_right {a b c : Ordinal} : a + b < c + b → a < c :=
  lt_imp_lt_of_le_imp_le fun h => add_le_add_right h _

@[simp]
theorem succ_lt_succ {a b : Ordinal} : succ a < succ b ↔ a < b := by
  rw [lt_succ, succ_le]

@[simp]
theorem succ_le_succ {a b : Ordinal} : succ a ≤ succ b ↔ a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 succ_lt_succ

theorem succ_inj {a b : Ordinal} : succ a = succ b ↔ a = b := by
  simp only [le_antisymm_iffₓ, succ_le_succ]

theorem add_le_add_iff_right {a b : Ordinal} (n : ℕ) : a + n ≤ b + n ↔ a ≤ b := by
  induction' n with n ih <;> [rw [Nat.cast_zeroₓ, add_zeroₓ, add_zeroₓ],
    rw [← nat_cast_succ, add_succ, add_succ, succ_le_succ, ih]]

theorem add_right_cancel {a b : Ordinal} (n : ℕ) : a + n = b + n ↔ a = b := by
  simp only [le_antisymm_iffₓ, add_le_add_iff_right]

/-! ### The zero ordinal -/


@[simp]
theorem card_eq_zero {o} : card o = 0 ↔ o = 0 :=
  ⟨(induction_on o) fun α r _ h => by
      refine' le_antisymmₓ (le_of_not_ltₓ fun hn => mk_ne_zero_iff.2 _ h) (Ordinal.zero_le _)
      rw [← succ_le, succ_zero] at hn
      cases' hn with f
      exact ⟨f PUnit.unit⟩,
    fun e => by
    simp only [e, card_zero]⟩

@[simp]
theorem type_eq_zero_of_empty [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  card_eq_zero.symm.mpr (mk_eq_zero _)

@[simp]
theorem type_eq_zero_iff_is_empty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α :=
  (@card_eq_zero (type r)).symm.trans mk_eq_zero_iff

theorem type_ne_zero_iff_nonempty [IsWellOrder α r] : type r ≠ 0 ↔ Nonempty α :=
  (not_congr (@card_eq_zero (type r))).symm.trans mk_ne_zero_iff

protected theorem one_ne_zero : (1 : Ordinal) ≠ 0 :=
  type_ne_zero_iff_nonempty.2 ⟨PUnit.unit⟩

instance : Nontrivial Ordinal.{u} :=
  ⟨⟨1, 0, Ordinal.one_ne_zero⟩⟩

theorem zero_lt_one : (0 : Ordinal) < 1 :=
  lt_iff_le_and_ne.2 ⟨Ordinal.zero_le _, Ne.symm <| Ordinal.one_ne_zero⟩

theorem le_one_iff {a : Ordinal} : a ≤ 1 ↔ a = 0 ∨ a = 1 := by
  refine' ⟨fun ha => _, _⟩
  · rcases eq_or_lt_of_le ha with (rfl | ha)
    exacts[Or.inr rfl, Or.inl (lt_one_iff_zero.1 ha)]
    
  · rintro (rfl | rfl)
    exacts[le_of_ltₓ zero_lt_one, le_reflₓ _]
    

/-! ### The predecessor of an ordinal -/


/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : Ordinal.{u}) : Ordinal.{u} :=
  if h : ∃ a, o = succ a then Classical.some h else o

@[simp]
theorem pred_succ o : pred (succ o) = o := by
  have h : ∃ a, succ o = succ a := ⟨_, rfl⟩ <;>
    simpa only [pred, dif_pos h] using (succ_inj.1 <| Classical.some_spec h).symm

theorem pred_le_self o : pred o ≤ o :=
  if h : ∃ a, o = succ a then by
    let ⟨a, e⟩ := h
    rw [e, pred_succ] <;> exact le_of_ltₓ (lt_succ_self _)
  else by
    rw [pred, dif_neg h]

theorem pred_eq_iff_not_succ {o} : pred o = o ↔ ¬∃ a, o = succ a :=
  ⟨fun e ⟨a, e'⟩ => by
    rw [e', pred_succ] at e <;> exact ne_of_ltₓ (lt_succ_self _) e, fun h => dif_neg h⟩

theorem pred_lt_iff_is_succ {o} : pred o < o ↔ ∃ a, o = succ a :=
  Iff.trans
    (by
      simp only [le_antisymm_iffₓ, pred_le_self, true_andₓ, not_leₓ])
    (iff_not_comm.1 pred_eq_iff_not_succ).symm

theorem succ_pred_iff_is_succ {o} : succ (pred o) = o ↔ ∃ a, o = succ a :=
  ⟨fun e => ⟨_, e.symm⟩, fun ⟨a, e⟩ => by
    simp only [e, pred_succ]⟩

theorem succ_lt_of_not_succ {o} (h : ¬∃ a, o = succ a) {b} : succ b < o ↔ b < o :=
  ⟨lt_transₓ (lt_succ_self _), fun l => lt_of_le_of_neₓ (succ_le.2 l) fun e => h ⟨_, e.symm⟩⟩

theorem lt_pred {a b} : a < pred b ↔ succ a < b :=
  if h : ∃ a, b = succ a then by
    let ⟨c, e⟩ := h
    rw [e, pred_succ, succ_lt_succ]
  else by
    simp only [pred, dif_neg h, succ_lt_of_not_succ h]

theorem pred_le {a b} : pred a ≤ b ↔ a ≤ succ b :=
  le_iff_le_iff_lt_iff_lt.2 lt_pred

@[simp]
theorem lift_is_succ {o} : (∃ a, lift o = succ a) ↔ ∃ a, o = succ a :=
  ⟨fun ⟨a, h⟩ =>
    let ⟨b, e⟩ := lift_down <| show a ≤ lift o from le_of_ltₓ <| h.symm ▸ lt_succ_self _
    ⟨b,
      lift_inj.1 <| by
        rw [h, ← e, lift_succ]⟩,
    fun ⟨a, h⟩ =>
    ⟨lift a, by
      simp only [h, lift_succ]⟩⟩

@[simp]
theorem lift_pred o : lift (pred o) = pred (lift o) :=
  if h : ∃ a, o = succ a then by
    cases' h with a e <;> simp only [e, pred_succ, lift_succ]
  else by
    rw [pred_eq_iff_not_succ.2 h, pred_eq_iff_not_succ.2 (mt lift_is_succ.1 h)]

/-! ### Limit ordinals -/


/-- A limit ordinal is an ordinal which is not zero and not a successor. -/
def IsLimit (o : Ordinal) : Prop :=
  o ≠ 0 ∧ ∀, ∀ a < o, ∀, succ a < o

theorem not_zero_is_limit : ¬IsLimit 0
  | ⟨h, _⟩ => h rfl

theorem not_succ_is_limit o : ¬IsLimit (succ o)
  | ⟨_, h⟩ => lt_irreflₓ _ (h _ (lt_succ_self _))

theorem not_succ_of_is_limit {o} (h : IsLimit o) : ¬∃ a, o = succ a
  | ⟨a, e⟩ => not_succ_is_limit a (e ▸ h)

theorem succ_lt_of_is_limit {o} (h : IsLimit o) {a} : succ a < o ↔ a < o :=
  ⟨lt_transₓ (lt_succ_self _), h.2 _⟩

theorem le_succ_of_is_limit {o} (h : IsLimit o) {a} : o ≤ succ a ↔ o ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 <| succ_lt_of_is_limit h

theorem limit_le {o} (h : IsLimit o) {a} : o ≤ a ↔ ∀, ∀ x < o, ∀, x ≤ a :=
  ⟨fun h x l => le_transₓ (le_of_ltₓ l) h, fun H =>
    (le_succ_of_is_limit h).1 <| le_of_not_ltₓ fun hn => not_lt_of_le (H _ hn) (lt_succ_self _)⟩

theorem lt_limit {o} (h : IsLimit o) {a} : a < o ↔ ∃ x < o, a < x := by
  simpa only [not_ball, not_leₓ] using not_congr (@limit_le _ h a)

@[simp]
theorem lift_is_limit o : IsLimit (lift o) ↔ IsLimit o :=
  and_congr
    (not_congr <| by
      simpa only [lift_zero] using @lift_inj o 0)
    ⟨fun H a h =>
      lift_lt.1 <| by
        simpa only [lift_succ] using H _ (lift_lt.2 h),
      fun H a h => by
      let ⟨a', e⟩ := lift_down (le_of_ltₓ h)
      rw [← e, ← lift_succ, lift_lt] <;> rw [← e, lift_lt] at h <;> exact H a' h⟩

theorem IsLimit.pos {o : Ordinal} (h : IsLimit o) : 0 < o :=
  lt_of_le_of_neₓ (Ordinal.zero_le _) h.1.symm

theorem IsLimit.one_lt {o : Ordinal} (h : IsLimit o) : 1 < o := by
  simpa only [succ_zero] using h.2 _ h.pos

theorem IsLimit.nat_lt {o : Ordinal} (h : IsLimit o) : ∀ n : ℕ, (n : Ordinal) < o
  | 0 => h.Pos
  | n + 1 => h.2 _ (is_limit.nat_lt n)

theorem zero_or_succ_or_limit (o : Ordinal) : o = 0 ∨ (∃ a, o = succ a) ∨ IsLimit o :=
  if o0 : o = 0 then Or.inl o0
  else if h : ∃ a, o = succ a then Or.inr (Or.inl h) else Or.inr <| Or.inr ⟨o0, fun a => (succ_lt_of_not_succ h).2⟩

/-- Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
@[elab_as_eliminator]
def limitRecOn {C : Ordinal → Sort _} (o : Ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
    (H₃ : ∀ o, IsLimit o → (∀, ∀ o' < o, ∀, C o') → C o) : C o :=
  wf.fix
    (fun o IH =>
      if o0 : o = 0 then by
        rw [o0] <;> exact H₁
      else
        if h : ∃ a, o = succ a then by
          rw [← succ_pred_iff_is_succ.2 h] <;> exact H₂ _ (IH _ <| pred_lt_iff_is_succ.2 h)
        else H₃ _ ⟨o0, fun a => (succ_lt_of_not_succ h).2⟩ IH)
    o

@[simp]
theorem limit_rec_on_zero {C} H₁ H₂ H₃ : @limitRecOn C 0 H₁ H₂ H₃ = H₁ := by
  rw [limit_rec_on, WellFounded.fix_eq, dif_pos rfl] <;> rfl

@[simp]
theorem limit_rec_on_succ {C} o H₁ H₂ H₃ : @limitRecOn C (succ o) H₁ H₂ H₃ = H₂ o (@limitRecOn C o H₁ H₂ H₃) := by
  have h : ∃ a, succ o = succ a := ⟨_, rfl⟩
  rw [limit_rec_on, WellFounded.fix_eq, dif_neg (succ_ne_zero o), dif_pos h]
  generalize limit_rec_on._proof_2 (succ o) h = h₂
  generalize limit_rec_on._proof_3 (succ o) h = h₃
  revert h₂ h₃
  generalize e : pred (succ o) = o'
  intros
  rw [pred_succ] at e
  subst o'
  rfl

@[simp]
theorem limit_rec_on_limit {C} o H₁ H₂ H₃ h : @limitRecOn C o H₁ H₂ H₃ = H₃ o h fun x h => @limitRecOn C x H₁ H₂ H₃ :=
  by
  rw [limit_rec_on, WellFounded.fix_eq, dif_neg h.1, dif_neg (not_succ_of_is_limit h)] <;> rfl

theorem has_succ_of_is_limit {α} {r : α → α → Prop} [wo : IsWellOrder α r] (h : (type r).IsLimit) (x : α) :
    ∃ y, r x y := by
  use enum r (typein r x).succ (h.2 _ (typein_lt_type r x))
  convert (enum_lt (typein_lt_type r x) _).mpr (lt_succ_self _)
  rw [enum_typein]

theorem type_subrel_lt (o : Ordinal.{u}) : type (Subrel (· < ·) { o' : Ordinal | o' < o }) = Ordinal.lift.{u + 1} o :=
  by
  refine' Quotientₓ.induction_on o _
  rintro ⟨α, r, wo⟩
  skip
  apply Quotientₓ.sound
  constructor
  symm
  refine' (RelIso.preimage Equivₓ.ulift r).trans (typein_iso r)

theorem mk_initial_seg (o : Ordinal.{u}) : # { o' : Ordinal | o' < o } = Cardinal.lift.{u + 1} o.card := by
  rw [lift_card, ← type_subrel_lt, card_type]

/-! ### Normal ordinal functions -/


/-- A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.  -/
def IsNormal (f : Ordinal → Ordinal) : Prop :=
  (∀ o, f o < f (succ o)) ∧ ∀ o, IsLimit o → ∀ a, f o ≤ a ↔ ∀, ∀ b < o, ∀, f b ≤ a

theorem IsNormal.limit_le {f} (H : IsNormal f) : ∀ {o}, IsLimit o → ∀ {a}, f o ≤ a ↔ ∀, ∀ b < o, ∀, f b ≤ a :=
  H.2

theorem IsNormal.limit_lt {f} (H : IsNormal f) {o} (h : IsLimit o) {a} : a < f o ↔ ∃ b < o, a < f b :=
  not_iff_not.1 <| by
    simpa only [exists_prop, not_exists, not_and, not_ltₓ] using H.2 _ h a

theorem IsNormal.strict_mono {f} (H : IsNormal f) : StrictMono f := fun a b =>
  limitRecOn b (Not.elim (not_lt_of_le <| Ordinal.zero_le _))
    (fun b IH h => (lt_or_eq_of_leₓ (lt_succ.1 h)).elim (fun h => lt_transₓ (IH h) (H.1 _)) fun e => e ▸ H.1 _)
    fun b l IH h => lt_of_lt_of_leₓ (H.1 a) ((H.2 _ l _).1 le_rfl _ (l.2 _ h))

theorem IsNormal.lt_iff {f} (H : IsNormal f) {a b} : f a < f b ↔ a < b :=
  StrictMono.lt_iff_lt <| H.StrictMono

theorem IsNormal.le_iff {f} (H : IsNormal f) {a b} : f a ≤ f b ↔ a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.lt_iff

theorem IsNormal.inj {f} (H : IsNormal f) {a b} : f a = f b ↔ a = b := by
  simp only [le_antisymm_iffₓ, H.le_iff]

theorem IsNormal.self_le {f} (H : IsNormal f) a : a ≤ f a :=
  wf.self_le_of_strict_mono H.StrictMono a

theorem IsNormal.le_set {f} (H : IsNormal f) (p : Set Ordinal) (p0 : p.Nonempty) b
    (H₂ : ∀ o, b ≤ o ↔ ∀, ∀ a ∈ p, ∀, a ≤ o) {o} : f b ≤ o ↔ ∀, ∀ a ∈ p, ∀, f a ≤ o :=
  ⟨fun h a pa => (H.le_iff.2 ((H₂ _).1 (le_reflₓ _) _ pa)).trans h, fun h => by
    revert H₂
    refine' limit_rec_on b (fun H₂ => _) (fun S _ H₂ => _) fun S L _ H₂ => (H.2 _ L _).2 fun a h' => _
    · cases' p0 with x px
      have := Ordinal.le_zero.1 ((H₂ _).1 (Ordinal.zero_le _) _ px)
      rw [this] at px
      exact h _ px
      
    · rcases not_ball.1 (mt (H₂ S).2 <| not_le_of_lt <| lt_succ_self _) with ⟨a, h₁, h₂⟩
      exact (H.le_iff.2 <| succ_le.2 <| not_leₓ.1 h₂).trans (h _ h₁)
      
    · rcases not_ball.1 (mt (H₂ a).2 (not_leₓ.2 h')) with ⟨b, h₁, h₂⟩
      exact (H.le_iff.2 <| le_of_ltₓ <| not_leₓ.1 h₂).trans (h _ h₁)
      ⟩

theorem IsNormal.le_set' {f} (H : IsNormal f) (p : Set α) (g : α → Ordinal) (p0 : p.Nonempty) b
    (H₂ : ∀ o, b ≤ o ↔ ∀, ∀ a ∈ p, ∀, g a ≤ o) {o} : f b ≤ o ↔ ∀, ∀ a ∈ p, ∀, f (g a) ≤ o :=
  (H.le_set (fun x => ∃ y, p y ∧ x = g y)
        (let ⟨x, px⟩ := p0
        ⟨_, _, px, rfl⟩)
        _ fun o => (H₂ o).trans ⟨fun H a ⟨y, h1, h2⟩ => h2.symm ▸ H y h1, fun H a h1 => H (g a) ⟨a, h1, rfl⟩⟩).trans
    ⟨fun H a h => H (g a) ⟨a, h, rfl⟩, fun H a ⟨y, h1, h2⟩ => h2.symm ▸ H y h1⟩

theorem IsNormal.refl : IsNormal id :=
  ⟨fun x => lt_succ_self _, fun o l a => limit_le l⟩

theorem IsNormal.trans {f g} (H₁ : IsNormal f) (H₂ : IsNormal g) : IsNormal fun x => f (g x) :=
  ⟨fun x => H₁.lt_iff.2 (H₂.1 _), fun o l a => H₁.le_set' (· < o) g ⟨_, l.Pos⟩ _ fun c => H₂.2 _ l _⟩

theorem IsNormal.is_limit {f} (H : IsNormal f) {o} (l : IsLimit o) : IsLimit (f o) :=
  ⟨ne_of_gtₓ <| lt_of_le_of_ltₓ (Ordinal.zero_le _) <| H.lt_iff.2 l.Pos, fun a h =>
    let ⟨b, h₁, h₂⟩ := (H.limit_lt l).1 h
    lt_of_le_of_ltₓ (succ_le.2 h₂) (H.lt_iff.2 h₁)⟩

theorem IsNormal.le_iff_eq {f} (H : IsNormal f) {a} : f a ≤ a ↔ f a = a :=
  (H.self_le a).le_iff_eq

theorem add_le_of_limit {a b c : Ordinal.{u}} (h : IsLimit b) : a + b ≤ c ↔ ∀, ∀ b' < b, ∀, a + b' ≤ c :=
  ⟨fun h b' l => le_transₓ (add_le_add_left (le_of_ltₓ l) _) h, fun H =>
    le_of_not_ltₓ <|
      induction_on a
        (fun α r _ =>
          (induction_on b) fun β s _ h H l => by
            skip
            suffices ∀ x : β, Sum.Lex r s (Sum.inr x) (enum _ _ l) by
              cases' enum _ _ l with x x
              · cases this (enum s 0 h.pos)
                
              · exact irrefl _ (this _)
                
            intro x
            rw [← typein_lt_typein (Sum.Lex r s), typein_enum]
            have := H _ (h.2 _ (typein_lt_type s x))
            rw [add_succ, succ_le] at this
            refine' lt_of_le_of_ltₓ (type_le'.2 ⟨RelEmbedding.ofMonotone (fun a => _) fun a b => _⟩) this
            · rcases a with ⟨a | b, h⟩
              · exact Sum.inl a
                
              · exact
                  Sum.inr
                    ⟨b, by
                      cases h <;> assumption⟩
                
              
            · rcases a with ⟨a | a, h₁⟩ <;>
                rcases b with ⟨b | b, h₂⟩ <;> cases h₁ <;> cases h₂ <;> rintro ⟨⟩ <;> constructor <;> assumption
              )
        h H⟩

theorem add_is_normal (a : Ordinal) : IsNormal ((· + ·) a) :=
  ⟨fun b => (add_lt_add_iff_left a).2 (lt_succ_self _), fun b l c => add_le_of_limit l⟩

theorem add_is_limit a {b} : IsLimit b → IsLimit (a + b) :=
  (add_is_normal a).IsLimit

/-! ### Subtraction on ordinals-/


/-- `a - b` is the unique ordinal satisfying `b + (a - b) = a` when `b ≤ a`. -/
def sub (a b : Ordinal.{u}) : Ordinal.{u} :=
  inf { o | a ≤ b + o }

/-- The set in the definition of subtraction is nonempty. -/
theorem sub_nonempty {a b : Ordinal.{u}} : { o | a ≤ b + o }.Nonempty :=
  ⟨a, le_add_left _ _⟩

instance : Sub Ordinal :=
  ⟨sub⟩

theorem le_add_sub (a b : Ordinal) : a ≤ b + (a - b) :=
  Inf_mem sub_nonempty

theorem sub_le {a b c : Ordinal} : a - b ≤ c ↔ a ≤ b + c :=
  ⟨fun h => le_transₓ (le_add_sub a b) (add_le_add_left h _), fun h => cInf_le' h⟩

theorem lt_sub {a b c : Ordinal} : a < b - c ↔ c + a < b :=
  lt_iff_lt_of_le_iff_le sub_le

theorem add_sub_cancel (a b : Ordinal) : a + b - a = b :=
  le_antisymmₓ (sub_le.2 <| le_rfl) ((add_le_add_iff_left a).1 <| le_add_sub _ _)

theorem sub_eq_of_add_eq {a b c : Ordinal} (h : a + b = c) : c - a = b :=
  h ▸ add_sub_cancel _ _

theorem sub_le_self (a b : Ordinal) : a - b ≤ a :=
  sub_le.2 <| le_add_left _ _

protected theorem add_sub_cancel_of_le {a b : Ordinal} (h : b ≤ a) : b + (a - b) = a :=
  le_antisymmₓ
    (by
      rcases zero_or_succ_or_limit (a - b) with (e | ⟨c, e⟩ | l)
      · simp only [e, add_zeroₓ, h]
        
      · rw [e, add_succ, succ_le, ← lt_sub, e]
        apply lt_succ_self
        
      · exact (add_le_of_limit l).2 fun c l => le_of_ltₓ (lt_sub.1 l)
        )
    (le_add_sub _ _)

@[simp]
theorem sub_zero (a : Ordinal) : a - 0 = a := by
  simpa only [zero_addₓ] using add_sub_cancel 0 a

@[simp]
theorem zero_sub (a : Ordinal) : 0 - a = 0 := by
  rw [← Ordinal.le_zero] <;> apply sub_le_self

@[simp]
theorem sub_self (a : Ordinal) : a - a = 0 := by
  simpa only [add_zeroₓ] using add_sub_cancel a 0

protected theorem sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h => by
    simpa only [h, add_zeroₓ] using le_add_sub a b, fun h => by
    rwa [← Ordinal.le_zero, sub_le, add_zeroₓ]⟩

theorem sub_sub (a b c : Ordinal) : a - b - c = a - (b + c) :=
  eq_of_forall_ge_iff fun d => by
    rw [sub_le, sub_le, sub_le, add_assocₓ]

theorem add_sub_add_cancel (a b c : Ordinal) : a + b - (a + c) = b - c := by
  rw [← sub_sub, add_sub_cancel]

theorem sub_is_limit {a b} (l : IsLimit a) (h : b < a) : IsLimit (a - b) :=
  ⟨ne_of_gtₓ <|
      lt_sub.2 <| by
        rwa [add_zeroₓ],
    fun c h => by
    rw [lt_sub, add_succ] <;> exact l.2 _ (lt_sub.1 h)⟩

@[simp]
theorem one_add_omega : 1 + omega.{u} = omega := by
  refine' le_antisymmₓ _ (le_add_left _ _)
  rw [omega, one_eq_lift_type_unit, ← lift_add, lift_le, type_add]
  have : IsWellOrder Unit EmptyRelation := by
    infer_instance
  refine' ⟨RelEmbedding.collapse (RelEmbedding.ofMonotone _ _)⟩
  · apply Sum.rec
    exact fun _ => 0
    exact Nat.succ
    
  · intro a b
    cases a <;>
      cases b <;> intro H <;> cases' H with _ _ H _ _ H <;> [cases H, exact Nat.succ_posₓ _, exact Nat.succ_lt_succₓ H]
    

@[simp]
theorem one_add_of_omega_le {o} (h : omega ≤ o) : 1 + o = o := by
  rw [← Ordinal.add_sub_cancel_of_le h, ← add_assocₓ, one_add_omega]

/-! ### Multiplication of ordinals-/


/-- The multiplication of ordinals `o₁` and `o₂` is the (well founded) lexicographic order on
`o₂ × o₁`. -/
instance : Monoidₓ Ordinal.{u} where
  mul := fun a b =>
    (Quotientₓ.liftOn₂ a b
        (fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => ⟦⟨β × α, Prod.Lex s r, Prod.Lex.is_well_order⟩⟧ :
          WellOrder → WellOrder → Ordinal))
      fun ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.prodLexCongr g f⟩
  one := 1
  mul_assoc := fun a b c =>
    (Quotientₓ.induction_on₃ a b c) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Eq.symm <|
        Quotientₓ.sound
          ⟨⟨prodAssoc _ _ _, fun a b => by
              rcases a with ⟨⟨a₁, a₂⟩, a₃⟩
              rcases b with ⟨⟨b₁, b₂⟩, b₃⟩
              simp [Prod.lex_def, and_or_distrib_left, or_assoc, and_assoc]⟩⟩
  mul_one := fun a =>
    (induction_on a) fun α r _ =>
      Quotientₓ.sound
        ⟨⟨punitProd _, fun a b => by
            rcases a with ⟨⟨⟨⟩⟩, a⟩ <;>
              rcases b with ⟨⟨⟨⟩⟩, b⟩ <;>
                simp only [Prod.lex_def, EmptyRelation, false_orₓ] <;> simp only [eq_self_iff_true, true_andₓ] <;> rfl⟩⟩
  one_mul := fun a =>
    (induction_on a) fun α r _ =>
      Quotientₓ.sound
        ⟨⟨prodPunit _, fun a b => by
            rcases a with ⟨a, ⟨⟨⟩⟩⟩ <;>
              rcases b with ⟨b, ⟨⟨⟩⟩⟩ <;> simp only [Prod.lex_def, EmptyRelation, and_falseₓ, or_falseₓ] <;> rfl⟩⟩

@[simp]
theorem type_mul {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s] :
    type r * type s = type (Prod.Lex s r) :=
  rfl

@[simp]
theorem lift_mul a b : lift (a * b) = lift a * lift b :=
  (Quotientₓ.induction_on₂ a b) fun ⟨α, r, _⟩ ⟨β, s, _⟩ =>
    Quotientₓ.sound
      ⟨(RelIso.preimage Equivₓ.ulift _).trans
          (RelIso.prodLexCongr (RelIso.preimage Equivₓ.ulift _) (RelIso.preimage Equivₓ.ulift _)).symm⟩

@[simp]
theorem card_mul a b : card (a * b) = card a * card b :=
  (Quotientₓ.induction_on₂ a b) fun ⟨α, r, _⟩ ⟨β, s, _⟩ => mul_comm (mk β) (mk α)

@[simp]
theorem mul_zero (a : Ordinal) : a * 0 = 0 :=
  (induction_on a) fun α _ _ => type_eq_zero_of_empty

@[simp]
theorem zero_mul (a : Ordinal) : 0 * a = 0 :=
  (induction_on a) fun α _ _ => type_eq_zero_of_empty

theorem mul_add (a b c : Ordinal) : a * (b + c) = a * b + a * c :=
  (Quotientₓ.induction_on₃ a b c) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
    Quotientₓ.sound
      ⟨⟨sumProdDistrib _ _ _, by
          rintro ⟨a₁ | a₁, a₂⟩ ⟨b₁ | b₁, b₂⟩ <;>
            simp only [Prod.lex_def, Sum.lex_inl_inl, Sum.Lex.sep, Sum.lex_inr_inl, Sum.lex_inr_inr,
                sum_prod_distrib_apply_left, sum_prod_distrib_apply_right] <;>
              simp only [Sum.inl.inj_iff, true_orₓ, false_andₓ, false_orₓ]⟩⟩

@[simp]
theorem mul_add_one (a b : Ordinal) : a * (b + 1) = a * b + a := by
  rw [mul_addₓ, mul_oneₓ]

@[simp]
theorem mul_one_add (a b : Ordinal) : a * (1 + b) = a + a * b := by
  rw [mul_addₓ, mul_oneₓ]

@[simp]
theorem mul_succ (a b : Ordinal) : a * succ b = a * b + a :=
  mul_add_one _ _

instance hasLe.Le.mul_covariant_class : CovariantClass Ordinal.{u} Ordinal.{u} (· * ·) (· ≤ ·) :=
  ⟨fun c a b =>
    (Quotientₓ.induction_on₃ a b c) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      skip
      refine' type_le'.2 ⟨RelEmbedding.ofMonotone (fun a => (f a.1, a.2)) fun a b h => _⟩
      clear_
      cases' h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h'
      · exact Prod.Lex.left _ _ (f.to_rel_embedding.map_rel_iff.2 h')
        
      · exact Prod.Lex.right _ h'
        ⟩

instance hasLe.Le.mul_swap_covariant_class : CovariantClass Ordinal.{u} Ordinal.{u} (Function.swap (· * ·)) (· ≤ ·) :=
  ⟨fun c a b =>
    (Quotientₓ.induction_on₃ a b c) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
      skip
      refine' type_le'.2 ⟨RelEmbedding.ofMonotone (fun a => (a.1, f a.2)) fun a b h => _⟩
      cases' h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h'
      · exact Prod.Lex.left _ _ h'
        
      · exact Prod.Lex.right _ (f.to_rel_embedding.map_rel_iff.2 h')
        ⟩

theorem le_mul_left (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ a * b := by
  convert mul_le_mul_left' (one_le_iff_pos.2 hb) a
  rw [mul_oneₓ a]

theorem le_mul_right (a : Ordinal) {b : Ordinal} (hb : 0 < b) : a ≤ b * a := by
  convert mul_le_mul_right' (one_le_iff_pos.2 hb) a
  rw [one_mulₓ a]

private theorem mul_le_of_limit_aux {α β r s} [IsWellOrder α r] [IsWellOrder β s] {c} (h : IsLimit (type s))
    (H : ∀, ∀ b' < type s, ∀, type r * b' ≤ c) (l : c < type r * type s) : False := by
  suffices ∀ a b, Prod.Lex s r (b, a) (enum _ _ l) by
    cases' enum _ _ l with b a
    exact irrefl _ (this _ _)
  intro a b
  rw [← typein_lt_typein (Prod.Lex s r), typein_enum]
  have := H _ (h.2 _ (typein_lt_type s b))
  rw [mul_succ] at this
  have := lt_of_lt_of_leₓ ((add_lt_add_iff_left _).2 (typein_lt_type _ a)) this
  refine' lt_of_le_of_ltₓ _ this
  refine' type_le'.2 _
  constructor
  refine' RelEmbedding.ofMonotone (fun a => _) fun a b => _
  · rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases' e : b = b'
    · refine' Sum.inr ⟨a', _⟩
      subst e
      cases' h with _ _ _ _ h _ _ _ h
      · exact (irrefl _ h).elim
        
      · exact h
        
      
    · refine' Sum.inl (⟨b', _⟩, a')
      cases' h with _ _ _ _ h _ _ _ h
      · exact h
        
      · exact (e rfl).elim
        
      
    
  · rcases a with ⟨⟨b₁, a₁⟩, h₁⟩
    rcases b with ⟨⟨b₂, a₂⟩, h₂⟩
    intro h
    by_cases' e₁ : b = b₁ <;> by_cases' e₂ : b = b₂
    · substs b₁ b₂
      simpa only [subrel_val, Prod.lex_def, @irrefl _ s _ b, true_andₓ, false_orₓ, eq_self_iff_true, dif_pos,
        Sum.lex_inr_inr] using h
      
    · subst b₁
      simp only [subrel_val, Prod.lex_def, e₂, Prod.lex_def, dif_pos, subrel_val, eq_self_iff_true, or_falseₓ, dif_neg,
        not_false_iff, Sum.lex_inr_inl, false_andₓ] at h⊢
      cases h₂ <;> [exact asymm h h₂_h, exact e₂ rfl]
      
    · simp [e₂, dif_neg e₁,
        show b₂ ≠ b₁ by
          cc]
      
    · simpa only [dif_neg e₁, dif_neg e₂, Prod.lex_def, subrel_val, Subtype.mk_eq_mk, Sum.lex_inl_inl] using h
      
    

theorem mul_le_of_limit {a b c : Ordinal.{u}} (h : IsLimit b) : a * b ≤ c ↔ ∀, ∀ b' < b, ∀, a * b' ≤ c :=
  ⟨fun h b' l => (mul_le_mul_left' (le_of_ltₓ l) _).trans h, fun H =>
    le_of_not_ltₓ <| induction_on a (fun α r _ => (induction_on b) fun β s _ => mul_le_of_limit_aux) h H⟩

theorem mul_is_normal {a : Ordinal} (h : 0 < a) : IsNormal ((· * ·) a) :=
  ⟨fun b => by
    rw [mul_succ] <;> simpa only [add_zeroₓ] using (add_lt_add_iff_left (a * b)).2 h, fun b l c => mul_le_of_limit l⟩

theorem lt_mul_of_limit {a b c : Ordinal.{u}} (h : IsLimit c) : a < b * c ↔ ∃ c' < c, a < b * c' := by
  simpa only [not_ball, not_leₓ] using not_congr (@mul_le_of_limit b c a h)

theorem mul_lt_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : a * b < a * c ↔ b < c :=
  (mul_is_normal a0).lt_iff

theorem mul_le_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  (mul_is_normal a0).le_iff

theorem mul_lt_mul_of_pos_left {a b c : Ordinal} (h : a < b) (c0 : 0 < c) : c * a < c * b :=
  (mul_lt_mul_iff_left c0).2 h

theorem mul_pos {a b : Ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left h₂ h₁

theorem mul_ne_zero {a b : Ordinal} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  simpa only [Ordinal.pos_iff_ne_zero] using mul_pos

theorem le_of_mul_le_mul_left {a b c : Ordinal} (h : c * a ≤ c * b) (h0 : 0 < c) : a ≤ b :=
  le_imp_le_of_lt_imp_ltₓ (fun h' => mul_lt_mul_of_pos_left h' h0) h

theorem mul_right_inj {a b c : Ordinal} (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  (mul_is_normal a0).inj

theorem mul_is_limit {a b : Ordinal} (a0 : 0 < a) : IsLimit b → IsLimit (a * b) :=
  (mul_is_normal a0).IsLimit

theorem mul_is_limit_left {a b : Ordinal} (l : IsLimit a) (b0 : 0 < b) : IsLimit (a * b) := by
  rcases zero_or_succ_or_limit b with (rfl | ⟨b, rfl⟩ | lb)
  · exact b0.false.elim
    
  · rw [mul_succ]
    exact add_is_limit _ l
    
  · exact mul_is_limit l.pos lb
    

/-! ### Division on ordinals -/


protected theorem div_aux (a b : Ordinal.{u}) (h : b ≠ 0) : Set.Nonempty { o | a < b * succ o } :=
  ⟨a,
    succ_le.1 <| by
      simpa only [succ_zero, one_mulₓ] using mul_le_mul_right' (succ_le.2 (Ordinal.pos_iff_ne_zero.2 h)) (succ a)⟩

/-- `a / b` is the unique ordinal `o` satisfying
  `a = b * o + o'` with `o' < b`. -/
protected def div (a b : Ordinal.{u}) : Ordinal.{u} :=
  if h : b = 0 then 0 else inf { o | a < b * succ o }

/-- The set in the definition of division is nonempty. -/
theorem div_nonempty {a b : Ordinal.{u}} (h : b ≠ 0) : { o | a < b * succ o }.Nonempty :=
  Ordinal.div_aux a b h

instance : Div Ordinal :=
  ⟨Ordinal.div⟩

@[simp]
theorem div_zero (a : Ordinal) : a / 0 = 0 :=
  dif_pos rfl

theorem div_def a {b : Ordinal} (h : b ≠ 0) : a / b = inf { o | a < b * succ o } :=
  dif_neg h

theorem lt_mul_succ_div a {b : Ordinal} (h : b ≠ 0) : a < b * succ (a / b) := by
  rw [div_def a h] <;> exact Inf_mem (div_nonempty h)

theorem lt_mul_div_add a {b : Ordinal} (h : b ≠ 0) : a < b * (a / b) + b := by
  simpa only [mul_succ] using lt_mul_succ_div a h

theorem div_le {a b c : Ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b * succ c :=
  ⟨fun h => (lt_mul_succ_div a b0).trans_le (mul_le_mul_left' (succ_le_succ.2 h) _), fun h => by
    rw [div_def a b0] <;> exact cInf_le' h⟩

theorem lt_div {a b c : Ordinal} (c0 : c ≠ 0) : a < b / c ↔ c * succ a ≤ b := by
  rw [← not_leₓ, div_le c0, not_ltₓ]

theorem le_div {a b c : Ordinal} (c0 : c ≠ 0) : a ≤ b / c ↔ c * a ≤ b := by
  apply limit_rec_on a
  · simp only [mul_zero, Ordinal.zero_le]
    
  · intros
    rw [succ_le, lt_div c0]
    
  · simp (config := { contextual := true })only [mul_le_of_limit, limit_le, iff_selfₓ, forall_true_iff]
    

theorem div_lt {a b c : Ordinal} (b0 : b ≠ 0) : a / b < c ↔ a < b * c :=
  lt_iff_lt_of_le_iff_le <| le_div b0

theorem div_le_of_le_mul {a b c : Ordinal} (h : a ≤ b * c) : a / b ≤ c :=
  if b0 : b = 0 then by
    simp only [b0, div_zero, Ordinal.zero_le]
  else (div_le b0).2 <| lt_of_le_of_ltₓ h <| mul_lt_mul_of_pos_left (lt_succ_self _) (Ordinal.pos_iff_ne_zero.2 b0)

theorem mul_lt_of_lt_div {a b c : Ordinal} : a < b / c → c * a < b :=
  lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp]
theorem zero_div (a : Ordinal) : 0 / a = 0 :=
  Ordinal.le_zero.1 <| div_le_of_le_mul <| Ordinal.zero_le _

theorem mul_div_le (a b : Ordinal) : b * (a / b) ≤ a :=
  if b0 : b = 0 then by
    simp only [b0, zero_mul, Ordinal.zero_le]
  else (le_div b0).1 le_rfl

theorem mul_add_div a {b : Ordinal} (b0 : b ≠ 0) c : (b * a + c) / b = a + c / b := by
  apply le_antisymmₓ
  · apply (div_le b0).2
    rw [mul_succ, mul_addₓ, add_assocₓ, add_lt_add_iff_left]
    apply lt_mul_div_add _ b0
    
  · rw [le_div b0, mul_addₓ, add_le_add_iff_left]
    apply mul_div_le
    

theorem div_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a / b = 0 := by
  rw [← Ordinal.le_zero, div_le <| Ordinal.pos_iff_ne_zero.1 <| lt_of_le_of_ltₓ (Ordinal.zero_le _) h]
  simpa only [succ_zero, mul_oneₓ] using h

@[simp]
theorem mul_div_cancel a {b : Ordinal} (b0 : b ≠ 0) : b * a / b = a := by
  simpa only [add_zeroₓ, zero_div] using mul_add_div a b0 0

@[simp]
theorem div_one (a : Ordinal) : a / 1 = a := by
  simpa only [one_mulₓ] using mul_div_cancel a Ordinal.one_ne_zero

@[simp]
theorem div_self {a : Ordinal} (h : a ≠ 0) : a / a = 1 := by
  simpa only [mul_oneₓ] using mul_div_cancel 1 h

theorem mul_sub (a b c : Ordinal) : a * (b - c) = a * b - a * c :=
  if a0 : a = 0 then by
    simp only [a0, zero_mul, sub_self]
  else
    eq_of_forall_ge_iff fun d => by
      rw [sub_le, ← le_div a0, sub_le, ← le_div a0, mul_add_div _ a0]

theorem is_limit_add_iff {a b} : IsLimit (a + b) ↔ IsLimit b ∨ b = 0 ∧ IsLimit a := by
  constructor <;> intro h
  · by_cases' h' : b = 0
    · rw [h', add_zeroₓ] at h
      right
      exact ⟨h', h⟩
      
    left
    rw [← add_sub_cancel a b]
    apply sub_is_limit h
    suffices : a + 0 < a + b
    simpa only [add_zeroₓ]
    rwa [add_lt_add_iff_left, Ordinal.pos_iff_ne_zero]
    
  rcases h with (h | ⟨rfl, h⟩)
  exact add_is_limit a h
  simpa only [add_zeroₓ]

theorem dvd_add_iff : ∀ {a b c : Ordinal}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
  | a, _, c, ⟨b, rfl⟩ =>
    ⟨fun ⟨d, e⟩ =>
      ⟨d - b, by
        rw [mul_sub, ← e, add_sub_cancel]⟩,
      fun ⟨d, e⟩ => by
      rw [e, ← mul_addₓ]
      apply dvd_mul_right⟩

theorem dvd_add {a b c : Ordinal} (h₁ : a ∣ b) : a ∣ c → a ∣ b + c :=
  (dvd_add_iff h₁).2

theorem dvd_zero (a : Ordinal) : a ∣ 0 :=
  ⟨_, (mul_zero _).symm⟩

theorem zero_dvd {a : Ordinal} : 0 ∣ a ↔ a = 0 :=
  ⟨fun ⟨h, e⟩ => by
    simp only [e, zero_mul], fun e => e.symm ▸ dvd_zero _⟩

theorem one_dvd (a : Ordinal) : 1 ∣ a :=
  ⟨a, (one_mulₓ _).symm⟩

theorem div_mul_cancel : ∀ {a b : Ordinal}, a ≠ 0 → a ∣ b → a * (b / a) = b
  | a, _, a0, ⟨b, rfl⟩ => by
    rw [mul_div_cancel _ a0]

theorem le_of_dvd : ∀ {a b : Ordinal}, b ≠ 0 → a ∣ b → a ≤ b
  | a, _, b0, ⟨b, rfl⟩ => by
    simpa only [mul_oneₓ] using
      mul_le_mul_left'
        (one_le_iff_ne_zero.2 fun h : b = 0 => by
          simpa only [h, mul_zero] using b0)
        a

theorem dvd_antisymm {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
  if a0 : a = 0 then by
    subst a <;> exact (zero_dvd.1 h₁).symm
  else
    if b0 : b = 0 then by
      subst b <;> exact zero_dvd.1 h₂
    else le_antisymmₓ (le_of_dvd b0 h₁) (le_of_dvd a0 h₂)

/-- `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
instance : Mod Ordinal :=
  ⟨fun a b => a - b * (a / b)⟩

theorem mod_def (a b : Ordinal) : a % b = a - b * (a / b) :=
  rfl

@[simp]
theorem mod_zero (a : Ordinal) : a % 0 = a := by
  simp only [mod_def, div_zero, zero_mul, sub_zero]

theorem mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b = a := by
  simp only [mod_def, div_eq_zero_of_lt h, mul_zero, sub_zero]

@[simp]
theorem zero_mod (b : Ordinal) : 0 % b = 0 := by
  simp only [mod_def, zero_div, mul_zero, sub_self]

theorem div_add_mod (a b : Ordinal) : b * (a / b) + a % b = a :=
  Ordinal.add_sub_cancel_of_le <| mul_div_le _ _

theorem mod_lt a {b : Ordinal} (h : b ≠ 0) : a % b < b :=
  (add_lt_add_iff_left (b * (a / b))).1 <| by
    rw [div_add_mod] <;> exact lt_mul_div_add a h

@[simp]
theorem mod_self (a : Ordinal) : a % a = 0 :=
  if a0 : a = 0 then by
    simp only [a0, zero_mod]
  else by
    simp only [mod_def, div_self a0, mul_oneₓ, sub_self]

@[simp]
theorem mod_one (a : Ordinal) : a % 1 = 0 := by
  simp only [mod_def, div_one, one_mulₓ, sub_self]

theorem dvd_of_mod_eq_zero {a b : Ordinal} (H : a % b = 0) : b ∣ a :=
  ⟨a / b, by
    simpa [H] using (div_add_mod a b).symm⟩

theorem mod_eq_zero_of_dvd {a b : Ordinal} (H : b ∣ a) : a % b = 0 := by
  rcases H with ⟨c, rfl⟩
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
    
  · simp [mod_def, hb]
    

theorem dvd_iff_mod_eq_zero {a b : Ordinal} : b ∣ a ↔ a % b = 0 :=
  ⟨mod_eq_zero_of_dvd, dvd_of_mod_eq_zero⟩

/-! ### Families of ordinals

There are two kinds of indexed families that naturally arise when dealing with ordinals: those
indexed by some type in the appropriate universe, and those indexed by ordinals less than another.
The following API allows one to convert from one kind of family to the other.

In many cases, this makes it easy to prove claims about one kind of family via the corresponding
claim on the other. -/


/-- Converts a family indexed by a `Type u` to one indexed by an `ordinal.{u}` using a specified
well-ordering. -/
def bfamilyOfFamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) : ∀, ∀ a < type r, ∀, α :=
  fun a ha => f (enum r a ha)

/-- Converts a family indexed by a `Type u` to one indexed by an `ordinal.{u}` using a well-ordering
given by the axiom of choice. -/
def bfamilyOfFamily {ι : Type u} : (ι → α) → ∀, ∀ a < type (@WellOrderingRel ι), ∀, α :=
  bfamilyOfFamily' WellOrderingRel

/-- Converts a family indexed by an `ordinal.{u}` to one indexed by an `Type u` using a specified
well-ordering. -/
def familyOfBfamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o) (f : ∀, ∀ a < o, ∀, α) :
    ι → α := fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)

/-- Converts a family indexed by an `ordinal.{u}` to one indexed by a `Type u` using a well-ordering
given by the axiom of choice. -/
def familyOfBfamily (o : Ordinal) (f : ∀, ∀ a < o, ∀, α) : o.out.α → α :=
  familyOfBfamily' o.out.R (type_out o) f

@[simp]
theorem bfamily_of_family'_typein {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) i :
    bfamilyOfFamily' r f (typein r i) (typein_lt_type r i) = f i := by
  simp only [bfamily_of_family', enum_typein]

@[simp]
theorem bfamily_of_family_typein {ι} (f : ι → α) i : bfamilyOfFamily f (typein _ i) (typein_lt_type _ i) = f i :=
  bfamily_of_family'_typein _ f i

@[simp]
theorem family_of_bfamily'_enum {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀, ∀ a < o, ∀, α) i hi :
    familyOfBfamily' r ho f
        (enum r i
          (by
            rwa [ho])) =
      f i hi :=
  by
  simp only [family_of_bfamily', typein_enum]

@[simp]
theorem family_of_bfamily_enum (o : Ordinal) (f : ∀, ∀ a < o, ∀, α) i hi :
    familyOfBfamily o f
        (enum o.out.R i
          (by
            convert hi
            exact type_out _)) =
      f i hi :=
  family_of_bfamily'_enum _ (type_out o) f _ _

/-- The range of a family indexed by ordinals. -/
def Brange (o : Ordinal) (f : ∀, ∀ a < o, ∀, α) : Set α :=
  { a | ∃ i hi, f i hi = a }

theorem mem_brange {o : Ordinal} {f : ∀, ∀ a < o, ∀, α} {a} : a ∈ Brange o f ↔ ∃ i hi, f i hi = a :=
  Iff.rfl

theorem mem_brange_self {o} (f : ∀, ∀ a < o, ∀, α) i hi : f i hi ∈ Brange o f :=
  ⟨i, hi, rfl⟩

@[simp]
theorem range_family_of_bfamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀, ∀ a < o, ∀, α) : Range (familyOfBfamily' r ho f) = Brange o f := by
  refine' Set.ext fun a => ⟨_, _⟩
  · rintro ⟨b, rfl⟩
    apply mem_brange_self
    
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, family_of_bfamily'_enum _ _ _ _ _⟩
    

@[simp]
theorem range_family_of_bfamily {o} (f : ∀, ∀ a < o, ∀, α) : Range (familyOfBfamily o f) = Brange o f :=
  range_family_of_bfamily' _ _ f

@[simp]
theorem brange_bfamily_of_family' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) :
    Brange _ (bfamilyOfFamily' r f) = Range f := by
  refine' Set.ext fun a => ⟨_, _⟩
  · rintro ⟨i, hi, rfl⟩
    apply mem_range_self
    
  · rintro ⟨b, rfl⟩
    exact ⟨_, _, bfamily_of_family'_typein _ _ _⟩
    

@[simp]
theorem brange_bfamily_of_family {ι : Type u} (f : ι → α) : Brange _ (bfamilyOfFamily f) = Range f :=
  brange_bfamily_of_family' _ _

theorem comp_bfamily_of_family' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → α) (g : α → β) :
    (fun i hi => g (bfamilyOfFamily' r f i hi)) = bfamilyOfFamily' r (g ∘ f) :=
  rfl

theorem comp_bfamily_of_family {ι : Type u} (f : ι → α) (g : α → β) :
    (fun i hi => g (bfamilyOfFamily f i hi)) = bfamilyOfFamily (g ∘ f) :=
  rfl

theorem comp_family_of_bfamily' {ι : Type u} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : ∀, ∀ a < o, ∀, α) (g : α → β) : g ∘ familyOfBfamily' r ho f = familyOfBfamily' r ho fun i hi => g (f i hi) :=
  rfl

theorem comp_family_of_bfamily {o} (f : ∀, ∀ a < o, ∀, α) (g : α → β) :
    g ∘ familyOfBfamily o f = familyOfBfamily o fun i hi => g (f i hi) :=
  rfl

/-! ### Supremum of a family of ordinals -/


/-- The supremum of a family of ordinals -/
def sup {ι : Type u} (f : ι → Ordinal.{max u v}) : Ordinal.{max u v} :=
  inf { c | ∀ i, f i ≤ c }

/-- The set in the definition of the supremum is nonempty. -/
theorem sup_nonempty {ι : Type u} {f : ι → Ordinal.{max u v}} : { c | ∀ i, f i ≤ c }.Nonempty :=
  ⟨(Cardinal.sup.{u, v} (Cardinal.succ ∘ card ∘ f)).ord, fun i =>
    le_of_ltₓ <| Cardinal.lt_ord.2 ((Cardinal.lt_succ_self _).trans_le (le_sup _ _))⟩

theorem le_sup {ι} (f : ι → Ordinal) : ∀ i, f i ≤ sup f :=
  Inf_mem sup_nonempty

theorem sup_le {ι} {f : ι → Ordinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
  ⟨fun h i => le_transₓ (le_sup _ _) h, fun h => cInf_le' h⟩

theorem lt_sup {ι} {f : ι → Ordinal} {a} : a < sup f ↔ ∃ i, a < f i := by
  simpa only [not_forall, not_leₓ] using not_congr (@sup_le _ f a)

theorem lt_sup_of_ne_sup {ι} {f : ι → Ordinal} : (∀ i, f i ≠ sup f) ↔ ∀ i, f i < sup f :=
  ⟨fun hf _ => lt_of_le_of_neₓ (le_sup _ _) (hf _), fun hf _ => ne_of_ltₓ (hf _)⟩

-- ././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'
theorem sup_not_succ_of_ne_sup {ι} {f : ι → Ordinal} (hf : ∀ i, f i ≠ sup f) {a} (hao : a < sup f) : succ a < sup f :=
  by
  "././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'"
  exact hao.not_le (sup_le.2 fun i => lt_succ.1 ((lt_of_le_of_neₓ (le_sup _ _) (hf i)).trans_le hoa))

@[simp]
theorem sup_eq_zero_iff {ι} {f : ι → Ordinal} : sup f = 0 ↔ ∀ i, f i = 0 := by
  refine' ⟨fun h i => _, fun h => le_antisymmₓ (sup_le.2 fun i => Ordinal.le_zero.2 (h i)) (Ordinal.zero_le _)⟩
  rw [← Ordinal.le_zero, ← h]
  exact le_sup f i

theorem IsNormal.sup {f} (H : IsNormal f) {ι} {g : ι → Ordinal} (h : Nonempty ι) : f (sup g) = sup (f ∘ g) :=
  eq_of_forall_ge_iff fun a => by
    rw [sup_le, comp,
        H.le_set' (fun _ : ι => True) g
          (let ⟨i⟩ := h
          ⟨i, ⟨⟩⟩)] <;>
      intros <;> simp only [sup_le, true_implies_iff] <;> tauto

theorem sup_empty {ι} [IsEmpty ι] (f : ι → Ordinal) : sup f = 0 :=
  sup_eq_zero_iff.2 isEmptyElim

theorem sup_ord {ι} (f : ι → Cardinal) : (sup fun i => (f i).ord) = (Cardinal.sup f).ord :=
  eq_of_forall_ge_iff fun a => by
    simp only [sup_le, Cardinal.ord_le, Cardinal.sup_le]

theorem sup_const {ι} [hι : Nonempty ι] (o : Ordinal) : (sup fun _ : ι => o) = o :=
  le_antisymmₓ (sup_le.2 fun _ => le_rfl) (le_sup _ hι.some)

theorem sup_le_of_range_subset {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal} (h : Set.Range f ⊆ Set.Range g) :
    sup.{u, max v w} f ≤ sup.{v, max u w} g :=
  sup_le.2 fun i =>
    match h (mem_range_self i) with
    | ⟨j, hj⟩ => hj ▸ le_sup _ _

theorem sup_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal} (h : Set.Range f = Set.Range g) :
    sup.{u, max v w} f = sup.{v, max u w} g :=
  (sup_le_of_range_subset h.le).antisymm (sup_le_of_range_subset.{v, u, w} h.Ge)

theorem unbounded_range_of_sup_ge {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ sup.{u, u} (typein r ∘ f)) : Unbounded r (Range f) :=
  (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
    not_lt_of_le h <|
      lt_of_le_of_ltₓ (sup_le.2 fun y => le_of_ltₓ <| (typein_lt_typein r).2 <| hx _ <| mem_range_self y)
        (typein_lt_type r x)

theorem sup_eq_sup {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r] [IsWellOrder ι' r']
    {o : Ordinal.{u}} (ho : type r = o) (ho' : type r' = o) (f : ∀, ∀ a < o, ∀, Ordinal.{max u v}) :
    sup (familyOfBfamily' r ho f) = sup (familyOfBfamily' r' ho' f) :=
  sup_eq_of_range_eq.{u, u, v}
    (by
      simp )

/-- The supremum of a family of ordinals indexed by the set of ordinals less than some
  `o : ordinal.{u}`. This is a special case of `sup` over the family provided by
  `family_of_bfamily`. -/
def bsup (o : Ordinal.{u}) (f : ∀, ∀ a < o, ∀, Ordinal.{max u v}) : Ordinal.{max u v} :=
  sup (familyOfBfamily o f)

theorem bsup_eq_sup {o} (f : ∀, ∀ a < o, ∀, Ordinal) : bsup o f = sup (familyOfBfamily o f) :=
  rfl

theorem bsup_eq_sup' {o ι} (r : ι → ι → Prop) [IsWellOrder ι r] (ho : type r = o) f :
    bsup o f = sup (familyOfBfamily' r ho f) :=
  sup_eq_sup _ r _ ho f

theorem sup_eq_bsup' {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → Ordinal) :
    sup f = bsup _ (bfamilyOfFamily' r f) := by
  simp only [bsup_eq_sup' r, enum_typein, family_of_bfamily', bfamily_of_family']

theorem bsup_eq_bsup {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r'] (f : ι → Ordinal) :
    bsup _ (bfamilyOfFamily' r f) = bsup _ (bfamilyOfFamily' r' f) := by
  rw [← sup_eq_bsup', ← sup_eq_bsup']

theorem sup_eq_bsup {ι} (f : ι → Ordinal) : sup f = bsup _ (bfamilyOfFamily f) :=
  sup_eq_bsup' _ f

theorem bsup_le {o f a} : bsup.{u, v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
  sup_le.trans
    ⟨fun h i hi => by
      rw [← family_of_bfamily_enum o f]
      exact h _, fun h i => h _ _⟩

theorem le_bsup {o} (f : ∀, ∀ a < o, ∀, Ordinal) i h : f i h ≤ bsup o f :=
  bsup_le.1 le_rfl _ _

theorem lt_bsup {o} (f : ∀, ∀ a < o, ∀, Ordinal) {a} : a < bsup o f ↔ ∃ i hi, a < f i hi := by
  simpa only [not_forall, not_leₓ] using not_congr (@bsup_le _ f a)

theorem IsNormal.bsup {f} (H : IsNormal f) {o} :
    ∀ g : ∀, ∀ a < o, ∀, Ordinal h : o ≠ 0, f (bsup o g) = bsup o fun a h => f (g a h) :=
  (induction_on o) fun α r _ g h => by
    skip
    rw [bsup_eq_sup' r, H.sup (type_ne_zero_iff_nonempty.1 h), bsup_eq_sup' r] <;> rfl

theorem lt_bsup_of_ne_bsup {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal} :
    (∀ i h, f i h ≠ o.bsup f) ↔ ∀ i h, f i h < o.bsup f :=
  ⟨fun hf _ _ => lt_of_le_of_neₓ (le_bsup _ _ _) (hf _ _), fun hf _ _ => ne_of_ltₓ (hf _ _)⟩

theorem bsup_not_succ_of_ne_bsup {o} {f : ∀, ∀ a < o, ∀, Ordinal} (hf : ∀ {i : Ordinal} h : i < o, f i h ≠ o.bsup f) a :
    a < bsup o f → succ a < bsup o f := by
  rw [bsup_eq_sup] at *
  exact sup_not_succ_of_ne_sup fun i => hf _

@[simp]
theorem bsup_eq_zero_iff {o} {f : ∀, ∀ a < o, ∀, Ordinal} : bsup o f = 0 ↔ ∀ i hi, f i hi = 0 := by
  refine'
    ⟨fun h i hi => _, fun h => le_antisymmₓ (bsup_le.2 fun i hi => Ordinal.le_zero.2 (h i hi)) (Ordinal.zero_le _)⟩
  rw [← Ordinal.le_zero, ← h]
  exact le_bsup f i hi

theorem lt_bsup_of_limit {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal}
    (hf : ∀ {a a'} ha : a < o ha' : a' < o, a < a' → f a ha < f a' ha') (ho : ∀, ∀ a < o, ∀, succ a < o) i h :
    f i h < bsup o f :=
  (hf _ _ <| lt_succ_self i).trans_le (le_bsup f i.succ <| ho _ h)

theorem bsup_zero {o : Ordinal} (ho : o = 0) (f : ∀, ∀ a < o, ∀, Ordinal) : bsup o f = 0 :=
  bsup_eq_zero_iff.2 fun i hi => by
    subst ho
    exact (Ordinal.not_lt_zero i hi).elim

theorem bsup_const {o : Ordinal} (ho : o ≠ 0) (a : Ordinal) : (bsup o fun _ _ => a) = a :=
  le_antisymmₓ (bsup_le.2 fun _ _ => le_rfl) (le_bsup _ 0 (Ordinal.pos_iff_ne_zero.2 ho))

theorem bsup_le_of_brange_subset {o o'} {f : ∀, ∀ a < o, ∀, Ordinal} {g : ∀, ∀ a < o', ∀, Ordinal}
    (h : Brange o f ⊆ Brange o' g) : bsup.{u, max v w} o f ≤ bsup.{v, max u w} o' g :=
  bsup_le.2 fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

theorem bsup_eq_of_brange_eq {o o'} {f : ∀, ∀ a < o, ∀, Ordinal} {g : ∀, ∀ a < o', ∀, Ordinal}
    (h : Brange o f = Brange o' g) : bsup.{u, max v w} o f = bsup.{v, max u w} o' g :=
  (bsup_le_of_brange_subset h.le).antisymm (bsup_le_of_brange_subset.{v, u, w} h.Ge)

theorem bsup_id_limit {o} (ho : ∀, ∀ a < o, ∀, succ a < o) : (bsup.{u, u} o fun x _ => x) = o :=
  le_antisymmₓ (bsup_le.2 fun i hi => hi.le)
    (not_ltₓ.1 fun h => (lt_bsup_of_limit.{u, u} (fun _ _ _ _ => id) ho _ h).False)

theorem bsup_id_succ o : (bsup.{u, u} (succ o) fun x _ => x) = o :=
  le_antisymmₓ (bsup_le.2 fun o => lt_succ.1) (le_bsup _ o (lt_succ_self o))

theorem IsNormal.bsup_eq {f} (H : IsNormal f) {o : Ordinal} (h : IsLimit o) : (bsup.{u} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup.{u, u} H (fun x _ => x) h.1, bsup_id_limit h.2]

/-- The least strict upper bound of a family of ordinals. -/
def lsub {ι} (f : ι → Ordinal) : Ordinal :=
  sup (Ordinal.succ ∘ f)

theorem lsub_le {ι} {f : ι → Ordinal} {a} : lsub f ≤ a ↔ ∀ i, f i < a := by
  convert sup_le
  simp [succ_le]

theorem lt_lsub {ι} (f : ι → Ordinal) i : f i < lsub f :=
  succ_le.1 (le_sup _ i)

theorem sup_le_lsub {ι} (f : ι → Ordinal) : sup f ≤ lsub f :=
  sup_le.2 fun i => le_of_ltₓ (lt_lsub f i)

theorem lsub_le_sup_succ {ι} (f : ι → Ordinal) : lsub f ≤ succ (sup f) :=
  lsub_le.2 fun i => lt_succ.2 (le_sup f i)

theorem sup_eq_lsub_or_sup_succ_eq_lsub {ι} (f : ι → Ordinal) : sup f = lsub f ∨ (sup f).succ = lsub f := by
  cases eq_or_lt_of_le (sup_le_lsub f)
  · exact Or.inl h
    
  · exact Or.inr ((succ_le.2 h).antisymm (lsub_le_sup_succ f))
    

-- ././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'
theorem sup_succ_le_lsub {ι} (f : ι → Ordinal) : (sup f).succ ≤ lsub f ↔ ∃ i, f i = sup f := by
  refine' ⟨fun h => _, _⟩
  · "././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'"
    exact ne_of_ltₓ (succ_le.1 h) (le_antisymmₓ (sup_le_lsub f) (lsub_le.2 (lt_sup_of_ne_sup.1 hf)))
    
  rintro ⟨_, hf⟩
  rw [succ_le, ← hf]
  exact lt_lsub _ _

theorem sup_succ_eq_lsub {ι} (f : ι → Ordinal) : (sup f).succ = lsub f ↔ ∃ i, f i = sup f :=
  (lsub_le_sup_succ f).le_iff_eq.symm.trans (sup_succ_le_lsub f)

-- ././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'
theorem sup_eq_lsub_iff_succ {ι} (f : ι → Ordinal) : sup f = lsub f ↔ ∀, ∀ a < lsub f, ∀, succ a < lsub f := by
  refine' ⟨fun h => _, fun hf => le_antisymmₓ (sup_le_lsub f) (lsub_le.2 fun i => _)⟩
  · rw [← h]
    exact fun a => sup_not_succ_of_ne_sup fun i => ne_of_ltₓ (lsub_le.1 (le_of_eqₓ h.symm) i)
    
  "././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'"
  have heq := (sup_succ_eq_lsub f).2 ⟨i, le_antisymmₓ (le_sup _ _) hle⟩
  have :=
    hf (sup f)
      (by
        rw [← HEq]
        exact lt_succ_self _)
  rw [HEq] at this
  exact this.false

theorem sup_eq_lsub_iff_lt_sup {ι} (f : ι → Ordinal) : sup f = lsub f ↔ ∀ i, f i < sup f :=
  ⟨fun h i => by
    rw [h]
    apply lt_lsub, fun h => le_antisymmₓ (sup_le_lsub f) (lsub_le.2 h)⟩

theorem lsub_empty {ι} [h : IsEmpty ι] (f : ι → Ordinal) : lsub f = 0 := by
  rw [← Ordinal.le_zero, lsub_le]
  exact h.elim

theorem lsub_pos {ι} [h : Nonempty ι] (f : ι → Ordinal) : 0 < lsub f :=
  h.elim fun i => (Ordinal.zero_le _).trans_lt (lt_lsub f i)

@[simp]
theorem lsub_eq_zero_iff {ι} {f : ι → Ordinal} : lsub f = 0 ↔ IsEmpty ι := by
  refine' ⟨fun h => ⟨fun i => _⟩, fun h => @lsub_empty _ h _⟩
  have := @lsub_pos _ ⟨i⟩ f
  rw [h] at this
  exact this.false

theorem lsub_const {ι} [hι : Nonempty ι] (o : Ordinal) : (lsub fun _ : ι => o) = o + 1 :=
  sup_const o.succ

theorem lsub_le_of_range_subset {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal} (h : Set.Range f ⊆ Set.Range g) :
    lsub f ≤ lsub g :=
  sup_le_of_range_subset
    (by
      convert Set.image_subset _ h <;> apply Set.range_comp)

theorem lsub_eq_of_range_eq {ι ι'} {f : ι → Ordinal} {g : ι' → Ordinal} (h : Set.Range f = Set.Range g) :
    lsub f = lsub g :=
  (lsub_le_of_range_subset h.le).antisymm (lsub_le_of_range_subset h.Ge)

theorem lsub_nmem_range {ι} (f : ι → Ordinal) : lsub f ∉ Set.Range f := fun ⟨i, h⟩ => h.not_lt (lt_lsub f i)

/-- The bounded least strict upper bound of a family of ordinals. -/
def blsub (o : Ordinal.{u}) (f : ∀, ∀ a < o, ∀, Ordinal.{max u v}) : Ordinal.{max u v} :=
  o.bsup fun a ha => (f a ha).succ

theorem blsub_eq_lsub' {ι} (r : ι → ι → Prop) [IsWellOrder ι r] {o} (ho : type r = o) f :
    blsub o f = lsub (familyOfBfamily' r ho f) :=
  bsup_eq_sup' r ho _

theorem lsub_eq_lsub {ι ι' : Type u} (r : ι → ι → Prop) (r' : ι' → ι' → Prop) [IsWellOrder ι r] [IsWellOrder ι' r'] {o}
    (ho : type r = o) (ho' : type r' = o) (f : ∀, ∀ a < o, ∀, Ordinal) :
    lsub (familyOfBfamily' r ho f) = lsub (familyOfBfamily' r' ho' f) := by
  rw [← blsub_eq_lsub', ← blsub_eq_lsub']

theorem blsub_eq_lsub {o} (f : ∀, ∀ a < o, ∀, Ordinal) : blsub o f = lsub (familyOfBfamily o f) :=
  bsup_eq_sup _

theorem lsub_eq_blsub' {ι} (r : ι → ι → Prop) [IsWellOrder ι r] (f : ι → Ordinal) :
    lsub f = blsub _ (bfamilyOfFamily' r f) :=
  sup_eq_bsup' r _

theorem blsub_eq_blsub {ι : Type u} (r r' : ι → ι → Prop) [IsWellOrder ι r] [IsWellOrder ι r'] (f : ι → Ordinal) :
    blsub _ (bfamilyOfFamily' r f) = blsub _ (bfamilyOfFamily' r' f) := by
  rw [← lsub_eq_blsub', ← lsub_eq_blsub']

theorem lsub_eq_blsub {ι} (f : ι → Ordinal) : lsub f = blsub _ (bfamilyOfFamily f) :=
  sup_eq_bsup _

theorem blsub_le {o f a} : blsub o f ≤ a ↔ ∀ i h, f i h < a := by
  convert bsup_le
  apply propext
  simp [succ_le]

theorem lt_blsub {o} (f : ∀, ∀ a < o, ∀, Ordinal) i h : f i h < blsub o f :=
  blsub_le.1 le_rfl _ _

theorem bsup_le_blsub {o} (f : ∀, ∀ a < o, ∀, Ordinal) : bsup o f ≤ blsub o f :=
  bsup_le.2 fun i h => le_of_ltₓ (lt_blsub f i h)

theorem blsub_le_bsup_succ {o} (f : ∀, ∀ a < o, ∀, Ordinal) : blsub o f ≤ (bsup o f).succ :=
  blsub_le.2 fun i h => lt_succ.2 (le_bsup f i h)

theorem bsup_eq_blsub_or_succ_bsup_eq_blsub {o} (f : ∀, ∀ a < o, ∀, Ordinal) :
    bsup o f = blsub o f ∨ succ (bsup o f) = blsub o f := by
  rw [bsup_eq_sup, blsub_eq_lsub]
  exact sup_eq_lsub_or_sup_succ_eq_lsub _

-- ././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'
theorem bsup_succ_le_blsub {o} (f : ∀, ∀ a < o, ∀, Ordinal) : (bsup o f).succ ≤ blsub o f ↔ ∃ i hi, f i hi = bsup o f :=
  by
  refine' ⟨fun h => _, _⟩
  · "././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'"
    exact ne_of_ltₓ (succ_le.1 h) (le_antisymmₓ (bsup_le_blsub f) (blsub_le.2 (lt_bsup_of_ne_bsup.1 hf)))
    
  rintro ⟨_, _, hf⟩
  rw [succ_le, ← hf]
  exact lt_blsub _ _ _

theorem bsup_succ_eq_blsub {o} (f : ∀, ∀ a < o, ∀, Ordinal) : (bsup o f).succ = blsub o f ↔ ∃ i hi, f i hi = bsup o f :=
  (blsub_le_bsup_succ f).le_iff_eq.symm.trans (bsup_succ_le_blsub f)

theorem bsup_eq_blsub_iff_succ {o} (f : ∀, ∀ a < o, ∀, Ordinal) :
    bsup o f = blsub o f ↔ ∀, ∀ a < blsub o f, ∀, succ a < blsub o f := by
  rw [bsup_eq_sup, blsub_eq_lsub]
  apply sup_eq_lsub_iff_succ

theorem bsup_eq_blsub_iff_lt_bsup {o} (f : ∀, ∀ a < o, ∀, Ordinal) : bsup o f = blsub o f ↔ ∀ i hi, f i hi < bsup o f :=
  ⟨fun h i => by
    rw [h]
    apply lt_blsub, fun h => le_antisymmₓ (bsup_le_blsub f) (blsub_le.2 h)⟩

@[simp]
theorem blsub_eq_zero_iff {o} {f : ∀, ∀ a < o, ∀, Ordinal} : blsub o f = 0 ↔ o = 0 := by
  rw [blsub_eq_lsub, lsub_eq_zero_iff]
  exact out_empty_iff_eq_zero

theorem blsub_zero {o : Ordinal} (ho : o = 0) (f : ∀, ∀ a < o, ∀, Ordinal) : blsub o f = 0 := by
  rwa [blsub_eq_zero_iff]

theorem blsub_pos {o : Ordinal} (ho : 0 < o) (f : ∀, ∀ a < o, ∀, Ordinal) : 0 < blsub o f :=
  (Ordinal.zero_le _).trans_lt (lt_blsub f 0 ho)

theorem blsub_type (r : α → α → Prop) [IsWellOrder α r] f :
    blsub (type r) f = lsub fun a => f (typein r a) (typein_lt_type _ _) :=
  eq_of_forall_ge_iff fun o => by
    rw [blsub_le, lsub_le] <;>
      exact
        ⟨fun H b => H _ _, fun H i h => by
          simpa only [typein_enum] using H (enum r i h)⟩

theorem blsub_const {o : Ordinal} (ho : o ≠ 0) (a : Ordinal) : (blsub.{u, v} o fun _ _ => a) = a + 1 :=
  bsup_const.{u, v} ho a.succ

-- ././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'
theorem blsub_id o : (blsub.{u, u} o fun x _ => x) = o := by
  apply le_antisymmₓ
  · rw [blsub_le]
    exact fun _ => id
    
  "././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'"
  exact (lt_blsub.{u, u} (fun x _ => x) _ h).False

theorem blsub_le_of_brange_subset {o o'} {f : ∀, ∀ a < o, ∀, Ordinal} {g : ∀, ∀ a < o', ∀, Ordinal}
    (h : Brange o f ⊆ Brange o' g) : blsub.{u, max v w} o f ≤ blsub.{v, max u w} o' g :=
  bsup_le_of_brange_subset fun a ⟨b, hb, hb'⟩ => by
    obtain ⟨c, hc, hc'⟩ := h ⟨b, hb, rfl⟩
    simp_rw [← hc']  at hb'
    exact ⟨c, hc, hb'⟩

theorem blsub_eq_of_brange_eq {o o'} {f : ∀, ∀ a < o, ∀, Ordinal} {g : ∀, ∀ a < o', ∀, Ordinal}
    (h : { o | ∃ i hi, f i hi = o } = { o | ∃ i hi, g i hi = o }) : blsub.{u, max v w} o f = blsub.{v, max u w} o' g :=
  (blsub_le_of_brange_subset h.le).antisymm (blsub_le_of_brange_subset.{v, u, w} h.Ge)

theorem lsub_typein (o : Ordinal) : lsub.{u, u} (typein o.out.R) = o := by
  have := blsub_id o
  rwa [blsub_eq_lsub] at this

theorem sup_typein_limit {o : Ordinal} (ho : ∀ a, a < o → succ a < o) : sup.{u, u} (typein o.out.R) = o := by
  rw [(sup_eq_lsub_iff_succ.{u, u} (typein o.out.r)).2] <;> rwa [lsub_typein o]

theorem sup_typein_succ (o : Ordinal) : sup.{u, u} (typein o.succ.out.R) = o := by
  cases' sup_eq_lsub_or_sup_succ_eq_lsub.{u, u} (typein o.succ.out.r) with h h
  · rw [sup_eq_lsub_iff_succ] at h
    simp only [lsub_typein] at h
    exact (h o (lt_succ_self o)).False.elim
    
  rw [← succ_inj, h]
  exact lsub_typein _

end Ordinal

/-! ### Results about injectivity and surjectivity -/


theorem not_surjective_of_ordinal {α : Type u} (f : α → Ordinal.{u}) : ¬Function.Surjective f := fun h =>
  Ordinal.lsub_nmem_range.{u, u} f (h _)

theorem not_injective_of_ordinal {α : Type u} (f : Ordinal.{u} → α) : ¬Function.Injective f := fun h =>
  not_surjective_of_ordinal _ (inv_fun_surjectiveₓ h)

theorem not_surjective_of_ordinal_of_small {α : Type v} [Small.{u} α] (f : α → Ordinal.{u}) : ¬Function.Surjective f :=
  fun h => not_surjective_of_ordinal _ (h.comp (equivShrink _).symm.Surjective)

theorem not_injective_of_ordinal_of_small {α : Type v} [Small.{u} α] (f : Ordinal.{u} → α) : ¬Function.Injective f :=
  fun h => not_injective_of_ordinal _ ((equivShrink _).Injective.comp h)

/-- The type of ordinals in universe `u` is not `small.{u}`. This is the type-theoretic analog of
the Burali-Forti paradox. -/
theorem not_small_ordinal : ¬Small.{u} Ordinal.{max u v} := fun h =>
  @not_injective_of_ordinal_of_small _ h _ fun a b => Ordinal.lift_inj.1

/-! ### Enumerating unbounded sets of ordinals with ordinals -/


namespace Ordinal

section

variable {S : Set Ordinal.{u}}

/-- Enumerator function for an unbounded set of ordinals. -/
def enumOrd (S : Set Ordinal.{u}) : Ordinal → Ordinal :=
  wf.fix fun o f => inf (S ∩ Set.Ici (blsub.{u, u} o f))

/-- The equation that characterizes `enum_ord` definitionally. This isn't the nicest expression to
    work with, so consider using `enum_ord_def` instead. -/
theorem enum_ord_def' o : enumOrd S o = inf (S ∩ Set.Ici (blsub.{u, u} o fun a _ => enumOrd S a)) :=
  wf.fix_eq _ _

/-- The set in `enum_ord_def'` is nonempty. -/
theorem enum_ord_def'_nonempty (hS : Unbounded (· < ·) S) a : (S ∩ Set.Ici a).Nonempty :=
  let ⟨b, hb, hb'⟩ := hS a
  ⟨b, hb, le_of_not_gtₓ hb'⟩

private theorem enum_ord_mem_aux (hS : Unbounded (· < ·) S) o :
    enumOrd S o ∈ S ∩ Set.Ici (blsub.{u, u} o fun c _ => enumOrd S c) := by
  rw [enum_ord_def']
  exact Inf_mem (enum_ord_def'_nonempty hS _)

theorem enum_ord_mem (hS : Unbounded (· < ·) S) o : enumOrd S o ∈ S :=
  (enum_ord_mem_aux hS o).left

theorem blsub_le_enum_ord (hS : Unbounded (· < ·) S) o : (blsub.{u, u} o fun c _ => enumOrd S c) ≤ enumOrd S o :=
  (enum_ord_mem_aux hS o).right

theorem enumOrd.strict_mono (hS : Unbounded (· < ·) S) : StrictMono (enumOrd S) := fun _ _ h =>
  (lt_blsub.{u, u} _ _ h).trans_le (blsub_le_enum_ord hS _)

/-- A more workable definition for `enum_ord`. -/
theorem enum_ord_def o : enumOrd S o = inf (S ∩ { b | ∀ c, c < o → enumOrd S c < b }) := by
  rw [enum_ord_def']
  congr
  ext
  exact ⟨fun h a hao => (lt_blsub.{u, u} _ _ hao).trans_le h, fun h => blsub_le.2 h⟩

/-- The set in `enum_ord_def` is nonempty. -/
theorem enum_ord_def_nonempty (hS : Unbounded (· < ·) S) {o} : { x | x ∈ S ∧ ∀ c, c < o → enumOrd S c < x }.Nonempty :=
  ⟨_, enum_ord_mem hS o, fun _ b => enumOrd.strict_mono hS b⟩

@[simp]
theorem enum_ord_zero : enumOrd S 0 = inf S := by
  rw [enum_ord_def]
  simp [Ordinal.not_lt_zero]

theorem enum_ord_zero_le {a} (ha : a ∈ S) : enumOrd S 0 ≤ a := by
  rw [enum_ord_zero]
  exact cInf_le' ha

theorem enum_ord_succ_le {a b} (hS : Unbounded (· < ·) S) (ha : a ∈ S) (hb : enumOrd S b < a) : enumOrd S b.succ ≤ a :=
  by
  rw [enum_ord_def]
  exact cInf_le' ⟨ha, fun c hc => ((enum_ord.strict_mono hS).Monotone (lt_succ.1 hc)).trans_lt hb⟩

-- ././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'
theorem enumOrd.surjective (hS : Unbounded (· < ·) S) : ∀, ∀ s ∈ S, ∀, ∃ a, enumOrd S a = s := fun s hs =>
  ⟨sup { a | enumOrd S a ≤ s }, by
    apply le_antisymmₓ
    · rw [enum_ord_def]
      apply cInf_le'
      use hs
      intro a ha
      rcases exists_lt_of_lt_cSup ⟨0, enum_ord_zero_le hs⟩ ha with ⟨b, hb, hab⟩
      exact (enum_ord.strict_mono hS hab).trans_le hb
      
    · "././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'"
      exact
        (le_cSup ⟨s, fun a => (WellFounded.self_le_of_strict_mono wf (enum_ord.strict_mono hS) a).trans⟩
              (enum_ord_succ_le hS hs h)).not_lt
          (lt_succ_self _)
      ⟩

/-- An order isomorphism between an unbounded set of ordinals and the ordinals. -/
def enumOrd.orderIso (hS : Unbounded (· < ·) S) : Ordinal ≃o S :=
  StrictMono.orderIsoOfSurjective (fun o => ⟨_, enum_ord_mem hS o⟩) (enumOrd.strict_mono hS) fun s =>
    let ⟨a, ha⟩ := enumOrd.surjective hS s s.Prop
    ⟨a, Subtype.eq ha⟩

theorem enum_ord_range (hS : Unbounded (· < ·) S) : Range (enumOrd S) = S := by
  rw [range_eq_iff]
  exact ⟨enum_ord_mem hS, enum_ord.surjective hS⟩

/-- A characterization of `enum_ord`: it is the unique strict monotonic function with range `S`. -/
theorem eq_enum_ord (f : Ordinal → Ordinal) (hS : Unbounded (· < ·) S) : StrictMono f ∧ Range f = S ↔ f = enumOrd S :=
  by
  constructor
  · rintro ⟨h₁, h₂⟩
    rwa [← wf.eq_strict_mono_iff_eq_range h₁ (enum_ord.strict_mono hS), enum_ord_range hS]
    
  · rintro rfl
    exact ⟨enum_ord.strict_mono hS, enum_ord_range hS⟩
    

end

/-! ### Ordinal exponential -/


/-- The ordinal exponential, defined by transfinite recursion. -/
def opow (a b : Ordinal) : Ordinal :=
  if a = 0 then 1 - b else limitRecOn b 1 (fun _ IH => IH * a) fun b _ => bsup.{u, u} b

instance : Pow Ordinal Ordinal :=
  ⟨opow⟩

-- mathport name: «expr ^ »
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

theorem zero_opow' (a : Ordinal) : (0^a) = 1 - a := by
  simp only [pow, opow, if_pos rfl]

@[simp]
theorem zero_opow {a : Ordinal} (a0 : a ≠ 0) : (0^a) = 0 := by
  rwa [zero_opow', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]
theorem opow_zero (a : Ordinal) : (a^0) = 1 := by
  by_cases' a = 0 <;> [simp only [pow, opow, if_pos h, sub_zero], simp only [pow, opow, if_neg h, limit_rec_on_zero]]

@[simp]
theorem opow_succ (a b : Ordinal) : (a^succ b) = (a^b) * a :=
  if h : a = 0 then by
    subst a <;> simp only [zero_opow (succ_ne_zero _), mul_zero]
  else by
    simp only [pow, opow, limit_rec_on_succ, if_neg h]

theorem opow_limit {a b : Ordinal} (a0 : a ≠ 0) (h : IsLimit b) : (a^b) = bsup.{u, u} b fun c _ => a^c := by
  simp only [pow, opow, if_neg a0] <;> rw [limit_rec_on_limit _ _ _ _ h] <;> rfl

theorem opow_le_of_limit {a b c : Ordinal} (a0 : a ≠ 0) (h : IsLimit b) : (a^b) ≤ c ↔ ∀, ∀ b' < b, ∀, (a^b') ≤ c := by
  rw [opow_limit a0 h, bsup_le]

theorem lt_opow_of_limit {a b c : Ordinal} (b0 : b ≠ 0) (h : IsLimit c) : a < (b^c) ↔ ∃ c' < c, a < (b^c') := by
  rw [← not_iff_not, not_exists] <;> simp only [not_ltₓ, opow_le_of_limit b0 h, exists_prop, not_and]

@[simp]
theorem opow_one (a : Ordinal) : (a^1) = a := by
  rw [← succ_zero, opow_succ] <;> simp only [opow_zero, one_mulₓ]

@[simp]
theorem one_opow (a : Ordinal) : (1^a) = 1 := by
  apply limit_rec_on a
  · simp only [opow_zero]
    
  · intro _ ih
    simp only [opow_succ, ih, mul_oneₓ]
    
  refine' fun b l IH => eq_of_forall_ge_iff fun c => _
  rw [opow_le_of_limit Ordinal.one_ne_zero l]
  exact
    ⟨fun H => by
      simpa only [opow_zero] using H 0 l.pos, fun H b' h => by
      rwa [IH _ h]⟩

theorem opow_pos {a : Ordinal} b (a0 : 0 < a) : 0 < (a^b) := by
  have h0 : 0 < (a^0) := by
    simp only [opow_zero, zero_lt_one]
  apply limit_rec_on b
  · exact h0
    
  · intro b IH
    rw [opow_succ]
    exact mul_pos IH a0
    
  · exact fun b l _ => (lt_opow_of_limit (Ordinal.pos_iff_ne_zero.1 a0) l).2 ⟨0, l.Pos, h0⟩
    

theorem opow_ne_zero {a : Ordinal} b (a0 : a ≠ 0) : (a^b) ≠ 0 :=
  Ordinal.pos_iff_ne_zero.1 <| opow_pos b <| Ordinal.pos_iff_ne_zero.2 a0

theorem opow_is_normal {a : Ordinal} (h : 1 < a) : IsNormal ((·^·) a) :=
  have a0 : 0 < a := lt_transₓ zero_lt_one h
  ⟨fun b => by
    simpa only [mul_oneₓ, opow_succ] using (mul_lt_mul_iff_left (opow_pos b a0)).2 h, fun b l c =>
    opow_le_of_limit (ne_of_gtₓ a0) l⟩

theorem opow_lt_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) < (a^c) ↔ b < c :=
  (opow_is_normal a1).lt_iff

theorem opow_le_opow_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) ≤ (a^c) ↔ b ≤ c :=
  (opow_is_normal a1).le_iff

theorem opow_right_inj {a b c : Ordinal} (a1 : 1 < a) : (a^b) = (a^c) ↔ b = c :=
  (opow_is_normal a1).inj

theorem opow_is_limit {a b : Ordinal} (a1 : 1 < a) : IsLimit b → IsLimit (a^b) :=
  (opow_is_normal a1).IsLimit

theorem opow_is_limit_left {a b : Ordinal} (l : IsLimit a) (hb : b ≠ 0) : IsLimit (a^b) := by
  rcases zero_or_succ_or_limit b with (e | ⟨b, rfl⟩ | l')
  · exact absurd e hb
    
  · rw [opow_succ]
    exact mul_is_limit (opow_pos _ l.pos) l
    
  · exact opow_is_limit l.one_lt l'
    

theorem opow_le_opow_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : (a^b) ≤ (a^c) := by
  cases' lt_or_eq_of_leₓ (one_le_iff_pos.2 h₁) with h₁ h₁
  · exact (opow_le_opow_iff_right h₁).2 h₂
    
  · subst a
    simp only [one_opow]
    

theorem opow_le_opow_left {a b : Ordinal} c (ab : a ≤ b) : (a^c) ≤ (b^c) := by
  by_cases' a0 : a = 0
  · subst a
    by_cases' c0 : c = 0
    · subst c
      simp only [opow_zero]
      
    · simp only [zero_opow c0, Ordinal.zero_le]
      
    
  · apply limit_rec_on c
    · simp only [opow_zero]
      
    · intro c IH
      simpa only [opow_succ] using mul_le_mul' IH ab
      
    · exact fun c l IH =>
        (opow_le_of_limit a0 l).2 fun b' h =>
          le_transₓ (IH _ h) (opow_le_opow_right (lt_of_lt_of_leₓ (Ordinal.pos_iff_ne_zero.2 a0) ab) (le_of_ltₓ h))
      
    

theorem le_opow_self {a : Ordinal} b (a1 : 1 < a) : b ≤ (a^b) :=
  (opow_is_normal a1).self_le _

theorem opow_lt_opow_left_of_succ {a b c : Ordinal} (ab : a < b) : (a^succ c) < (b^succ c) := by
  rw [opow_succ, opow_succ] <;>
    exact
      (mul_le_mul_right' (opow_le_opow_left _ (le_of_ltₓ ab)) a).trans_lt
        (mul_lt_mul_of_pos_left ab (opow_pos _ (lt_of_le_of_ltₓ (Ordinal.zero_le _) ab)))

theorem opow_add (a b c : Ordinal) : (a^b + c) = (a^b) * (a^c) := by
  by_cases' a0 : a = 0
  · subst a
    by_cases' c0 : c = 0
    · simp only [c0, add_zeroₓ, opow_zero, mul_oneₓ]
      
    have : b + c ≠ 0 := ne_of_gtₓ (lt_of_lt_of_leₓ (Ordinal.pos_iff_ne_zero.2 c0) (le_add_left _ _))
    simp only [zero_opow c0, zero_opow this, mul_zero]
    
  cases' eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1
  · subst a1
    simp only [one_opow, mul_oneₓ]
    
  apply limit_rec_on c
  · simp only [add_zeroₓ, opow_zero, mul_oneₓ]
    
  · intro c IH
    rw [add_succ, opow_succ, IH, opow_succ, mul_assoc]
    
  · intro c l IH
    refine' eq_of_forall_ge_iff fun d => (((opow_is_normal a1).trans (add_is_normal b)).limit_le l).trans _
    simp (config := { contextual := true })only [IH]
    exact (((mul_is_normal <| opow_pos b (Ordinal.pos_iff_ne_zero.2 a0)).trans (opow_is_normal a1)).limit_le l).symm
    

theorem opow_dvd_opow a {b c : Ordinal} (h : b ≤ c) : (a^b) ∣ (a^c) := by
  rw [← Ordinal.add_sub_cancel_of_le h, opow_add]
  apply dvd_mul_right

theorem opow_dvd_opow_iff {a b c : Ordinal} (a1 : 1 < a) : (a^b) ∣ (a^c) ↔ b ≤ c :=
  ⟨fun h =>
    le_of_not_ltₓ fun hn =>
      not_le_of_lt ((opow_lt_opow_iff_right a1).2 hn) <|
        le_of_dvd (opow_ne_zero _ <| one_le_iff_ne_zero.1 <| le_of_ltₓ a1) h,
    opow_dvd_opow _⟩

theorem opow_mul (a b c : Ordinal) : (a^b * c) = ((a^b)^c) := by
  by_cases' b0 : b = 0
  · simp only [b0, zero_mul, opow_zero, one_opow]
    
  by_cases' a0 : a = 0
  · subst a
    by_cases' c0 : c = 0
    · simp only [c0, mul_zero, opow_zero]
      
    simp only [zero_opow b0, zero_opow c0, zero_opow (mul_ne_zero b0 c0)]
    
  cases' eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1
  · subst a1
    simp only [one_opow]
    
  apply limit_rec_on c
  · simp only [mul_zero, opow_zero]
    
  · intro c IH
    rw [mul_succ, opow_add, IH, opow_succ]
    
  · intro c l IH
    refine'
      eq_of_forall_ge_iff fun d =>
        (((opow_is_normal a1).trans (mul_is_normal (Ordinal.pos_iff_ne_zero.2 b0))).limit_le l).trans _
    simp (config := { contextual := true })only [IH]
    exact (opow_le_of_limit (opow_ne_zero _ a0) l).symm
    

/-! ### Ordinal logarithm -/


/-- The ordinal logarithm is the solution `u` to the equation `x = b ^ u * v + w` where `v < b` and
    `w < b ^ u`. -/
def log (b : Ordinal) (x : Ordinal) : Ordinal :=
  if h : 1 < b then pred (inf { o | x < (b^o) }) else 0

/-- The set in the definition of `log` is nonempty. -/
theorem log_nonempty {b x : Ordinal} (h : 1 < b) : { o | x < (b^o) }.Nonempty :=
  ⟨succ x, succ_le.1 (le_opow_self _ h)⟩

@[simp]
theorem log_not_one_lt {b : Ordinal} (b1 : ¬1 < b) (x : Ordinal) : log b x = 0 := by
  simp only [log, dif_neg b1]

theorem log_def {b : Ordinal} (b1 : 1 < b) (x : Ordinal) : log b x = pred (inf { o | x < (b^o) }) := by
  simp only [log, dif_pos b1]

@[simp]
theorem log_zero (b : Ordinal) : log b 0 = 0 :=
  if b1 : 1 < b then by
    rw [log_def b1, ← Ordinal.le_zero, pred_le]
    apply cInf_le'
    dsimp
    rw [succ_zero, opow_one]
    exact zero_lt_one.trans b1
  else by
    simp only [log_not_one_lt b1]

theorem succ_log_def {b x : Ordinal} (b1 : 1 < b) (x0 : 0 < x) : succ (log b x) = inf { o | x < (b^o) } := by
  let t := Inf { o | x < (b^o) }
  have : x < (b^t) := Inf_mem (log_nonempty b1)
  rcases zero_or_succ_or_limit t with (h | h | h)
  · refine' (not_lt_of_le (one_le_iff_pos.2 x0) _).elim
    simpa only [h, opow_zero]
    
  · rw [show log b x = pred t from log_def b1 x, succ_pred_iff_is_succ.2 h]
    
  · rcases(lt_opow_of_limit (ne_of_gtₓ <| lt_transₓ zero_lt_one b1) h).1 this with ⟨a, h₁, h₂⟩
    exact (not_le_of_lt h₁).elim ((le_cInf_iff'' (log_nonempty b1)).1 (le_reflₓ t) a h₂)
    

theorem lt_opow_succ_log {b : Ordinal} (b1 : 1 < b) (x : Ordinal) : x < (b^succ (log b x)) := by
  cases' lt_or_eq_of_leₓ (Ordinal.zero_le x) with x0 x0
  · rw [succ_log_def b1 x0]
    exact Inf_mem (log_nonempty b1)
    
  · subst x
    apply opow_pos _ (lt_transₓ zero_lt_one b1)
    

theorem opow_log_le b {x : Ordinal} (x0 : 0 < x) : (b^log b x) ≤ x := by
  by_cases' b0 : b = 0
  · rw [b0, zero_opow']
    refine' le_transₓ (sub_le_self _ _) (one_le_iff_pos.2 x0)
    
  cases' lt_or_eq_of_leₓ (one_le_iff_ne_zero.2 b0) with b1 b1
  · refine' le_of_not_ltₓ fun h => not_le_of_lt (lt_succ_self (log b x)) _
    have := @cInf_le' _ _ { o | x < (b^o) } _ h
    rwa [← succ_log_def b1 x0] at this
    
  · rw [← b1, one_opow]
    exact one_le_iff_pos.2 x0
    

theorem le_log {b x c : Ordinal} (b1 : 1 < b) (x0 : 0 < x) : c ≤ log b x ↔ (b^c) ≤ x :=
  ⟨fun h => le_transₓ ((opow_le_opow_iff_right b1).2 h) (opow_log_le b x0), fun h =>
    le_of_not_ltₓ fun hn =>
      not_le_of_lt (lt_opow_succ_log b1 x) <| le_transₓ ((opow_le_opow_iff_right b1).2 (succ_le.2 hn)) h⟩

theorem log_lt {b x c : Ordinal} (b1 : 1 < b) (x0 : 0 < x) : log b x < c ↔ x < (b^c) :=
  lt_iff_lt_of_le_iff_le (le_log b1 x0)

theorem log_le_log b {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y :=
  if x0 : x = 0 then by
    simp only [x0, log_zero, Ordinal.zero_le]
  else
    have x0 : 0 < x := Ordinal.pos_iff_ne_zero.2 x0
    if b1 : 1 < b then (le_log b1 (lt_of_lt_of_leₓ x0 xy)).2 <| le_transₓ (opow_log_le _ x0) xy
    else by
      simp only [log_not_one_lt b1, Ordinal.zero_le]

theorem log_le_self (b x : Ordinal) : log b x ≤ x :=
  if x0 : x = 0 then by
    simp only [x0, log_zero, Ordinal.zero_le]
  else
    if b1 : 1 < b then le_transₓ (le_opow_self _ b1) (opow_log_le b (Ordinal.pos_iff_ne_zero.2 x0))
    else by
      simp only [log_not_one_lt b1, Ordinal.zero_le]

@[simp]
theorem log_one (b : Ordinal) : log b 1 = 0 :=
  if hb : 1 < b then by
    rwa [← lt_one_iff_zero, log_lt hb zero_lt_one, opow_one]
  else log_not_one_lt hb 1

theorem opow_mul_add_pos {b v : Ordinal} (hb : 0 < b) u (hv : 0 < v) w : 0 < (b^u) * v + w :=
  (opow_pos u hb).trans_le ((le_mul_left _ hv).trans (le_add_right _ _))

theorem opow_mul_add_lt_opow_mul_succ {b u w : Ordinal} (v : Ordinal) (hw : w < (b^u)) :
    (b^u) * v + w < (b^u) * v.succ := by
  rwa [mul_succ, add_lt_add_iff_left]

theorem opow_mul_add_lt_opow_succ {b u v w : Ordinal} (hvb : v < b) (hw : w < (b^u)) : (b^u) * v + w < (b^u.succ) := by
  convert (opow_mul_add_lt_opow_mul_succ v hw).trans_le (mul_le_mul_left' (succ_le.2 hvb) _)
  exact opow_succ b u

-- ././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'
theorem log_opow_mul_add {b u v w : Ordinal} (hb : 1 < b) (hv : 0 < v) (hvb : v < b) (hw : w < (b^u)) :
    log b ((b^u) * v + w) = u := by
  have hpos := opow_mul_add_pos (zero_lt_one.trans hb) u hv w
  "././Mathport/Syntax/Translate/Basic.lean:537:16: unsupported tactic `by_contra'"
  cases' lt_or_gt_of_neₓ hne with h h
  · rw [log_lt hb hpos] at h
    exact not_le_of_lt h ((le_mul_left _ hv).trans (le_add_right _ _))
    
  · change _ < _ at h
    rw [← succ_le, le_log hb hpos] at h
    exact (not_lt_of_le h) (opow_mul_add_lt_opow_succ hvb hw)
    

@[simp]
theorem log_opow {b : Ordinal} (hb : 1 < b) (x : Ordinal) : log b (b^x) = x := by
  convert log_opow_mul_add hb zero_lt_one hb (opow_pos x (zero_lt_one.trans hb))
  rw [add_zeroₓ, mul_oneₓ]

theorem add_log_le_log_mul {x y : Ordinal} (b : Ordinal) (x0 : 0 < x) (y0 : 0 < y) :
    log b x + log b y ≤ log b (x * y) := by
  by_cases' hb : 1 < b
  · rw [le_log hb (mul_pos x0 y0), opow_add]
    exact mul_le_mul' (opow_log_le b x0) (opow_log_le b y0)
    
  simp only [log_not_one_lt hb, zero_addₓ]

/-! ### The Cantor normal form -/


theorem CNF_aux {b o : Ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) : o % (b^log b o) < o :=
  lt_of_lt_of_leₓ (mod_lt _ <| opow_ne_zero _ b0) (opow_log_le _ <| Ordinal.pos_iff_ne_zero.2 o0)

/-- Proving properties of ordinals by induction over their Cantor normal form. -/
@[elab_as_eliminator]
noncomputable def cNFRec {b : Ordinal} (b0 : b ≠ 0) {C : Ordinal → Sort _} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → o % (b^log b o) < o → C (o % (b^log b o)) → C o) : ∀ o, C o
  | o =>
    if o0 : o = 0 then by
      rw [o0] <;> exact H0
    else
      have := CNF_aux b0 o0
      H o o0 this (CNF_rec (o % (b^log b o)))

@[simp]
theorem CNF_rec_zero {b} b0 {C H0 H} : @cNFRec b b0 C H0 H 0 = H0 := by
  rw [CNF_rec, dif_pos rfl] <;> rfl

@[simp]
theorem CNF_rec_ne_zero {b} b0 {C H0 H o} o0 : @cNFRec b b0 C H0 H o = H o o0 (CNF_aux b0 o0) (@cNFRec b b0 C H0 H _) :=
  by
  rw [CNF_rec, dif_neg o0]

/-- The Cantor normal form of an ordinal is the list of coefficients
  in the base-`b` expansion of `o`.

    CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)] -/
def cNF (b := omega) (o : Ordinal) : List (Ordinal × Ordinal) :=
  if b0 : b = 0 then [] else cNFRec b0 [] (fun o o0 h IH => (log b o, o / (b^log b o)) :: IH) o

@[simp]
theorem zero_CNF o : cNF 0 o = [] :=
  dif_pos rfl

@[simp]
theorem CNF_zero b : cNF b 0 = [] :=
  if b0 : b = 0 then dif_pos b0 else (dif_neg b0).trans <| CNF_rec_zero _

theorem CNF_ne_zero {b o : Ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) :
    cNF b o = (log b o, o / (b^log b o)) :: cNF b (o % (b^log b o)) := by
  unfold CNF <;> rw [dif_neg b0, dif_neg b0, CNF_rec_ne_zero b0 o0]

theorem one_CNF {o : Ordinal} (o0 : o ≠ 0) : cNF 1 o = [(0, o)] := by
  rw [CNF_ne_zero Ordinal.one_ne_zero o0, log_not_one_lt (lt_irreflₓ _), opow_zero, mod_one, CNF_zero, div_one]

theorem CNF_foldr {b : Ordinal} (b0 : b ≠ 0) o : (cNF b o).foldr (fun p r => (b^p.1) * p.2 + r) 0 = o :=
  cNFRec b0
    (by
      rw [CNF_zero] <;> rfl)
    (fun o o0 h IH => by
      rw [CNF_ne_zero b0 o0, List.foldr_cons, IH, div_add_mod])
    o

theorem CNF_pairwise_aux (b := omega) o :
    (∀, ∀ p ∈ cNF b o, ∀, Prod.fst p ≤ log b o) ∧ (cNF b o).Pairwise fun p q => q.1 < p.1 := by
  by_cases' b0 : b = 0
  · simp only [b0, zero_CNF, List.Pairwiseₓ.nil, and_trueₓ]
    exact fun _ => False.elim
    
  cases' lt_or_eq_of_leₓ (one_le_iff_ne_zero.2 b0) with b1 b1
  · refine' CNF_rec b0 _ _ o
    · simp only [CNF_zero, List.Pairwiseₓ.nil, and_trueₓ]
      exact fun _ => False.elim
      
    intro o o0 H IH
    cases' IH with IH₁ IH₂
    simp only [CNF_ne_zero b0 o0, List.forall_mem_consₓ, List.pairwise_cons, IH₂, and_trueₓ]
    refine' ⟨⟨le_rfl, fun p m => _⟩, fun p m => _⟩
    · exact le_transₓ (IH₁ p m) (log_le_log _ <| le_of_ltₓ H)
      
    · refine' lt_of_le_of_ltₓ (IH₁ p m) ((log_lt b1 _).2 _)
      · rw [Ordinal.pos_iff_ne_zero]
        intro e
        rw [e] at m
        simpa only [CNF_zero] using m
        
      · exact mod_lt _ (opow_ne_zero _ b0)
        
      
    
  · by_cases' o0 : o = 0
    · simp only [o0, CNF_zero, List.Pairwiseₓ.nil, and_trueₓ]
      exact fun _ => False.elim
      
    rw [← b1, one_CNF o0]
    simp only [List.mem_singleton, log_not_one_lt (lt_irreflₓ _), forall_eq, le_reflₓ, true_andₓ,
      List.pairwise_singleton]
    

theorem CNF_pairwise (b := omega) o : (cNF b o).Pairwise fun p q => Prod.fst q < p.1 :=
  (CNF_pairwise_aux _ _).2

theorem CNF_fst_le_log (b := omega) o : ∀, ∀ p ∈ cNF b o, ∀, Prod.fst p ≤ log b o :=
  (CNF_pairwise_aux _ _).1

-- ././Mathport/Syntax/Translate/Basic.lean:599:2: warning: expanding binder collection (p «expr ∈ » CNF b o)
theorem CNF_fst_le (b := omega) o p (_ : p ∈ cNF b o) : Prod.fst p ≤ o :=
  le_transₓ (CNF_fst_le_log _ _ p H) (log_le_self _ _)

theorem CNF_snd_lt {b : Ordinal} (b1 : 1 < b) o : ∀, ∀ p ∈ cNF b o, ∀, Prod.snd p < b := by
  have b0 := ne_of_gtₓ (lt_transₓ zero_lt_one b1)
  refine'
    CNF_rec b0
      (fun _ => by
        rw [CNF_zero] <;> exact False.elim)
      _ o
  intro o o0 H IH
  simp only [CNF_ne_zero b0 o0, List.mem_cons_iff, forall_eq_or_imp, iff_true_intro IH, and_trueₓ]
  rw [div_lt (opow_ne_zero _ b0), ← opow_succ]
  exact lt_opow_succ_log b1 _

theorem CNF_sorted (b := omega) o : ((cNF b o).map Prod.fst).Sorted (· > ·) := by
  rw [List.Sorted, List.pairwise_map] <;> exact CNF_pairwise b o

/-! ### Casting naturals into ordinals, compatibility with operations -/


@[simp]
theorem nat_cast_mul {m n : ℕ} : ((m * n : ℕ) : Ordinal) = m * n := by
  induction' n with n IH <;> [simp only [Nat.cast_zeroₓ, Nat.mul_zero, mul_zero],
    rw [Nat.mul_succ, Nat.cast_addₓ, IH, Nat.cast_succₓ, mul_add_one]]

@[simp]
theorem nat_cast_opow {m n : ℕ} : ((pow m n : ℕ) : Ordinal) = (m^n) := by
  induction' n with n IH <;> [simp only [pow_zeroₓ, Nat.cast_zeroₓ, opow_zero, Nat.cast_oneₓ],
    rw [pow_succ'ₓ, nat_cast_mul, IH, Nat.cast_succₓ, ← succ_eq_add_one, opow_succ]]

@[simp]
theorem nat_cast_le {m n : ℕ} : (m : Ordinal) ≤ n ↔ m ≤ n := by
  rw [← Cardinal.ord_nat, ← Cardinal.ord_nat, Cardinal.ord_le_ord, Cardinal.nat_cast_le]

@[simp]
theorem nat_cast_lt {m n : ℕ} : (m : Ordinal) < n ↔ m < n := by
  simp only [lt_iff_le_not_leₓ, nat_cast_le]

@[simp]
theorem nat_cast_inj {m n : ℕ} : (m : Ordinal) = n ↔ m = n := by
  simp only [le_antisymm_iffₓ, nat_cast_le]

@[simp]
theorem nat_cast_eq_zero {n : ℕ} : (n : Ordinal) = 0 ↔ n = 0 :=
  @nat_cast_inj n 0

theorem nat_cast_ne_zero {n : ℕ} : (n : Ordinal) ≠ 0 ↔ n ≠ 0 :=
  not_congr nat_cast_eq_zero

@[simp]
theorem nat_cast_pos {n : ℕ} : (0 : Ordinal) < n ↔ 0 < n :=
  @nat_cast_lt 0 n

@[simp]
theorem nat_cast_sub {m n : ℕ} : ((m - n : ℕ) : Ordinal) = m - n :=
  (le_totalₓ m n).elim
    (fun h => by
      rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (nat_cast_le.2 h)] <;> rfl)
    fun h =>
    (add_left_cancel n).1 <| by
      rw [← Nat.cast_addₓ, add_tsub_cancel_of_le h, Ordinal.add_sub_cancel_of_le (nat_cast_le.2 h)]

@[simp]
theorem nat_cast_div {m n : ℕ} : ((m / n : ℕ) : Ordinal) = m / n :=
  if n0 : n = 0 then by
    simp only [n0, Nat.div_zeroₓ, Nat.cast_zeroₓ, div_zero]
  else
    have n0' := nat_cast_ne_zero.2 n0
    le_antisymmₓ
      (by
        rw [le_div n0', ← nat_cast_mul, nat_cast_le, mul_comm] <;> apply Nat.div_mul_le_selfₓ)
      (by
        rw [div_le n0', succ, ← Nat.cast_succₓ, ← nat_cast_mul, nat_cast_lt, mul_comm, ←
            Nat.div_lt_iff_lt_mulₓ _ _ (Nat.pos_of_ne_zeroₓ n0)] <;>
          apply Nat.lt_succ_selfₓ)

@[simp]
theorem nat_cast_mod {m n : ℕ} : ((m % n : ℕ) : Ordinal) = m % n := by
  rw [← add_left_cancelₓ (n * (m / n)), div_add_mod, ← nat_cast_div, ← nat_cast_mul, ← Nat.cast_addₓ, Nat.div_add_mod]

@[simp]
theorem nat_le_card {o} {n : ℕ} : (n : Cardinal) ≤ card o ↔ (n : Ordinal) ≤ o :=
  ⟨fun h => by
    rwa [← Cardinal.ord_le, Cardinal.ord_nat] at h, fun h => card_nat n ▸ card_le_card h⟩

@[simp]
theorem nat_lt_card {o} {n : ℕ} : (n : Cardinal) < card o ↔ (n : Ordinal) < o := by
  rw [← succ_le, ← Cardinal.succ_le, ← Cardinal.nat_succ, nat_le_card] <;> rfl

@[simp]
theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card

@[simp]
theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]
theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n := by
  simp only [le_antisymm_iffₓ, card_le_nat, nat_le_card]

@[simp]
theorem type_fin (n : ℕ) : @type (Finₓ n) (· < ·) _ = n := by
  rw [← card_eq_nat, card_type, mk_fin]

@[simp]
theorem lift_nat_cast (n : ℕ) : lift n = n := by
  induction' n with n ih <;> [simp only [Nat.cast_zeroₓ, lift_zero], simp only [Nat.cast_succₓ, lift_add, ih, lift_one]]

theorem lift_type_fin (n : ℕ) : lift (@type (Finₓ n) (· < ·) _) = n := by
  simp only [type_fin, lift_nat_cast]

theorem type_fintype (r : α → α → Prop) [IsWellOrder α r] [Fintype α] : type r = Fintype.card α := by
  rw [← card_eq_nat, card_type, mk_fintype]

end Ordinal

/-! ### Properties of `omega` -/


namespace Cardinal

open Ordinal

@[simp]
theorem ord_omega : ord.{u} omega = Ordinal.omega :=
  le_antisymmₓ (ord_le.2 <| le_rfl) <|
    le_of_forall_lt fun o h => by
      rcases Ordinal.lt_lift_iff.1 h with ⟨o, rfl, h'⟩
      rw [lt_ord, ← lift_card, ← lift_omega.{0, u}, lift_lt, ← typein_enum (· < ·) h']
      exact lt_omega_iff_fintype.2 ⟨Set.fintypeLtNat _⟩

@[simp]
theorem add_one_of_omega_le {c} (h : omega ≤ c) : c + 1 = c := by
  rw [add_commₓ, ← card_ord c, ← card_one, ← card_add, one_add_of_omega_le] <;> rwa [← ord_omega, ord_le_ord]

end Cardinal

namespace Ordinal

theorem lt_add_of_limit {a b c : Ordinal.{u}} (h : IsLimit c) : a < b + c ↔ ∃ c' < c, a < b + c' := by
  rw [← IsNormal.bsup_eq.{u, u} (add_is_normal b) h, lt_bsup]

theorem lt_omega {o : Ordinal.{u}} : o < omega ↔ ∃ n : ℕ, o = n := by
  rw [← Cardinal.ord_omega, Cardinal.lt_ord, lt_omega] <;> simp only [card_eq_nat]

theorem nat_lt_omega (n : ℕ) : (n : Ordinal) < omega :=
  lt_omega.2 ⟨_, rfl⟩

theorem omega_pos : 0 < omega :=
  nat_lt_omega 0

theorem omega_ne_zero : omega ≠ 0 :=
  ne_of_gtₓ omega_pos

theorem one_lt_omega : 1 < omega := by
  simpa only [Nat.cast_oneₓ] using nat_lt_omega 1

theorem omega_is_limit : IsLimit omega :=
  ⟨omega_ne_zero, fun o h => by
    let ⟨n, e⟩ := lt_omega.1 h
    rw [e] <;> exact nat_lt_omega (n + 1)⟩

theorem omega_le {o : Ordinal.{u}} : omega ≤ o ↔ ∀ n : ℕ, (n : Ordinal) ≤ o :=
  ⟨fun h n => le_transₓ (le_of_ltₓ (nat_lt_omega _)) h, fun H =>
    le_of_forall_lt fun a h => by
      let ⟨n, e⟩ := lt_omega.1 h
      rw [e, ← succ_le] <;> exact H (n + 1)⟩

@[simp]
theorem sup_nat_cast : sup Nat.castₓ = omega :=
  (sup_le.2 fun n => (nat_lt_omega n).le).antisymm <| omega_le.2 <| le_sup _

theorem nat_lt_limit {o} (h : IsLimit o) : ∀ n : ℕ, (n : Ordinal) < o
  | 0 => lt_of_le_of_neₓ (Ordinal.zero_le o) h.1.symm
  | n + 1 => h.2 _ (nat_lt_limit n)

theorem omega_le_of_is_limit {o} (h : IsLimit o) : omega ≤ o :=
  omega_le.2 fun n => le_of_ltₓ <| nat_lt_limit h n

theorem add_omega {a : Ordinal} (h : a < omega) : a + omega = omega := by
  rcases lt_omega.1 h with ⟨n, rfl⟩
  clear h
  induction' n with n IH
  · rw [Nat.cast_zeroₓ, zero_addₓ]
    
  · rw [Nat.cast_succₓ, add_assocₓ, one_add_of_omega_le le_rfl, IH]
    

theorem add_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : a + b < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← Nat.cast_addₓ] <;> apply nat_lt_omega

theorem mul_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : a * b < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← nat_cast_mul] <;> apply nat_lt_omega

theorem is_limit_iff_omega_dvd {a : Ordinal} : IsLimit a ↔ a ≠ 0 ∧ omega ∣ a := by
  refine' ⟨fun l => ⟨l.1, ⟨a / omega, le_antisymmₓ _ (mul_div_le _ _)⟩⟩, fun h => _⟩
  · refine' (limit_le l).2 fun x hx => le_of_ltₓ _
    rw [← div_lt omega_ne_zero, ← succ_le, le_div omega_ne_zero, mul_succ, add_le_of_limit omega_is_limit]
    intro b hb
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    exact le_transₓ (add_le_add_right (mul_div_le _ _) _) (le_of_ltₓ <| lt_sub.1 <| nat_lt_limit (sub_is_limit l hx) _)
    
  · rcases h with ⟨a0, b, rfl⟩
    refine' mul_is_limit_left omega_is_limit (Ordinal.pos_iff_ne_zero.2 <| mt _ a0)
    intro e
    simp only [e, mul_zero]
    

-- mathport name: «expr ^ »
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

theorem opow_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : (a^b) < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← nat_cast_opow] <;> apply nat_lt_omega

theorem add_omega_opow {a b : Ordinal} (h : a < (omega^b)) : a + (omega^b) = (omega^b) := by
  refine' le_antisymmₓ _ (le_add_left _ _)
  revert h
  apply limit_rec_on b
  · intro h
    rw [opow_zero, ← succ_zero, lt_succ, Ordinal.le_zero] at h
    rw [h, zero_addₓ]
    
  · intro b _ h
    rw [opow_succ] at h
    rcases(lt_mul_of_limit omega_is_limit).1 h with ⟨x, xo, ax⟩
    refine' le_transₓ (add_le_add_right (le_of_ltₓ ax) _) _
    rw [opow_succ, ← mul_addₓ, add_omega xo]
    
  · intro b l IH h
    rcases(lt_opow_of_limit omega_ne_zero l).1 h with ⟨x, xb, ax⟩
    refine' (((add_is_normal a).trans (opow_is_normal one_lt_omega)).limit_le l).2 fun y yb => _
    let z := max x y
    have := IH z (max_ltₓ xb yb) (lt_of_lt_of_leₓ ax <| opow_le_opow_right omega_pos (le_max_leftₓ _ _))
    exact
      le_transₓ (add_le_add_left (opow_le_opow_right omega_pos (le_max_rightₓ _ _)) _)
        (le_transₓ this (opow_le_opow_right omega_pos <| le_of_ltₓ <| max_ltₓ xb yb))
    

theorem add_lt_omega_opow {a b c : Ordinal} (h₁ : a < (omega^c)) (h₂ : b < (omega^c)) : a + b < (omega^c) := by
  rwa [← add_omega_opow h₁, add_lt_add_iff_left]

theorem add_absorp {a b c : Ordinal} (h₁ : a < (omega^b)) (h₂ : (omega^b) ≤ c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le h₂, ← add_assocₓ, add_omega_opow h₁]

theorem add_absorp_iff {o : Ordinal} (o0 : 0 < o) : (∀, ∀ a < o, ∀, a + o = o) ↔ ∃ a, o = (omega^a) :=
  ⟨fun H =>
    ⟨log omega o, by
      refine' ((lt_or_eq_of_leₓ (opow_log_le _ o0)).resolve_left fun h => _).symm
      have := H _ h
      have := lt_opow_succ_log one_lt_omega o
      rw [opow_succ, lt_mul_of_limit omega_is_limit] at this
      rcases this with ⟨a, ao, h'⟩
      rcases lt_omega.1 ao with ⟨n, rfl⟩
      clear ao
      revert h'
      apply not_lt_of_le
      suffices e : (omega^log omega o) * ↑n + o = o
      · simpa only [e] using le_add_right ((omega^log omega o) * ↑n) o
        
      induction' n with n IH
      · simp only [Nat.cast_zeroₓ, mul_zero, zero_addₓ]
        
      simp only [Nat.cast_succₓ, mul_add_one, add_assocₓ, this, IH]⟩,
    fun ⟨b, e⟩ => e.symm ▸ fun a => add_omega_opow⟩

theorem add_mul_limit_aux {a b c : Ordinal} (ba : b + a = a) (l : IsLimit c)
    (IH : ∀, ∀ c' < c, ∀, (a + b) * succ c' = a * succ c' + b) : (a + b) * c = a * c :=
  le_antisymmₓ
    ((mul_le_of_limit l).2 fun c' h => by
      apply le_transₓ (mul_le_mul_left' (le_of_ltₓ <| lt_succ_self _) _)
      rw [IH _ h]
      apply le_transₓ (add_le_add_left _ _)
      · rw [← mul_succ]
        exact mul_le_mul_left' (succ_le.2 <| l.2 _ h) _
        
      · infer_instance
        
      · rw [← ba]
        exact le_add_right _ _
        )
    (mul_le_mul_right' (le_add_right _ _) _)

theorem add_mul_succ {a b : Ordinal} c (ba : b + a = a) : (a + b) * succ c = a * succ c + b := by
  apply limit_rec_on c
  · simp only [succ_zero, mul_oneₓ]
    
  · intro c IH
    rw [mul_succ, IH, ← add_assocₓ, add_assocₓ _ b, ba, ← mul_succ]
    
  · intro c l IH
    have := add_mul_limit_aux ba l IH
    rw [mul_succ, add_mul_limit_aux ba l IH, mul_succ, add_assocₓ]
    

theorem add_mul_limit {a b c : Ordinal} (ba : b + a = a) (l : IsLimit c) : (a + b) * c = a * c :=
  add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba

theorem mul_omega {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : a * omega = omega :=
  le_antisymmₓ ((mul_le_of_limit omega_is_limit).2 fun b hb => le_of_ltₓ (mul_lt_omega ha hb))
    (by
      simpa only [one_mulₓ] using mul_le_mul_right' (one_le_iff_pos.2 a0) omega)

theorem mul_lt_omega_opow {a b c : Ordinal} (c0 : 0 < c) (ha : a < (omega^c)) (hb : b < omega) : a * b < (omega^c) := by
  rcases zero_or_succ_or_limit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irreflₓ _).elim c0
    
  · rw [opow_succ] at ha
    rcases((mul_is_normal <| opow_pos _ omega_pos).limit_lt omega_is_limit).1 ha with ⟨n, hn, an⟩
    refine' (mul_le_mul_right' (le_of_ltₓ an) _).trans_lt _
    rw [opow_succ, mul_assoc, mul_lt_mul_iff_left (opow_pos _ omega_pos)]
    exact mul_lt_omega hn hb
    
  · rcases((opow_is_normal one_lt_omega).limit_lt l).1 ha with ⟨x, hx, ax⟩
    refine' (mul_le_mul' (le_of_ltₓ ax) (le_of_ltₓ hb)).trans_lt _
    rw [← opow_succ, opow_lt_opow_iff_right one_lt_omega]
    exact l.2 _ hx
    

theorem mul_omega_dvd {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : ∀ {b}, omega ∣ b → a * b = b
  | _, ⟨b, rfl⟩ => by
    rw [← mul_assoc, mul_omega a0 ha]

theorem mul_omega_opow_opow {a b : Ordinal} (a0 : 0 < a) (h : a < (omega^omega^b)) :
    a * (omega^omega^b) = (omega^omega^b) := by
  by_cases' b0 : b = 0
  · rw [b0, opow_zero, opow_one] at h⊢
    exact mul_omega a0 h
    
  refine'
    le_antisymmₓ _
      (by
        simpa only [one_mulₓ] using mul_le_mul_right' (one_le_iff_pos.2 a0) (omega^omega^b))
  rcases(lt_opow_of_limit omega_ne_zero (opow_is_limit_left omega_is_limit b0)).1 h with ⟨x, xb, ax⟩
  apply (mul_le_mul_right' (le_of_ltₓ ax) _).trans
  rw [← opow_add, add_omega_opow xb]

theorem opow_omega {a : Ordinal} (a1 : 1 < a) (h : a < omega) : (a^omega) = omega :=
  le_antisymmₓ
    ((opow_le_of_limit (one_le_iff_ne_zero.1 <| le_of_ltₓ a1) omega_is_limit).2 fun b hb =>
      le_of_ltₓ (opow_lt_omega h hb))
    (le_opow_self _ a1)

theorem IsNormal.apply_omega {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f) : sup.{0, u} (f ∘ Nat.castₓ) = f omega :=
  by
  rw [← sup_nat_cast, IsNormal.sup.{0, u, u} hf ⟨0⟩]

@[simp]
theorem sup_add_nat (o : Ordinal.{u}) : (sup fun n : ℕ => o + n) = o + omega :=
  (add_is_normal o).apply_omega

@[simp]
theorem sup_mul_nat (o : Ordinal) : (sup fun n : ℕ => o * n) = o * omega := by
  rcases eq_zero_or_pos o with (rfl | ho)
  · rw [zero_mul]
    exact sup_eq_zero_iff.2 fun n => zero_mul n
    
  · exact (mul_is_normal ho).apply_omega
    

theorem sup_opow_nat {o : Ordinal.{u}} (ho : 0 < o) : (sup fun n : ℕ => o^n) = (o^omega) := by
  rcases lt_or_eq_of_leₓ (one_le_iff_pos.2 ho) with (ho₁ | rfl)
  · exact (opow_is_normal ho₁).apply_omega
    
  · rw [one_opow]
    refine'
      le_antisymmₓ
        (sup_le.2 fun n => by
          rw [one_opow])
        _
    convert le_sup _ 0
    rw [Nat.cast_zeroₓ, opow_zero]
    

/-! ### Fixed points of normal functions -/


section

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f` above `a`. -/
def nfp (f : Ordinal → Ordinal) (a : Ordinal) :=
  sup fun n : ℕ => (f^[n]) a

theorem nfp_le {f a b} : nfp f a ≤ b ↔ ∀ n, (f^[n]) a ≤ b :=
  sup_le

theorem iterate_le_nfp f a n : (f^[n]) a ≤ nfp f a :=
  le_sup _ n

theorem le_nfp_self f a : a ≤ nfp f a :=
  iterate_le_nfp f a 0

theorem lt_nfp {f : Ordinal → Ordinal} {a b} : a < nfp f b ↔ ∃ n, a < (f^[n]) b :=
  lt_sup

protected theorem IsNormal.lt_nfp {f} (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a :=
  lt_sup.trans <|
    Iff.trans
      ⟨fun ⟨n, h⟩ => ⟨n, lt_of_le_of_ltₓ (H.self_le _) h⟩, fun ⟨n, h⟩ =>
        ⟨n + 1, by
          rw [iterate_succ'] <;> exact H.lt_iff.2 h⟩⟩
      lt_sup.symm

protected theorem IsNormal.nfp_le (H : IsNormal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.lt_nfp

theorem IsNormal.nfp_le_fp (H : IsNormal f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  sup_le.2 fun i => by
    induction' i with i IH generalizing a
    · exact ab
      
    exact IH (le_transₓ (H.le_iff.2 ab) h)

theorem IsNormal.nfp_fp (H : IsNormal f) a : f (nfp f a) = nfp f a := by
  refine' le_antisymmₓ _ (H.self_le _)
  cases' le_or_ltₓ (f a) a with aa aa
  · rwa [le_antisymmₓ (H.nfp_le_fp le_rfl aa) (le_nfp_self _ _)]
    
  rcases zero_or_succ_or_limit (nfp f a) with (e | ⟨b, e⟩ | l)
  · refine' @le_transₓ _ _ _ (f a) _ (H.le_iff.2 _) (iterate_le_nfp f a 1)
    simp only [e, Ordinal.zero_le]
    
  · have : f b < nfp f a :=
      H.lt_nfp.2
        (by
          simp only [e, lt_succ_self])
    rw [e, lt_succ] at this
    have ab : a ≤ b := by
      rw [← lt_succ, ← e]
      exact lt_of_lt_of_leₓ aa (iterate_le_nfp f a 1)
    refine' le_transₓ (H.le_iff.2 (H.nfp_le_fp ab this)) (le_transₓ this (le_of_ltₓ _))
    simp only [e, lt_succ_self]
    
  · exact (H.2 _ l _).2 fun b h => le_of_ltₓ (H.lt_nfp.2 h)
    

theorem IsNormal.le_nfp (H : IsNormal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨le_transₓ (H.self_le _), fun h => by
    simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {a} (h : f a = a) : nfp f a = a :=
  le_antisymmₓ
    (sup_le.mpr fun i => by
      rw [iterate_fixed h])
    (le_nfp_self f a)

protected theorem Monotone.nfp (hf : Monotone f) : Monotone (nfp f) := fun a b h =>
  nfp_le.2 fun n => (hf.iterate n h).trans (le_sup _ n)

/-- Fixed point lemma for normal functions: the fixed points of a normal function are unbounded. -/
theorem IsNormal.nfp_unbounded {f} (H : IsNormal f) : Unbounded (· < ·) (FixedPoints f) := fun a =>
  ⟨_, H.nfp_fp a, not_lt_of_geₓ (le_nfp_self f a)⟩

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`. -/
def deriv (f : Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limitRecOn o (nfp f 0) (fun a IH => nfp f (succ IH)) fun a l => bsup.{u, u} a

@[simp]
theorem deriv_zero f : deriv f 0 = nfp f 0 :=
  limit_rec_on_zero _ _ _

@[simp]
theorem deriv_succ f o : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  limit_rec_on_succ _ _ _ _

theorem deriv_limit f {o} : IsLimit o → deriv f o = bsup.{u, u} o fun a _ => deriv f a :=
  limit_rec_on_limit _ _ _ _

theorem deriv_is_normal f : IsNormal (deriv f) :=
  ⟨fun o => by
    rw [deriv_succ, ← succ_le] <;> apply le_nfp_self, fun o l a => by
    rw [deriv_limit _ l, bsup_le]⟩

theorem IsNormal.deriv_fp (H : IsNormal f) o : f (deriv.{u} f o) = deriv f o := by
  apply limit_rec_on o
  · rw [deriv_zero, H.nfp_fp]
    
  · intro o ih
    rw [deriv_succ, H.nfp_fp]
    
  intro o l IH
  rw [deriv_limit _ l, IsNormal.bsup.{u, u, u} H _ l.1]
  refine' eq_of_forall_ge_iff fun c => _
  simp (config := { contextual := true })only [bsup_le, IH]

theorem IsNormal.le_iff_deriv (H : IsNormal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a :=
  ⟨fun ha => by
    suffices : ∀ o _ : a ≤ deriv f o, ∃ o, deriv f o = a
    exact this a ((deriv_is_normal _).self_le _)
    refine' fun o => limit_rec_on o (fun h₁ => ⟨0, le_antisymmₓ _ h₁⟩) (fun o IH h₁ => _) fun o l IH h₁ => _
    · rw [deriv_zero]
      exact H.nfp_le_fp (Ordinal.zero_le _) ha
      
    · cases le_or_ltₓ a (deriv f o)
      · exact IH h
        
      refine' ⟨succ o, le_antisymmₓ _ h₁⟩
      rw [deriv_succ]
      exact H.nfp_le_fp (succ_le.2 h) ha
      
    · cases eq_or_lt_of_le h₁
      · exact ⟨_, h.symm⟩
        
      rw [deriv_limit _ l, ← not_leₓ, bsup_le, not_ball] at h
      exact
        let ⟨o', h, hl⟩ := h
        IH o' h (le_of_not_leₓ hl)
      ,
    fun ⟨o, e⟩ => e ▸ le_of_eqₓ (H.deriv_fp _)⟩

theorem IsNormal.apply_eq_self_iff_deriv (H : IsNormal f) {a} : f a = a ↔ ∃ o, deriv f o = a := by
  rw [← H.le_iff_deriv, H.le_iff_eq]

/-- `deriv f` is the fixed point enumerator of `f`. -/
theorem deriv_eq_enum_fp {f} (H : IsNormal f) : deriv f = enumOrd (FixedPoints f) := by
  rw [← eq_enum_ord _ H.nfp_unbounded, range_eq_iff]
  exact ⟨(deriv_is_normal f).StrictMono, H.deriv_fp, fun _ => H.apply_eq_self_iff_deriv.1⟩

end

/-! ### Fixed points of addition -/


@[simp]
theorem nfp_add_zero a : nfp ((· + ·) a) 0 = a * omega := by
  unfold nfp
  rw [← sup_mul_nat]
  congr
  funext
  induction' n with n hn
  · rw [Nat.cast_zeroₓ, mul_zero, iterate_zero_apply]
    
  · nth_rw 1[Nat.succ_eq_one_add]
    rw [Nat.cast_addₓ, Nat.cast_oneₓ, mul_one_add, iterate_succ_apply', hn]
    

theorem nfp_add_eq_mul_omega {a b} (hba : b ≤ a * omega) : nfp ((· + ·) a) b = a * omega := by
  apply le_antisymmₓ ((add_is_normal a).nfp_le_fp hba _)
  · rw [← nfp_add_zero]
    exact monotone.nfp (add_is_normal a).StrictMono.Monotone (Ordinal.zero_le b)
    
  · rw [← mul_one_add, one_add_omega]
    

theorem add_eq_right_iff_mul_omega_le {a b : Ordinal} : a + b = b ↔ a * omega ≤ b := by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← nfp_add_zero a, ← deriv_zero]
    cases' (add_is_normal a).apply_eq_self_iff_deriv.1 h with c hc
    rw [← hc]
    exact (deriv_is_normal _).StrictMono.Monotone (Ordinal.zero_le _)
    
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 0[← this]
    rwa [← add_assocₓ, ← mul_one_add, one_add_omega]
    

theorem add_le_right_iff_mul_omega_le {a b : Ordinal} : a + b ≤ b ↔ a * omega ≤ b := by
  rw [← add_eq_right_iff_mul_omega_le]
  exact (add_is_normal a).le_iff_eq

theorem deriv_add_eq_mul_omega_add (a b : Ordinal.{u}) : deriv ((· + ·) a) b = a * omega + b := by
  refine' b.limit_rec_on _ (fun o h => _) fun o ho h => _
  · rw [deriv_zero, add_zeroₓ]
    exact nfp_add_zero a
    
  · rw [deriv_succ, h, add_succ]
    exact nfp_eq_self (add_eq_right_iff_mul_omega_le.2 ((le_add_right _ _).trans (lt_succ_self _).le))
    
  · rw [← IsNormal.bsup_eq.{u, u} (add_is_normal _) ho, ← IsNormal.bsup_eq.{u, u} (deriv_is_normal _) ho]
    congr
    ext a hao
    exact h a hao
    

end Ordinal

