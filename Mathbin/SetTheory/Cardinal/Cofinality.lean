/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios

! This file was ported from Lean 3 source module set_theory.cardinal.cofinality
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Cardinal.Ordinal
import Mathbin.SetTheory.Ordinal.FixedPoint

/-!
# Cofinality

This file contains the definition of cofinality of an ordinal number and regular cardinals

## Main Definitions

* `ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `cardinal.is_limit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `cardinal.is_strong_limit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.
* `cardinal.is_regular c` means that `c` is a regular cardinal: `ℵ₀ ≤ c ∧ c.ord.cof = c`.
* `cardinal.is_inaccessible c` means that `c` is strongly inaccessible:
  `ℵ₀ < c ∧ is_regular c ∧ is_strong_limit c`.

## Main Statements

* `ordinal.infinite_pigeonhole_card`: the infinite pigeonhole principle
* `cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`
* `cardinal.univ_inaccessible`: The type of ordinals in `Type u` form an inaccessible cardinal
  (in `Type v` with `v > u`). This shows (externally) that in `Type u` there are at least `u`
  inaccessible cardinals.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.

## Tags

cofinality, regular cardinals, limits cardinals, inaccessible cardinals,
infinite pigeonhole principle
-/


noncomputable section

open Function Cardinal Set Order

open Classical Cardinal Ordinal

universe u v w

variable {α : Type _} {r : α → α → Prop}

/-! ### Cofinality of orders -/


namespace Order

/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) : Cardinal :=
  infₛ { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ (#S) = c }
#align order.cof Order.cof

/-- The set in the definition of `order.cof` is nonempty. -/
theorem cof_nonempty (r : α → α → Prop) [IsRefl α r] :
    { c | ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ (#S) = c }.Nonempty :=
  ⟨_, Set.univ, fun a => ⟨a, ⟨⟩, refl _⟩, rfl⟩
#align order.cof_nonempty Order.cof_nonempty

theorem cof_le (r : α → α → Prop) {S : Set α} (h : ∀ a, ∃ b ∈ S, r a b) : cof r ≤ (#S) :=
  cinfₛ_le' ⟨S, h, rfl⟩
#align order.cof_le Order.cof_le

theorem le_cof {r : α → α → Prop} [IsRefl α r] (c : Cardinal) :
    c ≤ cof r ↔ ∀ {S : Set α}, (∀ a, ∃ b ∈ S, r a b) → c ≤ (#S) :=
  by
  rw [cof, le_cinfₛ_iff'' (cof_nonempty r)]
  use fun H S h => H _ ⟨S, h, rfl⟩
  rintro H d ⟨S, h, rfl⟩
  exact H h
#align order.le_cof Order.le_cof

end Order

theorem RelIso.cof_le_lift {α : Type u} {β : Type v} {r : α → α → Prop} {s} [IsRefl β s]
    (f : r ≃r s) : Cardinal.lift.{max u v} (Order.cof r) ≤ Cardinal.lift.{max u v} (Order.cof s) :=
  by
  rw [Order.cof, Order.cof, lift_Inf, lift_Inf,
    le_cinfₛ_iff'' (nonempty_image_iff.2 (Order.cof_nonempty s))]
  rintro - ⟨-, ⟨u, H, rfl⟩, rfl⟩
  apply cinfₛ_le'
  refine'
    ⟨_, ⟨f.symm '' u, fun a => _, rfl⟩,
      lift_mk_eq.{u, v, max u v}.2 ⟨(f.symm.toEquiv.image u).symm⟩⟩
  rcases H (f a) with ⟨b, hb, hb'⟩
  refine' ⟨f.symm b, mem_image_of_mem _ hb, f.map_rel_iff.1 _⟩
  rwa [RelIso.apply_symm_apply]
#align rel_iso.cof_le_lift RelIso.cof_le_lift

theorem RelIso.cof_eq_lift {α : Type u} {β : Type v} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Cardinal.lift.{max u v} (Order.cof r) = Cardinal.lift.{max u v} (Order.cof s) :=
  (RelIso.cof_le_lift f).antisymm (RelIso.cof_le_lift f.symm)
#align rel_iso.cof_eq_lift RelIso.cof_eq_lift

theorem RelIso.cof_le {α β : Type u} {r : α → α → Prop} {s} [IsRefl β s] (f : r ≃r s) :
    Order.cof r ≤ Order.cof s :=
  lift_le.1 (RelIso.cof_le_lift f)
#align rel_iso.cof_le RelIso.cof_le

theorem RelIso.cof_eq {α β : Type u} {r s} [IsRefl α r] [IsRefl β s] (f : r ≃r s) :
    Order.cof r = Order.cof s :=
  lift_inj.1 (RelIso.cof_eq_lift f)
#align rel_iso.cof_eq RelIso.cof_eq

/-- Cofinality of a strict order `≺`. This is the smallest cardinality of a set `S : set α` such
that `∀ a, ∃ b ∈ S, ¬ b ≺ a`. -/
def StrictOrder.cof (r : α → α → Prop) : Cardinal :=
  Order.cof (swap rᶜ)
#align strict_order.cof StrictOrder.cof

/-- The set in the definition of `order.strict_order.cof` is nonempty. -/
theorem StrictOrder.cof_nonempty (r : α → α → Prop) [IsIrrefl α r] :
    { c | ∃ S : Set α, Unbounded r S ∧ (#S) = c }.Nonempty :=
  @Order.cof_nonempty α _ (IsRefl.swap (rᶜ))
#align strict_order.cof_nonempty StrictOrder.cof_nonempty

/-! ### Cofinality of ordinals -/


namespace Ordinal

/-- Cofinality of an ordinal. This is the smallest cardinal of a
  subset `S` of the ordinal which is unbounded, in the sense
  `∀ a, ∃ b ∈ S, a ≤ b`. It is defined for all ordinals, but
  `cof 0 = 0` and `cof (succ o) = 1`, so it is only really
  interesting on limit ordinals (when it is an infinite cardinal). -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOn (fun a => StrictOrder.cof a.R)
    (by
      rintro ⟨α, r, wo₁⟩ ⟨β, s, wo₂⟩ ⟨⟨f, hf⟩⟩
      haveI := wo₁; haveI := wo₂
      apply @RelIso.cof_eq _ _ _ _ _ _
      · constructor
        exact fun a b => not_iff_not.2 hf
      · exact ⟨(IsWellOrder.is_irrefl r).1⟩
      · exact ⟨(IsWellOrder.is_irrefl s).1⟩)
#align ordinal.cof Ordinal.cof

theorem cof_type (r : α → α → Prop) [IsWellOrder α r] : (type r).cof = StrictOrder.cof r :=
  rfl
#align ordinal.cof_type Ordinal.cof_type

theorem le_cof_type [IsWellOrder α r] {c} : c ≤ cof (type r) ↔ ∀ S, Unbounded r S → c ≤ (#S) :=
  (le_cinfₛ_iff'' (StrictOrder.cof_nonempty r)).trans
    ⟨fun H S h => H _ ⟨S, h, rfl⟩, by
      rintro H d ⟨S, h, rfl⟩
      exact H _ h⟩
#align ordinal.le_cof_type Ordinal.le_cof_type

theorem cof_type_le [IsWellOrder α r] {S : Set α} (h : Unbounded r S) : cof (type r) ≤ (#S) :=
  le_cof_type.1 le_rfl S h
#align ordinal.cof_type_le Ordinal.cof_type_le

theorem lt_cof_type [IsWellOrder α r] {S : Set α} : (#S) < cof (type r) → Bounded r S := by
  simpa using not_imp_not.2 cof_type_le
#align ordinal.lt_cof_type Ordinal.lt_cof_type

theorem cof_eq (r : α → α → Prop) [IsWellOrder α r] : ∃ S, Unbounded r S ∧ (#S) = cof (type r) :=
  cinfₛ_mem (StrictOrder.cof_nonempty r)
#align ordinal.cof_eq Ordinal.cof_eq

theorem ord_cof_eq (r : α → α → Prop) [IsWellOrder α r] :
    ∃ S, Unbounded r S ∧ type (Subrel r S) = (cof (type r)).ord :=
  by
  let ⟨S, hS, e⟩ := cof_eq r
  let ⟨s, _, e'⟩ := Cardinal.ord_eq S
  let T : Set α := { a | ∃ aS : a ∈ S, ∀ b : S, s b ⟨_, aS⟩ → r b a }
  skip; suffices
  · refine' ⟨T, this, le_antisymm _ (Cardinal.ord_le.2 <| cof_type_le this)⟩
    rw [← e, e']
    refine'
      (RelEmbedding.ofMonotone
          (fun a : T =>
            (⟨a,
                let ⟨aS, _⟩ := a.2
                aS⟩ :
              S))
          fun a b h => _).ordinal_type_le
    rcases a with ⟨a, aS, ha⟩
    rcases b with ⟨b, bS, hb⟩
    change s ⟨a, _⟩ ⟨b, _⟩
    refine' ((trichotomous_of s _ _).resolve_left fun hn => _).resolve_left _
    · exact asymm h (ha _ hn)
    · intro e
      injection e with e
      subst b
      exact irrefl _ h
  · intro a
    have : { b : S | ¬r b a }.Nonempty :=
      let ⟨b, bS, ba⟩ := hS a
      ⟨⟨b, bS⟩, ba⟩
    let b := IsWellFounded.wf.min _ this
    have ba : ¬r b a := IsWellFounded.wf.min_mem _ this
    refine' ⟨b, ⟨b.2, fun c => not_imp_not.1 fun h => _⟩, ba⟩
    rw [show ∀ b : S, (⟨b, b.2⟩ : S) = b by intro b <;> cases b <;> rfl]
    exact IsWellFounded.wf.not_lt_min _ this (IsOrderConnected.neg_trans h ba)
#align ordinal.ord_cof_eq Ordinal.ord_cof_eq

/-! ### Cofinality of suprema and least strict upper bounds -/


private theorem card_mem_cof {o} : ∃ (ι : _)(f : ι → Ordinal), lsub.{u, u} f = o ∧ (#ι) = o.card :=
  ⟨_, _, lsub_typein o, mk_ordinal_out o⟩
#align ordinal.card_mem_cof ordinal.card_mem_cof

/-- The set in the `lsub` characterization of `cof` is nonempty. -/
theorem cof_lsub_def_nonempty (o) :
    { a : Cardinal | ∃ (ι : _)(f : ι → Ordinal), lsub.{u, u} f = o ∧ (#ι) = a }.Nonempty :=
  ⟨_, card_mem_cof⟩
#align ordinal.cof_lsub_def_nonempty Ordinal.cof_lsub_def_nonempty

theorem cof_eq_Inf_lsub (o : Ordinal.{u}) :
    cof o = infₛ { a : Cardinal | ∃ (ι : Type u)(f : ι → Ordinal), lsub.{u, u} f = o ∧ (#ι) = a } :=
  by
  refine' le_antisymm (le_cinfₛ (cof_lsub_def_nonempty o) _) (cinfₛ_le' _)
  · rintro a ⟨ι, f, hf, rfl⟩
    rw [← type_lt o]
    refine'
      (cof_type_le fun a => _).trans
        (@mk_le_of_injective _ _
          (fun s : typein ((· < ·) : o.out.α → o.out.α → Prop) ⁻¹' Set.range f =>
            Classical.choose s.Prop)
          fun s t hst => by
          let H := congr_arg f hst
          rwa [Classical.choose_spec s.prop, Classical.choose_spec t.prop, typein_inj,
            Subtype.coe_inj] at H)
    have := typein_lt_self a
    simp_rw [← hf, lt_lsub_iff] at this
    cases' this with i hi
    refine' ⟨enum (· < ·) (f i) _, _, _⟩
    · rw [type_lt, ← hf]
      apply lt_lsub
    · rw [mem_preimage, typein_enum]
      exact mem_range_self i
    · rwa [← typein_le_typein, typein_enum]
  · rcases cof_eq (· < ·) with ⟨S, hS, hS'⟩
    let f : S → Ordinal := fun s => typein (· < ·) s.val
    refine'
      ⟨S, f, le_antisymm (lsub_le fun i => typein_lt_self i) (le_of_forall_lt fun a ha => _), by
        rwa [type_lt o] at hS'⟩
    rw [← type_lt o] at ha
    rcases hS (enum (· < ·) a ha) with ⟨b, hb, hb'⟩
    rw [← typein_le_typein, typein_enum] at hb'
    exact hb'.trans_lt (lt_lsub.{u, u} f ⟨b, hb⟩)
#align ordinal.cof_eq_Inf_lsub Ordinal.cof_eq_Inf_lsub

@[simp]
theorem lift_cof (o) : (cof o).lift = cof o.lift :=
  by
  refine' induction_on o _
  intro α r _
  apply le_antisymm
  · refine' le_cof_type.2 fun S H => _
    have : (#ULift.up ⁻¹' S).lift ≤ (#S) :=
      by
      rw [← Cardinal.lift_umax, ← Cardinal.lift_id' (#S)]
      exact mk_preimage_of_injective_lift ULift.up _ ULift.up_injective
    refine' (Cardinal.lift_le.2 <| cof_type_le _).trans this
    exact fun a =>
      let ⟨⟨b⟩, bs, br⟩ := H ⟨a⟩
      ⟨b, bs, br⟩
  · rcases cof_eq r with ⟨S, H, e'⟩
    have : (#ULift.down ⁻¹' S) ≤ (#S).lift :=
      ⟨⟨fun ⟨⟨x⟩, h⟩ => ⟨⟨x, h⟩⟩, fun ⟨⟨x⟩, h₁⟩ ⟨⟨y⟩, h₂⟩ e => by
          simp at e <;> congr <;> injections⟩⟩
    rw [e'] at this
    refine' (cof_type_le _).trans this
    exact fun ⟨a⟩ =>
      let ⟨b, bs, br⟩ := H a
      ⟨⟨b⟩, bs, br⟩
#align ordinal.lift_cof Ordinal.lift_cof

theorem cof_le_card (o) : cof o ≤ card o :=
  by
  rw [cof_eq_Inf_lsub]
  exact cinfₛ_le' card_mem_cof
#align ordinal.cof_le_card Ordinal.cof_le_card

theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by simpa using cof_le_card c.ord
#align ordinal.cof_ord_le Ordinal.cof_ord_le

theorem ord_cof_le (o : Ordinal.{u}) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)
#align ordinal.ord_cof_le Ordinal.ord_cof_le

theorem exists_lsub_cof (o : Ordinal) :
    ∃ (ι : _)(f : ι → Ordinal), lsub.{u, u} f = o ∧ (#ι) = cof o :=
  by
  rw [cof_eq_Inf_lsub]
  exact cinfₛ_mem (cof_lsub_def_nonempty o)
#align ordinal.exists_lsub_cof Ordinal.exists_lsub_cof

theorem cof_lsub_le {ι} (f : ι → Ordinal) : cof (lsub.{u, u} f) ≤ (#ι) :=
  by
  rw [cof_eq_Inf_lsub]
  exact cinfₛ_le' ⟨ι, f, rfl, rfl⟩
#align ordinal.cof_lsub_le Ordinal.cof_lsub_le

theorem cof_lsub_le_lift {ι} (f : ι → Ordinal) : cof (lsub f) ≤ Cardinal.lift.{v, u} (#ι) :=
  by
  rw [← mk_ulift]
  convert cof_lsub_le fun i : ULift ι => f i.down
  exact
    lsub_eq_of_range_eq.{u, max u v, max u v}
      (Set.ext fun x => ⟨fun ⟨i, hi⟩ => ⟨ULift.up i, hi⟩, fun ⟨i, hi⟩ => ⟨_, hi⟩⟩)
#align ordinal.cof_lsub_le_lift Ordinal.cof_lsub_le_lift

theorem le_cof_iff_lsub {o : Ordinal} {a : Cardinal} :
    a ≤ cof o ↔ ∀ {ι} (f : ι → Ordinal), lsub.{u, u} f = o → a ≤ (#ι) :=
  by
  rw [cof_eq_Inf_lsub]
  exact
    (le_cinfₛ_iff'' (cof_lsub_def_nonempty o)).trans
      ⟨fun H ι f hf => H _ ⟨ι, f, hf, rfl⟩, fun H b ⟨ι, f, hf, hb⟩ =>
        by
        rw [← hb]
        exact H _ hf⟩
#align ordinal.le_cof_iff_lsub Ordinal.le_cof_iff_lsub

theorem lsub_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift (#ι) < c.cof)
    (hf : ∀ i, f i < c) : lsub.{u, v} f < c :=
  lt_of_le_of_ne (lsub_le hf) fun h => by
    subst h
    exact (cof_lsub_le_lift f).not_lt hι
#align ordinal.lsub_lt_ord_lift Ordinal.lsub_lt_ord_lift

theorem lsub_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : (#ι) < c.cof) :
    (∀ i, f i < c) → lsub.{u, u} f < c :=
  lsub_lt_ord_lift (by rwa [(#ι).lift_id])
#align ordinal.lsub_lt_ord Ordinal.lsub_lt_ord

theorem cof_sup_le_lift {ι} {f : ι → Ordinal} (H : ∀ i, f i < sup f) : cof (sup f) ≤ (#ι).lift :=
  by
  rw [← sup_eq_lsub_iff_lt_sup] at H
  rw [H]
  exact cof_lsub_le_lift f
#align ordinal.cof_sup_le_lift Ordinal.cof_sup_le_lift

theorem cof_sup_le {ι} {f : ι → Ordinal} (H : ∀ i, f i < sup.{u, u} f) :
    cof (sup.{u, u} f) ≤ (#ι) := by
  rw [← (#ι).lift_id]
  exact cof_sup_le_lift H
#align ordinal.cof_sup_le Ordinal.cof_sup_le

theorem sup_lt_ord_lift {ι} {f : ι → Ordinal} {c : Ordinal} (hι : Cardinal.lift (#ι) < c.cof)
    (hf : ∀ i, f i < c) : sup.{u, v} f < c :=
  (sup_le_lsub.{u, v} f).trans_lt (lsub_lt_ord_lift hι hf)
#align ordinal.sup_lt_ord_lift Ordinal.sup_lt_ord_lift

theorem sup_lt_ord {ι} {f : ι → Ordinal} {c : Ordinal} (hι : (#ι) < c.cof) :
    (∀ i, f i < c) → sup.{u, u} f < c :=
  sup_lt_ord_lift (by rwa [(#ι).lift_id])
#align ordinal.sup_lt_ord Ordinal.sup_lt_ord

theorem supr_lt_lift {ι} {f : ι → Cardinal} {c : Cardinal} (hι : Cardinal.lift (#ι) < c.ord.cof)
    (hf : ∀ i, f i < c) : supᵢ f < c :=
  by
  rw [← ord_lt_ord, supr_ord (Cardinal.bdd_above_range _)]
  refine' sup_lt_ord_lift hι fun i => _
  rw [ord_lt_ord]
  apply hf
#align ordinal.supr_lt_lift Ordinal.supr_lt_lift

theorem supr_lt {ι} {f : ι → Cardinal} {c : Cardinal} (hι : (#ι) < c.ord.cof) :
    (∀ i, f i < c) → supᵢ f < c :=
  supr_lt_lift (by rwa [(#ι).lift_id])
#align ordinal.supr_lt Ordinal.supr_lt

theorem nfp_family_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : (#ι).lift < cof c) (hf : ∀ (i), ∀ b < c, f i b < c) {a} (ha : a < c) :
    nfpFamily.{u, v} f a < c :=
  by
  refine' sup_lt_ord_lift ((Cardinal.lift_le.2 (mk_list_le_max ι)).trans_lt _) fun l => _
  · rw [lift_max]
    apply max_lt _ hc'
    rwa [Cardinal.lift_aleph_0]
  · induction' l with i l H
    · exact ha
    · exact hf _ _ H
#align ordinal.nfp_family_lt_ord_lift Ordinal.nfp_family_lt_ord_lift

theorem nfp_family_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hc' : (#ι) < cof c)
    (hf : ∀ (i), ∀ b < c, f i b < c) {a} : a < c → nfpFamily.{u, u} f a < c :=
  nfp_family_lt_ord_lift hc (by rwa [(#ι).lift_id]) hf
#align ordinal.nfp_family_lt_ord Ordinal.nfp_family_lt_ord

theorem nfp_bfamily_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : o.card.lift < cof c) (hf : ∀ (i hi), ∀ b < c, f i hi b < c) {a} :
    a < c → nfpBfamily.{u, v} o f a < c :=
  nfp_family_lt_ord_lift hc (by rwa [mk_ordinal_out]) fun i => hf _ _
#align ordinal.nfp_bfamily_lt_ord_lift Ordinal.nfp_bfamily_lt_ord_lift

theorem nfp_bfamily_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c)
    (hc' : o.card < cof c) (hf : ∀ (i hi), ∀ b < c, f i hi b < c) {a} :
    a < c → nfpBfamily.{u, u} o f a < c :=
  nfp_bfamily_lt_ord_lift hc (by rwa [o.card.lift_id]) hf
#align ordinal.nfp_bfamily_lt_ord Ordinal.nfp_bfamily_lt_ord

theorem nfp_lt_ord {f : Ordinal → Ordinal} {c} (hc : ℵ₀ < cof c) (hf : ∀ i < c, f i < c) {a} :
    a < c → nfp f a < c :=
  nfp_family_lt_ord_lift hc (by simpa using cardinal.one_lt_aleph_0.trans hc) fun _ => hf
#align ordinal.nfp_lt_ord Ordinal.nfp_lt_ord

theorem exists_blsub_cof (o : Ordinal) : ∃ f : ∀ a < (cof o).ord, Ordinal, blsub.{u, u} _ f = o :=
  by
  rcases exists_lsub_cof o with ⟨ι, f, hf, hι⟩
  rcases Cardinal.ord_eq ι with ⟨r, hr, hι'⟩
  rw [← @blsub_eq_lsub' ι r hr] at hf
  rw [← hι, hι']
  exact ⟨_, hf⟩
#align ordinal.exists_blsub_cof Ordinal.exists_blsub_cof

theorem le_cof_iff_blsub {b : Ordinal} {a : Cardinal} :
    a ≤ cof b ↔ ∀ {o} (f : ∀ a < o, Ordinal), blsub.{u, u} o f = b → a ≤ o.card :=
  le_cof_iff_lsub.trans
    ⟨fun H o f hf => by simpa using H _ hf, fun H ι f hf =>
      by
      rcases Cardinal.ord_eq ι with ⟨r, hr, hι'⟩
      rw [← @blsub_eq_lsub' ι r hr] at hf
      simpa using H _ hf⟩
#align ordinal.le_cof_iff_blsub Ordinal.le_cof_iff_blsub

theorem cof_blsub_le_lift {o} (f : ∀ a < o, Ordinal) :
    cof (blsub o f) ≤ Cardinal.lift.{v, u} o.card :=
  by
  convert cof_lsub_le_lift _
  exact (mk_ordinal_out o).symm
#align ordinal.cof_blsub_le_lift Ordinal.cof_blsub_le_lift

theorem cof_blsub_le {o} (f : ∀ a < o, Ordinal) : cof (blsub.{u, u} o f) ≤ o.card :=
  by
  rw [← o.card.lift_id]
  exact cof_blsub_le_lift f
#align ordinal.cof_blsub_le Ordinal.cof_blsub_le

theorem blsub_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : o.card.lift < c.cof) (hf : ∀ i hi, f i hi < c) : blsub.{u, v} o f < c :=
  lt_of_le_of_ne (blsub_le hf) fun h =>
    ho.not_le (by simpa [← supr_ord, hf, h] using cof_blsub_le_lift.{u} f)
#align ordinal.blsub_lt_ord_lift Ordinal.blsub_lt_ord_lift

theorem blsub_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof)
    (hf : ∀ i hi, f i hi < c) : blsub.{u, u} o f < c :=
  blsub_lt_ord_lift (by rwa [o.card.lift_id]) hf
#align ordinal.blsub_lt_ord Ordinal.blsub_lt_ord

theorem cof_bsup_le_lift {o : Ordinal} {f : ∀ a < o, Ordinal} (H : ∀ i h, f i h < bsup o f) :
    cof (bsup o f) ≤ o.card.lift :=
  by
  rw [← bsup_eq_blsub_iff_lt_bsup] at H
  rw [H]
  exact cof_blsub_le_lift f
#align ordinal.cof_bsup_le_lift Ordinal.cof_bsup_le_lift

theorem cof_bsup_le {o : Ordinal} {f : ∀ a < o, Ordinal} :
    (∀ i h, f i h < bsup.{u, u} o f) → cof (bsup.{u, u} o f) ≤ o.card :=
  by
  rw [← o.card.lift_id]
  exact cof_bsup_le_lift
#align ordinal.cof_bsup_le Ordinal.cof_bsup_le

theorem bsup_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal}
    (ho : o.card.lift < c.cof) (hf : ∀ i hi, f i hi < c) : bsup.{u, v} o f < c :=
  (bsup_le_blsub f).trans_lt (blsub_lt_ord_lift ho hf)
#align ordinal.bsup_lt_ord_lift Ordinal.bsup_lt_ord_lift

theorem bsup_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal} {c : Ordinal} (ho : o.card < c.cof) :
    (∀ i hi, f i hi < c) → bsup.{u, u} o f < c :=
  bsup_lt_ord_lift (by rwa [o.card.lift_id])
#align ordinal.bsup_lt_ord Ordinal.bsup_lt_ord

/-! ### Basic results -/


@[simp]
theorem cof_zero : cof 0 = 0 :=
  (cof_le_card 0).antisymm (Cardinal.zero_le _)
#align ordinal.cof_zero Ordinal.cof_zero

@[simp]
theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 :=
  ⟨(induction_on o) fun α r _ z =>
      let ⟨S, hl, e⟩ := cof_eq r
      type_eq_zero_iff_is_empty.2 <|
        ⟨fun a =>
          let ⟨b, h, _⟩ := hl a
          (mk_eq_zero_iff.1 (e.trans z)).elim' ⟨_, h⟩⟩,
    fun e => by simp [e]⟩
#align ordinal.cof_eq_zero Ordinal.cof_eq_zero

theorem cof_ne_zero {o} : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero.Not
#align ordinal.cof_ne_zero Ordinal.cof_ne_zero

@[simp]
theorem cof_succ (o) : cof (succ o) = 1 :=
  by
  apply le_antisymm
  · refine' induction_on o fun α r _ => _
    change cof (type _) ≤ _
    rw [← (_ : (#_) = 1)]
    apply cof_type_le
    · refine' fun a => ⟨Sum.inr PUnit.unit, Set.mem_singleton _, _⟩
      rcases a with (a | ⟨⟨⟨⟩⟩⟩) <;> simp [EmptyRelation]
    · rw [Cardinal.mk_fintype, Set.card_singleton]
      simp
  · rw [← Cardinal.succ_zero, succ_le_iff]
    simpa [lt_iff_le_and_ne, Cardinal.zero_le] using fun h =>
      succ_ne_zero o (cof_eq_zero.1 (Eq.symm h))
#align ordinal.cof_succ Ordinal.cof_succ

@[simp]
theorem cof_eq_one_iff_is_succ {o} : cof.{u} o = 1 ↔ ∃ a, o = succ a :=
  ⟨(induction_on o) fun α r _ z => by
      skip
      rcases cof_eq r with ⟨S, hl, e⟩; rw [z] at e
      cases' mk_ne_zero_iff.1 (by rw [e] <;> exact one_ne_zero) with a
      refine'
        ⟨typein r a,
          Eq.symm <|
            Quotient.sound
              ⟨RelIso.ofSurjective (RelEmbedding.ofMonotone _ fun x y => _) fun x => _⟩⟩
      · apply Sum.rec <;> [exact Subtype.val, exact fun _ => a]
      · rcases x with (x | ⟨⟨⟨⟩⟩⟩) <;> rcases y with (y | ⟨⟨⟨⟩⟩⟩) <;>
          simp [Subrel, Order.Preimage, EmptyRelation]
        exact x.2
      · suffices r x a ∨ ∃ b : PUnit, ↑a = x by simpa
        rcases trichotomous_of r x a with (h | h | h)
        · exact Or.inl h
        · exact Or.inr ⟨PUnit.unit, h.symm⟩
        · rcases hl x with ⟨a', aS, hn⟩
          rw [(_ : ↑a = a')] at h
          · exact absurd h hn
          refine' congr_arg Subtype.val (_ : a = ⟨a', aS⟩)
          haveI := le_one_iff_subsingleton.1 (le_of_eq e)
          apply Subsingleton.elim,
    fun ⟨a, e⟩ => by simp [e]⟩
#align ordinal.cof_eq_one_iff_is_succ Ordinal.cof_eq_one_iff_is_succ

/-- A fundamental sequence for `a` is an increasing sequence of length `o = cof a` that converges at
    `a`. We provide `o` explicitly in order to avoid type rewrites. -/
def IsFundamentalSequence (a o : Ordinal.{u}) (f : ∀ b < o, Ordinal.{u}) : Prop :=
  o ≤ a.cof.ord ∧ (∀ {i j} (hi hj), i < j → f i hi < f j hj) ∧ blsub.{u, u} o f = a
#align ordinal.is_fundamental_sequence Ordinal.IsFundamentalSequence

namespace IsFundamentalSequence

variable {a o : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}}

protected theorem cof_eq (hf : IsFundamentalSequence a o f) : a.cof.ord = o :=
  hf.1.antisymm' <| by
    rw [← hf.2.2]
    exact (ord_le_ord.2 (cof_blsub_le f)).trans (ord_card_le o)
#align ordinal.is_fundamental_sequence.cof_eq Ordinal.IsFundamentalSequence.cof_eq

protected theorem strict_mono (hf : IsFundamentalSequence a o f) {i j} :
    ∀ hi hj, i < j → f i hi < f j hj :=
  hf.2.1
#align ordinal.is_fundamental_sequence.strict_mono Ordinal.IsFundamentalSequence.strict_mono

theorem blsub_eq (hf : IsFundamentalSequence a o f) : blsub.{u, u} o f = a :=
  hf.2.2
#align ordinal.is_fundamental_sequence.blsub_eq Ordinal.IsFundamentalSequence.blsub_eq

theorem ord_cof (hf : IsFundamentalSequence a o f) :
    IsFundamentalSequence a a.cof.ord fun i hi => f i (hi.trans_le (by rw [hf.cof_eq])) :=
  by
  have H := hf.cof_eq
  subst H
  exact hf
#align ordinal.is_fundamental_sequence.ord_cof Ordinal.IsFundamentalSequence.ord_cof

theorem id_of_le_cof (h : o ≤ o.cof.ord) : IsFundamentalSequence o o fun a _ => a :=
  ⟨h, fun _ _ _ _ => id, blsub_id o⟩
#align ordinal.is_fundamental_sequence.id_of_le_cof Ordinal.IsFundamentalSequence.id_of_le_cof

protected theorem zero {f : ∀ b < (0 : Ordinal), Ordinal} : IsFundamentalSequence 0 0 f :=
  ⟨by rw [cof_zero, ord_zero], fun i j hi => (Ordinal.not_lt_zero i hi).elim, blsub_zero f⟩
#align ordinal.is_fundamental_sequence.zero Ordinal.IsFundamentalSequence.zero

protected theorem succ : IsFundamentalSequence (succ o) 1 fun _ _ => o :=
  by
  refine' ⟨_, fun i j hi hj h => _, blsub_const Ordinal.one_ne_zero o⟩
  · rw [cof_succ, ord_one]
  · rw [lt_one_iff_zero] at hi hj
    rw [hi, hj] at h
    exact h.false.elim
#align ordinal.is_fundamental_sequence.succ Ordinal.IsFundamentalSequence.succ

protected theorem monotone (hf : IsFundamentalSequence a o f) {i j : Ordinal} (hi : i < o)
    (hj : j < o) (hij : i ≤ j) : f i hi ≤ f j hj :=
  by
  rcases lt_or_eq_of_le hij with (hij | rfl)
  · exact (hf.2.1 hi hj hij).le
  · rfl
#align ordinal.is_fundamental_sequence.monotone Ordinal.IsFundamentalSequence.monotone

theorem trans {a o o' : Ordinal.{u}} {f : ∀ b < o, Ordinal.{u}} (hf : IsFundamentalSequence a o f)
    {g : ∀ b < o', Ordinal.{u}} (hg : IsFundamentalSequence o o' g) :
    IsFundamentalSequence a o' fun i hi =>
      f (g i hi)
        (by
          rw [← hg.2.2]
          apply lt_blsub) :=
  by
  refine' ⟨_, fun i j _ _ h => hf.2.1 _ _ (hg.2.1 _ _ h), _⟩
  · rw [hf.cof_eq]
    exact hg.1.trans (ord_cof_le o)
  · rw [@blsub_comp.{u, u, u} o _ f (@is_fundamental_sequence.monotone _ _ f hf)]
    exact hf.2.2
#align ordinal.is_fundamental_sequence.trans Ordinal.IsFundamentalSequence.trans

end IsFundamentalSequence

/-- Every ordinal has a fundamental sequence. -/
theorem exists_fundamental_sequence (a : Ordinal.{u}) : ∃ f, IsFundamentalSequence a a.cof.ord f :=
  by
  rsuffices ⟨o, f, hf⟩ : ∃ o f, is_fundamental_sequence a o f
  · exact ⟨_, hf.ord_cof⟩
  rcases exists_lsub_cof a with ⟨ι, f, hf, hι⟩
  rcases ord_eq ι with ⟨r, wo, hr⟩
  haveI := wo
  let r' := Subrel r { i | ∀ j, r j i → f j < f i }
  let hrr' : r' ↪r r := Subrel.relEmbedding _ _
  haveI := hrr'.is_well_order
  refine'
    ⟨_, _, hrr'.ordinal_type_le.trans _, fun i j _ h _ => (enum r' j h).Prop _ _,
      le_antisymm (blsub_le fun i hi => lsub_le_iff.1 hf.le _) _⟩
  · rw [← hι, hr]
  · change r (hrr'.1 _) (hrr'.1 _)
    rwa [hrr'.2, @enum_lt_enum _ r']
  · rw [← hf, lsub_le_iff]
    intro i
    rsuffices ⟨i', hi', hfg⟩ : ∃ i' hi', f i ≤ bfamily_of_family' r' (fun i => f i) i' hi'
    · exact hfg.trans_lt (lt_blsub _ _ _)
    by_cases h : ∀ j, r j i → f j < f i
    · refine' ⟨typein r' ⟨i, h⟩, typein_lt_type _ _, _⟩
      rw [bfamily_of_family'_typein]
      rfl
    · push_neg  at h
      cases' wo.wf.min_mem _ h with hji hij
      refine' ⟨typein r' ⟨_, fun k hkj => lt_of_lt_of_le _ hij⟩, typein_lt_type _ _, _⟩
      · by_contra' H
        exact (wo.wf.not_lt_min _ h ⟨IsTrans.trans _ _ _ hkj hji, H⟩) hkj
      · rwa [bfamily_of_family'_typein]
#align ordinal.exists_fundamental_sequence Ordinal.exists_fundamental_sequence

@[simp]
theorem cof_cof (a : Ordinal.{u}) : cof (cof a).ord = cof a :=
  by
  cases' exists_fundamental_sequence a with f hf
  cases' exists_fundamental_sequence a.cof.ord with g hg
  exact ord_injective (hf.trans hg).cof_eq.symm
#align ordinal.cof_cof Ordinal.cof_cof

protected theorem IsNormal.is_fundamental_sequence {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f)
    {a o} (ha : IsLimit a) {g} (hg : IsFundamentalSequence a o g) :
    IsFundamentalSequence (f a) o fun b hb => f (g b hb) :=
  by
  refine' ⟨_, fun i j _ _ h => hf.strict_mono (hg.2.1 _ _ h), _⟩
  · rcases exists_lsub_cof (f a) with ⟨ι, f', hf', hι⟩
    rw [← hg.cof_eq, ord_le_ord, ← hι]
    suffices (lsub.{u, u} fun i => Inf { b : Ordinal | f' i ≤ f b }) = a
      by
      rw [← this]
      apply cof_lsub_le
    have H : ∀ i, ∃ b < a, f' i ≤ f b := fun i =>
      by
      have := lt_lsub.{u, u} f' i
      rwa [hf', ← IsNormal.blsub_eq.{u, u} hf ha, lt_blsub_iff] at this
    refine' (lsub_le fun i => _).antisymm (le_of_forall_lt fun b hb => _)
    · rcases H i with ⟨b, hb, hb'⟩
      exact lt_of_le_of_lt (cinfₛ_le' hb') hb
    · have := hf.strict_mono hb
      rw [← hf', lt_lsub_iff] at this
      cases' this with i hi
      rcases H i with ⟨b, _, hb⟩
      exact
        ((le_cinfₛ_iff'' ⟨b, hb⟩).2 fun c hc => hf.strict_mono.le_iff_le.1 (hi.trans hc)).trans_lt
          (lt_lsub _ i)
  · rw [@blsub_comp.{u, u, u} a _ (fun b _ => f b) (fun i j hi hj h => hf.strict_mono.monotone h) g
        hg.2.2]
    exact IsNormal.blsub_eq.{u, u} hf ha
#align ordinal.is_normal.is_fundamental_sequence Ordinal.IsNormal.is_fundamental_sequence

theorem IsNormal.cof_eq {f} (hf : IsNormal f) {a} (ha : IsLimit a) : cof (f a) = cof a :=
  let ⟨g, hg⟩ := exists_fundamental_sequence a
  ord_injective (hf.IsFundamentalSequence ha hg).cof_eq
#align ordinal.is_normal.cof_eq Ordinal.IsNormal.cof_eq

theorem IsNormal.cof_le {f} (hf : IsNormal f) (a) : cof a ≤ cof (f a) :=
  by
  rcases zero_or_succ_or_limit a with (rfl | ⟨b, rfl⟩ | ha)
  · rw [cof_zero]
    exact zero_le _
  · rw [cof_succ, Cardinal.one_le_iff_ne_zero, cof_ne_zero, ← Ordinal.pos_iff_ne_zero]
    exact (Ordinal.zero_le (f b)).trans_lt (hf.1 b)
  · rw [hf.cof_eq ha]
#align ordinal.is_normal.cof_le Ordinal.IsNormal.cof_le

@[simp]
theorem cof_add (a b : Ordinal) : b ≠ 0 → cof (a + b) = cof b := fun h =>
  by
  rcases zero_or_succ_or_limit b with (rfl | ⟨c, rfl⟩ | hb)
  · contradiction
  · rw [add_succ, cof_succ, cof_succ]
  · exact (add_is_normal a).cof_eq hb
#align ordinal.cof_add Ordinal.cof_add

theorem aleph_0_le_cof {o} : ℵ₀ ≤ cof o ↔ IsLimit o :=
  by
  rcases zero_or_succ_or_limit o with (rfl | ⟨o, rfl⟩ | l)
  · simp [not_zero_is_limit, Cardinal.aleph_0_ne_zero]
  · simp [not_succ_is_limit, Cardinal.one_lt_aleph_0]
  · simp [l]
    refine' le_of_not_lt fun h => _
    cases' Cardinal.lt_aleph_0.1 h with n e
    have := cof_cof o
    rw [e, ord_nat] at this
    cases n
    · simp at e
      simpa [e, not_zero_is_limit] using l
    · rw [nat_cast_succ, cof_succ] at this
      rw [← this, cof_eq_one_iff_is_succ] at e
      rcases e with ⟨a, rfl⟩
      exact not_succ_is_limit _ l
#align ordinal.aleph_0_le_cof Ordinal.aleph_0_le_cof

@[simp]
theorem aleph'_cof {o : Ordinal} (ho : o.IsLimit) : (aleph' o).ord.cof = o.cof :=
  aleph'_is_normal.cof_eq ho
#align ordinal.aleph'_cof Ordinal.aleph'_cof

@[simp]
theorem aleph_cof {o : Ordinal} (ho : o.IsLimit) : (aleph o).ord.cof = o.cof :=
  aleph_is_normal.cof_eq ho
#align ordinal.aleph_cof Ordinal.aleph_cof

@[simp]
theorem cof_omega : cof ω = ℵ₀ :=
  (aleph_0_le_cof.2 omega_is_limit).antisymm' <|
    by
    rw [← card_omega]
    apply cof_le_card
#align ordinal.cof_omega Ordinal.cof_omega

theorem cof_eq' (r : α → α → Prop) [IsWellOrder α r] (h : IsLimit (type r)) :
    ∃ S : Set α, (∀ a, ∃ b ∈ S, r a b) ∧ (#S) = cof (type r) :=
  let ⟨S, H, e⟩ := cof_eq r
  ⟨S, fun a =>
    let a' := enum r _ (h.2 _ (typein_lt_type r a))
    let ⟨b, h, ab⟩ := H a'
    ⟨b, h,
      (IsOrderConnected.conn a b a' <|
            (typein_lt_typein r).1
              (by
                rw [typein_enum]
                exact lt_succ (typein _ _))).resolve_right
        ab⟩,
    e⟩
#align ordinal.cof_eq' Ordinal.cof_eq'

@[simp]
theorem cof_univ : cof univ.{u, v} = Cardinal.univ :=
  le_antisymm (cof_le_card _)
    (by
      refine' le_of_forall_lt fun c h => _
      rcases lt_univ'.1 h with ⟨c, rfl⟩
      rcases@cof_eq Ordinal.{u} (· < ·) _ with ⟨S, H, Se⟩
      rw [univ, ← lift_cof, ← Cardinal.lift_lift, Cardinal.lift_lt, ← Se]
      refine' lt_of_not_ge fun h => _
      cases' Cardinal.lift_down h with a e
      refine' Quotient.induction_on a (fun α e => _) e
      cases' Quotient.exact e with f
      have f := equiv.ulift.symm.trans f
      let g a := (f a).1
      let o := succ (sup.{u, u} g)
      rcases H o with ⟨b, h, l⟩
      refine' l (lt_succ_iff.2 _)
      rw [← show g (f.symm ⟨b, h⟩) = b by dsimp [g] <;> simp]
      apply le_sup)
#align ordinal.cof_univ Ordinal.cof_univ

/-! ### Infinite pigeonhole principle -/


/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : IsWellOrder α r] {s : Set (Set α)}
    (h₁ : Unbounded r <| ⋃₀ s) (h₂ : (#s) < StrictOrder.cof r) : ∃ x ∈ s, Unbounded r x :=
  by
  by_contra' h
  simp_rw [not_unbounded_iff] at h
  let f : s → α := fun x : s => wo.wf.sup x (h x.1 x.2)
  refine' h₂.not_le (le_trans (cinfₛ_le' ⟨range f, fun x => _, rfl⟩) mk_range_le)
  rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩
  exact ⟨f ⟨c, hc⟩, mem_range_self _, fun hxz => hxy (trans (wo.wf.lt_sup _ hy) hxz)⟩
#align ordinal.unbounded_of_unbounded_sUnion Ordinal.unbounded_of_unbounded_sUnion

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_Union {α β : Type u} (r : α → α → Prop) [wo : IsWellOrder α r]
    (s : β → Set α) (h₁ : Unbounded r <| ⋃ x, s x) (h₂ : (#β) < StrictOrder.cof r) :
    ∃ x : β, Unbounded r (s x) := by
  rw [← sUnion_range] at h₁
  rcases unbounded_of_unbounded_sUnion r h₁ (mk_range_le.trans_lt h₂) with ⟨_, ⟨x, rfl⟩, u⟩
  exact ⟨x, u⟩
#align ordinal.unbounded_of_unbounded_Union Ordinal.unbounded_of_unbounded_Union

/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : ℵ₀ ≤ (#β)) (h₂ : (#α) < (#β).ord.cof) :
    ∃ a : α, (#f ⁻¹' {a}) = (#β) :=
  by
  have : ∃ a, (#β) ≤ (#f ⁻¹' {a}) := by
    by_contra' h
    apply mk_univ.not_lt
    rw [← preimage_univ, ← Union_of_singleton, preimage_Union]
    exact
      mk_Union_le_sum_mk.trans_lt
        ((sum_le_supr _).trans_lt <| mul_lt_of_lt h₁ (h₂.trans_le <| cof_ord_le _) (supr_lt h₂ h))
  cases' this with x h
  refine' ⟨x, h.antisymm' _⟩
  rw [le_mk_iff_exists_set]
  exact ⟨_, rfl⟩
#align ordinal.infinite_pigeonhole Ordinal.infinite_pigeonhole

/-- Pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : Cardinal) (hθ : θ ≤ (#β))
    (h₁ : ℵ₀ ≤ θ) (h₂ : (#α) < θ.ord.cof) : ∃ a : α, θ ≤ (#f ⁻¹' {a}) :=
  by
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩
  cases' infinite_pigeonhole (f ∘ Subtype.val : s → α) h₁ h₂ with a ha
  use a; rw [← ha, @preimage_comp _ _ _ Subtype.val f]
  exact mk_preimage_of_injective _ _ Subtype.val_injective
#align ordinal.infinite_pigeonhole_card Ordinal.infinite_pigeonhole_card

theorem infinite_pigeonhole_set {β α : Type u} {s : Set β} (f : s → α) (θ : Cardinal)
    (hθ : θ ≤ (#s)) (h₁ : ℵ₀ ≤ θ) (h₂ : (#α) < θ.ord.cof) :
    ∃ (a : α)(t : Set β)(h : t ⊆ s), θ ≤ (#t) ∧ ∀ ⦃x⦄ (hx : x ∈ t), f ⟨x, h hx⟩ = a :=
  by
  cases' infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha
  refine' ⟨a, { x | ∃ h, f ⟨x, h⟩ = a }, _, _, _⟩
  · rintro x ⟨hx, hx'⟩
    exact hx
  · refine'
      ha.trans
        (ge_of_eq <|
          Quotient.sound ⟨Equiv.trans _ (Equiv.subtypeSubtypeEquivSubtypeExists _ _).symm⟩)
    simp only [coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_set_of_eq]
  rintro x ⟨hx, hx'⟩; exact hx'
#align ordinal.infinite_pigeonhole_set Ordinal.infinite_pigeonhole_set

end Ordinal

/-! ### Regular and inaccessible cardinals -/


namespace Cardinal

open Ordinal

-- mathport name: cardinal.pow
local infixr:0 "^" => @pow Cardinal.{u} Cardinal Cardinal.hasPow

/-- A cardinal is a limit if it is not zero or a successor
  cardinal. Note that `ℵ₀` is a limit cardinal by this definition. -/
def IsLimit (c : Cardinal) : Prop :=
  c ≠ 0 ∧ ∀ x < c, succ x < c
#align cardinal.is_limit Cardinal.IsLimit

theorem IsLimit.ne_zero {c} (h : IsLimit c) : c ≠ 0 :=
  h.1
#align cardinal.is_limit.ne_zero Cardinal.IsLimit.ne_zero

theorem IsLimit.succ_lt {x c} (h : IsLimit c) : x < c → succ x < c :=
  h.2 x
#align cardinal.is_limit.succ_lt Cardinal.IsLimit.succ_lt

theorem IsLimit.aleph_0_le {c} (h : IsLimit c) : ℵ₀ ≤ c :=
  by
  by_contra' h'
  rcases lt_aleph_0.1 h' with ⟨_ | n, rfl⟩
  · exact h.1.irrefl
  · simpa using h.2 n
#align cardinal.is_limit.aleph_0_le Cardinal.IsLimit.aleph_0_le

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A cardinal is a strong limit if it is not zero and it is\n  closed under powersets. Note that `ℵ₀` is a strong limit by this definition. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `IsStrongLimit [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`c] [":" `Cardinal] [] ")")]
       [(Term.typeSpec ":" (Term.prop "Prop"))])
      (Command.declValSimple
       ":="
       («term_∧_»
        («term_≠_» `c "≠" (num "0"))
        "∧"
        (Std.ExtendedBinder.«term∀__,_»
         "∀"
         (Lean.binderIdent `x)
         (Std.ExtendedBinder.«binderTerm<_» "<" `c)
         ","
         («term_<_» (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x) "<" `c)))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∧_»
       («term_≠_» `c "≠" (num "0"))
       "∧"
       (Std.ExtendedBinder.«term∀__,_»
        "∀"
        (Lean.binderIdent `x)
        (Std.ExtendedBinder.«binderTerm<_» "<" `c)
        ","
        («term_<_» (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x) "<" `c)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `x)
       (Std.ExtendedBinder.«binderTerm<_» "<" `c)
       ","
       («term_<_» (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x) "<" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x) "<" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow', expected 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow._@.SetTheory.Cardinal.Cofinality._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A cardinal is a strong limit if it is not zero and it is
      closed under powersets. Note that `ℵ₀` is a strong limit by this definition. -/
  def IsStrongLimit ( c : Cardinal ) : Prop := c ≠ 0 ∧ ∀ x < c , 2 ^ x < c
#align cardinal.is_strong_limit Cardinal.IsStrongLimit

theorem IsStrongLimit.ne_zero {c} (h : IsStrongLimit c) : c ≠ 0 :=
  h.1
#align cardinal.is_strong_limit.ne_zero Cardinal.IsStrongLimit.ne_zero

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `IsStrongLimit.two_power_lt [])
      (Command.declSig
       [(Term.implicitBinder "{" [`x `c] [] "}")
        (Term.explicitBinder "(" [`h] [":" (Term.app `IsStrongLimit [`c])] [] ")")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term_<_» `x "<" `c)
         "→"
         («term_<_»
          (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
          "<"
          `c))))
      (Command.declValSimple ":=" (Term.app (Term.proj `h "." (fieldIdx "2")) [`x]) [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `h "." (fieldIdx "2")) [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `h "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_<_» `x "<" `c)
       "→"
       («term_<_» (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x) "<" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x) "<" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow', expected 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow._@.SetTheory.Cardinal.Cofinality._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem IsStrongLimit.two_power_lt { x c } ( h : IsStrongLimit c ) : x < c → 2 ^ x < c := h . 2 x
#align cardinal.is_strong_limit.two_power_lt Cardinal.IsStrongLimit.two_power_lt

theorem is_strong_limit_aleph_0 : IsStrongLimit ℵ₀ :=
  ⟨aleph_0_ne_zero, fun x hx => by
    rcases lt_aleph_0.1 hx with ⟨n, rfl⟩
    exact_mod_cast nat_lt_aleph_0 (pow 2 n)⟩
#align cardinal.is_strong_limit_aleph_0 Cardinal.is_strong_limit_aleph_0

theorem IsStrongLimit.is_limit {c} (H : IsStrongLimit c) : IsLimit c :=
  ⟨H.1, fun x h => (succ_le_of_lt <| cantor x).trans_lt (H.2 _ h)⟩
#align cardinal.is_strong_limit.is_limit Cardinal.IsStrongLimit.is_limit

theorem is_limit_aleph_0 : IsLimit ℵ₀ :=
  is_strong_limit_aleph_0.IsLimit
#align cardinal.is_limit_aleph_0 Cardinal.is_limit_aleph_0

theorem is_strong_limit_beth {o : Ordinal} (H : ∀ a < o, succ a < o) : IsStrongLimit (beth o) :=
  by
  rcases eq_or_ne o 0 with (rfl | h)
  · rw [beth_zero]
    exact is_strong_limit_aleph_0
  · refine' ⟨beth_ne_zero o, fun a ha => _⟩
    rw [beth_limit ⟨h, H⟩] at ha
    rcases exists_lt_of_lt_csupᵢ' ha with ⟨⟨i, hi⟩, ha⟩
    have := power_le_power_left two_ne_zero ha.le
    rw [← beth_succ] at this
    exact this.trans_lt (beth_lt.2 (H i hi))
#align cardinal.is_strong_limit_beth Cardinal.is_strong_limit_beth

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mk_bounded_subset [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `x)
           (Std.ExtendedBinder.«binderTerm<_»
            "<"
            (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))
           ","
           («term_<_»
            (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
            "<"
            (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))]
         []
         ")")
        (Term.implicitBinder
         "{"
         [`r]
         [":" (Term.arrow `α "→" (Term.arrow `α "→" (Term.prop "Prop")))]
         "}")
        (Term.instBinder "[" [] (Term.app `IsWellOrder [`α `r]) "]")
        (Term.explicitBinder
         "("
         [`hr]
         [":"
          («term_=_»
           (Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)
           "="
           (Term.app `type [`r]))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
          "#"
          («term{_:_//_}» "{" `s [":" (Term.app `Set [`α])] "//" (Term.app `Bounded [`r `s]) "}"))
         "="
         (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              (Term.app
               `eq_or_ne
               [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) (num "0")]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `ha)
                    "|"
                    (Std.Tactic.RCases.rcasesPat.one `ha)])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
             []
             (Std.Tactic.tacticHaveI_
              "haveI"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app (Term.proj `mk_eq_zero_iff "." (fieldIdx "1")) [`ha]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_eq_zero_iff)] "]")
              [])
             []
             (Tactic.constructor "constructor")
             []
             (Std.Tactic.rintro
              "rintro"
              [(Std.Tactic.RCases.rintroPat.one
                (Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                   [])]
                 "⟩"))]
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.app `not_unbounded_iff [`s]) "." (fieldIdx "2"))
               [`hs (Term.app `unbounded_of_is_empty [`s])]))])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h' []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `is_strong_limit
                 [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)]))]
              ":="
              (Term.anonymousCtor "⟨" [`ha "," `h] "⟩"))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl (Term.haveIdDecl [`ha []] [] ":=" `h'.is_limit.aleph_0_le)))
           []
           (Tactic.apply "apply" `le_antisymm)
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Set.«term{_|_}»
                    "{"
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `s)
                     [(group ":" (Term.app `Set [`α]))])
                    "|"
                    (Term.app `bounded [`r `s])
                    "}")
                   "="
                   (Set.Data.Set.Lattice.«term⋃_,_»
                    "⋃"
                    (Std.ExtendedBinder.extBinders
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                    ", "
                    (Set.term𝒫_
                     "𝒫"
                     (Set.«term{_|_}»
                      "{"
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [])
                      "|"
                      (Term.app `r [`j `i])
                      "}")))))]
                ":="
                (Term.app `set_of_exists [(Term.hole "_")]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_set_of)
                ","
                (Tactic.rwRule [] `this)]
               "]")
              [])
             []
             (convert
              "convert"
              []
              (Term.app
               `mk_Union_le_sum_mk.trans
               [(Term.app
                 (Term.proj (Term.app `sum_le_supr [(Term.hole "_")]) "." `trans)
                 [(Term.app `mul_le_max_of_aleph_0_le_left [`ha])])])
              [])
             []
             (Tactic.apply "apply" (Term.proj (Term.app `max_eq_left [(Term.hole "_")]) "." `symm))
             []
             (Tactic.apply
              "apply"
              (Term.app `csupᵢ_le' [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))
             []
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_powerset)] "]") [])
             []
             (Tactic.apply
              "apply"
              (Term.proj (Term.app `h'.two_power_lt [(Term.hole "_")]) "." `le))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `coe_set_of)
                ","
                (Tactic.rwRule [] `card_typein)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `lt_ord)
                ","
                (Tactic.rwRule [] `hr)]
               "]")
              [])
             []
             (Tactic.apply "apply" `typein_lt_type)])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.app
               (Term.explicit "@" `mk_le_of_injective)
               [`α
                (Term.hole "_")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
                  (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
                (Term.hole "_")]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.apply "apply" `bounded_singleton)
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)] "]")
                [])
               []
               (Tactic.apply "apply" (Term.app `ord_is_limit [`ha]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.intro "intro" [`a `b `hab])
               []
               (Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
                 ["using" `hab]))])])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              `eq_or_ne
              [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) (num "0")]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `ha) "|" (Std.Tactic.RCases.rcasesPat.one `ha)])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
            []
            (Std.Tactic.tacticHaveI_
             "haveI"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app (Term.proj `mk_eq_zero_iff "." (fieldIdx "1")) [`ha]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_eq_zero_iff)] "]")
             [])
            []
            (Tactic.constructor "constructor")
            []
            (Std.Tactic.rintro
             "rintro"
             [(Std.Tactic.RCases.rintroPat.one
               (Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
                  [])]
                "⟩"))]
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj (Term.app `not_unbounded_iff [`s]) "." (fieldIdx "2"))
              [`hs (Term.app `unbounded_of_is_empty [`s])]))])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h' []]
             [(Term.typeSpec
               ":"
               (Term.app
                `is_strong_limit
                [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)]))]
             ":="
             (Term.anonymousCtor "⟨" [`ha "," `h] "⟩"))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [`ha []] [] ":=" `h'.is_limit.aleph_0_le)))
          []
          (Tactic.apply "apply" `le_antisymm)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Set.«term{_|_}»
                   "{"
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `s)
                    [(group ":" (Term.app `Set [`α]))])
                   "|"
                   (Term.app `bounded [`r `s])
                   "}")
                  "="
                  (Set.Data.Set.Lattice.«term⋃_,_»
                   "⋃"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
                   ", "
                   (Set.term𝒫_
                    "𝒫"
                    (Set.«term{_|_}»
                     "{"
                     (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [])
                     "|"
                     (Term.app `r [`j `i])
                     "}")))))]
               ":="
               (Term.app `set_of_exists [(Term.hole "_")]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_set_of)
               ","
               (Tactic.rwRule [] `this)]
              "]")
             [])
            []
            (convert
             "convert"
             []
             (Term.app
              `mk_Union_le_sum_mk.trans
              [(Term.app
                (Term.proj (Term.app `sum_le_supr [(Term.hole "_")]) "." `trans)
                [(Term.app `mul_le_max_of_aleph_0_le_left [`ha])])])
             [])
            []
            (Tactic.apply "apply" (Term.proj (Term.app `max_eq_left [(Term.hole "_")]) "." `symm))
            []
            (Tactic.apply
             "apply"
             (Term.app `csupᵢ_le' [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))
            []
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_powerset)] "]") [])
            []
            (Tactic.apply "apply" (Term.proj (Term.app `h'.two_power_lt [(Term.hole "_")]) "." `le))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `coe_set_of)
               ","
               (Tactic.rwRule [] `card_typein)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `lt_ord)
               ","
               (Tactic.rwRule [] `hr)]
              "]")
             [])
            []
            (Tactic.apply "apply" `typein_lt_type)])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              (Term.explicit "@" `mk_le_of_injective)
              [`α
               (Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
               (Term.hole "_")]))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.apply "apply" `bounded_singleton)
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)] "]")
               [])
              []
              (Tactic.apply "apply" (Term.app `ord_is_limit [`ha]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.intro "intro" [`a `b `hab])
              []
              (Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                ["only"]
                [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
                ["using" `hab]))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          (Term.explicit "@" `mk_le_of_injective)
          [`α
           (Term.hole "_")
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
           (Term.hole "_")]))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.apply "apply" `bounded_singleton)
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)] "]")
           [])
          []
          (Tactic.apply "apply" (Term.app `ord_is_limit [`ha]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.intro "intro" [`a `b `hab])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
            ["using" `hab]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`a `b `hab])
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          ["only"]
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
          ["using" `hab]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
        ["using" `hab]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `singleton_eq_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a `b `hab])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.apply "apply" `bounded_singleton)
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)] "]")
         [])
        []
        (Tactic.apply "apply" (Term.app `ord_is_limit [`ha]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.app `ord_is_limit [`ha]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ord_is_limit [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ord_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hr)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `bounded_singleton)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `bounded_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.explicit "@" `mk_le_of_injective)
        [`α
         (Term.hole "_")
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `mk_le_of_injective)
       [`α
        (Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term{_}» "{" [`x] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`x]
       []
       "=>"
       (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `mk_le_of_injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_le_of_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `s)
                [(group ":" (Term.app `Set [`α]))])
               "|"
               (Term.app `bounded [`r `s])
               "}")
              "="
              (Set.Data.Set.Lattice.«term⋃_,_»
               "⋃"
               (Std.ExtendedBinder.extBinders
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
               ", "
               (Set.term𝒫_
                "𝒫"
                (Set.«term{_|_}»
                 "{"
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [])
                 "|"
                 (Term.app `r [`j `i])
                 "}")))))]
           ":="
           (Term.app `set_of_exists [(Term.hole "_")]))))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_set_of)
           ","
           (Tactic.rwRule [] `this)]
          "]")
         [])
        []
        (convert
         "convert"
         []
         (Term.app
          `mk_Union_le_sum_mk.trans
          [(Term.app
            (Term.proj (Term.app `sum_le_supr [(Term.hole "_")]) "." `trans)
            [(Term.app `mul_le_max_of_aleph_0_le_left [`ha])])])
         [])
        []
        (Tactic.apply "apply" (Term.proj (Term.app `max_eq_left [(Term.hole "_")]) "." `symm))
        []
        (Tactic.apply
         "apply"
         (Term.app `csupᵢ_le' [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_powerset)] "]") [])
        []
        (Tactic.apply "apply" (Term.proj (Term.app `h'.two_power_lt [(Term.hole "_")]) "." `le))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `coe_set_of)
           ","
           (Tactic.rwRule [] `card_typein)
           ","
           (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `lt_ord)
           ","
           (Tactic.rwRule [] `hr)]
          "]")
         [])
        []
        (Tactic.apply "apply" `typein_lt_type)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `typein_lt_type)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `typein_lt_type
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `coe_set_of)
         ","
         (Tactic.rwRule [] `card_typein)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `lt_ord)
         ","
         (Tactic.rwRule [] `hr)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_ord
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `card_typein
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_set_of
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.proj (Term.app `h'.two_power_lt [(Term.hole "_")]) "." `le))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `h'.two_power_lt [(Term.hole "_")]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `h'.two_power_lt [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h'.two_power_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `h'.two_power_lt [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_powerset)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_powerset
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app `csupᵢ_le' [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `csupᵢ_le' [(Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `csupᵢ_le'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.proj (Term.app `max_eq_left [(Term.hole "_")]) "." `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `max_eq_left [(Term.hole "_")]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `max_eq_left [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `max_eq_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `max_eq_left [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        `mk_Union_le_sum_mk.trans
        [(Term.app
          (Term.proj (Term.app `sum_le_supr [(Term.hole "_")]) "." `trans)
          [(Term.app `mul_le_max_of_aleph_0_le_left [`ha])])])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mk_Union_le_sum_mk.trans
       [(Term.app
         (Term.proj (Term.app `sum_le_supr [(Term.hole "_")]) "." `trans)
         [(Term.app `mul_le_max_of_aleph_0_le_left [`ha])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `sum_le_supr [(Term.hole "_")]) "." `trans)
       [(Term.app `mul_le_max_of_aleph_0_le_left [`ha])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_le_max_of_aleph_0_le_left [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_le_max_of_aleph_0_le_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `mul_le_max_of_aleph_0_le_left [`ha])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `sum_le_supr [(Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `sum_le_supr [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_le_supr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `sum_le_supr [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `sum_le_supr [(Term.hole "_")]) ")") "." `trans)
      [(Term.paren "(" (Term.app `mul_le_max_of_aleph_0_le_left [`ha]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk_Union_le_sum_mk.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `coe_set_of)
         ","
         (Tactic.rwRule [] `this)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `coe_set_of
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Set.«term{_|_}»
             "{"
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `Set [`α]))])
             "|"
             (Term.app `bounded [`r `s])
             "}")
            "="
            (Set.Data.Set.Lattice.«term⋃_,_»
             "⋃"
             (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
             ", "
             (Set.term𝒫_
              "𝒫"
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [])
               "|"
               (Term.app `r [`j `i])
               "}")))))]
         ":="
         (Term.app `set_of_exists [(Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `set_of_exists [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `set_of_exists
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `Set [`α]))])
        "|"
        (Term.app `bounded [`r `s])
        "}")
       "="
       (Set.Data.Set.Lattice.«term⋃_,_»
        "⋃"
        (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
        ", "
        (Set.term𝒫_
         "𝒫"
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [])
          "|"
          (Term.app `r [`j `i])
          "}"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Lattice.«term⋃_,_»
       "⋃"
       (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `i) []))
       ", "
       (Set.term𝒫_
        "𝒫"
        (Set.«term{_|_}»
         "{"
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [])
         "|"
         (Term.app `r [`j `i])
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.term𝒫_
       "𝒫"
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [])
        "|"
        (Term.app `r [`j `i])
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `j) [])
       "|"
       (Term.app `r [`j `i])
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `r [`j `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `j
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 100 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 100, (some 100, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `s) [(group ":" (Term.app `Set [`α]))])
       "|"
       (Term.app `bounded [`r `s])
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `bounded [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `bounded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `le_antisymm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_antisymm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [`ha []] [] ":=" `h'.is_limit.aleph_0_le)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'.is_limit.aleph_0_le
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h' []]
         [(Term.typeSpec
           ":"
           (Term.app `is_strong_limit [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)]))]
         ":="
         (Term.anonymousCtor "⟨" [`ha "," `h] "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`ha "," `h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_strong_limit [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Basic.cardinal.mk', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Basic.cardinal.mk', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_strong_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
        []
        (Std.Tactic.tacticHaveI_
         "haveI"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           []
           ":="
           (Term.app (Term.proj `mk_eq_zero_iff "." (fieldIdx "1")) [`ha]))))
        []
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_eq_zero_iff)] "]") [])
        []
        (Tactic.constructor "constructor")
        []
        (Std.Tactic.rintro
         "rintro"
         [(Std.Tactic.RCases.rintroPat.one
           (Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
              [])]
            "⟩"))]
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj (Term.app `not_unbounded_iff [`s]) "." (fieldIdx "2"))
          [`hs (Term.app `unbounded_of_is_empty [`s])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `not_unbounded_iff [`s]) "." (fieldIdx "2"))
        [`hs (Term.app `unbounded_of_is_empty [`s])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `not_unbounded_iff [`s]) "." (fieldIdx "2"))
       [`hs (Term.app `unbounded_of_is_empty [`s])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `unbounded_of_is_empty [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `unbounded_of_is_empty
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `unbounded_of_is_empty [`s])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `not_unbounded_iff [`s]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `not_unbounded_iff [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `not_unbounded_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `not_unbounded_iff [`s]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rintro
       "rintro"
       [(Std.Tactic.RCases.rintroPat.one
         (Std.Tactic.RCases.rcasesPat.tuple
          "⟨"
          [(Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `s)])
            [])
           ","
           (Std.Tactic.RCases.rcasesPatLo
            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hs)])
            [])]
          "⟩"))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_eq_zero_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_eq_zero_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app (Term.proj `mk_eq_zero_iff "." (fieldIdx "1")) [`ha]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `mk_eq_zero_iff "." (fieldIdx "1")) [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `mk_eq_zero_iff "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mk_eq_zero_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app `eq_or_ne [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) (num "0")]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `ha) "|" (Std.Tactic.RCases.rcasesPat.one `ha)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_or_ne [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Basic.cardinal.mk', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Basic.cardinal.mk', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_or_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
        "#"
        («term{_:_//_}» "{" `s [":" (Term.app `Set [`α])] "//" (Term.app `Bounded [`r `s]) "}"))
       "="
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
       "#"
       («term{_:_//_}» "{" `s [":" (Term.app `Set [`α])] "//" (Term.app `Bounded [`r `s]) "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `s [":" (Term.app `Set [`α])] "//" (Term.app `Bounded [`r `s]) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Bounded [`r `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Bounded
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
      "#"
      («term{_:_//_}» "{" `s [":" (Term.app `Set [`α])] "//" (Term.app `Bounded [`r `s]) "}"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)
       "="
       (Term.app `type [`r]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `type [`r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `type
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.instBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsWellOrder [`α `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsWellOrder
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.explicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.implicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `α "→" (Term.arrow `α "→" (Term.prop "Prop")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `α "→" (Term.prop "Prop"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.prop "Prop")
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `x)
       (Std.ExtendedBinder.«binderTerm<_»
        "<"
        (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))
       ","
       («term_<_»
        (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
        "<"
        (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
       "<"
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow', expected 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow._@.SetTheory.Cardinal.Cofinality._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mk_bounded_subset
  { α : Type _ }
      ( h : ∀ x < # α , 2 ^ x < # α )
      { r : α → α → Prop }
      [ IsWellOrder α r ]
      ( hr : # α . ord = type r )
    : # { s : Set α // Bounded r s } = # α
  :=
    by
      rcases eq_or_ne # α 0 with ( ha | ha )
        ·
          rw [ ha ]
            haveI := mk_eq_zero_iff . 1 ha
            rw [ mk_eq_zero_iff ]
            constructor
            rintro ⟨ s , hs ⟩
            exact not_unbounded_iff s . 2 hs unbounded_of_is_empty s
        have h' : is_strong_limit # α := ⟨ ha , h ⟩
        have ha := h'.is_limit.aleph_0_le
        apply le_antisymm
        ·
          have : { s : Set α | bounded r s } = ⋃ i , 𝒫 { j | r j i } := set_of_exists _
            rw [ ← coe_set_of , this ]
            convert mk_Union_le_sum_mk.trans sum_le_supr _ . trans mul_le_max_of_aleph_0_le_left ha
            apply max_eq_left _ . symm
            apply csupᵢ_le' fun i => _
            rw [ mk_powerset ]
            apply h'.two_power_lt _ . le
            rw [ coe_set_of , card_typein , ← lt_ord , hr ]
            apply typein_lt_type
        ·
          refine' @ mk_le_of_injective α _ fun x => Subtype.mk { x } _ _
            · apply bounded_singleton rw [ ← hr ] apply ord_is_limit ha
            · intro a b hab simpa only [ singleton_eq_singleton_iff ] using hab
#align cardinal.mk_bounded_subset Cardinal.mk_bounded_subset

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `mk_subset_mk_lt_cof [])
      (Command.declSig
       [(Term.implicitBinder "{" [`α] [":" (Term.type "Type" [(Level.hole "_")])] "}")
        (Term.explicitBinder
         "("
         [`h]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `x)
           (Std.ExtendedBinder.«binderTerm<_»
            "<"
            (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))
           ","
           («term_<_»
            (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
            "<"
            (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
          "#"
          («term{_:_//_}»
           "{"
           `s
           [":" (Term.app `Set [`α])]
           "//"
           («term_<_»
            (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `s)
            "<"
            (Term.app
             `cof
             [(Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)]))
           "}"))
         "="
         (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              (Term.app
               `eq_or_ne
               [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) (num "0")]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `ha)
                    "|"
                    (Std.Tactic.RCases.rcasesPat.one `ha)])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
             []
             (Tactic.simp
              "simp"
              []
              []
              []
              ["["
               [(Tactic.simpLemma
                 []
                 []
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`s]
                   []
                   "=>"
                   (Term.proj (Term.app `Cardinal.zero_le [`s]) "." `not_lt))))]
               "]"]
              [])])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`h' []]
              [(Term.typeSpec
                ":"
                (Term.app
                 `is_strong_limit
                 [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)]))]
              ":="
              (Term.anonymousCtor "⟨" [`ha "," `h] "⟩"))))
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `ord_eq [`α]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wo)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                   [])]
                 "⟩")])
              [])])
           []
           (Std.Tactic.tacticHaveI_ "haveI" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `wo)))
           []
           (Tactic.apply "apply" `le_antisymm)
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.nthRwRHS
              "nth_rw_rhs"
              (num "1")
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 (Term.app `mk_bounded_subset [`h `hr]))]
               "]")
              [])
             []
             (Tactic.apply
              "apply"
              (Term.app
               `mk_le_mk_of_subset
               [(Term.fun "fun" (Term.basicFun [`s `hs] [] "=>" (Term.hole "_")))]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hr)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hs] []))])
             []
             (Tactic.exact "exact" (Term.app `lt_cof_type [`hs]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine'
              "refine'"
              (Term.app
               (Term.explicit "@" `mk_le_of_injective)
               [`α
                (Term.hole "_")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x]
                  []
                  "=>"
                  (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
                (Term.hole "_")]))
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_singleton)] "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `one_lt_aleph_0.trans_le
                 [(Term.app
                   (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
                   [(Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])])]))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Tactic.intro "intro" [`a `b `hab])
               []
               (Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
                 ["using" `hab]))])])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              `eq_or_ne
              [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) (num "0")]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `ha) "|" (Std.Tactic.RCases.rcasesPat.one `ha)])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
            []
            (Tactic.simp
             "simp"
             []
             []
             []
             ["["
              [(Tactic.simpLemma
                []
                []
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`s]
                  []
                  "=>"
                  (Term.proj (Term.app `Cardinal.zero_le [`s]) "." `not_lt))))]
              "]"]
             [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`h' []]
             [(Term.typeSpec
               ":"
               (Term.app
                `is_strong_limit
                [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)]))]
             ":="
             (Term.anonymousCtor "⟨" [`ha "," `h] "⟩"))))
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `ord_eq [`α]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wo)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.tacticHaveI_ "haveI" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `wo)))
          []
          (Tactic.apply "apply" `le_antisymm)
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.nthRwRHS
             "nth_rw_rhs"
             (num "1")
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                (Term.app `mk_bounded_subset [`h `hr]))]
              "]")
             [])
            []
            (Tactic.apply
             "apply"
             (Term.app
              `mk_le_mk_of_subset
              [(Term.fun "fun" (Term.basicFun [`s `hs] [] "=>" (Term.hole "_")))]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hr)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hs] []))])
            []
            (Tactic.exact "exact" (Term.app `lt_cof_type [`hs]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine'
             "refine'"
             (Term.app
              (Term.explicit "@" `mk_le_of_injective)
              [`α
               (Term.hole "_")
               (Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
               (Term.hole "_")]))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_singleton)] "]")
               [])
              []
              (Tactic.exact
               "exact"
               (Term.app
                `one_lt_aleph_0.trans_le
                [(Term.app
                  (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
                  [(Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])])]))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.intro "intro" [`a `b `hab])
              []
              (Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest
                []
                []
                ["only"]
                [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
                ["using" `hab]))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.refine'
         "refine'"
         (Term.app
          (Term.explicit "@" `mk_le_of_injective)
          [`α
           (Term.hole "_")
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
           (Term.hole "_")]))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_singleton)] "]") [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `one_lt_aleph_0.trans_le
            [(Term.app
              (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
              [(Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])])]))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.intro "intro" [`a `b `hab])
          []
          (Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
            ["using" `hab]))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`a `b `hab])
        []
        (Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest
          []
          []
          ["only"]
          [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
          ["using" `hab]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `singleton_eq_singleton_iff)] "]")]
        ["using" `hab]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `singleton_eq_singleton_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`a `b `hab])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hab
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_singleton)] "]") [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `one_lt_aleph_0.trans_le
          [(Term.app
            (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
            [(Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `one_lt_aleph_0.trans_le
        [(Term.app
          (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
          [(Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `one_lt_aleph_0.trans_le
       [(Term.app
         (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
         [(Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
       [(Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h'.is_limit.aleph_0_le
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ord_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `ord_is_limit [`h'.is_limit.aleph_0_le])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `aleph_0_le_cof
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `aleph_0_le_cof "." (fieldIdx "2"))
      [(Term.paren "(" (Term.app `ord_is_limit [`h'.is_limit.aleph_0_le]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `one_lt_aleph_0.trans_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_singleton)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.explicit "@" `mk_le_of_injective)
        [`α
         (Term.hole "_")
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
         (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `mk_le_of_injective)
       [`α
        (Term.hole "_")
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
        (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      («term{_}» "{" [`x] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subtype.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`x]
       []
       "=>"
       (Term.app `Subtype.mk [(«term{_}» "{" [`x] "}") (Term.hole "_")])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `mk_le_of_injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_le_of_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.nthRwRHS
         "nth_rw_rhs"
         (num "1")
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            [(patternIgnore (token.«← » "←"))]
            (Term.app `mk_bounded_subset [`h `hr]))]
          "]")
         [])
        []
        (Tactic.apply
         "apply"
         (Term.app
          `mk_le_mk_of_subset
          [(Term.fun "fun" (Term.basicFun [`s `hs] [] "=>" (Term.hole "_")))]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hr)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hs] []))])
        []
        (Tactic.exact "exact" (Term.app `lt_cof_type [`hs]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `lt_cof_type [`hs]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_cof_type [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_cof_type
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hr)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hs] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `mk_le_mk_of_subset
        [(Term.fun "fun" (Term.basicFun [`s `hs] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mk_le_mk_of_subset
       [(Term.fun "fun" (Term.basicFun [`s `hs] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`s `hs] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk_le_mk_of_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.nthRwRHS
       "nth_rw_rhs"
       (num "1")
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `mk_bounded_subset [`h `hr]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mk_bounded_subset [`h `hr])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mk_bounded_subset
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `le_antisymm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_antisymm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_ "haveI" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `wo)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `wo
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `ord_eq [`α]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wo)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hr)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ord_eq [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ord_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`h' []]
         [(Term.typeSpec
           ":"
           (Term.app `is_strong_limit [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)]))]
         ":="
         (Term.anonymousCtor "⟨" [`ha "," `h] "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`ha "," `h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `is_strong_limit [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Basic.cardinal.mk', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Basic.cardinal.mk', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_strong_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
        []
        (Tactic.simp
         "simp"
         []
         []
         []
         ["["
          [(Tactic.simpLemma
            []
            []
            (Term.fun
             "fun"
             (Term.basicFun
              [`s]
              []
              "=>"
              (Term.proj (Term.app `Cardinal.zero_le [`s]) "." `not_lt))))]
          "]"]
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       []
       ["["
        [(Tactic.simpLemma
          []
          []
          (Term.fun
           "fun"
           (Term.basicFun [`s] [] "=>" (Term.proj (Term.app `Cardinal.zero_le [`s]) "." `not_lt))))]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`s] [] "=>" (Term.proj (Term.app `Cardinal.zero_le [`s]) "." `not_lt)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `Cardinal.zero_le [`s]) "." `not_lt)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Cardinal.zero_le [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Cardinal.zero_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Cardinal.zero_le [`s]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `ha)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget
         []
         (Term.app `eq_or_ne [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) (num "0")]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.paren
            "("
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `ha) "|" (Std.Tactic.RCases.rcasesPat.one `ha)])
             [])
            ")")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_or_ne [(Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Basic.cardinal.mk', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Basic.cardinal.mk', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 0, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_or_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
        "#"
        («term{_:_//_}»
         "{"
         `s
         [":" (Term.app `Set [`α])]
         "//"
         («term_<_»
          (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `s)
          "<"
          (Term.app
           `cof
           [(Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)]))
         "}"))
       "="
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
       "#"
       («term{_:_//_}»
        "{"
        `s
        [":" (Term.app `Set [`α])]
        "//"
        («term_<_»
         (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `s)
         "<"
         (Term.app
          `cof
          [(Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)]))
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}»
       "{"
       `s
       [":" (Term.app `Set [`α])]
       "//"
       («term_<_»
        (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `s)
        "<"
        (Term.app
         `cof
         [(Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)]))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `s)
       "<"
       (Term.app
        `cof
        [(Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cof [(Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) "." `ord)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cof
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `s)
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
      "#"
      («term{_:_//_}»
       "{"
       `s
       [":" (Term.app `Set [`α])]
       "//"
       («term_<_»
        (Term.paren "(" (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `s) ")")
        "<"
        (Term.app
         `cof
         [(Term.proj
           (Term.paren "(" (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α) ")")
           "."
           `ord)]))
       "}"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `x)
       (Std.ExtendedBinder.«binderTerm<_»
        "<"
        (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))
       ","
       («term_<_»
        (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
        "<"
        (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
       "<"
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow', expected 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow._@.SetTheory.Cardinal.Cofinality._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  mk_subset_mk_lt_cof
  { α : Type _ } ( h : ∀ x < # α , 2 ^ x < # α ) : # { s : Set α // # s < cof # α . ord } = # α
  :=
    by
      rcases eq_or_ne # α 0 with ( ha | ha )
        · rw [ ha ] simp [ fun s => Cardinal.zero_le s . not_lt ]
        have h' : is_strong_limit # α := ⟨ ha , h ⟩
        rcases ord_eq α with ⟨ r , wo , hr ⟩
        haveI := wo
        apply le_antisymm
        ·
          nth_rw_rhs 1 [ ← mk_bounded_subset h hr ]
            apply mk_le_mk_of_subset fun s hs => _
            rw [ hr ] at hs
            exact lt_cof_type hs
        ·
          refine' @ mk_le_of_injective α _ fun x => Subtype.mk { x } _ _
            ·
              rw [ mk_singleton ]
                exact one_lt_aleph_0.trans_le aleph_0_le_cof . 2 ord_is_limit h'.is_limit.aleph_0_le
            · intro a b hab simpa only [ singleton_eq_singleton_iff ] using hab
#align cardinal.mk_subset_mk_lt_cof Cardinal.mk_subset_mk_lt_cof

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def IsRegular (c : Cardinal) : Prop :=
  ℵ₀ ≤ c ∧ c ≤ c.ord.cof
#align cardinal.is_regular Cardinal.IsRegular

theorem IsRegular.aleph_0_le {c : Cardinal} (H : c.IsRegular) : ℵ₀ ≤ c :=
  H.1
#align cardinal.is_regular.aleph_0_le Cardinal.IsRegular.aleph_0_le

theorem IsRegular.cof_eq {c : Cardinal} (H : c.IsRegular) : c.ord.cof = c :=
  (cof_ord_le c).antisymm H.2
#align cardinal.is_regular.cof_eq Cardinal.IsRegular.cof_eq

theorem IsRegular.pos {c : Cardinal} (H : c.IsRegular) : 0 < c :=
  aleph_0_pos.trans_le H.1
#align cardinal.is_regular.pos Cardinal.IsRegular.pos

theorem IsRegular.ord_pos {c : Cardinal} (H : c.IsRegular) : 0 < c.ord :=
  by
  rw [Cardinal.lt_ord]
  exact H.pos
#align cardinal.is_regular.ord_pos Cardinal.IsRegular.ord_pos

theorem is_regular_cof {o : Ordinal} (h : o.IsLimit) : IsRegular o.cof :=
  ⟨aleph_0_le_cof.2 h, (cof_cof o).ge⟩
#align cardinal.is_regular_cof Cardinal.is_regular_cof

theorem is_regular_aleph_0 : IsRegular ℵ₀ :=
  ⟨le_rfl, by simp⟩
#align cardinal.is_regular_aleph_0 Cardinal.is_regular_aleph_0

theorem is_regular_succ {c : Cardinal.{u}} (h : ℵ₀ ≤ c) : IsRegular (succ c) :=
  ⟨h.trans (le_succ c),
    succ_le_of_lt
      (by
        cases' Quotient.exists_rep (@succ Cardinal _ _ c) with α αe; simp at αe
        rcases ord_eq α with ⟨r, wo, re⟩; skip
        have := ord_is_limit (h.trans (le_succ _))
        rw [← αe, re] at this⊢
        rcases cof_eq' r this with ⟨S, H, Se⟩
        rw [← Se]
        apply lt_imp_lt_of_le_imp_le fun h => mul_le_mul_right' h c
        rw [mul_eq_self h, ← succ_le_iff, ← αe, ← sum_const']
        refine' le_trans _ (sum_le_sum (fun x => card (typein r x)) _ fun i => _)
        · simp only [← card_typein, ← mk_sigma]
          exact
            ⟨embedding.of_surjective (fun x => x.2.1) fun a =>
                let ⟨b, h, ab⟩ := H a
                ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩⟩
        · rw [← lt_succ_iff, ← lt_ord, ← αe, re]
          apply typein_lt_type)⟩
#align cardinal.is_regular_succ Cardinal.is_regular_succ

theorem is_regular_aleph_one : IsRegular (aleph 1) :=
  by
  rw [← succ_aleph_0]
  exact is_regular_succ le_rfl
#align cardinal.is_regular_aleph_one Cardinal.is_regular_aleph_one

theorem is_regular_aleph'_succ {o : Ordinal} (h : ω ≤ o) : IsRegular (aleph' (succ o)) :=
  by
  rw [aleph'_succ]
  exact is_regular_succ (aleph_0_le_aleph'.2 h)
#align cardinal.is_regular_aleph'_succ Cardinal.is_regular_aleph'_succ

theorem is_regular_aleph_succ (o : Ordinal) : IsRegular (aleph (succ o)) :=
  by
  rw [aleph_succ]
  exact is_regular_succ (aleph_0_le_aleph o)
#align cardinal.is_regular_aleph_succ Cardinal.is_regular_aleph_succ

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α) (w : (#α) < (#β)) (w' : ℵ₀ ≤ (#α)) :
    ∃ a : α, (#α) < (#f ⁻¹' {a}) := by
  simp_rw [← succ_le_iff]
  exact
    Ordinal.infinite_pigeonhole_card f (succ (#α)) (succ_le_of_lt w) (w'.trans (lt_succ _).le)
      ((lt_succ _).trans_le (is_regular_succ w').2.ge)
#align cardinal.infinite_pigeonhole_card_lt Cardinal.infinite_pigeonhole_card_lt

/-- A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type _} (f : β → α) (w : (#α) < (#β)) (w' : Infinite α) :
    ∃ a : α, Infinite (f ⁻¹' {a}) :=
  by
  simp_rw [Cardinal.infinite_iff] at w'⊢
  cases' infinite_pigeonhole_card_lt f w w' with a ha
  exact ⟨a, w'.trans ha.le⟩
#align cardinal.exists_infinite_fiber Cardinal.exists_infinite_fiber

/-- If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`.
-/
theorem le_range_of_union_finset_eq_top {α β : Type _} [Infinite β] (f : α → Finset β)
    (w : (⋃ a, (f a : Set β)) = ⊤) : (#β) ≤ (#range f) :=
  by
  have k : _root_.infinite (range f) := by
    rw [infinite_coe_iff]
    apply mt (union_finset_finite_of_range_finite f)
    rw [w]
    exact infinite_univ
  by_contra h
  simp only [not_le] at h
  let u : ∀ b, ∃ a, b ∈ f a := fun b => by simpa using (w.ge : _) (Set.mem_univ b)
  let u' : β → range f := fun b => ⟨f (u b).some, by simp⟩
  have v' : ∀ a, u' ⁻¹' {⟨f a, by simp⟩} ≤ f a :=
    by
    rintro a p m
    simp at m
    rw [← m]
    apply fun b => (u b).some_spec
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h k
  exact (@Infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).False
#align cardinal.le_range_of_union_finset_eq_top Cardinal.le_range_of_union_finset_eq_top

theorem lsub_lt_ord_lift_of_is_regular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift (#ι) < c) : (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  lsub_lt_ord_lift (by rwa [hc.cof_eq])
#align cardinal.lsub_lt_ord_lift_of_is_regular Cardinal.lsub_lt_ord_lift_of_is_regular

theorem lsub_lt_ord_of_is_regular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : (#ι) < c) :
    (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord :=
  lsub_lt_ord (by rwa [hc.cof_eq])
#align cardinal.lsub_lt_ord_of_is_regular Cardinal.lsub_lt_ord_of_is_regular

theorem sup_lt_ord_lift_of_is_regular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift (#ι) < c) : (∀ i, f i < c.ord) → Ordinal.sup f < c.ord :=
  sup_lt_ord_lift (by rwa [hc.cof_eq])
#align cardinal.sup_lt_ord_lift_of_is_regular Cardinal.sup_lt_ord_lift_of_is_regular

theorem sup_lt_ord_of_is_regular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c) (hι : (#ι) < c) :
    (∀ i, f i < c.ord) → Ordinal.sup f < c.ord :=
  sup_lt_ord (by rwa [hc.cof_eq])
#align cardinal.sup_lt_ord_of_is_regular Cardinal.sup_lt_ord_of_is_regular

theorem blsub_lt_ord_lift_of_is_regular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : Cardinal.lift o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.blsub o f < c.ord :=
  blsub_lt_ord_lift (by rwa [hc.cof_eq])
#align cardinal.blsub_lt_ord_lift_of_is_regular Cardinal.blsub_lt_ord_lift_of_is_regular

theorem blsub_lt_ord_of_is_regular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (ho : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.blsub o f < c.ord :=
  blsub_lt_ord (by rwa [hc.cof_eq])
#align cardinal.blsub_lt_ord_of_is_regular Cardinal.blsub_lt_ord_of_is_regular

theorem bsup_lt_ord_lift_of_is_regular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.bsup o f < c.ord :=
  bsup_lt_ord_lift (by rwa [hc.cof_eq])
#align cardinal.bsup_lt_ord_lift_of_is_regular Cardinal.bsup_lt_ord_lift_of_is_regular

theorem bsup_lt_ord_of_is_regular {o : Ordinal} {f : ∀ a < o, Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) : (∀ i hi, f i hi < c.ord) → Ordinal.bsup o f < c.ord :=
  bsup_lt_ord (by rwa [hc.cof_eq])
#align cardinal.bsup_lt_ord_of_is_regular Cardinal.bsup_lt_ord_of_is_regular

theorem supr_lt_lift_of_is_regular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c)
    (hι : Cardinal.lift (#ι) < c) : (∀ i, f i < c) → supᵢ f < c :=
  supr_lt_lift (by rwa [hc.cof_eq])
#align cardinal.supr_lt_lift_of_is_regular Cardinal.supr_lt_lift_of_is_regular

theorem supr_lt_of_is_regular {ι} {f : ι → Cardinal} {c} (hc : IsRegular c) (hι : (#ι) < c) :
    (∀ i, f i < c) → supᵢ f < c :=
  supr_lt (by rwa [hc.cof_eq])
#align cardinal.supr_lt_of_is_regular Cardinal.supr_lt_of_is_regular

theorem sum_lt_lift_of_is_regular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c)
    (hι : Cardinal.lift.{v, u} (#ι) < c) (hf : ∀ i, f i < c) : sum f < c :=
  (sum_le_supr_lift _).trans_lt <| mul_lt_of_lt hc.1 hι (supr_lt_lift_of_is_regular hc hι hf)
#align cardinal.sum_lt_lift_of_is_regular Cardinal.sum_lt_lift_of_is_regular

theorem sum_lt_of_is_regular {ι : Type u} {f : ι → Cardinal} {c : Cardinal} (hc : IsRegular c)
    (hι : (#ι) < c) : (∀ i, f i < c) → sum f < c :=
  sum_lt_lift_of_is_regular.{u, u} hc (by rwa [lift_id])
#align cardinal.sum_lt_of_is_regular Cardinal.sum_lt_of_is_regular

theorem nfp_family_lt_ord_lift_of_is_regular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : (#ι).lift < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a}
    (ha : a < c.ord) : nfpFamily.{u, v} f a < c.ord :=
  by
  apply nfp_family_lt_ord_lift _ _ hf ha <;> rwa [hc.cof_eq]
  exact lt_of_le_of_ne hc.1 hc'.symm
#align cardinal.nfp_family_lt_ord_lift_of_is_regular Cardinal.nfp_family_lt_ord_lift_of_is_regular

theorem nfp_family_lt_ord_of_is_regular {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : (#ι) < c) (hc' : c ≠ ℵ₀) {a} (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) :
    a < c.ord → nfpFamily.{u, u} f a < c.ord :=
  nfp_family_lt_ord_lift_of_is_regular hc (by rwa [lift_id]) hc' hf
#align cardinal.nfp_family_lt_ord_of_is_regular Cardinal.nfp_family_lt_ord_of_is_regular

theorem nfp_bfamily_lt_ord_lift_of_is_regular {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (ho : o.card.lift < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → nfpBfamily.{u, v} o f a < c.ord :=
  nfp_family_lt_ord_lift_of_is_regular hc (by rwa [mk_ordinal_out]) hc' fun i => hf _ _
#align cardinal.nfp_bfamily_lt_ord_lift_of_is_regular Cardinal.nfp_bfamily_lt_ord_lift_of_is_regular

theorem nfp_bfamily_lt_ord_of_is_regular {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (ho : o.card < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → nfpBfamily.{u, u} o f a < c.ord :=
  nfp_bfamily_lt_ord_lift_of_is_regular hc (by rwa [lift_id]) hc' hf
#align cardinal.nfp_bfamily_lt_ord_of_is_regular Cardinal.nfp_bfamily_lt_ord_of_is_regular

theorem nfp_lt_ord_of_is_regular {f : Ordinal → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → nfp f a < c.ord :=
  nfp_lt_ord
    (by
      rw [hc.cof_eq]
      exact lt_of_le_of_ne hc.1 hc'.symm)
    hf
#align cardinal.nfp_lt_ord_of_is_regular Cardinal.nfp_lt_ord_of_is_regular

theorem deriv_family_lt_ord_lift {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : (#ι).lift < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily.{u, v} f a < c.ord :=
  by
  have hω : ℵ₀ < c.ord.cof := by
    rw [hc.cof_eq]
    exact lt_of_le_of_ne hc.1 hc'.symm
  apply a.limit_rec_on
  · rw [deriv_family_zero]
    exact nfp_family_lt_ord_lift hω (by rwa [hc.cof_eq]) hf
  · intro b hb hb'
    rw [deriv_family_succ]
    exact
      nfp_family_lt_ord_lift hω (by rwa [hc.cof_eq]) hf
        ((ord_is_limit hc.1).2 _ (hb ((lt_succ b).trans hb')))
  · intro b hb H hb'
    rw [deriv_family_limit f hb]
    exact
      bsup_lt_ord_of_is_regular hc (ord_lt_ord.1 ((ord_card_le b).trans_lt hb')) fun o' ho' =>
        H o' ho' (ho'.trans hb')
#align cardinal.deriv_family_lt_ord_lift Cardinal.deriv_family_lt_ord_lift

theorem deriv_family_lt_ord {ι} {f : ι → Ordinal → Ordinal} {c} (hc : IsRegular c) (hι : (#ι) < c)
    (hc' : c ≠ ℵ₀) (hf : ∀ (i), ∀ b < c.ord, f i b < c.ord) {a} :
    a < c.ord → derivFamily.{u, u} f a < c.ord :=
  deriv_family_lt_ord_lift hc (by rwa [lift_id]) hc' hf
#align cardinal.deriv_family_lt_ord Cardinal.deriv_family_lt_ord

theorem deriv_bfamily_lt_ord_lift {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c}
    (hc : IsRegular c) (hι : o.card.lift < c) (hc' : c ≠ ℵ₀)
    (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → derivBfamily.{u, v} o f a < c.ord :=
  deriv_family_lt_ord_lift hc (by rwa [mk_ordinal_out]) hc' fun i => hf _ _
#align cardinal.deriv_bfamily_lt_ord_lift Cardinal.deriv_bfamily_lt_ord_lift

theorem deriv_bfamily_lt_ord {o : Ordinal} {f : ∀ a < o, Ordinal → Ordinal} {c} (hc : IsRegular c)
    (hι : o.card < c) (hc' : c ≠ ℵ₀) (hf : ∀ (i hi), ∀ b < c.ord, f i hi b < c.ord) {a} :
    a < c.ord → derivBfamily.{u, u} o f a < c.ord :=
  deriv_bfamily_lt_ord_lift hc (by rwa [lift_id]) hc' hf
#align cardinal.deriv_bfamily_lt_ord Cardinal.deriv_bfamily_lt_ord

theorem deriv_lt_ord {f : Ordinal.{u} → Ordinal} {c} (hc : IsRegular c) (hc' : c ≠ ℵ₀)
    (hf : ∀ i < c.ord, f i < c.ord) {a} : a < c.ord → deriv f a < c.ord :=
  deriv_family_lt_ord_lift hc
    (by simpa using cardinal.one_lt_aleph_0.trans (lt_of_le_of_ne hc.1 hc'.symm)) hc' fun _ => hf
#align cardinal.deriv_lt_ord Cardinal.deriv_lt_ord

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def IsInaccessible (c : Cardinal) :=
  ℵ₀ < c ∧ IsRegular c ∧ IsStrongLimit c
#align cardinal.is_inaccessible Cardinal.IsInaccessible

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `IsInaccessible.mk [])
      (Command.declSig
       [(Term.implicitBinder "{" [`c] [] "}")
        (Term.explicitBinder
         "("
         [`h₁]
         [":" («term_<_» (Cardinal.SetTheory.Cardinal.Basic.cardinal.aleph_0 "ℵ₀") "<" `c)]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h₂]
         [":" («term_≤_» `c "≤" (Term.proj (Term.proj `c "." `ord) "." `cof))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`h₃]
         [":"
          (Std.ExtendedBinder.«term∀__,_»
           "∀"
           (Lean.binderIdent `x)
           (Std.ExtendedBinder.«binderTerm<_» "<" `c)
           ","
           («term_<_»
            (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
            "<"
            `c))]
         []
         ")")]
       (Term.typeSpec ":" (Term.app `IsInaccessible [`c])))
      (Command.declValSimple
       ":="
       (Term.anonymousCtor
        "⟨"
        [`h₁
         ","
         (Term.anonymousCtor "⟨" [(Term.proj `h₁ "." `le) "," `h₂] "⟩")
         ","
         (Term.proj (Term.app (Term.proj `aleph_0_pos "." `trans) [`h₁]) "." `ne')
         ","
         `h₃]
        "⟩")
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`h₁
        ","
        (Term.anonymousCtor "⟨" [(Term.proj `h₁ "." `le) "," `h₂] "⟩")
        ","
        (Term.proj (Term.app (Term.proj `aleph_0_pos "." `trans) [`h₁]) "." `ne')
        ","
        `h₃]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₃
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app (Term.proj `aleph_0_pos "." `trans) [`h₁]) "." `ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `aleph_0_pos "." `trans) [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `aleph_0_pos "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `aleph_0_pos
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `aleph_0_pos "." `trans) [`h₁])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.proj `h₁ "." `le) "," `h₂] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `h₁ "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `IsInaccessible [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsInaccessible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.ExtendedBinder.«term∀__,_»
       "∀"
       (Lean.binderIdent `x)
       (Std.ExtendedBinder.«binderTerm<_» "<" `c)
       ","
       («term_<_» (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x) "<" `c))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x) "<" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow (num "2") "^" `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow', expected 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow._@.SetTheory.Cardinal.Cofinality._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  IsInaccessible.mk
  { c } ( h₁ : ℵ₀ < c ) ( h₂ : c ≤ c . ord . cof ) ( h₃ : ∀ x < c , 2 ^ x < c ) : IsInaccessible c
  := ⟨ h₁ , ⟨ h₁ . le , h₂ ⟩ , aleph_0_pos . trans h₁ . ne' , h₃ ⟩
#align cardinal.is_inaccessible.mk Cardinal.IsInaccessible.mk

-- Lean's foundations prove the existence of ℵ₀ many inaccessible cardinals
theorem univ_inaccessible : IsInaccessible univ.{u, v} :=
  IsInaccessible.mk (by simpa using lift_lt_univ' ℵ₀) (by simp) fun c h =>
    by
    rcases lt_univ'.1 h with ⟨c, rfl⟩
    rw [← lift_two_power.{u, max (u + 1) v}]
    apply lift_lt_univ'
#align cardinal.univ_inaccessible Cardinal.univ_inaccessible

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_power_cof [])
      (Command.declSig
       [(Term.implicitBinder "{" [`c] [":" (Term.explicitUniv `Cardinal ".{" [`u] "}")] "}")]
       (Term.typeSpec
        ":"
        (Term.arrow
         («term_≤_» (Cardinal.SetTheory.Cardinal.Basic.cardinal.aleph_0 "ℵ₀") "≤" `c)
         "→"
         («term_<_»
          `c
          "<"
          (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow
           `c
           "^"
           (Term.app `cof [(Term.proj `c "." `ord)]))))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.app `Quotient.induction_on [`c])
        [(Term.fun
          "fun"
          (Term.basicFun
           [`α `h]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `ord_eq [`α]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wo)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `re)])
                       [])]
                     "⟩")])
                  [])])
               ";"
               (Tactic.skip "skip")
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `ord_is_limit [`h]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_def) "," (Tactic.rwRule [] `re)] "]")
                [(Tactic.location
                  "at"
                  (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `cof_eq' [`r `this]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Se)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  []
                  ":="
                  (Term.app
                   `sum_lt_prod
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      [(Term.typeSpec ":" `S)]
                      "=>"
                      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
                       "#"
                       («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))))
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.hole "_")]
                      []
                      "=>"
                      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
                    (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `Cardinal.prod_const)
                    ","
                    (Tactic.simpLemma [] [] `Cardinal.lift_id)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Se)
                    ","
                    (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mk_sigma)
                    ","
                    (Tactic.simpLemma [] [] `power_def)]
                   "]"]
                  [(Tactic.location
                    "at"
                    (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
                 []
                 (Tactic.refine' "refine'" (Term.app `lt_of_le_of_lt [(Term.hole "_") `this]))
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `embedding.of_surjective [(Term.hole "_") (Term.hole "_")])]
                   "⟩"))
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`x]
                      []
                      "=>"
                      (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.let
                       "let"
                       (Term.letDecl
                        (Term.letPatDecl
                         (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
                         []
                         []
                         ":="
                         (Term.app `H [`a])))
                       []
                       (Term.anonymousCtor
                        "⟨"
                        [(Term.anonymousCtor
                          "⟨"
                          [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")
                           ","
                           (Term.hole "_")
                           ","
                           `ab]
                          "⟩")
                         ","
                         `rfl]
                        "⟩")))))])])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `typein_lt_type [`r `i]))))
                 []
                 (Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `re)
                    ","
                    (Tactic.rwRule [] `lt_ord)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])])))))])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `Quotient.induction_on [`c])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`α `h]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `ord_eq [`α]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wo)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `re)])
                      [])]
                    "⟩")])
                 [])])
              ";"
              (Tactic.skip "skip")
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `ord_is_limit [`h]))))
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_def) "," (Tactic.rwRule [] `re)] "]")
               [(Tactic.location
                 "at"
                 (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `cof_eq' [`r `this]))]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Se)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 []
                 []
                 ":="
                 (Term.app
                  `sum_lt_prod
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     [(Term.typeSpec ":" `S)]
                     "=>"
                     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
                      "#"
                      («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))))
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.hole "_")]
                     []
                     "=>"
                     (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
                   (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `Cardinal.prod_const)
                   ","
                   (Tactic.simpLemma [] [] `Cardinal.lift_id)
                   ","
                   (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Se)
                   ","
                   (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mk_sigma)
                   ","
                   (Tactic.simpLemma [] [] `power_def)]
                  "]"]
                 [(Tactic.location
                   "at"
                   (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
                []
                (Tactic.refine' "refine'" (Term.app `lt_of_le_of_lt [(Term.hole "_") `this]))
                []
                (Tactic.refine'
                 "refine'"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app `embedding.of_surjective [(Term.hole "_") (Term.hole "_")])]
                  "⟩"))
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact
                   "exact"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`x]
                     []
                     "=>"
                     (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact
                   "exact"
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.let
                      "let"
                      (Term.letDecl
                       (Term.letPatDecl
                        (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
                        []
                        []
                        ":="
                        (Term.app `H [`a])))
                      []
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.anonymousCtor
                         "⟨"
                         [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")
                          ","
                          (Term.hole "_")
                          ","
                          `ab]
                         "⟩")
                        ","
                        `rfl]
                       "⟩")))))])])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `typein_lt_type [`r `i]))))
                []
                (Std.Tactic.tacticRwa__
                 "rwa"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `re)
                   ","
                   (Tactic.rwRule [] `lt_ord)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`α `h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `ord_eq [`α]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wo)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `re)])
                    [])]
                  "⟩")])
               [])])
            ";"
            (Tactic.skip "skip")
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `ord_is_limit [`h]))))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_def) "," (Tactic.rwRule [] `re)] "]")
             [(Tactic.location
               "at"
               (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `cof_eq' [`r `this]))]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Se)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app
                `sum_lt_prod
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`a]
                   [(Term.typeSpec ":" `S)]
                   "=>"
                   (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
                    "#"
                    («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))))
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.hole "_")]
                   []
                   "=>"
                   (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
                 (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Cardinal.prod_const)
                 ","
                 (Tactic.simpLemma [] [] `Cardinal.lift_id)
                 ","
                 (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Se)
                 ","
                 (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mk_sigma)
                 ","
                 (Tactic.simpLemma [] [] `power_def)]
                "]"]
               [(Tactic.location
                 "at"
                 (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
              []
              (Tactic.refine' "refine'" (Term.app `lt_of_le_of_lt [(Term.hole "_") `this]))
              []
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `embedding.of_surjective [(Term.hole "_") (Term.hole "_")])]
                "⟩"))
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact
                 "exact"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`x]
                   []
                   "=>"
                   (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))))])
              []
              (tactic__
               (cdotTk (patternIgnore (token.«· » "·")))
               [(Tactic.exact
                 "exact"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`a]
                   []
                   "=>"
                   (Term.let
                    "let"
                    (Term.letDecl
                     (Term.letPatDecl
                      (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
                      []
                      []
                      ":="
                      (Term.app `H [`a])))
                    []
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor
                       "⟨"
                       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")
                        ","
                        (Term.hole "_")
                        ","
                        `ab]
                       "⟩")
                      ","
                      `rfl]
                     "⟩")))))])])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `typein_lt_type [`r `i]))))
              []
              (Std.Tactic.tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `re)
                 ","
                 (Tactic.rwRule [] `lt_ord)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `ord_eq [`α]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wo)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `re)])
                  [])]
                "⟩")])
             [])])
          ";"
          (Tactic.skip "skip")
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `ord_is_limit [`h]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_def) "," (Tactic.rwRule [] `re)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `cof_eq' [`r `this]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Se)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `sum_lt_prod
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 [(Term.typeSpec ":" `S)]
                 "=>"
                 (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
                  "#"
                  («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.hole "_")]
                 []
                 "=>"
                 (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
               (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Cardinal.prod_const)
               ","
               (Tactic.simpLemma [] [] `Cardinal.lift_id)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Se)
               ","
               (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mk_sigma)
               ","
               (Tactic.simpLemma [] [] `power_def)]
              "]"]
             [(Tactic.location
               "at"
               (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
            []
            (Tactic.refine' "refine'" (Term.app `lt_of_le_of_lt [(Term.hole "_") `this]))
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `embedding.of_surjective [(Term.hole "_") (Term.hole "_")])]
              "⟩"))
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.fun
                "fun"
                (Term.basicFun
                 [`x]
                 []
                 "=>"
                 (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact
               "exact"
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.let
                  "let"
                  (Term.letDecl
                   (Term.letPatDecl
                    (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
                    []
                    []
                    ":="
                    (Term.app `H [`a])))
                  []
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.anonymousCtor
                     "⟨"
                     [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")
                      ","
                      (Term.hole "_")
                      ","
                      `ab]
                     "⟩")
                    ","
                    `rfl]
                   "⟩")))))])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `typein_lt_type [`r `i]))))
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `re)
               ","
               (Tactic.rwRule [] `lt_ord)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `typein_lt_type [`r `i]))))
        []
        (Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `re) "," (Tactic.rwRule [] `lt_ord)]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`this] []))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `re) "," (Tactic.rwRule [] `lt_ord)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `lt_ord
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `re
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `typein_lt_type [`r `i]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `typein_lt_type [`r `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `typein_lt_type
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Cardinal.prod_const)
           ","
           (Tactic.simpLemma [] [] `Cardinal.lift_id)
           ","
           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Se)
           ","
           (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mk_sigma)
           ","
           (Tactic.simpLemma [] [] `power_def)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
        []
        (Tactic.refine' "refine'" (Term.app `lt_of_le_of_lt [(Term.hole "_") `this]))
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.app `embedding.of_surjective [(Term.hole "_") (Term.hole "_")])]
          "⟩"))
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`x]
             []
             "=>"
             (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (Term.let
              "let"
              (Term.letDecl
               (Term.letPatDecl
                (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
                []
                []
                ":="
                (Term.app `H [`a])))
              []
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩") "," (Term.hole "_") "," `ab]
                 "⟩")
                ","
                `rfl]
               "⟩")))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.let
            "let"
            (Term.letDecl
             (Term.letPatDecl
              (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
              []
              []
              ":="
              (Term.app `H [`a])))
            []
            (Term.anonymousCtor
             "⟨"
             [(Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩") "," (Term.hole "_") "," `ab]
               "⟩")
              ","
              `rfl]
             "⟩")))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun
         [`a]
         []
         "=>"
         (Term.let
          "let"
          (Term.letDecl
           (Term.letPatDecl
            (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
            []
            []
            ":="
            (Term.app `H [`a])))
          []
          (Term.anonymousCtor
           "⟨"
           [(Term.anonymousCtor
             "⟨"
             [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩") "," (Term.hole "_") "," `ab]
             "⟩")
            ","
            `rfl]
           "⟩")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.let
         "let"
         (Term.letDecl
          (Term.letPatDecl
           (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
           []
           []
           ":="
           (Term.app `H [`a])))
         []
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩") "," (Term.hole "_") "," `ab]
            "⟩")
           ","
           `rfl]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.let
       "let"
       (Term.letDecl
        (Term.letPatDecl
         (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
         []
         []
         ":="
         (Term.app `H [`a])))
       []
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩") "," (Term.hole "_") "," `ab]
          "⟩")
         ","
         `rfl]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩") "," (Term.hole "_") "," `ab]
         "⟩")
        ","
        `rfl]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩") "," (Term.hole "_") "," `ab]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letPatDecl', expected 'Lean.Parser.Term.letIdDecl'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `H [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `H
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`b "," `h "," `ab] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ab
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun
         [`x]
         []
         "=>"
         (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.proj `x "." (fieldIdx "2")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.app `embedding.of_surjective [(Term.hole "_") (Term.hole "_")])]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app `embedding.of_surjective [(Term.hole "_") (Term.hole "_")])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `embedding.of_surjective [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `embedding.of_surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `lt_of_le_of_lt [(Term.hole "_") `this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `lt_of_le_of_lt [(Term.hole "_") `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_of_le_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Cardinal.prod_const)
         ","
         (Tactic.simpLemma [] [] `Cardinal.lift_id)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Se)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `mk_sigma)
         ","
         (Tactic.simpLemma [] [] `power_def)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `power_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_sigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Se
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Cardinal.lift_id
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Cardinal.prod_const
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          `sum_lt_prod
          [(Term.fun
            "fun"
            (Term.basicFun
             [`a]
             [(Term.typeSpec ":" `S)]
             "=>"
             (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
              "#"
              («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))))
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.hole "_")]
             []
             "=>"
             (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
           (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sum_lt_prod
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
          [(Term.typeSpec ":" `S)]
          "=>"
          (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
           "#"
           («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.hole "_")]
          []
          "=>"
          (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
        (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`i] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.hole "_")]
        []
        "=>"
        (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.hole "_")]
       []
       "=>"
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk "#" `α)))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        [(Term.typeSpec ":" `S)]
        "=>"
        (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
         "#"
         («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
       "#"
       («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `r [`x `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`a]
       [(Term.typeSpec ":" `S)]
       "=>"
       (Cardinal.SetTheory.Cardinal.Basic.cardinal.mk
        "#"
        («term{_:_//_}» "{" `x [] "//" (Term.app `r [`x `a]) "}"))))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sum_lt_prod
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `cof_eq' [`r `this]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `S)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `Se)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cof_eq' [`r `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cof_eq'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mk_def) "," (Tactic.rwRule [] `re)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] [(patternIgnore (token.«⊢» "⊢"))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `re
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mk_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `ord_is_limit [`h]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ord_is_limit [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ord_is_limit
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.skip "skip")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `ord_eq [`α]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `r)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `wo)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `re)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ord_eq [`α])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ord_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `α
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `Quotient.induction_on [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.induction_on
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Quotient.induction_on [`c])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_≤_» (Cardinal.SetTheory.Cardinal.Basic.cardinal.aleph_0 "ℵ₀") "≤" `c)
       "→"
       («term_<_»
        `c
        "<"
        (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow
         `c
         "^"
         (Term.app `cof [(Term.proj `c "." `ord)]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_»
       `c
       "<"
       (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow
        `c
        "^"
        (Term.app `cof [(Term.proj `c "." `ord)])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow
       `c
       "^"
       (Term.app `cof [(Term.proj `c "." `ord)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow', expected 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow._@.SetTheory.Cardinal.Cofinality._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_power_cof
  { c : Cardinal .{ u } } : ℵ₀ ≤ c → c < c ^ cof c . ord
  :=
    Quotient.induction_on c
      fun
        α h
          =>
          by
            rcases ord_eq α with ⟨ r , wo , re ⟩
              ;
              skip
              have := ord_is_limit h
              rw [ mk_def , re ] at this ⊢
              rcases cof_eq' r this with ⟨ S , H , Se ⟩
              have := sum_lt_prod fun a : S => # { x // r x a } fun _ => # α fun i => _
              ·
                simp
                    only
                    [ Cardinal.prod_const , Cardinal.lift_id , ← Se , ← mk_sigma , power_def ]
                    at this ⊢
                  refine' lt_of_le_of_lt _ this
                  refine' ⟨ embedding.of_surjective _ _ ⟩
                  · exact fun x => x . 2 . 1
                  · exact fun a => let ⟨ b , h , ab ⟩ := H a ⟨ ⟨ ⟨ _ , h ⟩ , _ , ab ⟩ , rfl ⟩
              · have := typein_lt_type r i rwa [ ← re , lt_ord ] at this
#align cardinal.lt_power_cof Cardinal.lt_power_cof

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `lt_cof_power [])
      (Command.declSig
       [(Term.implicitBinder "{" [`a `b] [":" `Cardinal] "}")
        (Term.explicitBinder
         "("
         [`ha]
         [":" («term_≤_» (Cardinal.SetTheory.Cardinal.Basic.cardinal.aleph_0 "ℵ₀") "≤" `a)]
         []
         ")")
        (Term.explicitBinder "(" [`b1] [":" («term_<_» (num "1") "<" `b)] [] ")")]
       (Term.typeSpec
        ":"
        («term_<_»
         `a
         "<"
         (Term.app
          `cof
          [(Term.proj (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow `b "^" `a) "." `ord)]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`b0 []]
              [(Term.typeSpec ":" («term_≠_» `b "≠" (num "0")))]
              ":="
              (Term.proj (Term.app `zero_lt_one.trans [`b1]) "." `ne'))))
           []
           (Tactic.apply
            "apply"
            (Term.app
             `lt_imp_lt_of_le_imp_le
             [(«term_<|_» `power_le_power_left "<|" (Term.app `power_ne_zero [`a `b0]))]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `power_mul)
              ","
              (Tactic.rwRule [] (Term.app `mul_eq_self [`ha]))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.app
             `lt_power_cof
             [(«term_<|_»
               `ha.trans
               "<|"
               (Term.proj (Term.app `cantor' [(Term.hole "_") `b1]) "." `le))]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`b0 []]
             [(Term.typeSpec ":" («term_≠_» `b "≠" (num "0")))]
             ":="
             (Term.proj (Term.app `zero_lt_one.trans [`b1]) "." `ne'))))
          []
          (Tactic.apply
           "apply"
           (Term.app
            `lt_imp_lt_of_le_imp_le
            [(«term_<|_» `power_le_power_left "<|" (Term.app `power_ne_zero [`a `b0]))]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `power_mul)
             ","
             (Tactic.rwRule [] (Term.app `mul_eq_self [`ha]))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            `lt_power_cof
            [(«term_<|_»
              `ha.trans
              "<|"
              (Term.proj (Term.app `cantor' [(Term.hole "_") `b1]) "." `le))]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `lt_power_cof
        [(«term_<|_»
          `ha.trans
          "<|"
          (Term.proj (Term.app `cantor' [(Term.hole "_") `b1]) "." `le))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_power_cof
       [(«term_<|_» `ha.trans "<|" (Term.proj (Term.app `cantor' [(Term.hole "_") `b1]) "." `le))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `ha.trans "<|" (Term.proj (Term.app `cantor' [(Term.hole "_") `b1]) "." `le))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `cantor' [(Term.hole "_") `b1]) "." `le)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `cantor' [(Term.hole "_") `b1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cantor'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `cantor' [(Term.hole "_") `b1])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `ha.trans
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      `ha.trans
      "<|"
      (Term.proj (Term.paren "(" (Term.app `cantor' [(Term.hole "_") `b1]) ")") "." `le))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_power_cof
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `power_mul)
         ","
         (Tactic.rwRule [] (Term.app `mul_eq_self [`ha]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_eq_self [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_eq_self
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `power_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply
       "apply"
       (Term.app
        `lt_imp_lt_of_le_imp_le
        [(«term_<|_» `power_le_power_left "<|" (Term.app `power_ne_zero [`a `b0]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `lt_imp_lt_of_le_imp_le
       [(«term_<|_» `power_le_power_left "<|" (Term.app `power_ne_zero [`a `b0]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_» `power_le_power_left "<|" (Term.app `power_ne_zero [`a `b0]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `power_ne_zero [`a `b0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `power_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `power_le_power_left
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_» `power_le_power_left "<|" (Term.app `power_ne_zero [`a `b0]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `lt_imp_lt_of_le_imp_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`b0 []]
         [(Term.typeSpec ":" («term_≠_» `b "≠" (num "0")))]
         ":="
         (Term.proj (Term.app `zero_lt_one.trans [`b1]) "." `ne'))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `zero_lt_one.trans [`b1]) "." `ne')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `zero_lt_one.trans [`b1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `zero_lt_one.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `zero_lt_one.trans [`b1]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≠_» `b "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `b
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_<_»
       `a
       "<"
       (Term.app
        `cof
        [(Term.proj (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow `b "^" `a) "." `ord)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `cof
       [(Term.proj (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow `b "^" `a) "." `ord)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow `b "^" `a) "." `ord)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow `b "^" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow', expected 'Cardinal.SetTheory.Cardinal.Cofinality.cardinal.pow._@.SetTheory.Cardinal.Cofinality._hyg.16'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_cof_power
  { a b : Cardinal } ( ha : ℵ₀ ≤ a ) ( b1 : 1 < b ) : a < cof b ^ a . ord
  :=
    by
      have b0 : b ≠ 0 := zero_lt_one.trans b1 . ne'
        apply lt_imp_lt_of_le_imp_le power_le_power_left <| power_ne_zero a b0
        rw [ ← power_mul , mul_eq_self ha ]
        exact lt_power_cof ha.trans <| cantor' _ b1 . le
#align cardinal.lt_cof_power Cardinal.lt_cof_power

end Cardinal

