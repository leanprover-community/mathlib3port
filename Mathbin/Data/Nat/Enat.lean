/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Algebra.Hom.Equiv
import Mathbin.Data.Part
import Mathbin.Tactic.NormNum

/-!
# Natural numbers with infinity

The natural numbers and an extra `top` element `⊤`.

## Main definitions

The following instances are defined:

* `ordered_add_comm_monoid enat`
* `canonically_ordered_add_monoid enat`

There is no additive analogue of `monoid_with_zero`; if there were then `enat` could
be an `add_monoid_with_top`.

* `to_with_top` : the map from `enat` to `with_top ℕ`, with theorems that it plays well
with `+` and `≤`.

* `with_top_add_equiv : enat ≃+ with_top ℕ`
* `with_top_order_iso : enat ≃o with_top ℕ`

## Implementation details

`enat` is defined to be `part ℕ`.

`+` and `≤` are defined on `enat`, but there is an issue with `*` because it's not
clear what `0 * ⊤` should be. `mul` is hence left undefined. Similarly `⊤ - ⊤` is ambiguous
so there is no `-` defined on `enat`.

Before the `open_locale classical` line, various proofs are made with decidability assumptions.
This can cause issues -- see for example the non-simp lemma `to_with_top_zero` proved by `rfl`,
followed by `@[simp] lemma to_with_top_zero'` whose proof uses `convert`.


## Tags

enat, with_top ℕ
-/


open Part hiding some

/-- Type of natural numbers with infinity (`⊤`) -/
def Enat : Type :=
  Part ℕ

namespace Enat

/-- The computable embedding `ℕ → enat`.

This coincides with the coercion `coe : ℕ → enat`, see `enat.some_eq_coe`.
However, `coe` is noncomputable so `some` is preferable when computability is a concern. -/
def some : ℕ → Enat :=
  Part.some

instance : Zero Enat :=
  ⟨some 0⟩

instance : Inhabited Enat :=
  ⟨0⟩

instance : One Enat :=
  ⟨some 1⟩

instance : Add Enat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => get x h.1 + get y h.2⟩⟩

instance (n : ℕ) : Decidable (some n).Dom :=
  isTrue trivialₓ

theorem some_eq_coe (n : ℕ) : some n = n := by
  induction' n with n ih
  · rfl
    
  apply Part.ext'
  · show True ↔ (n : Enat).Dom ∧ True
    rw [← ih, and_trueₓ]
    exact Iff.rfl
    
  · intro h H
    show n.succ = (n : Enat).get H.1 + 1
    rw [Nat.cast_succₓ] at H
    revert H
    simp only [← ih]
    intro
    rfl
    

@[simp]
theorem coe_inj {x y : ℕ} : (x : Enat) = y ↔ x = y := by
  simpa only [← some_eq_coe] using Part.some_inj

@[simp]
theorem dom_some (x : ℕ) : (some x).Dom :=
  trivialₓ

@[simp]
theorem dom_coe (x : ℕ) : (x : Enat).Dom := by
  rw [← some_eq_coe] <;> trivial

instance : AddCommMonoidₓ Enat where
  add := (· + ·)
  zero := 0
  add_comm := fun x y => Part.ext' And.comm fun _ _ => add_commₓ _ _
  zero_add := fun x => Part.ext' (true_andₓ _) fun _ _ => zero_addₓ _
  add_zero := fun x => Part.ext' (and_trueₓ _) fun _ _ => add_zeroₓ _
  add_assoc := fun x y z => Part.ext' And.assoc fun _ _ => add_assocₓ _ _ _

instance : LE Enat :=
  ⟨fun x y => ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy⟩

instance : HasTop Enat :=
  ⟨none⟩

instance : HasBot Enat :=
  ⟨0⟩

instance : HasSup Enat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => x.get h.1⊔y.get h.2⟩⟩

theorem le_def (x y : Enat) : x ≤ y ↔ ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy :=
  Iff.rfl

@[elab_as_eliminator]
protected theorem cases_on' {P : Enat → Prop} : ∀ a : Enat, P ⊤ → (∀ n : ℕ, P (some n)) → P a :=
  Part.induction_on

@[elab_as_eliminator]
protected theorem cases_on {P : Enat → Prop} : ∀ a : Enat, P ⊤ → (∀ n : ℕ, P n) → P a := by
  simp only [← some_eq_coe]
  exact Enat.cases_on'

@[simp]
theorem top_add (x : Enat) : ⊤ + x = ⊤ :=
  Part.ext' (false_andₓ _) fun h => h.left.elim

@[simp]
theorem add_top (x : Enat) : x + ⊤ = ⊤ := by
  rw [add_commₓ, top_add]

@[simp]
theorem coe_get {x : Enat} (h : x.Dom) : (x.get h : Enat) = x := by
  rw [← some_eq_coe]
  exact Part.ext' (iff_of_true trivialₓ h) fun _ _ => rfl

@[simp, norm_cast]
theorem get_coe' (x : ℕ) (h : (x : Enat).Dom) : get (x : Enat) h = x := by
  rw [← coe_inj, coe_get]

theorem get_coe {x : ℕ} : get (x : Enat) (dom_coe x) = x :=
  get_coe' _ _

theorem coe_add_get {x : ℕ} {y : Enat} (h : ((x : Enat) + y).Dom) : get ((x : Enat) + y) h = x + get y h.2 := by
  simp only [← some_eq_coe] at h⊢
  rfl

@[simp]
theorem get_add {x y : Enat} (h : (x + y).Dom) : get (x + y) h = x.get h.1 + y.get h.2 :=
  rfl

@[simp]
theorem get_zero (h : (0 : Enat).Dom) : (0 : Enat).get h = 0 :=
  rfl

@[simp]
theorem get_one (h : (1 : Enat).Dom) : (1 : Enat).get h = 1 :=
  rfl

theorem get_eq_iff_eq_some {a : Enat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = some b :=
  get_eq_iff_eq_some

theorem get_eq_iff_eq_coe {a : Enat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = b := by
  rw [get_eq_iff_eq_some, some_eq_coe]

theorem dom_of_le_of_dom {x y : Enat} : x ≤ y → y.Dom → x.Dom := fun ⟨h, _⟩ => h

theorem dom_of_le_some {x : Enat} {y : ℕ} (h : x ≤ some y) : x.Dom :=
  dom_of_le_of_dom h trivialₓ

theorem dom_of_le_coe {x : Enat} {y : ℕ} (h : x ≤ y) : x.Dom := by
  rw [← some_eq_coe] at h
  exact dom_of_le_some h

instance decidableLe (x y : Enat) [Decidable x.Dom] [Decidable y.Dom] : Decidable (x ≤ y) :=
  if hx : x.Dom then
    decidableOfDecidableOfIff
        (show Decidable (∀ hy : (y : Enat).Dom, x.get hx ≤ (y : Enat).get hy) from forallPropDecidable _) <|
      by
      dsimp' [(· ≤ ·)]
      simp only [hx, exists_prop_of_true, forall_true_iff]
  else
    if hy : y.Dom then is_false fun h => hx <| dom_of_le_of_dom h hy
    else isTrue ⟨fun h => (hy h).elim, fun h => (hy h).elim⟩

/-- The coercion `ℕ → enat` preserves `0` and addition. -/
def coeHom : ℕ →+ Enat :=
  ⟨coe, Nat.cast_zeroₓ, Nat.cast_addₓ⟩

@[simp]
theorem coe_coe_hom : ⇑coe_hom = coe :=
  rfl

instance : PartialOrderₓ Enat where
  le := (· ≤ ·)
  le_refl := fun x => ⟨id, fun _ => le_rfl⟩
  le_trans := fun x y z ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩ => ⟨hxy₁ ∘ hyz₁, fun _ => le_transₓ (hxy₂ _) (hyz₂ _)⟩
  le_antisymm := fun x y ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩ => Part.ext' ⟨hyx₁, hxy₁⟩ fun _ _ => le_antisymmₓ (hxy₂ _) (hyx₂ _)

theorem lt_def (x y : Enat) : x < y ↔ ∃ hx : x.Dom, ∀ hy : y.Dom, x.get hx < y.get hy := by
  rw [lt_iff_le_not_leₓ, le_def, le_def, not_exists]
  constructor
  · rintro ⟨⟨hyx, H⟩, h⟩
    by_cases' hx : x.dom
    · use hx
      intro hy
      specialize H hy
      specialize h fun _ => hy
      rw [not_forall] at h
      cases' h with hx' h
      rw [not_leₓ] at h
      exact h
      
    · specialize h fun hx' => (hx hx').elim
      rw [not_forall] at h
      cases' h with hx' h
      exact (hx hx').elim
      
    
  · rintro ⟨hx, H⟩
    exact ⟨⟨fun _ => hx, fun hy => (H hy).le⟩, fun hxy h => not_lt_of_le (h _) (H _)⟩
    

@[simp, norm_cast]
theorem coe_le_coe {x y : ℕ} : (x : Enat) ≤ y ↔ x ≤ y := by
  rw [← some_eq_coe, ← some_eq_coe]
  exact ⟨fun ⟨_, h⟩ => h trivialₓ, fun h => ⟨fun _ => trivialₓ, fun _ => h⟩⟩

@[simp, norm_cast]
theorem coe_lt_coe {x y : ℕ} : (x : Enat) < y ↔ x < y := by
  rw [lt_iff_le_not_leₓ, lt_iff_le_not_leₓ, coe_le_coe, coe_le_coe]

@[simp]
theorem get_le_get {x y : Enat} {hx : x.Dom} {hy : y.Dom} : x.get hx ≤ y.get hy ↔ x ≤ y := by
  conv => lhs rw [← coe_le_coe, coe_get, coe_get]

theorem le_coe_iff (x : Enat) (n : ℕ) : x ≤ n ↔ ∃ h : x.Dom, x.get h ≤ n := by
  rw [← some_eq_coe]
  show (∃ h : True → x.dom, _) ↔ ∃ h : x.dom, x.get h ≤ n
  simp only [forall_prop_of_true, some_eq_coe, dom_coe, get_coe']

theorem lt_coe_iff (x : Enat) (n : ℕ) : x < n ↔ ∃ h : x.Dom, x.get h < n := by
  simp only [lt_def, forall_prop_of_true, get_coe', dom_coe]

theorem coe_le_iff (n : ℕ) (x : Enat) : (n : Enat) ≤ x ↔ ∀ h : x.Dom, n ≤ x.get h := by
  rw [← some_eq_coe]
  simp only [le_def, exists_prop_of_true, dom_some, forall_true_iff]
  rfl

theorem coe_lt_iff (n : ℕ) (x : Enat) : (n : Enat) < x ↔ ∀ h : x.Dom, n < x.get h := by
  rw [← some_eq_coe]
  simp only [lt_def, exists_prop_of_true, dom_some, forall_true_iff]
  rfl

protected theorem zero_lt_one : (0 : Enat) < 1 := by
  norm_cast
  norm_num

instance semilatticeSup : SemilatticeSup Enat :=
  { Enat.partialOrder with sup := (·⊔·), le_sup_left := fun _ _ => ⟨And.left, fun _ => le_sup_left⟩,
    le_sup_right := fun _ _ => ⟨And.right, fun _ => le_sup_right⟩,
    sup_le := fun x y z ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ => ⟨fun hz => ⟨hx₁ hz, hy₁ hz⟩, fun _ => sup_le (hx₂ _) (hy₂ _)⟩ }

instance orderBot : OrderBot Enat where
  bot := ⊥
  bot_le := fun _ => ⟨fun _ => trivialₓ, fun _ => Nat.zero_leₓ _⟩

instance orderTop : OrderTop Enat where
  top := ⊤
  le_top := fun x => ⟨fun h => False.elim h, fun hy => False.elim hy⟩

theorem dom_of_lt {x y : Enat} : x < y → x.Dom :=
  (Enat.cases_on x not_top_lt) fun _ _ => dom_coe _

theorem top_eq_none : (⊤ : Enat) = none :=
  rfl

@[simp]
theorem coe_lt_top (x : ℕ) : (x : Enat) < ⊤ :=
  Ne.lt_top fun h =>
    absurd (congr_arg Dom h) <| by
      simpa only [dom_coe] using true_ne_false

@[simp]
theorem coe_ne_top (x : ℕ) : (x : Enat) ≠ ⊤ :=
  ne_of_ltₓ (coe_lt_top x)

theorem ne_top_iff {x : Enat} : x ≠ ⊤ ↔ ∃ n : ℕ, x = n := by
  simpa only [← some_eq_coe] using Part.ne_none_iff

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem ne_top_iff_dom {x : Enat} : x ≠ ⊤ ↔ x.Dom := by
  classical <;> exact not_iff_comm.1 part.eq_none_iff'.symm

theorem ne_top_of_lt {x y : Enat} (h : x < y) : x ≠ ⊤ :=
  ne_of_ltₓ <| lt_of_lt_of_leₓ h le_top

theorem eq_top_iff_forall_lt (x : Enat) : x = ⊤ ↔ ∀ n : ℕ, (n : Enat) < x := by
  constructor
  · rintro rfl n
    exact coe_lt_top _
    
  · contrapose!
    rw [ne_top_iff]
    rintro ⟨n, rfl⟩
    exact ⟨n, irrefl _⟩
    

theorem eq_top_iff_forall_le (x : Enat) : x = ⊤ ↔ ∀ n : ℕ, (n : Enat) ≤ x :=
  (eq_top_iff_forall_lt x).trans
    ⟨fun h n => (h n).le, fun h n => lt_of_lt_of_leₓ (coe_lt_coe.mpr n.lt_succ_self) (h (n + 1))⟩

theorem pos_iff_one_le {x : Enat} : 0 < x ↔ 1 ≤ x :=
  (Enat.cases_on x
      (by
        simp only [iff_trueₓ, le_top, coe_lt_top, ← @Nat.cast_zeroₓ Enat]))
    fun n => by
    rw [← Nat.cast_zeroₓ, ← Nat.cast_oneₓ, Enat.coe_lt_coe, Enat.coe_le_coe]
    rfl

instance : IsTotal Enat (· ≤ ·) where
  Total := fun x y =>
    Enat.cases_on x (Or.inr le_top)
      (Enat.cases_on y (fun _ => Or.inl le_top) fun x y =>
        (le_totalₓ x y).elim (Or.inr ∘ coe_le_coe.2) (Or.inl ∘ coe_le_coe.2))

noncomputable instance : LinearOrderₓ Enat :=
  { Enat.partialOrder with le_total := IsTotal.total, decidableLe := Classical.decRel _, max := (·⊔·),
    max_def := @sup_eq_max_default _ _ (id _) _ }

instance : BoundedOrder Enat :=
  { Enat.orderTop, Enat.orderBot with }

noncomputable instance : Lattice Enat :=
  { Enat.semilatticeSup with inf := min, inf_le_left := min_le_leftₓ, inf_le_right := min_le_rightₓ,
    le_inf := fun _ _ _ => le_minₓ }

instance : OrderedAddCommMonoid Enat :=
  { Enat.linearOrder, Enat.addCommMonoid with
    add_le_add_left := fun c =>
      Enat.cases_on c
        (by
          simp )
        fun c =>
        ⟨fun h => And.intro (dom_coe _) (h₁ h.2), fun h => by
          simpa only [coe_add_get] using add_le_add_left (h₂ _) c⟩ }

instance : CanonicallyOrderedAddMonoid Enat :=
  { Enat.semilatticeSup, Enat.orderBot, Enat.orderedAddCommMonoid with
    le_self_add := fun a b =>
      (Enat.cases_on b (le_top.trans_eq (add_top _).symm)) fun b =>
        (Enat.cases_on a (top_add _).Ge) fun a => (coe_le_coe.2 le_self_add).trans_eq (Nat.cast_addₓ _ _),
    exists_add_of_le := fun a b =>
      (Enat.cases_on b fun _ => ⟨⊤, (add_top _).symm⟩) fun b =>
        (Enat.cases_on a fun h => ((coe_lt_top _).not_le h).elim) fun a h =>
          ⟨(b - a : ℕ), by
            rw [← Nat.cast_addₓ, coe_inj, add_commₓ, tsub_add_cancel_of_le (coe_le_coe.1 h)]⟩ }

protected theorem add_lt_add_right {x y z : Enat} (h : x < y) (hz : z ≠ ⊤) : x + z < y + z := by
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  rcases ne_top_iff.mp hz with ⟨k, rfl⟩
  induction' y using Enat.cases_on with n
  · rw [top_add]
    apply_mod_cast coe_lt_top
    
  norm_cast  at h
  apply_mod_cast add_lt_add_right h

protected theorem add_lt_add_iff_right {x y z : Enat} (hz : z ≠ ⊤) : x + z < y + z ↔ x < y :=
  ⟨lt_of_add_lt_add_right, fun h => Enat.add_lt_add_right h hz⟩

protected theorem add_lt_add_iff_left {x y z : Enat} (hz : z ≠ ⊤) : z + x < z + y ↔ x < y := by
  rw [add_commₓ z, add_commₓ z, Enat.add_lt_add_iff_right hz]

protected theorem lt_add_iff_pos_right {x y : Enat} (hx : x ≠ ⊤) : x < x + y ↔ 0 < y := by
  conv_rhs => rw [← Enat.add_lt_add_iff_left hx]
  rw [add_zeroₓ]

theorem lt_add_one {x : Enat} (hx : x ≠ ⊤) : x < x + 1 := by
  rw [Enat.lt_add_iff_pos_right hx]
  norm_cast
  norm_num

theorem le_of_lt_add_one {x y : Enat} (h : x < y + 1) : x ≤ y := by
  induction' y using Enat.cases_on with n
  apply le_top
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  apply_mod_cast Nat.le_of_lt_succₓ
  apply_mod_cast h

theorem add_one_le_of_lt {x y : Enat} (h : x < y) : x + 1 ≤ y := by
  induction' y using Enat.cases_on with n
  apply le_top
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  apply_mod_cast Nat.succ_le_of_ltₓ
  apply_mod_cast h

theorem add_one_le_iff_lt {x y : Enat} (hx : x ≠ ⊤) : x + 1 ≤ y ↔ x < y := by
  constructor
  swap
  exact add_one_le_of_lt
  intro h
  rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  induction' y using Enat.cases_on with n
  apply coe_lt_top
  apply_mod_cast Nat.lt_of_succ_leₓ
  apply_mod_cast h

theorem lt_add_one_iff_lt {x y : Enat} (hx : x ≠ ⊤) : x < y + 1 ↔ x ≤ y := by
  constructor
  exact le_of_lt_add_one
  intro h
  rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  induction' y using Enat.cases_on with n
  · rw [top_add]
    apply coe_lt_top
    
  apply_mod_cast Nat.lt_succ_of_leₓ
  apply_mod_cast h

theorem add_eq_top_iff {a b : Enat} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  apply Enat.cases_on a <;>
    apply Enat.cases_on b <;> simp <;> simp only [(Nat.cast_addₓ _ _).symm, Enat.coe_ne_top] <;> simp

protected theorem add_right_cancel_iff {a b c : Enat} (hc : c ≠ ⊤) : a + c = b + c ↔ a = b := by
  rcases ne_top_iff.1 hc with ⟨c, rfl⟩
  apply Enat.cases_on a <;>
    apply Enat.cases_on b <;>
      simp [add_eq_top_iff, coe_ne_top, @eq_comm _ (⊤ : Enat)] <;>
        simp only [(Nat.cast_addₓ _ _).symm, add_left_cancel_iffₓ, Enat.coe_inj, add_commₓ] <;> tauto

protected theorem add_left_cancel_iff {a b c : Enat} (ha : a ≠ ⊤) : a + b = a + c ↔ b = c := by
  rw [add_commₓ a, add_commₓ a, Enat.add_right_cancel_iff ha]

section WithTop

/-- Computably converts an `enat` to a `with_top ℕ`. -/
def toWithTop (x : Enat) [Decidable x.Dom] : WithTop ℕ :=
  x.toOption

theorem to_with_top_top : toWithTop ⊤ = ⊤ :=
  rfl

@[simp]
theorem to_with_top_top' {h : Decidable (⊤ : Enat).Dom} : toWithTop ⊤ = ⊤ := by
  convert to_with_top_top

theorem to_with_top_zero : toWithTop 0 = 0 :=
  rfl

@[simp]
theorem to_with_top_zero' {h : Decidable (0 : Enat).Dom} : toWithTop 0 = 0 := by
  convert to_with_top_zero

theorem to_with_top_some (n : ℕ) : toWithTop (some n) = n :=
  rfl

theorem to_with_top_coe (n : ℕ) {_ : Decidable (n : Enat).Dom} : toWithTop n = n := by
  simp only [← some_eq_coe, ← to_with_top_some]

@[simp]
theorem to_with_top_coe' (n : ℕ) {h : Decidable (n : Enat).Dom} : toWithTop (n : Enat) = n := by
  convert to_with_top_coe n

@[simp]
theorem to_with_top_le {x y : Enat} : ∀ [Decidable x.Dom] [Decidable y.Dom], to_with_top x ≤ to_with_top y ↔ x ≤ y :=
  Enat.cases_on y
    (by
      simp )
    (Enat.cases_on x
      (by
        simp )
      (by
        intros <;> simp ))

@[simp]
theorem to_with_top_lt {x y : Enat} [Decidable x.Dom] [Decidable y.Dom] : toWithTop x < toWithTop y ↔ x < y :=
  lt_iff_lt_of_le_iff_le to_with_top_le

end WithTop

section WithTopEquiv

open Classical

@[simp]
theorem to_with_top_add {x y : Enat} : toWithTop (x + y) = toWithTop x + toWithTop y := by
  apply Enat.cases_on y <;> apply Enat.cases_on x <;> simp [← Nat.cast_addₓ, ← WithTop.coe_add]

/-- `equiv` between `enat` and `with_top ℕ` (for the order isomorphism see `with_top_order_iso`). -/
noncomputable def withTopEquiv : Enat ≃ WithTop ℕ where
  toFun := fun x => toWithTop x
  invFun := fun x =>
    match x with
    | Option.some n => coe n
    | none => ⊤
  left_inv := fun x => by
    apply Enat.cases_on x <;> intros <;> simp <;> rfl
  right_inv := fun x => by
    cases x <;> simp [with_top_equiv._match_1] <;> rfl

@[simp]
theorem with_top_equiv_top : withTopEquiv ⊤ = ⊤ :=
  to_with_top_top'

@[simp]
theorem with_top_equiv_coe (n : Nat) : withTopEquiv n = n :=
  to_with_top_coe' _

@[simp]
theorem with_top_equiv_zero : withTopEquiv 0 = 0 := by
  simpa only [Nat.cast_zeroₓ] using with_top_equiv_coe 0

@[simp]
theorem with_top_equiv_le {x y : Enat} : withTopEquiv x ≤ withTopEquiv y ↔ x ≤ y :=
  to_with_top_le

@[simp]
theorem with_top_equiv_lt {x y : Enat} : withTopEquiv x < withTopEquiv y ↔ x < y :=
  to_with_top_lt

/-- `to_with_top` induces an order isomorphism between `enat` and `with_top ℕ`. -/
noncomputable def withTopOrderIso : Enat ≃o WithTop ℕ :=
  { withTopEquiv with map_rel_iff' := fun _ _ => with_top_equiv_le }

@[simp]
theorem with_top_equiv_symm_top : withTopEquiv.symm ⊤ = ⊤ :=
  rfl

@[simp]
theorem with_top_equiv_symm_coe (n : Nat) : withTopEquiv.symm n = n :=
  rfl

@[simp]
theorem with_top_equiv_symm_zero : withTopEquiv.symm 0 = 0 :=
  rfl

@[simp]
theorem with_top_equiv_symm_le {x y : WithTop ℕ} : withTopEquiv.symm x ≤ withTopEquiv.symm y ↔ x ≤ y := by
  rw [← with_top_equiv_le] <;> simp

@[simp]
theorem with_top_equiv_symm_lt {x y : WithTop ℕ} : withTopEquiv.symm x < withTopEquiv.symm y ↔ x < y := by
  rw [← with_top_equiv_lt] <;> simp

/-- `to_with_top` induces an additive monoid isomorphism between `enat` and `with_top ℕ`. -/
noncomputable def withTopAddEquiv : Enat ≃+ WithTop ℕ :=
  { withTopEquiv with
    map_add' := fun x y => by
      simp only [with_top_equiv] <;> convert to_with_top_add }

end WithTopEquiv

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem lt_wf : @WellFounded Enat (· < ·) := by
  classical
  change WellFounded fun a b : Enat => a < b
  simp_rw [← to_with_top_lt]
  exact InvImage.wfₓ _ (WithTop.well_founded_lt Nat.lt_wf)

instance : IsWellOrder Enat (· < ·) :=
  ⟨lt_wf⟩

instance : HasWellFounded Enat :=
  ⟨(· < ·), lt_wf⟩

section Find

variable (P : ℕ → Prop) [DecidablePred P]

/-- The smallest `enat` satisfying a (decidable) predicate `P : ℕ → Prop` -/
def find : Enat :=
  ⟨∃ n, P n, Nat.findₓ⟩

@[simp]
theorem find_get (h : (find P).Dom) : (find P).get h = Nat.findₓ h :=
  rfl

theorem find_dom (h : ∃ n, P n) : (find P).Dom :=
  h

theorem lt_find (n : ℕ) (h : ∀, ∀ m ≤ n, ∀, ¬P m) : (n : Enat) < find P := by
  rw [coe_lt_iff]
  intro h'
  rw [find_get]
  have := @Nat.find_specₓ P _ h'
  contrapose! this
  exact h _ this

theorem lt_find_iff (n : ℕ) : (n : Enat) < find P ↔ ∀, ∀ m ≤ n, ∀, ¬P m := by
  refine' ⟨_, lt_find P n⟩
  intro h m hm
  by_cases' H : (find P).Dom
  · apply Nat.find_minₓ H
    rw [coe_lt_iff] at h
    specialize h H
    exact lt_of_le_of_ltₓ hm h
    
  · exact not_exists.mp H m
    

theorem find_le (n : ℕ) (h : P n) : find P ≤ n := by
  rw [le_coe_iff]
  refine' ⟨⟨_, h⟩, @Nat.find_min'ₓ P _ _ _ h⟩

theorem find_eq_top_iff : find P = ⊤ ↔ ∀ n, ¬P n :=
  (eq_top_iff_forall_lt _).trans
    ⟨fun h n => (lt_find_iff P n).mp (h n) _ le_rfl, fun h n => (lt_find P n) fun _ _ => h _⟩

end Find

noncomputable instance : LinearOrderedAddCommMonoidWithTop Enat :=
  { Enat.linearOrder, Enat.orderedAddCommMonoid, Enat.orderTop with top_add' := top_add }

end Enat

