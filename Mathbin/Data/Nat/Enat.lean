import Mathbin.Data.Equiv.MulAdd 
import Mathbin.Tactic.NormNum 
import Mathbin.Data.Part

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

instance : HasZero Enat :=
  ⟨some 0⟩

instance : Inhabited Enat :=
  ⟨0⟩

instance : HasOne Enat :=
  ⟨some 1⟩

instance : Add Enat :=
  ⟨fun x y => ⟨x.dom ∧ y.dom, fun h => get x h.1+get y h.2⟩⟩

instance (n : ℕ) : Decidable (some n).Dom :=
  is_true trivialₓ

theorem some_eq_coe (n : ℕ) : some n = n :=
  by 
    induction' n with n ih
    ·
      rfl 
    apply Part.ext'
    ·
      show True ↔ (n : Enat).Dom ∧ True 
      rw [←ih, and_trueₓ]
      exact Iff.rfl
    ·
      intro h H 
      show n.succ = (n : Enat).get H.1+1
      rw [Nat.cast_succ] at H 
      revert H 
      simp only [←ih]
      intro 
      rfl

@[simp]
theorem coe_inj {x y : ℕ} : (x : Enat) = y ↔ x = y :=
  by 
    simpa only [←some_eq_coe] using Part.some_inj

@[simp]
theorem dom_some (x : ℕ) : (some x).Dom :=
  trivialₓ

@[simp]
theorem dom_coe (x : ℕ) : (x : Enat).Dom :=
  by 
    rw [←some_eq_coe] <;> trivial

instance : AddCommMonoidₓ Enat :=
  { add := ·+·, zero := 0, add_comm := fun x y => Part.ext' And.comm fun _ _ => add_commₓ _ _,
    zero_add := fun x => Part.ext' (true_andₓ _) fun _ _ => zero_addₓ _,
    add_zero := fun x => Part.ext' (and_trueₓ _) fun _ _ => add_zeroₓ _,
    add_assoc := fun x y z => Part.ext' And.assoc fun _ _ => add_assocₓ _ _ _ }

instance : LE Enat :=
  ⟨fun x y => ∃ h : y.dom → x.dom, ∀ hy : y.dom, x.get (h hy) ≤ y.get hy⟩

instance : HasTop Enat :=
  ⟨none⟩

instance : HasBot Enat :=
  ⟨0⟩

instance : HasSup Enat :=
  ⟨fun x y => ⟨x.dom ∧ y.dom, fun h => x.get h.1⊔y.get h.2⟩⟩

theorem le_def (x y : Enat) : x ≤ y ↔ ∃ h : y.dom → x.dom, ∀ hy : y.dom, x.get (h hy) ≤ y.get hy :=
  Iff.rfl

@[elab_as_eliminator]
protected theorem cases_on' {P : Enat → Prop} : ∀ a : Enat, P ⊤ → (∀ n : ℕ, P (some n)) → P a :=
  Part.induction_on

@[elab_as_eliminator]
protected theorem cases_on {P : Enat → Prop} : ∀ a : Enat, P ⊤ → (∀ n : ℕ, P n) → P a :=
  by 
    simp only [←some_eq_coe]
    exact Enat.cases_on'

@[simp]
theorem top_add (x : Enat) : (⊤+x) = ⊤ :=
  Part.ext' (false_andₓ _) fun h => h.left.elim

@[simp]
theorem add_top (x : Enat) : (x+⊤) = ⊤ :=
  by 
    rw [add_commₓ, top_add]

@[simp]
theorem coe_get {x : Enat} (h : x.dom) : (x.get h : Enat) = x :=
  by 
    rw [←some_eq_coe]
    exact Part.ext' (iff_of_true trivialₓ h) fun _ _ => rfl

@[simp, normCast]
theorem get_coe' (x : ℕ) (h : (x : Enat).Dom) : get (x : Enat) h = x :=
  by 
    rw [←coe_inj, coe_get]

theorem get_coe {x : ℕ} : get (x : Enat) (dom_coe x) = x :=
  get_coe' _ _

theorem coe_add_get {x : ℕ} {y : Enat} (h : ((x : Enat)+y).Dom) : get ((x : Enat)+y) h = x+get y h.2 :=
  by 
    simp only [←some_eq_coe] at h⊢
    rfl

@[simp]
theorem get_add {x y : Enat} (h : (x+y).Dom) : get (x+y) h = x.get h.1+y.get h.2 :=
  rfl

@[simp]
theorem get_zero (h : (0 : Enat).Dom) : (0 : Enat).get h = 0 :=
  rfl

@[simp]
theorem get_one (h : (1 : Enat).Dom) : (1 : Enat).get h = 1 :=
  rfl

theorem get_eq_iff_eq_some {a : Enat} {ha : a.dom} {b : ℕ} : a.get ha = b ↔ a = some b :=
  get_eq_iff_eq_some

theorem get_eq_iff_eq_coe {a : Enat} {ha : a.dom} {b : ℕ} : a.get ha = b ↔ a = b :=
  by 
    rw [get_eq_iff_eq_some, some_eq_coe]

theorem dom_of_le_of_dom {x y : Enat} : x ≤ y → y.dom → x.dom :=
  fun ⟨h, _⟩ => h

theorem dom_of_le_some {x : Enat} {y : ℕ} (h : x ≤ some y) : x.dom :=
  dom_of_le_of_dom h trivialₓ

theorem dom_of_le_coe {x : Enat} {y : ℕ} (h : x ≤ y) : x.dom :=
  by 
    rw [←some_eq_coe] at h 
    exact dom_of_le_some h

instance decidable_le (x y : Enat) [Decidable x.dom] [Decidable y.dom] : Decidable (x ≤ y) :=
  if hx : x.dom then
    decidableOfDecidableOfIff
        (show Decidable (∀ hy : (y : Enat).Dom, x.get hx ≤ (y : Enat).get hy) from forallPropDecidable _)$
      by 
        dsimp [· ≤ ·]
        simp only [hx, exists_prop_of_true, forall_true_iff]
  else
    if hy : y.dom then is_false$ fun h => hx$ dom_of_le_of_dom h hy else
      is_true ⟨fun h => (hy h).elim, fun h => (hy h).elim⟩

/-- The coercion `ℕ → enat` preserves `0` and addition. -/
def coe_hom : ℕ →+ Enat :=
  ⟨coeₓ, Nat.cast_zero, Nat.cast_add⟩

@[simp]
theorem coe_coe_hom : «expr⇑ » coe_hom = coeₓ :=
  rfl

instance : PartialOrderₓ Enat :=
  { le := · ≤ ·, le_refl := fun x => ⟨id, fun _ => le_reflₓ _⟩,
    le_trans := fun x y z ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩ => ⟨hxy₁ ∘ hyz₁, fun _ => le_transₓ (hxy₂ _) (hyz₂ _)⟩,
    le_antisymm :=
      fun x y ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩ => Part.ext' ⟨hyx₁, hxy₁⟩ fun _ _ => le_antisymmₓ (hxy₂ _) (hyx₂ _) }

theorem lt_def (x y : Enat) : x < y ↔ ∃ hx : x.dom, ∀ hy : y.dom, x.get hx < y.get hy :=
  by 
    rw [lt_iff_le_not_leₓ, le_def, le_def, not_exists]
    split 
    ·
      rintro ⟨⟨hyx, H⟩, h⟩
      byCases' hx : x.dom
      ·
        use hx 
        intro hy 
        specialize H hy 
        specialize h fun _ => hy 
        rw [not_forall] at h 
        cases' h with hx' h 
        rw [not_leₓ] at h 
        exact h
      ·
        specialize h fun hx' => (hx hx').elim 
        rw [not_forall] at h 
        cases' h with hx' h 
        exact (hx hx').elim
    ·
      rintro ⟨hx, H⟩
      exact ⟨⟨fun _ => hx, fun hy => (H hy).le⟩, fun hxy h => not_lt_of_le (h _) (H _)⟩

@[simp, normCast]
theorem coe_le_coe {x y : ℕ} : (x : Enat) ≤ y ↔ x ≤ y :=
  by 
    rw [←some_eq_coe, ←some_eq_coe]
    exact ⟨fun ⟨_, h⟩ => h trivialₓ, fun h => ⟨fun _ => trivialₓ, fun _ => h⟩⟩

@[simp, normCast]
theorem coe_lt_coe {x y : ℕ} : (x : Enat) < y ↔ x < y :=
  by 
    rw [lt_iff_le_not_leₓ, lt_iff_le_not_leₓ, coe_le_coe, coe_le_coe]

@[simp]
theorem get_le_get {x y : Enat} {hx : x.dom} {hy : y.dom} : x.get hx ≤ y.get hy ↔ x ≤ y :=
  by 
    conv  => toLHS rw [←coe_le_coe, coe_get, coe_get]

theorem le_coe_iff (x : Enat) (n : ℕ) : x ≤ n ↔ ∃ h : x.dom, x.get h ≤ n :=
  by 
    rw [←some_eq_coe]
    show (∃ h : True → x.dom, _) ↔ ∃ h : x.dom, x.get h ≤ n 
    simp only [forall_prop_of_true, some_eq_coe, dom_coe, get_coe']
    split  <;>
      rintro ⟨_, _⟩ <;>
        refine' ⟨_, _⟩ <;>
          intros  <;>
            try 
              assumption

theorem lt_coe_iff (x : Enat) (n : ℕ) : x < n ↔ ∃ h : x.dom, x.get h < n :=
  by 
    simp only [lt_def, forall_prop_of_true, get_coe', dom_coe]

theorem coe_le_iff (n : ℕ) (x : Enat) : (n : Enat) ≤ x ↔ ∀ h : x.dom, n ≤ x.get h :=
  by 
    rw [←some_eq_coe]
    simp only [le_def, exists_prop_of_true, dom_some, forall_true_iff]
    rfl

theorem coe_lt_iff (n : ℕ) (x : Enat) : (n : Enat) < x ↔ ∀ h : x.dom, n < x.get h :=
  by 
    rw [←some_eq_coe]
    simp only [lt_def, exists_prop_of_true, dom_some, forall_true_iff]
    rfl

protected theorem zero_lt_one : (0 : Enat) < 1 :=
  by 
    normCast 
    normNum

instance SemilatticeSup : SemilatticeSup Enat :=
  { Enat.partialOrder with sup := ·⊔·, le_sup_left := fun _ _ => ⟨And.left, fun _ => le_sup_left⟩,
    le_sup_right := fun _ _ => ⟨And.right, fun _ => le_sup_right⟩,
    sup_le := fun x y z ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ => ⟨fun hz => ⟨hx₁ hz, hy₁ hz⟩, fun _ => sup_le (hx₂ _) (hy₂ _)⟩ }

instance OrderBot : OrderBot Enat :=
  { bot := ⊥, bot_le := fun _ => ⟨fun _ => trivialₓ, fun _ => Nat.zero_leₓ _⟩ }

instance OrderTop : OrderTop Enat :=
  { top := ⊤, le_top := fun x => ⟨fun h => False.elim h, fun hy => False.elim hy⟩ }

theorem dom_of_lt {x y : Enat} : x < y → x.dom :=
  Enat.cases_on x not_top_lt$ fun _ _ => dom_coe _

theorem top_eq_none : (⊤ : Enat) = none :=
  rfl

@[simp]
theorem coe_lt_top (x : ℕ) : (x : Enat) < ⊤ :=
  Ne.lt_top
    fun h =>
      absurd (congr_argₓ dom h)$
        by 
          simpa only [dom_coe] using true_ne_false

@[simp]
theorem coe_ne_top (x : ℕ) : (x : Enat) ≠ ⊤ :=
  ne_of_ltₓ (coe_lt_top x)

theorem ne_top_iff {x : Enat} : x ≠ ⊤ ↔ ∃ n : ℕ, x = n :=
  by 
    simpa only [←some_eq_coe] using Part.ne_none_iff

theorem ne_top_iff_dom {x : Enat} : x ≠ ⊤ ↔ x.dom :=
  by 
    classical <;> exact not_iff_comm.1 part.eq_none_iff'.symm

theorem ne_top_of_lt {x y : Enat} (h : x < y) : x ≠ ⊤ :=
  ne_of_ltₓ$ lt_of_lt_of_leₓ h le_top

theorem eq_top_iff_forall_lt (x : Enat) : x = ⊤ ↔ ∀ n : ℕ, (n : Enat) < x :=
  by 
    split 
    ·
      rintro rfl n 
      exact coe_lt_top _
    ·
      contrapose! 
      rw [ne_top_iff]
      rintro ⟨n, rfl⟩
      exact ⟨n, irrefl _⟩

theorem eq_top_iff_forall_le (x : Enat) : x = ⊤ ↔ ∀ n : ℕ, (n : Enat) ≤ x :=
  (eq_top_iff_forall_lt x).trans
    ⟨fun h n => (h n).le, fun h n => lt_of_lt_of_leₓ (coe_lt_coe.mpr n.lt_succ_self) (h (n+1))⟩

theorem pos_iff_one_le {x : Enat} : 0 < x ↔ 1 ≤ x :=
  Enat.cases_on x
      (by 
        simp only [iff_trueₓ, le_top, coe_lt_top, ←@Nat.cast_zero Enat])$
    fun n =>
      by 
        rw [←Nat.cast_zero, ←Nat.cast_one, Enat.coe_lt_coe, Enat.coe_le_coe]
        rfl

noncomputable instance : LinearOrderₓ Enat :=
  { Enat.partialOrder with
    le_total :=
      fun x y =>
        Enat.cases_on x (Or.inr le_top)
          (Enat.cases_on y (fun _ => Or.inl le_top)
            fun x y => (le_totalₓ x y).elim (Or.inr ∘ coe_le_coe.2) (Or.inl ∘ coe_le_coe.2)),
    decidableLe := Classical.decRel _ }

instance : BoundedOrder Enat :=
  { Enat.orderTop, Enat.orderBot with  }

noncomputable instance : Lattice Enat :=
  { Enat.semilatticeSup with inf := min, inf_le_left := min_le_leftₓ, inf_le_right := min_le_rightₓ,
    le_inf := fun _ _ _ => le_minₓ }

theorem sup_eq_max {a b : Enat} : a⊔b = max a b :=
  le_antisymmₓ (sup_le (le_max_leftₓ _ _) (le_max_rightₓ _ _)) (max_leₓ le_sup_left le_sup_right)

theorem inf_eq_min {a b : Enat} : a⊓b = min a b :=
  rfl

instance : OrderedAddCommMonoid Enat :=
  { Enat.linearOrder, Enat.addCommMonoid with
    add_le_add_left :=
      fun a b ⟨h₁, h₂⟩ c =>
        Enat.cases_on c
          (by 
            simp )
          fun c =>
            ⟨fun h => And.intro (dom_coe _) (h₁ h.2),
              fun h =>
                by 
                  simpa only [coe_add_get] using add_le_add_left (h₂ _) c⟩ }

instance : CanonicallyOrderedAddMonoid Enat :=
  { Enat.semilatticeSup, Enat.orderBot, Enat.orderedAddCommMonoid with
    le_iff_exists_add :=
      fun a b =>
        Enat.cases_on b (iff_of_true le_top ⟨⊤, (add_top _).symm⟩)
          fun b =>
            Enat.cases_on a
              (iff_of_false (not_le_of_gtₓ (coe_lt_top _))
                (not_exists.2
                  fun x =>
                    ne_of_ltₓ
                      (by 
                        rw [top_add] <;> exact coe_lt_top _)))
              fun a =>
                ⟨fun h =>
                    ⟨(b - a : ℕ),
                      by 
                        rw [←Nat.cast_add, coe_inj, add_commₓ, tsub_add_cancel_of_le (coe_le_coe.1 h)]⟩,
                  fun ⟨c, hc⟩ =>
                    Enat.cases_on c
                      (fun hc =>
                        hc.symm ▸
                          show (a : Enat) ≤ a+⊤by 
                            rw [add_top] <;> exact le_top)
                      (fun c hc : (b : Enat) = a+c =>
                        coe_le_coe.2
                          (by 
                            rw [←Nat.cast_add, coe_inj] at hc <;> rw [hc] <;> exact Nat.le_add_rightₓ _ _))
                      hc⟩ }

protected theorem add_lt_add_right {x y z : Enat} (h : x < y) (hz : z ≠ ⊤) : (x+z) < y+z :=
  by 
    rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
    rcases ne_top_iff.mp hz with ⟨k, rfl⟩
    induction' y using Enat.cases_on with n
    ·
      rw [top_add]
      applyModCast coe_lt_top 
    normCast  at h 
    applyModCast add_lt_add_right h

protected theorem add_lt_add_iff_right {x y z : Enat} (hz : z ≠ ⊤) : ((x+z) < y+z) ↔ x < y :=
  ⟨lt_of_add_lt_add_right, fun h => Enat.add_lt_add_right h hz⟩

protected theorem add_lt_add_iff_left {x y z : Enat} (hz : z ≠ ⊤) : ((z+x) < z+y) ↔ x < y :=
  by 
    rw [add_commₓ z, add_commₓ z, Enat.add_lt_add_iff_right hz]

protected theorem lt_add_iff_pos_right {x y : Enat} (hx : x ≠ ⊤) : (x < x+y) ↔ 0 < y :=
  by 
    convRHS => rw [←Enat.add_lt_add_iff_left hx]
    rw [add_zeroₓ]

theorem lt_add_one {x : Enat} (hx : x ≠ ⊤) : x < x+1 :=
  by 
    rw [Enat.lt_add_iff_pos_right hx]
    normCast 
    normNum

theorem le_of_lt_add_one {x y : Enat} (h : x < y+1) : x ≤ y :=
  by 
    induction' y using Enat.cases_on with n 
    apply le_top 
    rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
    applyModCast Nat.le_of_lt_succₓ 
    applyModCast h

theorem add_one_le_of_lt {x y : Enat} (h : x < y) : (x+1) ≤ y :=
  by 
    induction' y using Enat.cases_on with n 
    apply le_top 
    rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
    applyModCast Nat.succ_le_of_ltₓ 
    applyModCast h

theorem add_one_le_iff_lt {x y : Enat} (hx : x ≠ ⊤) : (x+1) ≤ y ↔ x < y :=
  by 
    split 
    swap 
    exact add_one_le_of_lt 
    intro h 
    rcases ne_top_iff.mp hx with ⟨m, rfl⟩
    induction' y using Enat.cases_on with n 
    apply coe_lt_top 
    applyModCast Nat.lt_of_succ_leₓ 
    applyModCast h

theorem lt_add_one_iff_lt {x y : Enat} (hx : x ≠ ⊤) : (x < y+1) ↔ x ≤ y :=
  by 
    split 
    exact le_of_lt_add_one 
    intro h 
    rcases ne_top_iff.mp hx with ⟨m, rfl⟩
    induction' y using Enat.cases_on with n
    ·
      rw [top_add]
      apply coe_lt_top 
    applyModCast Nat.lt_succ_of_leₓ 
    applyModCast h

theorem add_eq_top_iff {a b : Enat} : (a+b) = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
  by 
    apply Enat.cases_on a <;>
      apply Enat.cases_on b <;> simp  <;> simp only [(Nat.cast_add _ _).symm, Enat.coe_ne_top] <;> simp 

protected theorem add_right_cancel_iffₓ {a b c : Enat} (hc : c ≠ ⊤) : ((a+c) = b+c) ↔ a = b :=
  by 
    rcases ne_top_iff.1 hc with ⟨c, rfl⟩
    apply Enat.cases_on a <;>
      apply Enat.cases_on b <;>
        simp [add_eq_top_iff, coe_ne_top, @eq_comm _ (⊤ : Enat)] <;>
          simp only [(Nat.cast_add _ _).symm, add_left_cancel_iffₓ, Enat.coe_inj, add_commₓ] <;> tauto

protected theorem add_left_cancel_iffₓ {a b c : Enat} (ha : a ≠ ⊤) : ((a+b) = a+c) ↔ b = c :=
  by 
    rw [add_commₓ a, add_commₓ a, Enat.add_right_cancel_iff ha]

section WithTop

/-- Computably converts an `enat` to a `with_top ℕ`. -/
def to_with_top (x : Enat) [Decidable x.dom] : WithTop ℕ :=
  x.to_option

theorem to_with_top_top : to_with_top ⊤ = ⊤ :=
  rfl

@[simp]
theorem to_with_top_top' {h : Decidable (⊤ : Enat).Dom} : to_with_top ⊤ = ⊤ :=
  by 
    convert to_with_top_top

theorem to_with_top_zero : to_with_top 0 = 0 :=
  rfl

@[simp]
theorem to_with_top_zero' {h : Decidable (0 : Enat).Dom} : to_with_top 0 = 0 :=
  by 
    convert to_with_top_zero

theorem to_with_top_some (n : ℕ) : to_with_top (some n) = n :=
  rfl

theorem to_with_top_coe (n : ℕ) {_ : Decidable (n : Enat).Dom} : to_with_top n = n :=
  by 
    simp only [←some_eq_coe, ←to_with_top_some]
    congr

@[simp]
theorem to_with_top_coe' (n : ℕ) {h : Decidable (n : Enat).Dom} : to_with_top (n : Enat) = n :=
  by 
    convert to_with_top_coe n

@[simp]
theorem to_with_top_le {x y : Enat} :
  ∀ [Decidable x.dom] [Decidable y.dom],
    by 
      exact to_with_top x ≤ to_with_top y ↔ x ≤ y :=
  Enat.cases_on y
    (by 
      simp )
    (Enat.cases_on x
      (by 
        simp )
      (by 
        intros  <;> simp ))

@[simp]
theorem to_with_top_lt {x y : Enat} [Decidable x.dom] [Decidable y.dom] : to_with_top x < to_with_top y ↔ x < y :=
  lt_iff_lt_of_le_iff_le to_with_top_le

end WithTop

section WithTopEquiv

open_locale Classical

@[simp]
theorem to_with_top_add {x y : Enat} : to_with_top (x+y) = to_with_top x+to_with_top y :=
  by 
    apply Enat.cases_on y <;> apply Enat.cases_on x
    ·
      simp 
    ·
      simp 
    ·
      simp 
    ·
      intros 
      rw [to_with_top_coe', to_with_top_coe']
      normCast 
      exact to_with_top_coe' _

/-- `equiv` between `enat` and `with_top ℕ` (for the order isomorphism see `with_top_order_iso`). -/
noncomputable def with_top_equiv : Enat ≃ WithTop ℕ :=
  { toFun := fun x => to_with_top x,
    invFun :=
      fun x =>
        match x with 
        | Option.some n => coeₓ n
        | none => ⊤,
    left_inv :=
      fun x =>
        by 
          apply Enat.cases_on x <;> intros  <;> simp  <;> rfl,
    right_inv :=
      fun x =>
        by 
          cases x <;> simp [with_top_equiv._match_1] <;> rfl }

@[simp]
theorem with_top_equiv_top : with_top_equiv ⊤ = ⊤ :=
  to_with_top_top'

@[simp]
theorem with_top_equiv_coe (n : Nat) : with_top_equiv n = n :=
  to_with_top_coe' _

@[simp]
theorem with_top_equiv_zero : with_top_equiv 0 = 0 :=
  by 
    simpa only [Nat.cast_zero] using with_top_equiv_coe 0

@[simp]
theorem with_top_equiv_le {x y : Enat} : with_top_equiv x ≤ with_top_equiv y ↔ x ≤ y :=
  to_with_top_le

@[simp]
theorem with_top_equiv_lt {x y : Enat} : with_top_equiv x < with_top_equiv y ↔ x < y :=
  to_with_top_lt

/-- `to_with_top` induces an order isomorphism between `enat` and `with_top ℕ`. -/
noncomputable def with_top_order_iso : Enat ≃o WithTop ℕ :=
  { with_top_equiv with map_rel_iff' := fun _ _ => with_top_equiv_le }

@[simp]
theorem with_top_equiv_symm_top : with_top_equiv.symm ⊤ = ⊤ :=
  rfl

@[simp]
theorem with_top_equiv_symm_coe (n : Nat) : with_top_equiv.symm n = n :=
  rfl

@[simp]
theorem with_top_equiv_symm_zero : with_top_equiv.symm 0 = 0 :=
  rfl

@[simp]
theorem with_top_equiv_symm_le {x y : WithTop ℕ} : with_top_equiv.symm x ≤ with_top_equiv.symm y ↔ x ≤ y :=
  by 
    rw [←with_top_equiv_le] <;> simp 

@[simp]
theorem with_top_equiv_symm_lt {x y : WithTop ℕ} : with_top_equiv.symm x < with_top_equiv.symm y ↔ x < y :=
  by 
    rw [←with_top_equiv_lt] <;> simp 

/-- `to_with_top` induces an additive monoid isomorphism between `enat` and `with_top ℕ`. -/
noncomputable def with_top_add_equiv : Enat ≃+ WithTop ℕ :=
  { with_top_equiv with
    map_add' :=
      fun x y =>
        by 
          simp only [with_top_equiv] <;> convert to_with_top_add }

end WithTopEquiv

-- error in Data.Nat.Enat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_wf : well_founded ((«expr < ») : enat → enat → exprProp()) :=
show well_founded (λ
 a
 b : enat, «expr < »(a, b)), by haveI [] [] [":=", expr classical.dec]; simp [] [] ["only"] ["[", expr to_with_top_lt.symm, "]"] [] [] { eta := ff }; exact [expr inv_image.wf _ (with_top.well_founded_lt nat.lt_wf)]

instance : HasWellFounded Enat :=
  ⟨· < ·, lt_wf⟩

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

-- error in Data.Nat.Enat: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem lt_find (n : exprℕ()) (h : ∀ m «expr ≤ » n, «expr¬ »(P m)) : «expr < »((n : enat), find P) :=
begin
  rw [expr coe_lt_iff] [],
  intro [ident h'],
  rw [expr find_get] [],
  have [] [] [":=", expr @nat.find_spec P _ h'],
  contrapose ["!"] [ident this],
  exact [expr h _ this]
end

theorem lt_find_iff (n : ℕ) : (n : Enat) < find P ↔ ∀ m _ : m ≤ n, ¬P m :=
  by 
    refine' ⟨_, lt_find P n⟩
    intro h m hm 
    byCases' H : (find P).Dom
    ·
      apply Nat.find_minₓ H 
      rw [coe_lt_iff] at h 
      specialize h H 
      exact lt_of_le_of_ltₓ hm h
    ·
      exact not_exists.mp H m

theorem find_le (n : ℕ) (h : P n) : find P ≤ n :=
  by 
    rw [le_coe_iff]
    refine' ⟨⟨_, h⟩, @Nat.find_min'ₓ P _ _ _ h⟩

theorem find_eq_top_iff : find P = ⊤ ↔ ∀ n, ¬P n :=
  (eq_top_iff_forall_lt _).trans
    ⟨fun h n => (lt_find_iff P n).mp (h n) _ le_rfl, fun h n => lt_find P n$ fun _ _ => h _⟩

end Find

noncomputable instance : LinearOrderedAddCommMonoidWithTop Enat :=
  { Enat.linearOrder, Enat.orderedAddCommMonoid, Enat.orderTop with top_add' := top_add }

end Enat

