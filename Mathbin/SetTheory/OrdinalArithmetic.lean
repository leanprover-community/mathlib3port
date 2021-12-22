import Mathbin.SetTheory.Ordinal

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
* `nfp f a`: the next fixed point of a function `f` on ordinals, above `a`. It behaves well
  for normal functions.

* `CNF b o` is the Cantor normal form of the ordinal `o` in base `b`.

* `sup`: the supremum of an indexed family of ordinals in `Type u`, as an ordinal in `Type u`.
* `bsup`: the supremum of a set of ordinals indexed by ordinals less than a given ordinal `o`.
-/


noncomputable section

open Function Cardinal Set Equivₓ

open_locale Classical Cardinal

universe u v w

variable {α : Type _} {β : Type _} {γ : Type _} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

namespace Ordinal

/-! ### Further properties of addition on ordinals -/


@[simp]
theorem lift_add a b : lift (a+b) = lift a+lift b :=
  Quotientₓ.induction_on₂ a b $ fun ⟨α, r, _⟩ ⟨β, s, _⟩ =>
    Quotientₓ.sound
      ⟨(RelIso.preimage Equivₓ.ulift _).trans
          (RelIso.sumLexCongr (RelIso.preimage Equivₓ.ulift _) (RelIso.preimage Equivₓ.ulift _)).symm⟩

@[simp]
theorem lift_succ a : lift (succ a) = succ (lift a) := by
  unfold succ <;> simp only [lift_add, lift_one]

theorem add_le_add_iff_left a {b c : Ordinal} : ((a+b) ≤ a+c) ↔ b ≤ c :=
  ⟨induction_on a $ fun α r hr =>
      induction_on b $ fun β₁ s₁ hs₁ =>
        induction_on c $ fun β₂ s₂ hs₂ ⟨f⟩ =>
          ⟨have fl : ∀ a, f (Sum.inl a) = Sum.inl a := fun a => by
              simpa only [InitialSeg.trans_apply, InitialSeg.le_add_apply] using
                @InitialSeg.eq _ _ _ _ (@Sum.Lex.is_well_order _ _ _ _ hr hs₂) ((InitialSeg.leAdd r s₁).trans f)
                  (InitialSeg.leAdd r s₂) a
            have : ∀ b, { b' // f (Sum.inr b) = Sum.inr b' } := by
              intro b
              cases e : f (Sum.inr b)
              ·
                rw [← fl] at e
                have := f.inj' e
                contradiction
              ·
                exact ⟨_, rfl⟩
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
              ·
                rw [fl] at h
                cases h
              ·
                rw [fr] at h
                exact ⟨a', Sum.inr.injₓ h⟩⟩⟩,
    fun h => add_le_add_left h _⟩

theorem add_succ (o₁ o₂ : Ordinal) : (o₁+succ o₂) = succ (o₁+o₂) :=
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
  ne_of_gtₓ $ succ_pos o

@[simp]
theorem card_succ (o : Ordinal) : card (succ o) = card o+1 := by
  simp only [succ, card_add, card_one]

theorem nat_cast_succ (n : ℕ) : (succ n : Ordinal) = n.succ :=
  rfl

theorem add_left_cancelₓ a {b c : Ordinal} : ((a+b) = a+c) ↔ b = c := by
  simp only [le_antisymm_iffₓ, add_le_add_iff_left]

theorem lt_succ {a b : Ordinal} : a < succ b ↔ a ≤ b := by
  rw [← not_leₓ, succ_le, not_ltₓ]

theorem add_lt_add_iff_left a {b c : Ordinal} : ((a+b) < a+c) ↔ b < c := by
  rw [← not_leₓ, ← not_leₓ, add_le_add_iff_left]

theorem lt_of_add_lt_add_right {a b c : Ordinal} : ((a+b) < c+b) → a < c :=
  lt_imp_lt_of_le_imp_le fun h => add_le_add_right h _

@[simp]
theorem succ_lt_succ {a b : Ordinal} : succ a < succ b ↔ a < b := by
  rw [lt_succ, succ_le]

@[simp]
theorem succ_le_succ {a b : Ordinal} : succ a ≤ succ b ↔ a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 succ_lt_succ

theorem succ_inj {a b : Ordinal} : succ a = succ b ↔ a = b := by
  simp only [le_antisymm_iffₓ, succ_le_succ]

theorem add_le_add_iff_right {a b : Ordinal} (n : ℕ) : ((a+n) ≤ b+n) ↔ a ≤ b := by
  induction' n with n ih <;> [rw [Nat.cast_zero, add_zeroₓ, add_zeroₓ],
    rw [← nat_cast_succ, add_succ, add_succ, succ_le_succ, ih]]

theorem add_right_cancelₓ {a b : Ordinal} (n : ℕ) : ((a+n) = b+n) ↔ a = b := by
  simp only [le_antisymm_iffₓ, add_le_add_iff_right]

/-! ### The zero ordinal -/


@[simp]
theorem card_eq_zero {o} : card o = 0 ↔ o = 0 :=
  ⟨induction_on o $ fun α r _ h => by
      refine' le_antisymmₓ (le_of_not_ltₓ $ fun hn => mk_ne_zero_iff.2 _ h) (Ordinal.zero_le _)
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
  lt_iff_le_and_ne.2 ⟨Ordinal.zero_le _, Ne.symm $ Ordinal.one_ne_zero⟩

/-! ### The predecessor of an ordinal -/


/--  The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : Ordinal.{u}) : Ordinal.{u} :=
  if h : ∃ a, o = succ a then Classical.some h else o

@[simp]
theorem pred_succ o : pred (succ o) = o := by
  have h : ∃ a, succ o = succ a := ⟨_, rfl⟩ <;>
    simpa only [pred, dif_pos h] using (succ_inj.1 $ Classical.some_spec h).symm

theorem pred_le_self o : pred o ≤ o :=
  if h : ∃ a, o = succ a then
    let ⟨a, e⟩ := h
    by
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
  if h : ∃ a, b = succ a then
    let ⟨c, e⟩ := h
    by
    rw [e, pred_succ, succ_lt_succ]
  else by
    simp only [pred, dif_neg h, succ_lt_of_not_succ h]

theorem pred_le {a b} : pred a ≤ b ↔ a ≤ succ b :=
  le_iff_le_iff_lt_iff_lt.2 lt_pred

@[simp]
theorem lift_is_succ {o} : (∃ a, lift o = succ a) ↔ ∃ a, o = succ a :=
  ⟨fun ⟨a, h⟩ =>
    let ⟨b, e⟩ := lift_down $ show a ≤ lift o from le_of_ltₓ $ h.symm ▸ lt_succ_self _
    ⟨b,
      lift_inj.1 $ by
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


/--  A limit ordinal is an ordinal which is not zero and not a successor. -/
def is_limit (o : Ordinal) : Prop :=
  o ≠ 0 ∧ ∀, ∀ a < o, ∀, succ a < o

theorem not_zero_is_limit : ¬is_limit 0
  | ⟨h, _⟩ => h rfl

theorem not_succ_is_limit o : ¬is_limit (succ o)
  | ⟨_, h⟩ => lt_irreflₓ _ (h _ (lt_succ_self _))

theorem not_succ_of_is_limit {o} (h : is_limit o) : ¬∃ a, o = succ a
  | ⟨a, e⟩ => not_succ_is_limit a (e ▸ h)

theorem succ_lt_of_is_limit {o} (h : is_limit o) {a} : succ a < o ↔ a < o :=
  ⟨lt_transₓ (lt_succ_self _), h.2 _⟩

theorem le_succ_of_is_limit {o} (h : is_limit o) {a} : o ≤ succ a ↔ o ≤ a :=
  le_iff_le_iff_lt_iff_lt.2 $ succ_lt_of_is_limit h

theorem limit_le {o} (h : is_limit o) {a} : o ≤ a ↔ ∀, ∀ x < o, ∀, x ≤ a :=
  ⟨fun h x l => le_transₓ (le_of_ltₓ l) h, fun H =>
    (le_succ_of_is_limit h).1 $ le_of_not_ltₓ $ fun hn => not_lt_of_le (H _ hn) (lt_succ_self _)⟩

theorem lt_limit {o} (h : is_limit o) {a} : a < o ↔ ∃ x < o, a < x := by
  simpa only [not_ball, not_leₓ] using not_congr (@limit_le _ h a)

@[simp]
theorem lift_is_limit o : is_limit (lift o) ↔ is_limit o :=
  and_congr
    (not_congr $ by
      simpa only [lift_zero] using @lift_inj o 0)
    ⟨fun H a h =>
      lift_lt.1 $ by
        simpa only [lift_succ] using H _ (lift_lt.2 h),
      fun H a h =>
      let ⟨a', e⟩ := lift_down (le_of_ltₓ h)
      by
      rw [← e, ← lift_succ, lift_lt] <;> rw [← e, lift_lt] at h <;> exact H a' h⟩

theorem is_limit.pos {o : Ordinal} (h : is_limit o) : 0 < o :=
  lt_of_le_of_neₓ (Ordinal.zero_le _) h.1.symm

theorem is_limit.one_lt {o : Ordinal} (h : is_limit o) : 1 < o := by
  simpa only [succ_zero] using h.2 _ h.pos

theorem is_limit.nat_lt {o : Ordinal} (h : is_limit o) : ∀ n : ℕ, (n : Ordinal) < o
  | 0 => h.pos
  | n+1 => h.2 _ (is_limit.nat_lt n)

theorem zero_or_succ_or_limit (o : Ordinal) : o = 0 ∨ (∃ a, o = succ a) ∨ is_limit o :=
  if o0 : o = 0 then Or.inl o0
  else if h : ∃ a, o = succ a then Or.inr (Or.inl h) else Or.inr $ Or.inr ⟨o0, fun a => (succ_lt_of_not_succ h).2⟩

/--  Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
@[elab_as_eliminator]
def limit_rec_on {C : Ordinal → Sort _} (o : Ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
    (H₃ : ∀ o, is_limit o → (∀, ∀ o' < o, ∀, C o') → C o) : C o :=
  wf.fix
    (fun o IH =>
      if o0 : o = 0 then by
        rw [o0] <;> exact H₁
      else
        if h : ∃ a, o = succ a then by
          rw [← succ_pred_iff_is_succ.2 h] <;> exact H₂ _ (IH _ $ pred_lt_iff_is_succ.2 h)
        else H₃ _ ⟨o0, fun a => (succ_lt_of_not_succ h).2⟩ IH)
    o

@[simp]
theorem limit_rec_on_zero {C} H₁ H₂ H₃ : @limit_rec_on C 0 H₁ H₂ H₃ = H₁ := by
  rw [limit_rec_on, WellFounded.fix_eq, dif_pos rfl] <;> rfl

@[simp]
theorem limit_rec_on_succ {C} o H₁ H₂ H₃ : @limit_rec_on C (succ o) H₁ H₂ H₃ = H₂ o (@limit_rec_on C o H₁ H₂ H₃) := by
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
theorem limit_rec_on_limit {C} o H₁ H₂ H₃ h :
    @limit_rec_on C o H₁ H₂ H₃ = H₃ o h fun x h => @limit_rec_on C x H₁ H₂ H₃ := by
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


/--  A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.  -/
def is_normal (f : Ordinal → Ordinal) : Prop :=
  (∀ o, f o < f (succ o)) ∧ ∀ o, is_limit o → ∀ a, f o ≤ a ↔ ∀, ∀ b < o, ∀, f b ≤ a

theorem is_normal.limit_le {f} (H : is_normal f) : ∀ {o}, is_limit o → ∀ {a}, f o ≤ a ↔ ∀, ∀ b < o, ∀, f b ≤ a :=
  H.2

theorem is_normal.limit_lt {f} (H : is_normal f) {o} (h : is_limit o) {a} : a < f o ↔ ∃ b < o, a < f b :=
  not_iff_not.1 $ by
    simpa only [exists_prop, not_exists, not_and, not_ltₓ] using H.2 _ h a

theorem is_normal.strict_mono {f} (H : is_normal f) : StrictMono f := fun a b =>
  limit_rec_on b (Not.elim (not_lt_of_le $ Ordinal.zero_le _))
    (fun b IH h => (lt_or_eq_of_leₓ (lt_succ.1 h)).elim (fun h => lt_transₓ (IH h) (H.1 _)) fun e => e ▸ H.1 _)
    fun b l IH h => lt_of_lt_of_leₓ (H.1 a) ((H.2 _ l _).1 (le_reflₓ _) _ (l.2 _ h))

theorem is_normal.lt_iff {f} (H : is_normal f) {a b} : f a < f b ↔ a < b :=
  StrictMono.lt_iff_lt $ H.strict_mono

theorem is_normal.le_iff {f} (H : is_normal f) {a b} : f a ≤ f b ↔ a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.lt_iff

theorem is_normal.inj {f} (H : is_normal f) {a b} : f a = f b ↔ a = b := by
  simp only [le_antisymm_iffₓ, H.le_iff]

theorem is_normal.le_self {f} (H : is_normal f) a : a ≤ f a :=
  well_founded.self_le_of_strict_mono wf H.strict_mono a

theorem is_normal.le_set {f} (H : is_normal f) (p : Ordinal → Prop) (p0 : ∃ x, p x) S
    (H₂ : ∀ o, S ≤ o ↔ ∀ a, p a → a ≤ o) {o} : f S ≤ o ↔ ∀ a, p a → f a ≤ o :=
  ⟨fun h a pa => le_transₓ (H.le_iff.2 ((H₂ _).1 (le_reflₓ _) _ pa)) h, fun h => by
    revert H₂
    apply limit_rec_on S
    ·
      intro H₂
      cases' p0 with x px
      have := Ordinal.le_zero.1 ((H₂ _).1 (Ordinal.zero_le _) _ px)
      rw [this] at px
      exact h _ px
    ·
      intro S _ H₂
      rcases not_ball.1 (mt (H₂ S).2 $ not_le_of_lt $ lt_succ_self _) with ⟨a, h₁, h₂⟩
      exact le_transₓ (H.le_iff.2 $ succ_le.2 $ not_leₓ.1 h₂) (h _ h₁)
    ·
      intro S L _ H₂
      apply (H.2 _ L _).2
      intro a h'
      rcases not_ball.1 (mt (H₂ a).2 (not_leₓ.2 h')) with ⟨b, h₁, h₂⟩
      exact le_transₓ (H.le_iff.2 $ le_of_ltₓ $ not_leₓ.1 h₂) (h _ h₁)⟩

theorem is_normal.le_set' {f} (H : is_normal f) (p : α → Prop) (g : α → Ordinal) (p0 : ∃ x, p x) S
    (H₂ : ∀ o, S ≤ o ↔ ∀ a, p a → g a ≤ o) {o} : f S ≤ o ↔ ∀ a, p a → f (g a) ≤ o :=
  (H.le_set (fun x => ∃ y, p y ∧ x = g y)
        (let ⟨x, px⟩ := p0
        ⟨_, _, px, rfl⟩)
        _ fun o => (H₂ o).trans ⟨fun H a ⟨y, h1, h2⟩ => h2.symm ▸ H y h1, fun H a h1 => H (g a) ⟨a, h1, rfl⟩⟩).trans
    ⟨fun H a h => H (g a) ⟨a, h, rfl⟩, fun H a ⟨y, h1, h2⟩ => h2.symm ▸ H y h1⟩

theorem is_normal.refl : is_normal id :=
  ⟨fun x => lt_succ_self _, fun o l a => limit_le l⟩

theorem is_normal.trans {f g} (H₁ : is_normal f) (H₂ : is_normal g) : is_normal fun x => f (g x) :=
  ⟨fun x => H₁.lt_iff.2 (H₂.1 _), fun o l a => H₁.le_set' (· < o) g ⟨_, l.pos⟩ _ fun c => H₂.2 _ l _⟩

theorem is_normal.is_limit {f} (H : is_normal f) {o} (l : is_limit o) : is_limit (f o) :=
  ⟨ne_of_gtₓ $ lt_of_le_of_ltₓ (Ordinal.zero_le _) $ H.lt_iff.2 l.pos, fun a h =>
    let ⟨b, h₁, h₂⟩ := (H.limit_lt l).1 h
    lt_of_le_of_ltₓ (succ_le.2 h₂) (H.lt_iff.2 h₁)⟩

theorem add_le_of_limit {a b c : Ordinal.{u}} (h : is_limit b) : (a+b) ≤ c ↔ ∀, ∀ b' < b, ∀, (a+b') ≤ c :=
  ⟨fun h b' l => le_transₓ (add_le_add_left (le_of_ltₓ l) _) h, fun H =>
    le_of_not_ltₓ $
      induction_on a
        (fun α r _ =>
          induction_on b $ fun β s _ h H l => by
            skip
            suffices ∀ x : β, Sum.Lex r s (Sum.inr x) (enum _ _ l)by
              cases' enum _ _ l with x x
              ·
                cases this (enum s 0 h.pos)
              ·
                exact irrefl _ (this _)
            intro x
            rw [← typein_lt_typein (Sum.Lex r s), typein_enum]
            have := H _ (h.2 _ (typein_lt_type s x))
            rw [add_succ, succ_le] at this
            refine' lt_of_le_of_ltₓ (type_le'.2 ⟨RelEmbedding.ofMonotone (fun a => _) fun a b => _⟩) this
            ·
              rcases a with ⟨a | b, h⟩
              ·
                exact Sum.inl a
              ·
                exact
                  Sum.inr
                    ⟨b, by
                      cases h <;> assumption⟩
            ·
              rcases a with ⟨a | a, h₁⟩ <;>
                rcases b with ⟨b | b, h₂⟩ <;> cases h₁ <;> cases h₂ <;> rintro ⟨⟩ <;> constructor <;> assumption)
        h H⟩

theorem add_is_normal (a : Ordinal) : is_normal ((·+·) a) :=
  ⟨fun b => (add_lt_add_iff_left a).2 (lt_succ_self _), fun b l c => add_le_of_limit l⟩

theorem add_is_limit a {b} : is_limit b → is_limit (a+b) :=
  (add_is_normal a).IsLimit

/-! ### Subtraction on ordinals-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " `a - b` is the unique ordinal satisfying\n  `b + (a - b) = a` when `b ≤ a`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `sub [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`a `b] [":" (Term.explicitUniv `Ordinal ".{" [`u] "}")] [] ")")]
   [(Term.typeSpec ":" (Term.explicitUniv `Ordinal ".{" [`u] "}"))])
  (Command.declValSimple
   ":="
   (Term.app
    `omin
    [(Set.«term{_|_}» "{" `o "|" («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" `o)) "}")
     (Term.anonymousCtor "⟨" [`a "," (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])] "⟩")])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin
   [(Set.«term{_|_}» "{" `o "|" («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" `o)) "}")
    (Term.anonymousCtor "⟨" [`a "," (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`a "," (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_add_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}» "{" `o "|" («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" `o)) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" `o))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `b "+" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    `a - b` is the unique ordinal satisfying
      `b + (a - b) = a` when `b ≤ a`. -/
  def sub ( a b : Ordinal .{ u } ) : Ordinal .{ u } := omin { o | a ≤ b + o } ⟨ a , le_add_left _ _ ⟩

instance : Sub Ordinal :=
  ⟨sub⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `le_add_sub [])
  (Command.declSig
   [(Term.explicitBinder "(" [`a `b] [":" `Ordinal] [] ")")]
   (Term.typeSpec ":" («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" («term_-_» `a "-" `b)))))
  (Command.declValSimple
   ":="
   (Term.app
    `omin_mem
    [(Set.«term{_|_}» "{" `o "|" («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" `o)) "}") (Term.hole "_")])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin_mem
   [(Set.«term{_|_}» "{" `o "|" («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" `o)) "}") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}» "{" `o "|" («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" `o)) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» `a "≤" (Init.Logic.«term_+_» `b "+" `o))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `b "+" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem le_add_sub ( a b : Ordinal ) : a ≤ b + a - b := omin_mem { o | a ≤ b + o } _

theorem sub_le {a b c : Ordinal} : a - b ≤ c ↔ a ≤ b+c :=
  ⟨fun h => le_transₓ (le_add_sub a b) (add_le_add_left h _), fun h => omin_le h⟩

theorem lt_sub {a b c : Ordinal} : a < b - c ↔ (c+a) < b :=
  lt_iff_lt_of_le_iff_le sub_le

theorem add_sub_cancel (a b : Ordinal) : (a+b) - a = b :=
  le_antisymmₓ (sub_le.2 $ le_reflₓ _) ((add_le_add_iff_left a).1 $ le_add_sub _ _)

theorem sub_eq_of_add_eq {a b c : Ordinal} (h : (a+b) = c) : c - a = b :=
  h ▸ add_sub_cancel _ _

theorem sub_le_self (a b : Ordinal) : a - b ≤ a :=
  sub_le.2 $ le_add_left _ _

protected theorem add_sub_cancel_of_le {a b : Ordinal} (h : b ≤ a) : (b+a - b) = a :=
  le_antisymmₓ
    (by
      rcases zero_or_succ_or_limit (a - b) with (e | ⟨c, e⟩ | l)
      ·
        simp only [e, add_zeroₓ, h]
      ·
        rw [e, add_succ, succ_le, ← lt_sub, e]
        apply lt_succ_self
      ·
        exact (add_le_of_limit l).2 fun c l => le_of_ltₓ (lt_sub.1 l))
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

theorem sub_sub (a b c : Ordinal) : a - b - c = a - b+c :=
  eq_of_forall_ge_iff $ fun d => by
    rw [sub_le, sub_le, sub_le, add_assocₓ]

theorem add_sub_add_cancel (a b c : Ordinal) : ((a+b) - a+c) = b - c := by
  rw [← sub_sub, add_sub_cancel]

theorem sub_is_limit {a b} (l : is_limit a) (h : b < a) : is_limit (a - b) :=
  ⟨ne_of_gtₓ $
      lt_sub.2 $ by
        rwa [add_zeroₓ],
    fun c h => by
    rw [lt_sub, add_succ] <;> exact l.2 _ (lt_sub.1 h)⟩

@[simp]
theorem one_add_omega : (1+omega.{u}) = omega := by
  refine' le_antisymmₓ _ (le_add_left _ _)
  rw [omega, one_eq_lift_type_unit, ← lift_add, lift_le, type_add]
  have : IsWellOrder Unit EmptyRelation := by
    infer_instance
  refine' ⟨RelEmbedding.collapse (RelEmbedding.ofMonotone _ _)⟩
  ·
    apply Sum.rec
    exact fun _ => 0
    exact Nat.succ
  ·
    intro a b
    cases a <;>
      cases b <;> intro H <;> cases' H with _ _ H _ _ H <;> [cases H, exact Nat.succ_posₓ _, exact Nat.succ_lt_succₓ H]

@[simp]
theorem one_add_of_omega_le {o} (h : omega ≤ o) : (1+o) = o := by
  rw [← Ordinal.add_sub_cancel_of_le h, ← add_assocₓ, one_add_omega]

/-! ### Multiplication of ordinals-/


-- failed to format: format: uncaught backtrack exception
/--
    The multiplication of ordinals `o₁` and `o₂` is the (well founded) lexicographic order on
    `o₂ × o₁`. -/
  instance
    : Monoidₓ Ordinal .{ u }
    where
      mul
          a b
          :=
          Quotientₓ.liftOn₂
              a
                b
                (
                  fun ⟨ α , r , wo ⟩ ⟨ β , s , wo' ⟩ => ⟦ ⟨ β × α , Prod.Lex s r , by exact Prod.Lex.is_well_order ⟩ ⟧
                    : WellOrder → WellOrder → Ordinal
                  )
            $
            fun
              ⟨ α₁ , r₁ , o₁ ⟩ ⟨ α₂ , r₂ , o₂ ⟩ ⟨ β₁ , s₁ , p₁ ⟩ ⟨ β₂ , s₂ , p₂ ⟩ ⟨ f ⟩ ⟨ g ⟩
                =>
                Quot.sound ⟨ RelIso.prodLexCongr g f ⟩
        one := 1
        mul_assoc
          a b c
          :=
          Quotientₓ.induction_on₃ a b c
            $
            fun
              ⟨ α , r , _ ⟩ ⟨ β , s , _ ⟩ ⟨ γ , t , _ ⟩
                =>
                Eq.symm
                  $
                  Quotientₓ.sound
                    ⟨
                      ⟨
                        prod_assoc _ _ _
                          ,
                          fun
                            a b
                              =>
                              by
                                rcases a with ⟨ ⟨ a₁ , a₂ ⟩ , a₃ ⟩
                                  rcases b with ⟨ ⟨ b₁ , b₂ ⟩ , b₃ ⟩
                                  simp [ Prod.lex_def , and_or_distrib_left , or_assoc , and_assoc ]
                        ⟩
                      ⟩
        mul_one
          a
          :=
          induction_on a
            $
            fun
              α r _
                =>
                Quotientₓ.sound
                  ⟨
                    ⟨
                      punit_prod _
                        ,
                        fun
                          a b
                            =>
                            by
                              rcases a with ⟨ ⟨ ⟨ ⟩ ⟩ , a ⟩
                                <;>
                                rcases b with ⟨ ⟨ ⟨ ⟩ ⟩ , b ⟩
                                  <;>
                                  simp only [ Prod.lex_def , EmptyRelation , false_orₓ ]
                                    <;>
                                    simp only [ eq_self_iff_true , true_andₓ ] <;> rfl
                      ⟩
                    ⟩
        one_mul
          a
          :=
          induction_on a
            $
            fun
              α r _
                =>
                Quotientₓ.sound
                  ⟨
                    ⟨
                      prod_punit _
                        ,
                        fun
                          a b
                            =>
                            by
                              rcases a with ⟨ a , ⟨ ⟨ ⟩ ⟩ ⟩
                                <;>
                                rcases b with ⟨ b , ⟨ ⟨ ⟩ ⟩ ⟩
                                  <;>
                                  simp only [ Prod.lex_def , EmptyRelation , and_falseₓ , or_falseₓ ] <;> rfl
                      ⟩
                    ⟩

@[simp]
theorem type_mul {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s] :
    (type r*type s) = type (Prod.Lex s r) :=
  rfl

@[simp]
theorem lift_mul a b : lift (a*b) = lift a*lift b :=
  Quotientₓ.induction_on₂ a b $ fun ⟨α, r, _⟩ ⟨β, s, _⟩ =>
    Quotientₓ.sound
      ⟨(RelIso.preimage Equivₓ.ulift _).trans
          (RelIso.prodLexCongr (RelIso.preimage Equivₓ.ulift _) (RelIso.preimage Equivₓ.ulift _)).symm⟩

@[simp]
theorem card_mul a b : card (a*b) = card a*card b :=
  Quotientₓ.induction_on₂ a b $ fun ⟨α, r, _⟩ ⟨β, s, _⟩ => mul_commₓ (mk β) (mk α)

@[simp]
theorem mul_zero (a : Ordinal) : (a*0) = 0 :=
  induction_on a $ fun α _ _ => by
    exact type_eq_zero_of_empty

@[simp]
theorem zero_mul (a : Ordinal) : (0*a) = 0 :=
  induction_on a $ fun α _ _ => by
    exact type_eq_zero_of_empty

theorem mul_addₓ (a b c : Ordinal) : (a*b+c) = (a*b)+a*c :=
  Quotientₓ.induction_on₃ a b c $ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
    Quotientₓ.sound
      ⟨⟨sum_prod_distrib _ _ _, by
          rintro ⟨a₁ | a₁, a₂⟩ ⟨b₁ | b₁, b₂⟩ <;>
            simp only [Prod.lex_def, Sum.lex_inl_inl, Sum.Lex.sep, Sum.lex_inr_inl, Sum.lex_inr_inr,
                sum_prod_distrib_apply_left, sum_prod_distrib_apply_right] <;>
              simp only [Sum.inl.inj_iff, true_orₓ, false_andₓ, false_orₓ]⟩⟩

@[simp]
theorem mul_add_one (a b : Ordinal) : (a*b+1) = (a*b)+a := by
  simp only [mul_addₓ, mul_oneₓ]

@[simp]
theorem mul_succ (a b : Ordinal) : (a*succ b) = (a*b)+a :=
  mul_add_one _ _

theorem mul_le_mul_left {a b} (c : Ordinal) : a ≤ b → (c*a) ≤ c*b :=
  Quotientₓ.induction_on₃ a b c $ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
    skip
    refine' type_le'.2 ⟨RelEmbedding.ofMonotone (fun a => (f a.1, a.2)) fun a b h => _⟩
    clear_
    cases' h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h'
    ·
      exact Prod.Lex.left _ _ (f.to_rel_embedding.map_rel_iff.2 h')
    ·
      exact Prod.Lex.right _ h'

theorem mul_le_mul_right {a b} (c : Ordinal) : a ≤ b → (a*c) ≤ b*c :=
  Quotientₓ.induction_on₃ a b c $ fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ => by
    skip
    refine' type_le'.2 ⟨RelEmbedding.ofMonotone (fun a => (a.1, f a.2)) fun a b h => _⟩
    cases' h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h'
    ·
      exact Prod.Lex.left _ _ h'
    ·
      exact Prod.Lex.right _ (f.to_rel_embedding.map_rel_iff.2 h')

theorem mul_le_mul {a b c d : Ordinal} (h₁ : a ≤ c) (h₂ : b ≤ d) : (a*b) ≤ c*d :=
  le_transₓ (mul_le_mul_left _ h₂) (mul_le_mul_right _ h₁)

private theorem mul_le_of_limit_aux {α β r s} [IsWellOrder α r] [IsWellOrder β s] {c} (h : is_limit (type s))
    (H : ∀, ∀ b' < type s, ∀, (type r*b') ≤ c) (l : c < type r*type s) : False := by
  suffices ∀ a b, Prod.Lex s r (b, a) (enum _ _ l)by
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
  ·
    rcases a with ⟨⟨b', a'⟩, h⟩
    by_cases' e : b = b'
    ·
      refine' Sum.inr ⟨a', _⟩
      subst e
      cases' h with _ _ _ _ h _ _ _ h
      ·
        exact (irrefl _ h).elim
      ·
        exact h
    ·
      refine' Sum.inl (⟨b', _⟩, a')
      cases' h with _ _ _ _ h _ _ _ h
      ·
        exact h
      ·
        exact (e rfl).elim
  ·
    rcases a with ⟨⟨b₁, a₁⟩, h₁⟩
    rcases b with ⟨⟨b₂, a₂⟩, h₂⟩
    intro h
    by_cases' e₁ : b = b₁ <;> by_cases' e₂ : b = b₂
    ·
      substs b₁ b₂
      simpa only [subrel_val, Prod.lex_def, @irrefl _ s _ b, true_andₓ, false_orₓ, eq_self_iff_true, dif_pos,
        Sum.lex_inr_inr] using h
    ·
      subst b₁
      simp only [subrel_val, Prod.lex_def, e₂, Prod.lex_def, dif_pos, subrel_val, eq_self_iff_true, or_falseₓ, dif_neg,
        not_false_iff, Sum.lex_inr_inl, false_andₓ] at h⊢
      cases h₂ <;> [exact asymm h h₂_h, exact e₂ rfl]
    ·
      simp only [e₂, dif_pos, eq_self_iff_true, dif_neg e₁, not_false_iff, Sum.Lex.sep]
    ·
      simpa only [dif_neg e₁, dif_neg e₂, Prod.lex_def, subrel_val, Subtype.mk_eq_mk, Sum.lex_inl_inl] using h

theorem mul_le_of_limit {a b c : Ordinal.{u}} (h : is_limit b) : (a*b) ≤ c ↔ ∀, ∀ b' < b, ∀, (a*b') ≤ c :=
  ⟨fun h b' l => le_transₓ (mul_le_mul_left _ (le_of_ltₓ l)) h, fun H =>
    le_of_not_ltₓ $
      induction_on a
        (fun α r _ =>
          induction_on b $ fun β s _ => by
            exact mul_le_of_limit_aux)
        h H⟩

theorem mul_is_normal {a : Ordinal} (h : 0 < a) : is_normal ((·*·) a) :=
  ⟨fun b => by
    rw [mul_succ] <;> simpa only [add_zeroₓ] using (add_lt_add_iff_left (a*b)).2 h, fun b l c => mul_le_of_limit l⟩

theorem lt_mul_of_limit {a b c : Ordinal.{u}} (h : is_limit c) : (a < b*c) ↔ ∃ c' < c, a < b*c' := by
  simpa only [not_ball, not_leₓ] using not_congr (@mul_le_of_limit b c a h)

theorem mul_lt_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : ((a*b) < a*c) ↔ b < c :=
  (mul_is_normal a0).lt_iff

theorem mul_le_mul_iff_left {a b c : Ordinal} (a0 : 0 < a) : ((a*b) ≤ a*c) ↔ b ≤ c :=
  (mul_is_normal a0).le_iff

theorem mul_lt_mul_of_pos_left {a b c : Ordinal} (h : a < b) (c0 : 0 < c) : (c*a) < c*b :=
  (mul_lt_mul_iff_left c0).2 h

theorem mul_pos {a b : Ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a*b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left h₂ h₁

theorem mul_ne_zero {a b : Ordinal} : a ≠ 0 → b ≠ 0 → (a*b) ≠ 0 := by
  simpa only [Ordinal.pos_iff_ne_zero] using mul_pos

theorem le_of_mul_le_mul_left {a b c : Ordinal} (h : (c*a) ≤ c*b) (h0 : 0 < c) : a ≤ b :=
  le_imp_le_of_lt_imp_ltₓ (fun h' => mul_lt_mul_of_pos_left h' h0) h

theorem mul_right_injₓ {a b c : Ordinal} (a0 : 0 < a) : ((a*b) = a*c) ↔ b = c :=
  (mul_is_normal a0).inj

theorem mul_is_limit {a b : Ordinal} (a0 : 0 < a) : is_limit b → is_limit (a*b) :=
  (mul_is_normal a0).IsLimit

theorem mul_is_limit_left {a b : Ordinal} (l : is_limit a) (b0 : 0 < b) : is_limit (a*b) := by
  rcases zero_or_succ_or_limit b with (rfl | ⟨b, rfl⟩ | lb)
  ·
    exact (lt_irreflₓ _).elim b0
  ·
    rw [mul_succ]
    exact add_is_limit _ l
  ·
    exact mul_is_limit l.pos lb

/-! ### Division on ordinals -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `div_aux [])
  (Command.declSig
   [(Term.explicitBinder "(" [`a `b] [":" (Term.explicitUniv `Ordinal ".{" [`u] "}")] [] ")")
    (Term.explicitBinder "(" [`h] [":" («term_≠_» `b "≠" (numLit "0"))] [] ")")]
   (Term.typeSpec
    ":"
    (Term.app
     `Set.Nonempty
     [(Set.«term{_|_}»
       "{"
       `o
       "|"
       («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
       "}")])))
  (Command.declValSimple
   ":="
   (Term.anonymousCtor
    "⟨"
    [`a
     ","
     («term_$__»
      (Term.proj `succ_le "." (fieldIdx "1"))
      "$"
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.simpa
            "simpa"
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `succ_zero) "," (Tactic.simpLemma [] [] `one_mulₓ)] "]"]
            []
            ["using"
             (Term.app
              `mul_le_mul_right
              [(Term.app `succ [`a])
               (Term.app
                (Term.proj `succ_le "." (fieldIdx "2"))
                [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h])])])])
           [])]))))]
    "⟩")
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`a
    ","
    («term_$__»
     (Term.proj `succ_le "." (fieldIdx "1"))
     "$"
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simpa
           "simpa"
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `succ_zero) "," (Tactic.simpLemma [] [] `one_mulₓ)] "]"]
           []
           ["using"
            (Term.app
             `mul_le_mul_right
             [(Term.app `succ [`a])
              (Term.app
               (Term.proj `succ_le "." (fieldIdx "2"))
               [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h])])])])
          [])]))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.proj `succ_le "." (fieldIdx "1"))
   "$"
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simpa
         "simpa"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `succ_zero) "," (Tactic.simpLemma [] [] `one_mulₓ)] "]"]
         []
         ["using"
          (Term.app
           `mul_le_mul_right
           [(Term.app `succ [`a])
            (Term.app
             (Term.proj `succ_le "." (fieldIdx "2"))
             [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h])])])])
        [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `succ_zero) "," (Tactic.simpLemma [] [] `one_mulₓ)] "]"]
        []
        ["using"
         (Term.app
          `mul_le_mul_right
          [(Term.app `succ [`a])
           (Term.app
            (Term.proj `succ_le "." (fieldIdx "2"))
            [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h])])])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `succ_zero) "," (Tactic.simpLemma [] [] `one_mulₓ)] "]"]
   []
   ["using"
    (Term.app
     `mul_le_mul_right
     [(Term.app `succ [`a])
      (Term.app
       (Term.proj `succ_le "." (fieldIdx "2"))
       [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h])])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `mul_le_mul_right
   [(Term.app `succ [`a])
    (Term.app
     (Term.proj `succ_le "." (fieldIdx "2"))
     [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `succ_le "." (fieldIdx "2"))
   [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Ordinal.pos_iff_ne_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `succ_le "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `succ_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj `succ_le "." (fieldIdx "2"))
   [(Term.paren "(" [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`h]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `succ [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `succ [`a]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_le_mul_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_mulₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `succ_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj `succ_le "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `succ_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.app
   `Set.Nonempty
   [(Set.«term{_|_}»
     "{"
     `o
     "|"
     («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
     "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `succ [`o])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    div_aux
    ( a b : Ordinal .{ u } ) ( h : b ≠ 0 ) : Set.Nonempty { o | a < b * succ o }
    :=
      ⟨
        a
          ,
          succ_le . 1
            $
            by
              simpa
                only
                [ succ_zero , one_mulₓ ]
                using mul_le_mul_right succ a succ_le . 2 Ordinal.pos_iff_ne_zero . 2 h
        ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " `a / b` is the unique ordinal `o` satisfying\n  `a = b * o + o'` with `o' < b`. -/")]
  []
  [(Command.protected "protected")]
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `div [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`a `b] [":" (Term.explicitUniv `Ordinal ".{" [`u] "}")] [] ")")]
   [(Term.typeSpec ":" (Term.explicitUniv `Ordinal ".{" [`u] "}"))])
  (Command.declValSimple
   ":="
   (termDepIfThenElse
    "if"
    `h
    ":"
    («term_=_» `b "=" (numLit "0"))
    "then"
    (numLit "0")
    "else"
    (Term.app
     `omin
     [(Set.«term{_|_}»
       "{"
       `o
       "|"
       («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
       "}")
      (Term.app `Ordinal.div_aux [`a `b `h])]))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termDepIfThenElse
   "if"
   `h
   ":"
   («term_=_» `b "=" (numLit "0"))
   "then"
   (numLit "0")
   "else"
   (Term.app
    `omin
    [(Set.«term{_|_}»
      "{"
      `o
      "|"
      («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
      "}")
     (Term.app `Ordinal.div_aux [`a `b `h])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termDepIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin
   [(Set.«term{_|_}» "{" `o "|" («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))) "}")
    (Term.app `Ordinal.div_aux [`a `b `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Ordinal.div_aux [`a `b `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ordinal.div_aux
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Ordinal.div_aux [`a `b `h]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `succ [`o])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `a / b` is the unique ordinal `o` satisfying
        `a = b * o + o'` with `o' < b`. -/
    protected
  def
    div
    ( a b : Ordinal .{ u } ) : Ordinal .{ u }
    := if h : b = 0 then 0 else omin { o | a < b * succ o } Ordinal.div_aux a b h

instance : Div Ordinal :=
  ⟨Ordinal.div⟩

@[simp]
theorem div_zero (a : Ordinal) : a / 0 = 0 :=
  dif_pos rfl

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `div_def [])
  (Command.declSig
   [(Term.simpleBinder [`a] [])
    (Term.implicitBinder "{" [`b] [":" `Ordinal] "}")
    (Term.explicitBinder "(" [`h] [":" («term_≠_» `b "≠" (numLit "0"))] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     («term_/_» `a "/" `b)
     "="
     (Term.app
      `omin
      [(Set.«term{_|_}»
        "{"
        `o
        "|"
        («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
        "}")
       (Term.app `Ordinal.div_aux [`a `b `h])]))))
  (Command.declValSimple ":=" (Term.app `dif_neg [`h]) [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dif_neg [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dif_neg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   («term_/_» `a "/" `b)
   "="
   (Term.app
    `omin
    [(Set.«term{_|_}»
      "{"
      `o
      "|"
      («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
      "}")
     (Term.app `Ordinal.div_aux [`a `b `h])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin
   [(Set.«term{_|_}» "{" `o "|" («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))) "}")
    (Term.app `Ordinal.div_aux [`a `b `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Ordinal.div_aux [`a `b `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ordinal.div_aux
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Ordinal.div_aux [`a `b `h]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `succ [`o])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem div_def a { b : Ordinal } ( h : b ≠ 0 ) : a / b = omin { o | a < b * succ o } Ordinal.div_aux a b h := dif_neg h

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `lt_mul_succ_div [])
  (Command.declSig
   [(Term.simpleBinder [`a] [])
    (Term.implicitBinder "{" [`b] [":" `Ordinal] "}")
    (Term.explicitBinder "(" [`h] [":" («term_≠_» `b "≠" (numLit "0"))] [] ")")]
   (Term.typeSpec
    ":"
    («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [(«term_/_» `a "/" `b)])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.«tactic_<;>_»
         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `div_def [`a `h]))] "]") [])
         "<;>"
         (Tactic.exact
          "exact"
          (Term.app
           `omin_mem
           [(Set.«term{_|_}»
             "{"
             `o
             "|"
             («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
             "}")
            (Term.hole "_")])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `div_def [`a `h]))] "]") [])
        "<;>"
        (Tactic.exact
         "exact"
         (Term.app
          `omin_mem
          [(Set.«term{_|_}»
            "{"
            `o
            "|"
            («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
            "}")
           (Term.hole "_")])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `div_def [`a `h]))] "]") [])
   "<;>"
   (Tactic.exact
    "exact"
    (Term.app
     `omin_mem
     [(Set.«term{_|_}»
       "{"
       `o
       "|"
       («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
       "}")
      (Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `omin_mem
    [(Set.«term{_|_}»
      "{"
      `o
      "|"
      («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
      "}")
     (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin_mem
   [(Set.«term{_|_}» "{" `o "|" («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))) "}")
    (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `a "<" (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `b "*" (Term.app `succ [`o]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `succ [`o])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_mul_succ_div
  a { b : Ordinal } ( h : b ≠ 0 ) : a < b * succ a / b
  := by rw [ div_def a h ] <;> exact omin_mem { o | a < b * succ o } _

theorem lt_mul_div_add a {b : Ordinal} (h : b ≠ 0) : a < (b*a / b)+b := by
  simpa only [mul_succ] using lt_mul_succ_div a h

theorem div_le {a b c : Ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b*succ c :=
  ⟨fun h => lt_of_lt_of_leₓ (lt_mul_succ_div a b0) (mul_le_mul_left _ $ succ_le_succ.2 h), fun h => by
    rw [div_def a b0] <;> exact omin_le h⟩

theorem lt_div {a b c : Ordinal} (c0 : c ≠ 0) : a < b / c ↔ (c*succ a) ≤ b := by
  rw [← not_leₓ, div_le c0, not_ltₓ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `le_div [])
  (Command.declSig
   [(Term.implicitBinder "{" [`a `b `c] [":" `Ordinal] "}")
    (Term.explicitBinder "(" [`c0] [":" («term_≠_» `c "≠" (numLit "0"))] [] ")")]
   (Term.typeSpec
    ":"
    («term_↔_»
     («term_≤_» `a "≤" («term_/_» `b "/" `c))
     "↔"
     («term_≤_» (Finset.Data.Finset.Fold.«term_*_» `c "*" `a) "≤" `b))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" (Term.app `limit_rec_on [`a])) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `mul_zero) "," (Tactic.simpLemma [] [] `Ordinal.zero_le)] "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intros "intros" []) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `succ_le) "," (Tactic.rwRule [] (Term.app `lt_div [`c0]))] "]")
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              ["("
               "config"
               ":="
               (Term.structInst
                "{"
                []
                [(group
                  (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                  [])]
                (Term.optEllipsis [])
                []
                "}")
               ")"]
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `mul_le_of_limit)
                ","
                (Tactic.simpLemma [] [] `limit_le)
                ","
                (Tactic.simpLemma [] [] `iff_selfₓ)
                ","
                (Tactic.simpLemma [] [] `forall_true_iff)]
               "]"]
              [])
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" (Term.app `limit_rec_on [`a])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `mul_zero) "," (Tactic.simpLemma [] [] `Ordinal.zero_le)] "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intros "intros" []) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `succ_le) "," (Tactic.rwRule [] (Term.app `lt_div [`c0]))] "]")
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             ["("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                 [])]
               (Term.optEllipsis [])
               []
               "}")
              ")"]
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `mul_le_of_limit)
               ","
               (Tactic.simpLemma [] [] `limit_le)
               ","
               (Tactic.simpLemma [] [] `iff_selfₓ)
               ","
               (Tactic.simpLemma [] [] `forall_true_iff)]
              "]"]
             [])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        ["("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
          (Term.optEllipsis [])
          []
          "}")
         ")"]
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `mul_le_of_limit)
          ","
          (Tactic.simpLemma [] [] `limit_le)
          ","
          (Tactic.simpLemma [] [] `iff_selfₓ)
          ","
          (Tactic.simpLemma [] [] `forall_true_iff)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `mul_le_of_limit)
     ","
     (Tactic.simpLemma [] [] `limit_le)
     ","
     (Tactic.simpLemma [] [] `iff_selfₓ)
     ","
     (Tactic.simpLemma [] [] `forall_true_iff)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `forall_true_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `iff_selfₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `limit_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_le_of_limit
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  le_div
  { a b c : Ordinal } ( c0 : c ≠ 0 ) : a ≤ b / c ↔ c * a ≤ b
  :=
    by
      apply limit_rec_on a
        · simp only [ mul_zero , Ordinal.zero_le ]
        · intros rw [ succ_le , lt_div c0 ]
        ·
          simp
            ( config := { contextual := Bool.true._@._internal._hyg.0 } )
            only
            [ mul_le_of_limit , limit_le , iff_selfₓ , forall_true_iff ]

theorem div_lt {a b c : Ordinal} (b0 : b ≠ 0) : a / b < c ↔ a < b*c :=
  lt_iff_lt_of_le_iff_le $ le_div b0

theorem div_le_of_le_mul {a b c : Ordinal} (h : a ≤ b*c) : a / b ≤ c :=
  if b0 : b = 0 then by
    simp only [b0, div_zero, Ordinal.zero_le]
  else (div_le b0).2 $ lt_of_le_of_ltₓ h $ mul_lt_mul_of_pos_left (lt_succ_self _) (Ordinal.pos_iff_ne_zero.2 b0)

theorem mul_lt_of_lt_div {a b c : Ordinal} : a < b / c → (c*a) < b :=
  lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp]
theorem zero_div (a : Ordinal) : 0 / a = 0 :=
  Ordinal.le_zero.1 $ div_le_of_le_mul $ Ordinal.zero_le _

theorem mul_div_le (a b : Ordinal) : (b*a / b) ≤ a :=
  if b0 : b = 0 then by
    simp only [b0, zero_mul, Ordinal.zero_le]
  else (le_div b0).1 (le_reflₓ _)

theorem mul_add_div a {b : Ordinal} (b0 : b ≠ 0) c : ((b*a)+c) / b = a+c / b := by
  apply le_antisymmₓ
  ·
    apply (div_le b0).2
    rw [mul_succ, mul_addₓ, add_assocₓ, add_lt_add_iff_left]
    apply lt_mul_div_add _ b0
  ·
    rw [le_div b0, mul_addₓ, add_le_add_iff_left]
    apply mul_div_le

theorem div_eq_zero_of_lt {a b : Ordinal} (h : a < b) : a / b = 0 := by
  rw [← Ordinal.le_zero, div_le $ Ordinal.pos_iff_ne_zero.1 $ lt_of_le_of_ltₓ (Ordinal.zero_le _) h]
  simpa only [succ_zero, mul_oneₓ] using h

@[simp]
theorem mul_div_cancel a {b : Ordinal} (b0 : b ≠ 0) : (b*a) / b = a := by
  simpa only [add_zeroₓ, zero_div] using mul_add_div a b0 0

@[simp]
theorem div_one (a : Ordinal) : a / 1 = a := by
  simpa only [one_mulₓ] using mul_div_cancel a Ordinal.one_ne_zero

@[simp]
theorem div_self {a : Ordinal} (h : a ≠ 0) : a / a = 1 := by
  simpa only [mul_oneₓ] using mul_div_cancel 1 h

theorem mul_sub (a b c : Ordinal) : (a*b - c) = (a*b) - a*c :=
  if a0 : a = 0 then by
    simp only [a0, zero_mul, sub_self]
  else
    eq_of_forall_ge_iff $ fun d => by
      rw [sub_le, ← le_div a0, sub_le, ← le_div a0, mul_add_div _ a0]

theorem is_limit_add_iff {a b} : is_limit (a+b) ↔ is_limit b ∨ b = 0 ∧ is_limit a := by
  constructor <;> intro h
  ·
    by_cases' h' : b = 0
    ·
      rw [h', add_zeroₓ] at h
      right
      exact ⟨h', h⟩
    left
    rw [← add_sub_cancel a b]
    apply sub_is_limit h
    suffices : (a+0) < a+b
    simpa only [add_zeroₓ]
    rwa [add_lt_add_iff_left, Ordinal.pos_iff_ne_zero]
  rcases h with (h | ⟨rfl, h⟩)
  exact add_is_limit a h
  simpa only [add_zeroₓ]

theorem dvd_add_iff : ∀ {a b c : Ordinal}, a ∣ b → ((a ∣ b+c) ↔ a ∣ c)
  | a, _, c, ⟨b, rfl⟩ =>
    ⟨fun ⟨d, e⟩ =>
      ⟨d - b, by
        rw [mul_sub, ← e, add_sub_cancel]⟩,
      fun ⟨d, e⟩ => by
      rw [e, ← mul_addₓ]
      apply dvd_mul_right⟩

theorem dvd_add {a b c : Ordinal} (h₁ : a ∣ b) : a ∣ c → a ∣ b+c :=
  (dvd_add_iff h₁).2

theorem dvd_zero (a : Ordinal) : a ∣ 0 :=
  ⟨_, (mul_zero _).symm⟩

theorem zero_dvd {a : Ordinal} : 0 ∣ a ↔ a = 0 :=
  ⟨fun ⟨h, e⟩ => by
    simp only [e, zero_mul], fun e => e.symm ▸ dvd_zero _⟩

theorem one_dvd (a : Ordinal) : 1 ∣ a :=
  ⟨a, (one_mulₓ _).symm⟩

theorem div_mul_cancel : ∀ {a b : Ordinal}, a ≠ 0 → a ∣ b → (a*b / a) = b
  | a, _, a0, ⟨b, rfl⟩ => by
    rw [mul_div_cancel _ a0]

theorem le_of_dvd : ∀ {a b : Ordinal}, b ≠ 0 → a ∣ b → a ≤ b
  | a, _, b0, ⟨b, rfl⟩ => by
    simpa only [mul_oneₓ] using
      mul_le_mul_left a
        (one_le_iff_ne_zero.2 fun h : b = 0 => by
          simpa only [h, mul_zero] using b0)

theorem dvd_antisymm {a b : Ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
  if a0 : a = 0 then by
    subst a <;> exact (zero_dvd.1 h₁).symm
  else
    if b0 : b = 0 then by
      subst b <;> exact zero_dvd.1 h₂
    else le_antisymmₓ (le_of_dvd b0 h₁) (le_of_dvd a0 h₂)

/--  `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
instance : Mod Ordinal :=
  ⟨fun a b => a - b*a / b⟩

theorem mod_def (a b : Ordinal) : a % b = a - b*a / b :=
  rfl

@[simp]
theorem mod_zero (a : Ordinal) : a % 0 = a := by
  simp only [mod_def, div_zero, zero_mul, sub_zero]

theorem mod_eq_of_lt {a b : Ordinal} (h : a < b) : a % b = a := by
  simp only [mod_def, div_eq_zero_of_lt h, mul_zero, sub_zero]

@[simp]
theorem zero_mod (b : Ordinal) : 0 % b = 0 := by
  simp only [mod_def, zero_div, mul_zero, sub_self]

theorem div_add_mod (a b : Ordinal) : ((b*a / b)+a % b) = a :=
  Ordinal.add_sub_cancel_of_le $ mul_div_le _ _

theorem mod_lt a {b : Ordinal} (h : b ≠ 0) : a % b < b :=
  (add_lt_add_iff_left (b*a / b)).1 $ by
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

/-! ### Supremum of a family of ordinals -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [(Command.docComment "/--" " The supremum of a family of ordinals -/")] [] [] [] [] [])
 (Command.def
  "def"
  (Command.declId `sup [])
  (Command.optDeclSig
   [(Term.implicitBinder "{" [`ι] [] "}") (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" `Ordinal)] [] ")")]
   [(Term.typeSpec ":" `Ordinal)])
  (Command.declValSimple
   ":="
   (Term.app
    `omin
    [(Set.«term{_|_}»
      "{"
      `c
      "|"
      (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" `c))
      "}")
     (Term.anonymousCtor
      "⟨"
      [(Term.proj (Term.app `sup [(«term_∘_» `Cardinal.succ "∘" («term_∘_» `card "∘" `f))]) "." `ord)
       ","
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`i] [])]
         "=>"
         («term_$__»
          `le_of_ltₓ
          "$"
          (Term.app
           (Term.proj `Cardinal.lt_ord "." (fieldIdx "2"))
           [(Term.app
             `lt_of_lt_of_leₓ
             [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")])
              (Term.app `le_sup [(Term.hole "_") (Term.hole "_")])])]))))]
      "⟩")])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin
   [(Set.«term{_|_}»
     "{"
     `c
     "|"
     (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" `c))
     "}")
    (Term.anonymousCtor
     "⟨"
     [(Term.proj (Term.app `sup [(«term_∘_» `Cardinal.succ "∘" («term_∘_» `card "∘" `f))]) "." `ord)
      ","
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`i] [])]
        "=>"
        («term_$__»
         `le_of_ltₓ
         "$"
         (Term.app
          (Term.proj `Cardinal.lt_ord "." (fieldIdx "2"))
          [(Term.app
            `lt_of_lt_of_leₓ
            [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")])
             (Term.app `le_sup [(Term.hole "_") (Term.hole "_")])])]))))]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.proj (Term.app `sup [(«term_∘_» `Cardinal.succ "∘" («term_∘_» `card "∘" `f))]) "." `ord)
    ","
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [])]
      "=>"
      («term_$__»
       `le_of_ltₓ
       "$"
       (Term.app
        (Term.proj `Cardinal.lt_ord "." (fieldIdx "2"))
        [(Term.app
          `lt_of_lt_of_leₓ
          [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")])
           (Term.app `le_sup [(Term.hole "_") (Term.hole "_")])])]))))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`i] [])]
    "=>"
    («term_$__»
     `le_of_ltₓ
     "$"
     (Term.app
      (Term.proj `Cardinal.lt_ord "." (fieldIdx "2"))
      [(Term.app
        `lt_of_lt_of_leₓ
        [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")]) (Term.app `le_sup [(Term.hole "_") (Term.hole "_")])])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `le_of_ltₓ
   "$"
   (Term.app
    (Term.proj `Cardinal.lt_ord "." (fieldIdx "2"))
    [(Term.app
      `lt_of_lt_of_leₓ
      [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")]) (Term.app `le_sup [(Term.hole "_") (Term.hole "_")])])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `Cardinal.lt_ord "." (fieldIdx "2"))
   [(Term.app
     `lt_of_lt_of_leₓ
     [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")]) (Term.app `le_sup [(Term.hole "_") (Term.hole "_")])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `lt_of_lt_of_leₓ
   [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")]) (Term.app `le_sup [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_sup [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_sup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `le_sup [(Term.hole "_") (Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Cardinal.lt_succ_self [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Cardinal.lt_succ_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_of_lt_of_leₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `lt_of_lt_of_leₓ
   [(Term.paren "(" [(Term.app `Cardinal.lt_succ_self [(Term.hole "_")]) []] ")")
    (Term.paren "(" [(Term.app `le_sup [(Term.hole "_") (Term.hole "_")]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Cardinal.lt_ord "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Cardinal.lt_ord
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `le_of_ltₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `sup [(«term_∘_» `Cardinal.succ "∘" («term_∘_» `card "∘" `f))]) "." `ord)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `sup [(«term_∘_» `Cardinal.succ "∘" («term_∘_» `card "∘" `f))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∘_» `Cardinal.succ "∘" («term_∘_» `card "∘" `f))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∘_» `card "∘" `f)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∘_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 90 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
  `card
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 90 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 90, term))
  `Cardinal.succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 91 >? 1024, (none, [anonymous]) <=? (some 90, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 90, (some 90, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_∘_» `Cardinal.succ "∘" («term_∘_» `card "∘" `f)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sup
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `sup [(Term.paren "(" [(«term_∘_» `Cardinal.succ "∘" («term_∘_» `card "∘" `f)) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}»
   "{"
   `c
   "|"
   (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" `c))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" `c))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.app `f [`i]) "≤" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The supremum of a family of ordinals -/
  def
    sup
    { ι } ( f : ι → Ordinal ) : Ordinal
    :=
      omin
        { c | ∀ i , f i ≤ c }
          ⟨
            sup Cardinal.succ ∘ card ∘ f . ord
              ,
              fun i => le_of_ltₓ $ Cardinal.lt_ord . 2 lt_of_lt_of_leₓ Cardinal.lt_succ_self _ le_sup _ _
            ⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `le_sup [])
  (Command.declSig
   [(Term.implicitBinder "{" [`ι] [] "}") (Term.explicitBinder "(" [`f] [":" (Term.arrow `ι "→" `Ordinal)] [] ")")]
   (Term.typeSpec
    ":"
    (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" (Term.app `sup [`f])))))
  (Command.declValSimple
   ":="
   (Term.app
    `omin_mem
    [(Set.«term{_|_}»
      "{"
      `c
      "|"
      (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" `c))
      "}")
     (Term.hole "_")])
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin_mem
   [(Set.«term{_|_}»
     "{"
     `c
     "|"
     (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" `c))
     "}")
    (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}»
   "{"
   `c
   "|"
   (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" `c))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_≤_» (Term.app `f [`i]) "≤" `c))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.app `f [`i]) "≤" `c)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `f [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem le_sup { ι } ( f : ι → Ordinal ) : ∀ i , f i ≤ sup f := omin_mem { c | ∀ i , f i ≤ c } _

theorem sup_le {ι} {f : ι → Ordinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
  ⟨fun h i => le_transₓ (le_sup _ _) h, fun h => omin_le h⟩

theorem lt_sup {ι} {f : ι → Ordinal} {a} : a < sup f ↔ ∃ i, a < f i := by
  simpa only [not_forall, not_leₓ] using not_congr (@sup_le _ f a)

theorem is_normal.sup {f} (H : is_normal f) {ι} {g : ι → Ordinal} (h : Nonempty ι) : f (sup g) = sup (f ∘ g) :=
  eq_of_forall_ge_iff $ fun a => by
    rw [sup_le, comp,
        H.le_set' (fun _ : ι => True) g
          (let ⟨i⟩ := h
          ⟨i, ⟨⟩⟩)] <;>
      intros <;> simp only [sup_le, true_implies_iff]

theorem sup_ord {ι} (f : ι → Cardinal) : (sup fun i => (f i).ord) = (Cardinal.sup f).ord :=
  eq_of_forall_ge_iff $ fun a => by
    simp only [sup_le, Cardinal.ord_le, Cardinal.sup_le]

theorem sup_succ {ι} (f : ι → Ordinal) : (sup fun i => succ (f i)) ≤ succ (sup f) := by
  rw [Ordinal.sup_le]
  intro i
  rw [Ordinal.succ_le_succ]
  apply Ordinal.le_sup

theorem unbounded_range_of_sup_ge {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β → α)
    (h : type r ≤ sup.{u, u} (typein r ∘ f)) : Unbounded r (range f) := by
  apply (not_bounded_iff _).mp
  rintro ⟨x, hx⟩
  apply not_lt_of_geₓ h
  refine' lt_of_le_of_ltₓ _ (typein_lt_type r x)
  rw [sup_le]
  intro y
  apply le_of_ltₓ
  rw [typein_lt_typein]
  apply hx
  apply mem_range_self

/--  The supremum of a family of ordinals indexed by the set
  of ordinals less than some `o : ordinal.{u}`.
  (This is not a special case of `sup` over the subtype,
  because `{a // a < o} : Type (u+1)` and `sup` only works over
  families in `Type u`.) -/
def bsup (o : Ordinal.{u}) : (∀, ∀ a < o, ∀, Ordinal.{max u v}) → Ordinal.{max u v} :=
  match o, o.out, o.out_eq with
  | _, ⟨α, r, _⟩, rfl, f => by
    exact sup fun a => f (typein r a) (typein_lt_type _ _)

theorem bsup_le {o f a} : bsup.{u, v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
  match o, o.out, o.out_eq, f with
  | _, ⟨α, r, _⟩, rfl, f => by
    rw [bsup._match_1, sup_le] <;>
      exact
        ⟨fun H i h => by
          simpa only [typein_enum] using H (enum r i h), fun H b => H _ _⟩

theorem bsup_type (r : α → α → Prop) [IsWellOrder α r] f :
    bsup (type r) f = sup fun a => f (typein r a) (typein_lt_type _ _) :=
  eq_of_forall_ge_iff $ fun o => by
    rw [bsup_le, sup_le] <;>
      exact
        ⟨fun H b => H _ _, fun H i h => by
          simpa only [typein_enum] using H (enum r i h)⟩

theorem le_bsup {o} (f : ∀, ∀ a < o, ∀, Ordinal) i h : f i h ≤ bsup o f :=
  bsup_le.1 (le_reflₓ _) _ _

theorem lt_bsup {o : Ordinal} {f : ∀, ∀ a < o, ∀, Ordinal}
    (hf : ∀ {a a'} ha : a < o ha' : a' < o, a < a' → f a ha < f a' ha') (ho : o.is_limit) i h : f i h < bsup o f :=
  lt_of_lt_of_leₓ (hf _ _ $ lt_succ_self i) (le_bsup f i.succ $ ho.2 _ h)

theorem bsup_id {o} (ho : is_limit o) : (bsup.{u, u} o fun x _ => x) = o := by
  apply le_antisymmₓ
  rw [bsup_le]
  intro i
  apply le_of_ltₓ
  rw [← not_ltₓ]
  intro h
  apply lt_irreflₓ (bsup.{u, u} o fun x _ => x)
  apply lt_of_le_of_ltₓ _ (lt_bsup _ ho _ h)
  rfl
  intros
  assumption

theorem is_normal.bsup {f} (H : is_normal f) {o : Ordinal} :
    ∀ g : ∀, ∀ a < o, ∀, Ordinal h : o ≠ 0, f (bsup o g) = bsup o fun a h => f (g a h) :=
  induction_on o $ fun α r _ g h => by
    skip <;> rw [bsup_type, H.sup (type_ne_zero_iff_nonempty.1 h), bsup_type]

theorem is_normal.bsup_eq {f} (H : is_normal f) {o : Ordinal} (h : is_limit o) : (bsup.{u} o fun x _ => f x) = f o := by
  rw [← is_normal.bsup.{u, u} H (fun x _ => x) h.1, bsup_id h]

/-! ### Ordinal exponential -/


/--  The ordinal exponential, defined by transfinite recursion. -/
def power (a b : Ordinal) : Ordinal :=
  if a = 0 then 1 - b else limit_rec_on b 1 (fun _ IH => IH*a) fun b _ => bsup.{u, u} b

instance : Pow Ordinal Ordinal :=
  ⟨power⟩

local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

theorem zero_power' (a : Ordinal) : (0^a) = 1 - a := by
  simp only [pow, power, if_pos rfl]

@[simp]
theorem zero_power {a : Ordinal} (a0 : a ≠ 0) : (0^a) = 0 := by
  rwa [zero_power', Ordinal.sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp]
theorem power_zero (a : Ordinal) : (a^0) = 1 := by
  by_cases' a = 0 <;> [simp only [pow, power, if_pos h, sub_zero], simp only [pow, power, if_neg h, limit_rec_on_zero]]

@[simp]
theorem power_succ (a b : Ordinal) : (a^succ b) = (a^b)*a :=
  if h : a = 0 then by
    subst a <;> simp only [zero_power (succ_ne_zero _), mul_zero]
  else by
    simp only [pow, power, limit_rec_on_succ, if_neg h]

theorem power_limit {a b : Ordinal} (a0 : a ≠ 0) (h : is_limit b) : (a^b) = bsup.{u, u} b fun c _ => a^c := by
  simp only [pow, power, if_neg a0] <;> rw [limit_rec_on_limit _ _ _ _ h] <;> rfl

theorem power_le_of_limit {a b c : Ordinal} (a0 : a ≠ 0) (h : is_limit b) : (a^b) ≤ c ↔ ∀, ∀ b' < b, ∀, (a^b') ≤ c := by
  rw [power_limit a0 h, bsup_le]

theorem lt_power_of_limit {a b c : Ordinal} (b0 : b ≠ 0) (h : is_limit c) : a < (b^c) ↔ ∃ c' < c, a < (b^c') := by
  rw [← not_iff_not, not_exists] <;> simp only [not_ltₓ, power_le_of_limit b0 h, exists_prop, not_and]

@[simp]
theorem power_one (a : Ordinal) : (a^1) = a := by
  rw [← succ_zero, power_succ] <;> simp only [power_zero, one_mulₓ]

@[simp]
theorem one_power (a : Ordinal) : (1^a) = 1 := by
  apply limit_rec_on a
  ·
    simp only [power_zero]
  ·
    intro _ ih
    simp only [power_succ, ih, mul_oneₓ]
  refine' fun b l IH => eq_of_forall_ge_iff fun c => _
  rw [power_le_of_limit Ordinal.one_ne_zero l]
  exact
    ⟨fun H => by
      simpa only [power_zero] using H 0 l.pos, fun H b' h => by
      rwa [IH _ h]⟩

theorem power_pos {a : Ordinal} b (a0 : 0 < a) : 0 < (a^b) := by
  have h0 : 0 < (a^0) := by
    simp only [power_zero, zero_lt_one]
  apply limit_rec_on b
  ·
    exact h0
  ·
    intro b IH
    rw [power_succ]
    exact mul_pos IH a0
  ·
    exact fun b l _ => (lt_power_of_limit (Ordinal.pos_iff_ne_zero.1 a0) l).2 ⟨0, l.pos, h0⟩

theorem power_ne_zero {a : Ordinal} b (a0 : a ≠ 0) : (a^b) ≠ 0 :=
  Ordinal.pos_iff_ne_zero.1 $ power_pos b $ Ordinal.pos_iff_ne_zero.2 a0

theorem power_is_normal {a : Ordinal} (h : 1 < a) : is_normal ((·^·) a) :=
  have a0 : 0 < a := lt_transₓ zero_lt_one h
  ⟨fun b => by
    simpa only [mul_oneₓ, power_succ] using (mul_lt_mul_iff_left (power_pos b a0)).2 h, fun b l c =>
    power_le_of_limit (ne_of_gtₓ a0) l⟩

theorem power_lt_power_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) < (a^c) ↔ b < c :=
  (power_is_normal a1).lt_iff

theorem power_le_power_iff_right {a b c : Ordinal} (a1 : 1 < a) : (a^b) ≤ (a^c) ↔ b ≤ c :=
  (power_is_normal a1).le_iff

theorem power_right_inj {a b c : Ordinal} (a1 : 1 < a) : (a^b) = (a^c) ↔ b = c :=
  (power_is_normal a1).inj

theorem power_is_limit {a b : Ordinal} (a1 : 1 < a) : is_limit b → is_limit (a^b) :=
  (power_is_normal a1).IsLimit

theorem power_is_limit_left {a b : Ordinal} (l : is_limit a) (hb : b ≠ 0) : is_limit (a^b) := by
  rcases zero_or_succ_or_limit b with (e | ⟨b, rfl⟩ | l')
  ·
    exact absurd e hb
  ·
    rw [power_succ]
    exact mul_is_limit (power_pos _ l.pos) l
  ·
    exact power_is_limit l.one_lt l'

theorem power_le_power_right {a b c : Ordinal} (h₁ : 0 < a) (h₂ : b ≤ c) : (a^b) ≤ (a^c) := by
  cases' lt_or_eq_of_leₓ (one_le_iff_pos.2 h₁) with h₁ h₁
  ·
    exact (power_le_power_iff_right h₁).2 h₂
  ·
    subst a
    simp only [one_power]

theorem power_le_power_left {a b : Ordinal} c (ab : a ≤ b) : (a^c) ≤ (b^c) := by
  by_cases' a0 : a = 0
  ·
    subst a
    by_cases' c0 : c = 0
    ·
      subst c
      simp only [power_zero]
    ·
      simp only [zero_power c0, Ordinal.zero_le]
  ·
    apply limit_rec_on c
    ·
      simp only [power_zero]
    ·
      intro c IH
      simpa only [power_succ] using mul_le_mul IH ab
    ·
      exact fun c l IH =>
        (power_le_of_limit a0 l).2 fun b' h =>
          le_transₓ (IH _ h) (power_le_power_right (lt_of_lt_of_leₓ (Ordinal.pos_iff_ne_zero.2 a0) ab) (le_of_ltₓ h))

theorem le_power_self {a : Ordinal} b (a1 : 1 < a) : b ≤ (a^b) :=
  (power_is_normal a1).le_self _

theorem power_lt_power_left_of_succ {a b c : Ordinal} (ab : a < b) : (a^succ c) < (b^succ c) := by
  rw [power_succ, power_succ] <;>
    exact
      lt_of_le_of_ltₓ (mul_le_mul_right _ $ power_le_power_left _ $ le_of_ltₓ ab)
        (mul_lt_mul_of_pos_left ab (power_pos _ (lt_of_le_of_ltₓ (Ordinal.zero_le _) ab)))

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `power_add [])
  (Command.declSig
   [(Term.explicitBinder "(" [`a `b `c] [":" `Ordinal] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `a "^" (Init.Logic.«term_+_» `b "+" `c))
     "="
     (Finset.Data.Finset.Fold.«term_*_»
      (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `a "^" `b)
      "*"
      (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `a "^" `c)))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.byCases' "by_cases'" [`a0 ":"] («term_=_» `a "=" (numLit "0"))) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.subst "subst" [`a]) [])
            (group (Tactic.byCases' "by_cases'" [`c0 ":"] («term_=_» `c "=" (numLit "0"))) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `c0)
                     ","
                     (Tactic.simpLemma [] [] `add_zeroₓ)
                     ","
                     (Tactic.simpLemma [] [] `power_zero)
                     ","
                     (Tactic.simpLemma [] [] `mul_oneₓ)]
                    "]"]
                   [])
                  [])])))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_≠_» (Init.Logic.«term_+_» `b "+" `c) "≠" (numLit "0")))]
                ":="
                (Term.app
                 `ne_of_gtₓ
                 [(Term.app
                   `lt_of_lt_of_leₓ
                   [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`c0])
                    (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])])]))))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] (Term.app `zero_power [`c0]))
                ","
                (Tactic.simpLemma [] [] (Term.app `zero_power [`this]))
                ","
                (Tactic.simpLemma [] [] `mul_zero)]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget
           []
           (Term.app `eq_or_lt_of_le [(Term.app (Term.proj `one_le_iff_ne_zero "." (fieldIdx "2")) [`a0])]))]
         []
         ["with" [(Lean.binderIdent `a1) (Lean.binderIdent `a1)]])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.subst "subst" [`a1]) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `one_power) "," (Tactic.simpLemma [] [] `mul_oneₓ)] "]"]
              [])
             [])])))
        [])
       (group (Tactic.apply "apply" (Term.app `limit_rec_on [`c])) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `add_zeroₓ)
                ","
                (Tactic.simpLemma [] [] `power_zero)
                ","
                (Tactic.simpLemma [] [] `mul_oneₓ)]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`c `IH]) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `add_succ)
                ","
                (Tactic.rwRule [] `power_succ)
                ","
                (Tactic.rwRule [] `IH)
                ","
                (Tactic.rwRule [] `power_succ)
                ","
                (Tactic.rwRule [] `mul_assocₓ)]
               "]")
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`c `l `IH]) [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               `eq_of_forall_ge_iff
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`d] [])]
                  "=>"
                  (Term.app
                   (Term.proj
                    (Term.app
                     (Term.proj
                      (Term.app
                       (Term.proj (Term.app `power_is_normal [`a1]) "." `trans)
                       [(Term.app `add_is_normal [`b])])
                      "."
                      `limit_le)
                     [`l])
                    "."
                    `trans)
                   [(Term.hole "_")])))]))
             [])
            (group
             (Tactic.simp
              "simp"
              ["("
               "config"
               ":="
               (Term.structInst
                "{"
                []
                [(group
                  (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                  [])]
                (Term.optEllipsis [])
                []
                "}")
               ")"]
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `IH)] "]"]
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.proj
               (Term.app
                (Term.proj
                 (Term.app
                  (Term.proj
                   («term_$__»
                    `mul_is_normal
                    "$"
                    (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
                   "."
                   `trans)
                  [(Term.app `power_is_normal [`a1])])
                 "."
                 `limit_le)
                [`l])
               "."
               `symm))
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.byCases' "by_cases'" [`a0 ":"] («term_=_» `a "=" (numLit "0"))) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.subst "subst" [`a]) [])
           (group (Tactic.byCases' "by_cases'" [`c0 ":"] («term_=_» `c "=" (numLit "0"))) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `c0)
                    ","
                    (Tactic.simpLemma [] [] `add_zeroₓ)
                    ","
                    (Tactic.simpLemma [] [] `power_zero)
                    ","
                    (Tactic.simpLemma [] [] `mul_oneₓ)]
                   "]"]
                  [])
                 [])])))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_≠_» (Init.Logic.«term_+_» `b "+" `c) "≠" (numLit "0")))]
               ":="
               (Term.app
                `ne_of_gtₓ
                [(Term.app
                  `lt_of_lt_of_leₓ
                  [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`c0])
                   (Term.app `le_add_left [(Term.hole "_") (Term.hole "_")])])]))))
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] (Term.app `zero_power [`c0]))
               ","
               (Tactic.simpLemma [] [] (Term.app `zero_power [`this]))
               ","
               (Tactic.simpLemma [] [] `mul_zero)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget
          []
          (Term.app `eq_or_lt_of_le [(Term.app (Term.proj `one_le_iff_ne_zero "." (fieldIdx "2")) [`a0])]))]
        []
        ["with" [(Lean.binderIdent `a1) (Lean.binderIdent `a1)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.subst "subst" [`a1]) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `one_power) "," (Tactic.simpLemma [] [] `mul_oneₓ)] "]"]
             [])
            [])])))
       [])
      (group (Tactic.apply "apply" (Term.app `limit_rec_on [`c])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `add_zeroₓ)
               ","
               (Tactic.simpLemma [] [] `power_zero)
               ","
               (Tactic.simpLemma [] [] `mul_oneₓ)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`c `IH]) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `add_succ)
               ","
               (Tactic.rwRule [] `power_succ)
               ","
               (Tactic.rwRule [] `IH)
               ","
               (Tactic.rwRule [] `power_succ)
               ","
               (Tactic.rwRule [] `mul_assocₓ)]
              "]")
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`c `l `IH]) [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `eq_of_forall_ge_iff
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`d] [])]
                 "=>"
                 (Term.app
                  (Term.proj
                   (Term.app
                    (Term.proj
                     (Term.app
                      (Term.proj (Term.app `power_is_normal [`a1]) "." `trans)
                      [(Term.app `add_is_normal [`b])])
                     "."
                     `limit_le)
                    [`l])
                   "."
                   `trans)
                  [(Term.hole "_")])))]))
            [])
           (group
            (Tactic.simp
             "simp"
             ["("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                 [])]
               (Term.optEllipsis [])
               []
               "}")
              ")"]
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `IH)] "]"]
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.proj
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj
                  («term_$__»
                   `mul_is_normal
                   "$"
                   (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
                  "."
                  `trans)
                 [(Term.app `power_is_normal [`a1])])
                "."
                `limit_le)
               [`l])
              "."
              `symm))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`c `l `IH]) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `eq_of_forall_ge_iff
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`d] [])]
            "=>"
            (Term.app
             (Term.proj
              (Term.app
               (Term.proj
                (Term.app (Term.proj (Term.app `power_is_normal [`a1]) "." `trans) [(Term.app `add_is_normal [`b])])
                "."
                `limit_le)
               [`l])
              "."
              `trans)
             [(Term.hole "_")])))]))
       [])
      (group
       (Tactic.simp
        "simp"
        ["("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
          (Term.optEllipsis [])
          []
          "}")
         ")"]
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `IH)] "]"]
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.proj
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj
             («term_$__»
              `mul_is_normal
              "$"
              (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
             "."
             `trans)
            [(Term.app `power_is_normal [`a1])])
           "."
           `limit_le)
          [`l])
         "."
         `symm))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.proj
    (Term.app
     (Term.proj
      (Term.app
       (Term.proj
        («term_$__»
         `mul_is_normal
         "$"
         (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
        "."
        `trans)
       [(Term.app `power_is_normal [`a1])])
      "."
      `limit_le)
     [`l])
    "."
    `symm))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app
    (Term.proj
     (Term.app
      (Term.proj
       («term_$__»
        `mul_is_normal
        "$"
        (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
       "."
       `trans)
      [(Term.app `power_is_normal [`a1])])
     "."
     `limit_le)
    [`l])
   "."
   `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj
    (Term.app
     (Term.proj
      («term_$__»
       `mul_is_normal
       "$"
       (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
      "."
      `trans)
     [(Term.app `power_is_normal [`a1])])
    "."
    `limit_le)
   [`l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app
    (Term.proj
     («term_$__»
      `mul_is_normal
      "$"
      (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
     "."
     `trans)
    [(Term.app `power_is_normal [`a1])])
   "."
   `limit_le)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   (Term.proj
    («term_$__»
     `mul_is_normal
     "$"
     (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
    "."
    `trans)
   [(Term.app `power_is_normal [`a1])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `power_is_normal [`a1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `power_is_normal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `power_is_normal [`a1]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   («term_$__»
    `mul_is_normal
    "$"
    (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
   "."
   `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_$__»
   `mul_is_normal
   "$"
   (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `power_pos [`b (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `Ordinal.pos_iff_ne_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `power_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `mul_is_normal
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__»
   `mul_is_normal
   "$"
   (Term.app
    `power_pos
    [`b (Term.paren "(" [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0]) []] ")")]))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.paren
     "("
     [(«term_$__»
       `mul_is_normal
       "$"
       (Term.app
        `power_pos
        [`b (Term.paren "(" [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0]) []] ")")]))
      []]
     ")")
    "."
    `trans)
   [(Term.paren "(" [(Term.app `power_is_normal [`a1]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.paren
     "("
     [(Term.app
       (Term.proj
        (Term.paren
         "("
         [(«term_$__»
           `mul_is_normal
           "$"
           (Term.app
            `power_pos
            [`b (Term.paren "(" [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`a0]) []] ")")]))
          []]
         ")")
        "."
        `trans)
       [(Term.paren "(" [(Term.app `power_is_normal [`a1]) []] ")")])
      []]
     ")")
    "."
    `limit_le)
   [`l])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `IH)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IH
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  power_add
  ( a b c : Ordinal ) : a ^ b + c = a ^ b * a ^ c
  :=
    by
      by_cases' a0 : a = 0
        ·
          subst a
            by_cases' c0 : c = 0
            · simp only [ c0 , add_zeroₓ , power_zero , mul_oneₓ ]
            have : b + c ≠ 0 := ne_of_gtₓ lt_of_lt_of_leₓ Ordinal.pos_iff_ne_zero . 2 c0 le_add_left _ _
            simp only [ zero_power c0 , zero_power this , mul_zero ]
        cases' eq_or_lt_of_le one_le_iff_ne_zero . 2 a0 with a1 a1
        · subst a1 simp only [ one_power , mul_oneₓ ]
        apply limit_rec_on c
        · simp only [ add_zeroₓ , power_zero , mul_oneₓ ]
        · intro c IH rw [ add_succ , power_succ , IH , power_succ , mul_assocₓ ]
        ·
          intro c l IH
            refine' eq_of_forall_ge_iff fun d => power_is_normal a1 . trans add_is_normal b . limit_le l . trans _
            simp ( config := { contextual := Bool.true._@._internal._hyg.0 } ) only [ IH ]
            exact
              mul_is_normal $ power_pos b Ordinal.pos_iff_ne_zero . 2 a0 . trans power_is_normal a1 . limit_le l . symm

theorem power_dvd_power a {b c : Ordinal} (h : b ≤ c) : (a^b) ∣ (a^c) := by
  rw [← Ordinal.add_sub_cancel_of_le h, power_add]
  apply dvd_mul_right

theorem power_dvd_power_iff {a b c : Ordinal} (a1 : 1 < a) : (a^b) ∣ (a^c) ↔ b ≤ c :=
  ⟨fun h =>
    le_of_not_ltₓ $ fun hn =>
      not_le_of_lt ((power_lt_power_iff_right a1).2 hn) $
        le_of_dvd (power_ne_zero _ $ one_le_iff_ne_zero.1 $ le_of_ltₓ a1) h,
    power_dvd_power _⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `power_mul [])
  (Command.declSig
   [(Term.explicitBinder "(" [`a `b `c] [":" `Ordinal] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `a "^" (Finset.Data.Finset.Fold.«term_*_» `b "*" `c))
     "="
     (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `a "^" `b) "^" `c))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.byCases' "by_cases'" [`b0 ":"] («term_=_» `b "=" (numLit "0"))) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `b0)
                ","
                (Tactic.simpLemma [] [] `zero_mul)
                ","
                (Tactic.simpLemma [] [] `power_zero)
                ","
                (Tactic.simpLemma [] [] `one_power)]
               "]"]
              [])
             [])])))
        [])
       (group (Tactic.byCases' "by_cases'" [`a0 ":"] («term_=_» `a "=" (numLit "0"))) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.subst "subst" [`a]) [])
            (group (Tactic.byCases' "by_cases'" [`c0 ":"] («term_=_» `c "=" (numLit "0"))) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `c0)
                     ","
                     (Tactic.simpLemma [] [] `mul_zero)
                     ","
                     (Tactic.simpLemma [] [] `power_zero)]
                    "]"]
                   [])
                  [])])))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] (Term.app `zero_power [`b0]))
                ","
                (Tactic.simpLemma [] [] (Term.app `zero_power [`c0]))
                ","
                (Tactic.simpLemma [] [] (Term.app `zero_power [(Term.app `mul_ne_zero [`b0 `c0])]))]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget
           []
           (Term.app `eq_or_lt_of_le [(Term.app (Term.proj `one_le_iff_ne_zero "." (fieldIdx "2")) [`a0])]))]
         []
         ["with" [(Lean.binderIdent `a1) (Lean.binderIdent `a1)]])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.subst "subst" [`a1]) [])
            (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `one_power)] "]"] []) [])])))
        [])
       (group (Tactic.apply "apply" (Term.app `limit_rec_on [`c])) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `mul_zero) "," (Tactic.simpLemma [] [] `power_zero)] "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`c `IH]) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `mul_succ)
                ","
                (Tactic.rwRule [] `power_add)
                ","
                (Tactic.rwRule [] `IH)
                ","
                (Tactic.rwRule [] `power_succ)]
               "]")
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`c `l `IH]) [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               `eq_of_forall_ge_iff
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`d] [])]
                  "=>"
                  (Term.app
                   (Term.proj
                    (Term.app
                     (Term.proj
                      (Term.app
                       (Term.proj (Term.app `power_is_normal [`a1]) "." `trans)
                       [(Term.app
                         `mul_is_normal
                         [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`b0])])])
                      "."
                      `limit_le)
                     [`l])
                    "."
                    `trans)
                   [(Term.hole "_")])))]))
             [])
            (group
             (Tactic.simp
              "simp"
              ["("
               "config"
               ":="
               (Term.structInst
                "{"
                []
                [(group
                  (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                  [])]
                (Term.optEllipsis [])
                []
                "}")
               ")"]
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `IH)] "]"]
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.proj (Term.app `power_le_of_limit [(Term.app `power_ne_zero [(Term.hole "_") `a0]) `l]) "." `symm))
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.byCases' "by_cases'" [`b0 ":"] («term_=_» `b "=" (numLit "0"))) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `b0)
               ","
               (Tactic.simpLemma [] [] `zero_mul)
               ","
               (Tactic.simpLemma [] [] `power_zero)
               ","
               (Tactic.simpLemma [] [] `one_power)]
              "]"]
             [])
            [])])))
       [])
      (group (Tactic.byCases' "by_cases'" [`a0 ":"] («term_=_» `a "=" (numLit "0"))) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.subst "subst" [`a]) [])
           (group (Tactic.byCases' "by_cases'" [`c0 ":"] («term_=_» `c "=" (numLit "0"))) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.simp
                  "simp"
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `c0)
                    ","
                    (Tactic.simpLemma [] [] `mul_zero)
                    ","
                    (Tactic.simpLemma [] [] `power_zero)]
                   "]"]
                  [])
                 [])])))
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] (Term.app `zero_power [`b0]))
               ","
               (Tactic.simpLemma [] [] (Term.app `zero_power [`c0]))
               ","
               (Tactic.simpLemma [] [] (Term.app `zero_power [(Term.app `mul_ne_zero [`b0 `c0])]))]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget
          []
          (Term.app `eq_or_lt_of_le [(Term.app (Term.proj `one_le_iff_ne_zero "." (fieldIdx "2")) [`a0])]))]
        []
        ["with" [(Lean.binderIdent `a1) (Lean.binderIdent `a1)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.subst "subst" [`a1]) [])
           (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `one_power)] "]"] []) [])])))
       [])
      (group (Tactic.apply "apply" (Term.app `limit_rec_on [`c])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `mul_zero) "," (Tactic.simpLemma [] [] `power_zero)] "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`c `IH]) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mul_succ)
               ","
               (Tactic.rwRule [] `power_add)
               ","
               (Tactic.rwRule [] `IH)
               ","
               (Tactic.rwRule [] `power_succ)]
              "]")
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`c `l `IH]) [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `eq_of_forall_ge_iff
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`d] [])]
                 "=>"
                 (Term.app
                  (Term.proj
                   (Term.app
                    (Term.proj
                     (Term.app
                      (Term.proj (Term.app `power_is_normal [`a1]) "." `trans)
                      [(Term.app
                        `mul_is_normal
                        [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`b0])])])
                     "."
                     `limit_le)
                    [`l])
                   "."
                   `trans)
                  [(Term.hole "_")])))]))
            [])
           (group
            (Tactic.simp
             "simp"
             ["("
              "config"
              ":="
              (Term.structInst
               "{"
               []
               [(group
                 (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0)
                 [])]
               (Term.optEllipsis [])
               []
               "}")
              ")"]
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `IH)] "]"]
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.proj (Term.app `power_le_of_limit [(Term.app `power_ne_zero [(Term.hole "_") `a0]) `l]) "." `symm))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`c `l `IH]) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `eq_of_forall_ge_iff
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`d] [])]
            "=>"
            (Term.app
             (Term.proj
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj (Term.app `power_is_normal [`a1]) "." `trans)
                 [(Term.app `mul_is_normal [(Term.app (Term.proj `Ordinal.pos_iff_ne_zero "." (fieldIdx "2")) [`b0])])])
                "."
                `limit_le)
               [`l])
              "."
              `trans)
             [(Term.hole "_")])))]))
       [])
      (group
       (Tactic.simp
        "simp"
        ["("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
          (Term.optEllipsis [])
          []
          "}")
         ")"]
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `IH)] "]"]
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.proj (Term.app `power_le_of_limit [(Term.app `power_ne_zero [(Term.hole "_") `a0]) `l]) "." `symm))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.proj (Term.app `power_le_of_limit [(Term.app `power_ne_zero [(Term.hole "_") `a0]) `l]) "." `symm))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `power_le_of_limit [(Term.app `power_ne_zero [(Term.hole "_") `a0]) `l]) "." `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `power_le_of_limit [(Term.app `power_ne_zero [(Term.hole "_") `a0]) `l])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `l
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `power_ne_zero [(Term.hole "_") `a0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `power_ne_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `power_ne_zero [(Term.hole "_") `a0]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `power_le_of_limit
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `power_le_of_limit [(Term.paren "(" [(Term.app `power_ne_zero [(Term.hole "_") `a0]) []] ")") `l]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `IH)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IH
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  power_mul
  ( a b c : Ordinal ) : a ^ b * c = a ^ b ^ c
  :=
    by
      by_cases' b0 : b = 0
        · simp only [ b0 , zero_mul , power_zero , one_power ]
        by_cases' a0 : a = 0
        ·
          subst a
            by_cases' c0 : c = 0
            · simp only [ c0 , mul_zero , power_zero ]
            simp only [ zero_power b0 , zero_power c0 , zero_power mul_ne_zero b0 c0 ]
        cases' eq_or_lt_of_le one_le_iff_ne_zero . 2 a0 with a1 a1
        · subst a1 simp only [ one_power ]
        apply limit_rec_on c
        · simp only [ mul_zero , power_zero ]
        · intro c IH rw [ mul_succ , power_add , IH , power_succ ]
        ·
          intro c l IH
            refine'
              eq_of_forall_ge_iff
                fun d => power_is_normal a1 . trans mul_is_normal Ordinal.pos_iff_ne_zero . 2 b0 . limit_le l . trans _
            simp ( config := { contextual := Bool.true._@._internal._hyg.0 } ) only [ IH ]
            exact power_le_of_limit power_ne_zero _ a0 l . symm

/-! ### Ordinal logarithm -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The ordinal logarithm is the solution `u` to the equation\n  `x = b ^ u * v + w` where `v < b` and `w < b`. -/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `log [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`b] [":" `Ordinal] [] ")") (Term.explicitBinder "(" [`x] [":" `Ordinal] [] ")")]
   [(Term.typeSpec ":" `Ordinal)])
  (Command.declValSimple
   ":="
   (termDepIfThenElse
    "if"
    `h
    ":"
    («term_<_» (numLit "1") "<" `b)
    "then"
    («term_$__»
     `pred
     "$"
     (Term.app
      `omin
      [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
       (Term.anonymousCtor
        "⟨"
        [(Term.app `succ [`x])
         ","
         (Term.app (Term.proj `succ_le "." (fieldIdx "1")) [(Term.app `le_power_self [(Term.hole "_") `h])])]
        "⟩")]))
    "else"
    (numLit "0"))
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termDepIfThenElse
   "if"
   `h
   ":"
   («term_<_» (numLit "1") "<" `b)
   "then"
   («term_$__»
    `pred
    "$"
    (Term.app
     `omin
     [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
      (Term.anonymousCtor
       "⟨"
       [(Term.app `succ [`x])
        ","
        (Term.app (Term.proj `succ_le "." (fieldIdx "1")) [(Term.app `le_power_self [(Term.hole "_") `h])])]
       "⟩")]))
   "else"
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termDepIfThenElse', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   `pred
   "$"
   (Term.app
    `omin
    [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
     (Term.anonymousCtor
      "⟨"
      [(Term.app `succ [`x])
       ","
       (Term.app (Term.proj `succ_le "." (fieldIdx "1")) [(Term.app `le_power_self [(Term.hole "_") `h])])]
      "⟩")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin
   [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
    (Term.anonymousCtor
     "⟨"
     [(Term.app `succ [`x])
      ","
      (Term.app (Term.proj `succ_le "." (fieldIdx "1")) [(Term.app `le_power_self [(Term.hole "_") `h])])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `succ [`x])
    ","
    (Term.app (Term.proj `succ_le "." (fieldIdx "1")) [(Term.app `le_power_self [(Term.hole "_") `h])])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `succ_le "." (fieldIdx "1")) [(Term.app `le_power_self [(Term.hole "_") `h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_power_self [(Term.hole "_") `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_power_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_power_self [(Term.hole "_") `h]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `succ_le "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `succ_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `succ [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.OrdinalArithmetic.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    The ordinal logarithm is the solution `u` to the equation
      `x = b ^ u * v + w` where `v < b` and `w < b`. -/
  def
    log
    ( b : Ordinal ) ( x : Ordinal ) : Ordinal
    := if h : 1 < b then pred $ omin { o | x < b ^ o } ⟨ succ x , succ_le . 1 le_power_self _ h ⟩ else 0

@[simp]
theorem log_not_one_lt {b : Ordinal} (b1 : ¬1 < b) (x : Ordinal) : log b x = 0 := by
  simp only [log, dif_neg b1]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `log_def [])
  (Command.declSig
   [(Term.implicitBinder "{" [`b] [":" `Ordinal] "}")
    (Term.explicitBinder "(" [`b1] [":" («term_<_» (numLit "1") "<" `b)] [] ")")
    (Term.explicitBinder "(" [`x] [":" `Ordinal] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `log [`b `x])
     "="
     (Term.app
      `pred
      [(Term.app
        `omin
        [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
         (Term.app `log._proof_1 [`b `x `b1])])]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `log) "," (Tactic.simpLemma [] [] (Term.app `dif_pos [`b1]))] "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `log) "," (Tactic.simpLemma [] [] (Term.app `dif_pos [`b1]))] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `log) "," (Tactic.simpLemma [] [] (Term.app `dif_pos [`b1]))] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dif_pos [`b1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dif_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `log
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `log [`b `x])
   "="
   (Term.app
    `pred
    [(Term.app
      `omin
      [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
       (Term.app `log._proof_1 [`b `x `b1])])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `pred
   [(Term.app
     `omin
     [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
      (Term.app `log._proof_1 [`b `x `b1])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin
   [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
    (Term.app `log._proof_1 [`b `x `b1])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `log._proof_1 [`b `x `b1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `log._proof_1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `log._proof_1 [`b `x `b1]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.OrdinalArithmetic.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  log_def
  { b : Ordinal } ( b1 : 1 < b ) ( x : Ordinal ) : log b x = pred omin { o | x < b ^ o } log._proof_1 b x b1
  := by simp only [ log , dif_pos b1 ]

@[simp]
theorem log_zero (b : Ordinal) : log b 0 = 0 :=
  if b1 : 1 < b then by
    rw [log_def b1, ← Ordinal.le_zero, pred_le] <;>
      apply omin_le <;> change 0 < (b^succ 0) <;> rw [succ_zero, power_one] <;> exact lt_transₓ zero_lt_one b1
  else by
    simp only [log_not_one_lt b1]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `succ_log_def [])
  (Command.declSig
   [(Term.implicitBinder "{" [`b `x] [":" `Ordinal] "}")
    (Term.explicitBinder "(" [`b1] [":" («term_<_» (numLit "1") "<" `b)] [] ")")
    (Term.explicitBinder "(" [`x0] [":" («term_<_» (numLit "0") "<" `x)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `succ [(Term.app `log [`b `x])])
     "="
     (Term.app
      `omin
      [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
       (Term.app `log._proof_1 [`b `x `b1])]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `t
           []
           ":="
           (Term.app
            `omin
            [(Set.«term{_|_}»
              "{"
              `o
              "|"
              («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
              "}")
             (Term.app `log._proof_1 [`b `x `b1])]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `t)))]
           ":="
           (Term.app
            `omin_mem
            [(Set.«term{_|_}»
              "{"
              `o
              "|"
              («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
              "}")
             (Term.hole "_")]))))
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `zero_or_succ_or_limit [`t]))]
         ["with"
          (Tactic.rcasesPat.paren
           "("
           (Tactic.rcasesPatLo
            (Tactic.rcasesPatMed
             [(Tactic.rcasesPat.one `h) "|" (Tactic.rcasesPat.one `h) "|" (Tactic.rcasesPat.one `h)])
            [])
           ")")])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.proj
               (Term.app
                `not_lt_of_le
                [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]) (Term.hole "_")])
               "."
               `elim))
             [])
            (group
             (Tactic.simpa
              "simpa"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `power_zero)] "]"]
              []
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.show
                  "show"
                  («term_=_» (Term.app `log [`b `x]) "=" (Term.app `pred [`t]))
                  (Term.fromTerm "from" (Term.app `log_def [`b1 `x]))))
                ","
                (Tactic.rwRule [] (Term.app (Term.proj `succ_pred_iff_is_succ "." (fieldIdx "2")) [`h]))]
               "]")
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app
                 (Term.proj
                  (Term.app
                   `lt_power_of_limit
                   [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) `h])
                  "."
                  (fieldIdx "1"))
                 [`this]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h₁)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h₂)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.app `not_le_of_lt [`h₁]) "." `elim)
               [(Term.app (Term.proj `le_omin "." (fieldIdx "1")) [(Term.app `le_reflₓ [`t]) `a `h₂])]))
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `t
          []
          ":="
          (Term.app
           `omin
           [(Set.«term{_|_}»
             "{"
             `o
             "|"
             («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
             "}")
            (Term.app `log._proof_1 [`b `x `b1])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `t)))]
          ":="
          (Term.app
           `omin_mem
           [(Set.«term{_|_}»
             "{"
             `o
             "|"
             («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
             "}")
            (Term.hole "_")]))))
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `zero_or_succ_or_limit [`t]))]
        ["with"
         (Tactic.rcasesPat.paren
          "("
          (Tactic.rcasesPatLo
           (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h) "|" (Tactic.rcasesPat.one `h) "|" (Tactic.rcasesPat.one `h)])
           [])
          ")")])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.proj
              (Term.app `not_lt_of_le [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]) (Term.hole "_")])
              "."
              `elim))
            [])
           (group
            (Tactic.simpa
             "simpa"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `power_zero)] "]"]
             []
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.show
                 "show"
                 («term_=_» (Term.app `log [`b `x]) "=" (Term.app `pred [`t]))
                 (Term.fromTerm "from" (Term.app `log_def [`b1 `x]))))
               ","
               (Tactic.rwRule [] (Term.app (Term.proj `succ_pred_iff_is_succ "." (fieldIdx "2")) [`h]))]
              "]")
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app
                (Term.proj
                 (Term.app `lt_power_of_limit [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) `h])
                 "."
                 (fieldIdx "1"))
                [`this]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h₁)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h₂)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj (Term.app `not_le_of_lt [`h₁]) "." `elim)
              [(Term.app (Term.proj `le_omin "." (fieldIdx "1")) [(Term.app `le_reflₓ [`t]) `a `h₂])]))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget
          []
          (Term.app
           (Term.proj
            (Term.app `lt_power_of_limit [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) `h])
            "."
            (fieldIdx "1"))
           [`this]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h₁)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h₂)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj (Term.app `not_le_of_lt [`h₁]) "." `elim)
         [(Term.app (Term.proj `le_omin "." (fieldIdx "1")) [(Term.app `le_reflₓ [`t]) `a `h₂])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    (Term.proj (Term.app `not_le_of_lt [`h₁]) "." `elim)
    [(Term.app (Term.proj `le_omin "." (fieldIdx "1")) [(Term.app `le_reflₓ [`t]) `a `h₂])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `not_le_of_lt [`h₁]) "." `elim)
   [(Term.app (Term.proj `le_omin "." (fieldIdx "1")) [(Term.app `le_reflₓ [`t]) `a `h₂])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `le_omin "." (fieldIdx "1")) [(Term.app `le_reflₓ [`t]) `a `h₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `le_reflₓ [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_reflₓ [`t]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `le_omin "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `le_omin
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `le_omin "." (fieldIdx "1")) [(Term.paren "(" [(Term.app `le_reflₓ [`t]) []] ")") `a `h₂]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `not_le_of_lt [`h₁]) "." `elim)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `not_le_of_lt [`h₁])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h₁
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `not_le_of_lt
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `not_le_of_lt [`h₁]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget
     []
     (Term.app
      (Term.proj
       (Term.app `lt_power_of_limit [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) `h])
       "."
       (fieldIdx "1"))
      [`this]))]
   ["with"
    (Tactic.rcasesPat.tuple
     "⟨"
     [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h₁)]) [])
      ","
      (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h₂)]) [])]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app `lt_power_of_limit [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) `h])
    "."
    (fieldIdx "1"))
   [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app `lt_power_of_limit [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) `h])
   "."
   (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `lt_power_of_limit [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  («term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `lt_transₓ [`zero_lt_one `b1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `zero_lt_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_transₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `ne_of_gtₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_power_of_limit
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `lt_power_of_limit
   [(Term.paren "(" [(«term_$__» `ne_of_gtₓ "$" (Term.app `lt_transₓ [`zero_lt_one `b1])) []] ")") `h])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           []
           (Term.show
            "show"
            («term_=_» (Term.app `log [`b `x]) "=" (Term.app `pred [`t]))
            (Term.fromTerm "from" (Term.app `log_def [`b1 `x]))))
          ","
          (Tactic.rwRule [] (Term.app (Term.proj `succ_pred_iff_is_succ "." (fieldIdx "2")) [`h]))]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      []
      (Term.show
       "show"
       («term_=_» (Term.app `log [`b `x]) "=" (Term.app `pred [`t]))
       (Term.fromTerm "from" (Term.app `log_def [`b1 `x]))))
     ","
     (Tactic.rwRule [] (Term.app (Term.proj `succ_pred_iff_is_succ "." (fieldIdx "2")) [`h]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `succ_pred_iff_is_succ "." (fieldIdx "2")) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `succ_pred_iff_is_succ "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `succ_pred_iff_is_succ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   («term_=_» (Term.app `log [`b `x]) "=" (Term.app `pred [`t]))
   (Term.fromTerm "from" (Term.app `log_def [`b1 `x])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.show.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fromTerm', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `log_def [`b1 `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `log_def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_» (Term.app `log [`b `x]) "=" (Term.app `pred [`t]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `pred [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pred
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `log [`b `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `log
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.proj
         (Term.app `not_lt_of_le [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]) (Term.hole "_")])
         "."
         `elim))
       [])
      (group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `power_zero)] "]"]
        []
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `h) "," (Tactic.simpLemma [] [] `power_zero)] "]"]
   []
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `power_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.proj
    (Term.app `not_lt_of_le [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]) (Term.hole "_")])
    "."
    `elim))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.app `not_lt_of_le [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]) (Term.hole "_")])
   "."
   `elim)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `not_lt_of_le [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `one_le_iff_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `one_le_iff_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `not_lt_of_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `not_lt_of_le
   [(Term.paren "(" [(Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]) []] ")") (Term.hole "_")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rcases
   "rcases"
   [(Tactic.casesTarget [] (Term.app `zero_or_succ_or_limit [`t]))]
   ["with"
    (Tactic.rcasesPat.paren
     "("
     (Tactic.rcasesPatLo
      (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h) "|" (Tactic.rcasesPat.one `h) "|" (Tactic.rcasesPat.one `h)])
      [])
     ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.paren', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `zero_or_succ_or_limit [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `zero_or_succ_or_limit
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec ":" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `t)))]
     ":="
     (Term.app
      `omin_mem
      [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
       (Term.hole "_")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin_mem
   [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
    (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.OrdinalArithmetic.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  succ_log_def
  { b x : Ordinal } ( b1 : 1 < b ) ( x0 : 0 < x ) : succ log b x = omin { o | x < b ^ o } log._proof_1 b x b1
  :=
    by
      let t := omin { o | x < b ^ o } log._proof_1 b x b1
        have : x < b ^ t := omin_mem { o | x < b ^ o } _
        rcases zero_or_succ_or_limit t with ( h | h | h )
        · refine' not_lt_of_le one_le_iff_pos . 2 x0 _ . elim simpa only [ h , power_zero ]
        · rw [ show log b x = pred t from log_def b1 x , succ_pred_iff_is_succ . 2 h ]
        ·
          rcases lt_power_of_limit ne_of_gtₓ $ lt_transₓ zero_lt_one b1 h . 1 this with ⟨ a , h₁ , h₂ ⟩
            exact not_le_of_lt h₁ . elim le_omin . 1 le_reflₓ t a h₂

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `lt_power_succ_log [])
  (Command.declSig
   [(Term.implicitBinder "{" [`b] [":" `Ordinal] "}")
    (Term.explicitBinder "(" [`b1] [":" («term_<_» (numLit "1") "<" `b)] [] ")")
    (Term.explicitBinder "(" [`x] [":" `Ordinal] [] ")")]
   (Term.typeSpec
    ":"
    («term_<_»
     `x
     "<"
     (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" (Term.app `succ [(Term.app `log [`b `x])])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] (Term.app `lt_or_eq_of_leₓ [(Term.app `Ordinal.zero_le [`x])]))]
         []
         ["with" [(Lean.binderIdent `x0) (Lean.binderIdent `x0)]])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `succ_log_def [`b1 `x0]))] "]")
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               `omin_mem
               [(Set.«term{_|_}»
                 "{"
                 `o
                 "|"
                 («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
                 "}")
                (Term.hole "_")]))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.subst "subst" [`x]) [])
            (group
             (Tactic.apply "apply" (Term.app `power_pos [(Term.hole "_") (Term.app `lt_transₓ [`zero_lt_one `b1])]))
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `lt_or_eq_of_leₓ [(Term.app `Ordinal.zero_le [`x])]))]
        []
        ["with" [(Lean.binderIdent `x0) (Lean.binderIdent `x0)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `succ_log_def [`b1 `x0]))] "]") [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              `omin_mem
              [(Set.«term{_|_}»
                "{"
                `o
                "|"
                («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
                "}")
               (Term.hole "_")]))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.subst "subst" [`x]) [])
           (group
            (Tactic.apply "apply" (Term.app `power_pos [(Term.hole "_") (Term.app `lt_transₓ [`zero_lt_one `b1])]))
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.subst "subst" [`x]) [])
      (group
       (Tactic.apply "apply" (Term.app `power_pos [(Term.hole "_") (Term.app `lt_transₓ [`zero_lt_one `b1])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply "apply" (Term.app `power_pos [(Term.hole "_") (Term.app `lt_transₓ [`zero_lt_one `b1])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `power_pos [(Term.hole "_") (Term.app `lt_transₓ [`zero_lt_one `b1])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `lt_transₓ [`zero_lt_one `b1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `zero_lt_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_transₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `lt_transₓ [`zero_lt_one `b1]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `power_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.subst "subst" [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.subst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `succ_log_def [`b1 `x0]))] "]") [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `omin_mem
         [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
          (Term.hole "_")]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `omin_mem
    [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
     (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `omin_mem
   [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
    (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.OrdinalArithmetic.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  lt_power_succ_log
  { b : Ordinal } ( b1 : 1 < b ) ( x : Ordinal ) : x < b ^ succ log b x
  :=
    by
      cases' lt_or_eq_of_leₓ Ordinal.zero_le x with x0 x0
        · rw [ succ_log_def b1 x0 ] exact omin_mem { o | x < b ^ o } _
        · subst x apply power_pos _ lt_transₓ zero_lt_one b1

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `power_log_le [])
  (Command.declSig
   [(Term.simpleBinder [`b] [])
    (Term.implicitBinder "{" [`x] [":" `Ordinal] "}")
    (Term.explicitBinder "(" [`x0] [":" («term_<_» (numLit "0") "<" `x)] [] ")")]
   (Term.typeSpec
    ":"
    («term_≤_» (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" (Term.app `log [`b `x])) "≤" `x)))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.byCases' "by_cases'" [`b0 ":"] («term_=_» `b "=" (numLit "0"))) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `b0) "," (Tactic.rwRule [] `zero_power')] "]")
              [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               `le_transₓ
               [(Term.app `sub_le_self [(Term.hole "_") (Term.hole "_")])
                (Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0])]))
             [])])))
        [])
       (group
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget
           []
           (Term.app `lt_or_eq_of_leₓ [(Term.app (Term.proj `one_le_iff_ne_zero "." (fieldIdx "2")) [`b0])]))]
         []
         ["with" [(Lean.binderIdent `b1) (Lean.binderIdent `b1)]])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               `le_of_not_ltₓ
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`h] [])]
                  "=>"
                  (Term.app `not_le_of_lt [(Term.app `lt_succ_self [(Term.app `log [`b `x])]) (Term.hole "_")])))]))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app
                 (Term.explicit "@" `omin_le)
                 [(Set.«term{_|_}»
                   "{"
                   `o
                   "|"
                   («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
                   "}")
                  (Term.hole "_")
                  (Term.hole "_")
                  `h]))))
             [])
            (group
             (tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `succ_log_def [`b1 `x0]))] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `b1) "," (Tactic.rwRule [] `one_power)] "]")
              [])
             [])
            (group (Tactic.exact "exact" (Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0])) [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.byCases' "by_cases'" [`b0 ":"] («term_=_» `b "=" (numLit "0"))) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `b0) "," (Tactic.rwRule [] `zero_power')] "]")
             [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `le_transₓ
              [(Term.app `sub_le_self [(Term.hole "_") (Term.hole "_")])
               (Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0])]))
            [])])))
       [])
      (group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget
          []
          (Term.app `lt_or_eq_of_leₓ [(Term.app (Term.proj `one_le_iff_ne_zero "." (fieldIdx "2")) [`b0])]))]
        []
        ["with" [(Lean.binderIdent `b1) (Lean.binderIdent `b1)]])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              `le_of_not_ltₓ
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`h] [])]
                 "=>"
                 (Term.app `not_le_of_lt [(Term.app `lt_succ_self [(Term.app `log [`b `x])]) (Term.hole "_")])))]))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app
                (Term.explicit "@" `omin_le)
                [(Set.«term{_|_}»
                  "{"
                  `o
                  "|"
                  («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
                  "}")
                 (Term.hole "_")
                 (Term.hole "_")
                 `h]))))
            [])
           (group
            (tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `succ_log_def [`b1 `x0]))] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `b1) "," (Tactic.rwRule [] `one_power)] "]")
             [])
            [])
           (group (Tactic.exact "exact" (Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0])) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `b1) "," (Tactic.rwRule [] `one_power)] "]")
        [])
       [])
      (group (Tactic.exact "exact" (Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj `one_le_iff_pos "." (fieldIdx "2")) [`x0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `one_le_iff_pos "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `one_le_iff_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `b1) "," (Tactic.rwRule [] `one_power)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_power
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         `le_of_not_ltₓ
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`h] [])]
            "=>"
            (Term.app `not_le_of_lt [(Term.app `lt_succ_self [(Term.app `log [`b `x])]) (Term.hole "_")])))]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          []
          ":="
          (Term.app
           (Term.explicit "@" `omin_le)
           [(Set.«term{_|_}»
             "{"
             `o
             "|"
             («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
             "}")
            (Term.hole "_")
            (Term.hole "_")
            `h]))))
       [])
      (group
       (tacticRwa__
        "rwa"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `succ_log_def [`b1 `x0]))] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticRwa__
   "rwa"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `succ_log_def [`b1 `x0]))] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `succ_log_def [`b1 `x0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x0
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `b1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `succ_log_def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     []
     ":="
     (Term.app
      (Term.explicit "@" `omin_le)
      [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
       (Term.hole "_")
       (Term.hole "_")
       `h]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `omin_le)
   [(Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
    (Term.hole "_")
    (Term.hole "_")
    `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Set.«term{_|_}» "{" `o "|" («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `x "<" (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ordinal.SetTheory.OrdinalArithmetic.«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `o
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 0, term))
  `b
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1 >? 1024, (none, [anonymous]) <=? (some 0, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 0, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Ordinal.SetTheory.OrdinalArithmetic.«term_^_» `b "^" `o) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  power_log_le
  b { x : Ordinal } ( x0 : 0 < x ) : b ^ log b x ≤ x
  :=
    by
      by_cases' b0 : b = 0
        · rw [ b0 , zero_power' ] refine' le_transₓ sub_le_self _ _ one_le_iff_pos . 2 x0
        cases' lt_or_eq_of_leₓ one_le_iff_ne_zero . 2 b0 with b1 b1
        ·
          refine' le_of_not_ltₓ fun h => not_le_of_lt lt_succ_self log b x _
            have := @ omin_le { o | x < b ^ o } _ _ h
            rwa [ ← succ_log_def b1 x0 ] at this
        · rw [ ← b1 , one_power ] exact one_le_iff_pos . 2 x0

theorem le_log {b x c : Ordinal} (b1 : 1 < b) (x0 : 0 < x) : c ≤ log b x ↔ (b^c) ≤ x :=
  ⟨fun h => le_transₓ ((power_le_power_iff_right b1).2 h) (power_log_le b x0), fun h =>
    le_of_not_ltₓ $ fun hn =>
      not_le_of_lt (lt_power_succ_log b1 x) $ le_transₓ ((power_le_power_iff_right b1).2 (succ_le.2 hn)) h⟩

theorem log_lt {b x c : Ordinal} (b1 : 1 < b) (x0 : 0 < x) : log b x < c ↔ x < (b^c) :=
  lt_iff_lt_of_le_iff_le (le_log b1 x0)

theorem log_le_log b {x y : Ordinal} (xy : x ≤ y) : log b x ≤ log b y :=
  if x0 : x = 0 then by
    simp only [x0, log_zero, Ordinal.zero_le]
  else
    have x0 : 0 < x := Ordinal.pos_iff_ne_zero.2 x0
    if b1 : 1 < b then (le_log b1 (lt_of_lt_of_leₓ x0 xy)).2 $ le_transₓ (power_log_le _ x0) xy
    else by
      simp only [log_not_one_lt b1, Ordinal.zero_le]

theorem log_le_self (b x : Ordinal) : log b x ≤ x :=
  if x0 : x = 0 then by
    simp only [x0, log_zero, Ordinal.zero_le]
  else
    if b1 : 1 < b then le_transₓ (le_power_self _ b1) (power_log_le b (Ordinal.pos_iff_ne_zero.2 x0))
    else by
      simp only [log_not_one_lt b1, Ordinal.zero_le]

/-! ### The Cantor normal form -/


theorem CNF_aux {b o : Ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) : o % (b^log b o) < o :=
  lt_of_lt_of_leₓ (mod_lt _ $ power_ne_zero _ b0) (power_log_le _ $ Ordinal.pos_iff_ne_zero.2 o0)

/--  Proving properties of ordinals by induction over their Cantor normal form. -/
@[elab_as_eliminator]
noncomputable def CNF_rec {b : Ordinal} (b0 : b ≠ 0) {C : Ordinal → Sort _} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → o % (b^log b o) < o → C (o % (b^log b o)) → C o) : ∀ o, C o
  | o =>
    if o0 : o = 0 then by
      rw [o0] <;> exact H0
    else
      have := CNF_aux b0 o0
      H o o0 this (CNF_rec (o % (b^log b o)))

@[simp]
theorem CNF_rec_zero {b} b0 {C H0 H} : @CNF_rec b b0 C H0 H 0 = H0 := by
  rw [CNF_rec, dif_pos rfl] <;> rfl

@[simp]
theorem CNF_rec_ne_zero {b} b0 {C H0 H o} o0 :
    @CNF_rec b b0 C H0 H o = H o o0 (CNF_aux b0 o0) (@CNF_rec b b0 C H0 H _) := by
  rw [CNF_rec, dif_neg o0]

/--  The Cantor normal form of an ordinal is the list of coefficients
  in the base-`b` expansion of `o`.

    CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)] -/
noncomputable def CNF (b := omega) (o : Ordinal) : List (Ordinal × Ordinal) :=
  if b0 : b = 0 then [] else CNF_rec b0 [] (fun o o0 h IH => (log b o, o / (b^log b o)) :: IH) o

@[simp]
theorem zero_CNF o : CNF 0 o = [] :=
  dif_pos rfl

@[simp]
theorem CNF_zero b : CNF b 0 = [] :=
  if b0 : b = 0 then dif_pos b0 else (dif_neg b0).trans $ CNF_rec_zero _

theorem CNF_ne_zero {b o : Ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) :
    CNF b o = (log b o, o / (b^log b o)) :: CNF b (o % (b^log b o)) := by
  unfold CNF <;> rw [dif_neg b0, dif_neg b0, CNF_rec_ne_zero b0 o0]

theorem one_CNF {o : Ordinal} (o0 : o ≠ 0) : CNF 1 o = [(0, o)] := by
  rw [CNF_ne_zero Ordinal.one_ne_zero o0, log_not_one_lt (lt_irreflₓ _), power_zero, mod_one, CNF_zero, div_one]

theorem CNF_foldr {b : Ordinal} (b0 : b ≠ 0) o : (CNF b o).foldr (fun p r => ((b^p.1)*p.2)+r) 0 = o :=
  CNF_rec b0
    (by
      rw [CNF_zero] <;> rfl)
    (fun o o0 h IH => by
      rw [CNF_ne_zero b0 o0, List.foldr_cons, IH, div_add_mod])
    o

theorem CNF_pairwise_aux (b := omega) o :
    (∀, ∀ p ∈ CNF b o, ∀, Prod.fst p ≤ log b o) ∧ (CNF b o).Pairwise fun p q => q.1 < p.1 := by
  by_cases' b0 : b = 0
  ·
    simp only [b0, zero_CNF, List.Pairwiseₓ.nil, and_trueₓ]
    exact fun _ => False.elim
  cases' lt_or_eq_of_leₓ (one_le_iff_ne_zero.2 b0) with b1 b1
  ·
    refine' CNF_rec b0 _ _ o
    ·
      simp only [CNF_zero, List.Pairwiseₓ.nil, and_trueₓ]
      exact fun _ => False.elim
    intro o o0 H IH
    cases' IH with IH₁ IH₂
    simp only [CNF_ne_zero b0 o0, List.forall_mem_consₓ, List.pairwise_cons, IH₂, and_trueₓ]
    refine' ⟨⟨le_reflₓ _, fun p m => _⟩, fun p m => _⟩
    ·
      exact le_transₓ (IH₁ p m) (log_le_log _ $ le_of_ltₓ H)
    ·
      refine' lt_of_le_of_ltₓ (IH₁ p m) ((log_lt b1 _).2 _)
      ·
        rw [Ordinal.pos_iff_ne_zero]
        intro e
        rw [e] at m
        simpa only [CNF_zero] using m
      ·
        exact mod_lt _ (power_ne_zero _ b0)
  ·
    by_cases' o0 : o = 0
    ·
      simp only [o0, CNF_zero, List.Pairwiseₓ.nil, and_trueₓ]
      exact fun _ => False.elim
    rw [← b1, one_CNF o0]
    simp only [List.mem_singleton, log_not_one_lt (lt_irreflₓ _), forall_eq, le_reflₓ, true_andₓ,
      List.pairwise_singleton]

theorem CNF_pairwise (b := omega) o : (CNF b o).Pairwise fun p q => Prod.fst q < p.1 :=
  (CNF_pairwise_aux _ _).2

theorem CNF_fst_le_log (b := omega) o : ∀, ∀ p ∈ CNF b o, ∀, Prod.fst p ≤ log b o :=
  (CNF_pairwise_aux _ _).1

-- ././Mathport/Syntax/Translate/Basic.lean:477:2: warning: expanding binder collection (p «expr ∈ » CNF b o)
theorem CNF_fst_le (b := omega) o p (_ : p ∈ CNF b o) : Prod.fst p ≤ o :=
  le_transₓ (CNF_fst_le_log _ _ p H) (log_le_self _ _)

theorem CNF_snd_lt {b : Ordinal} (b1 : 1 < b) o : ∀, ∀ p ∈ CNF b o, ∀, Prod.snd p < b := by
  have b0 := ne_of_gtₓ (lt_transₓ zero_lt_one b1)
  refine'
    CNF_rec b0
      (fun _ => by
        rw [CNF_zero] <;> exact False.elim)
      _ o
  intro o o0 H IH
  simp only [CNF_ne_zero b0 o0, List.mem_cons_iff, forall_eq_or_imp, iff_true_intro IH, and_trueₓ]
  rw [div_lt (power_ne_zero _ b0), ← power_succ]
  exact lt_power_succ_log b1 _

theorem CNF_sorted (b := omega) o : ((CNF b o).map Prod.fst).Sorted (· > ·) := by
  rw [List.Sorted, List.pairwise_map] <;> exact CNF_pairwise b o

/-! ### Casting naturals into ordinals, compatibility with operations -/


@[simp]
theorem nat_cast_mul {m n : ℕ} : ((m*n : ℕ) : Ordinal) = m*n := by
  induction' n with n IH <;> [simp only [Nat.cast_zero, Nat.mul_zero, mul_zero],
    rw [Nat.mul_succ, Nat.cast_add, IH, Nat.cast_succ, mul_add_one]]

@[simp]
theorem nat_cast_power {m n : ℕ} : ((pow m n : ℕ) : Ordinal) = (m^n) := by
  induction' n with n IH <;> [simp only [pow_zeroₓ, Nat.cast_zero, power_zero, Nat.cast_one],
    rw [pow_succ'ₓ, nat_cast_mul, IH, Nat.cast_succ, ← succ_eq_add_one, power_succ]]

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
  (_root_.le_total m n).elim
    (fun h => by
      rw [tsub_eq_zero_iff_le.2 h, Ordinal.sub_eq_zero_iff_le.2 (nat_cast_le.2 h)] <;> rfl)
    fun h =>
    (add_left_cancelₓ n).1 $ by
      rw [← Nat.cast_add, add_tsub_cancel_of_le h, Ordinal.add_sub_cancel_of_le (nat_cast_le.2 h)]

@[simp]
theorem nat_cast_div {m n : ℕ} : ((m / n : ℕ) : Ordinal) = m / n :=
  if n0 : n = 0 then by
    simp only [n0, Nat.div_zeroₓ, Nat.cast_zero, div_zero]
  else
    have n0' := nat_cast_ne_zero.2 n0
    le_antisymmₓ
      (by
        rw [le_div n0', ← nat_cast_mul, nat_cast_le, mul_commₓ] <;> apply Nat.div_mul_le_selfₓ)
      (by
        rw [div_le n0', succ, ← Nat.cast_succ, ← nat_cast_mul, nat_cast_lt, mul_commₓ, ←
            Nat.div_lt_iff_lt_mulₓ _ _ (Nat.pos_of_ne_zeroₓ n0)] <;>
          apply Nat.lt_succ_selfₓ)

@[simp]
theorem nat_cast_mod {m n : ℕ} : ((m % n : ℕ) : Ordinal) = m % n := by
  rw [← add_left_cancelₓ (n*m / n), div_add_mod, ← nat_cast_div, ← nat_cast_mul, ← Nat.cast_add, Nat.div_add_mod]

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
  induction' n with n ih <;> [simp only [Nat.cast_zero, lift_zero], simp only [Nat.cast_succ, lift_add, ih, lift_one]]

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
  le_antisymmₓ (ord_le.2 $ le_reflₓ _) $
    le_of_forall_lt $ fun o h => by
      rcases Ordinal.lt_lift_iff.1 h with ⟨o, rfl, h'⟩
      rw [lt_ord, ← lift_card, ← lift_omega.{0, u}, lift_lt, ← typein_enum (· < ·) h']
      exact lt_omega_iff_fintype.2 ⟨Set.fintypeLtNat _⟩

@[simp]
theorem add_one_of_omega_le {c} (h : omega ≤ c) : (c+1) = c := by
  rw [add_commₓ, ← card_ord c, ← card_one, ← card_add, one_add_of_omega_le] <;> rwa [← ord_omega, ord_le_ord]

end Cardinal

namespace Ordinal

theorem lt_omega {o : Ordinal.{u}} : o < omega ↔ ∃ n : ℕ, o = n := by
  rw [← Cardinal.ord_omega, Cardinal.lt_ord, lt_omega] <;> simp only [card_eq_nat]

theorem nat_lt_omega (n : ℕ) : (n : Ordinal) < omega :=
  lt_omega.2 ⟨_, rfl⟩

theorem omega_pos : 0 < omega :=
  nat_lt_omega 0

theorem omega_ne_zero : omega ≠ 0 :=
  ne_of_gtₓ omega_pos

theorem one_lt_omega : 1 < omega := by
  simpa only [Nat.cast_one] using nat_lt_omega 1

theorem omega_is_limit : is_limit omega :=
  ⟨omega_ne_zero, fun o h =>
    let ⟨n, e⟩ := lt_omega.1 h
    by
    rw [e] <;> exact nat_lt_omega (n+1)⟩

theorem omega_le {o : Ordinal.{u}} : omega ≤ o ↔ ∀ n : ℕ, (n : Ordinal) ≤ o :=
  ⟨fun h n => le_transₓ (le_of_ltₓ (nat_lt_omega _)) h, fun H =>
    le_of_forall_lt $ fun a h =>
      let ⟨n, e⟩ := lt_omega.1 h
      by
      rw [e, ← succ_le] <;> exact H (n+1)⟩

theorem nat_lt_limit {o} (h : is_limit o) : ∀ n : ℕ, (n : Ordinal) < o
  | 0 => lt_of_le_of_neₓ (Ordinal.zero_le o) h.1.symm
  | n+1 => h.2 _ (nat_lt_limit n)

theorem omega_le_of_is_limit {o} (h : is_limit o) : omega ≤ o :=
  omega_le.2 $ fun n => le_of_ltₓ $ nat_lt_limit h n

theorem add_omega {a : Ordinal} (h : a < omega) : (a+omega) = omega := by
  rcases lt_omega.1 h with ⟨n, rfl⟩
  clear h
  induction' n with n IH
  ·
    rw [Nat.cast_zero, zero_addₓ]
  ·
    rw [Nat.cast_succ, add_assocₓ, one_add_of_omega_le (le_reflₓ _), IH]

theorem add_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : (a+b) < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← Nat.cast_add] <;> apply nat_lt_omega

theorem mul_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : (a*b) < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← nat_cast_mul] <;> apply nat_lt_omega

theorem is_limit_iff_omega_dvd {a : Ordinal} : is_limit a ↔ a ≠ 0 ∧ omega ∣ a := by
  refine' ⟨fun l => ⟨l.1, ⟨a / omega, le_antisymmₓ _ (mul_div_le _ _)⟩⟩, fun h => _⟩
  ·
    refine' (limit_le l).2 fun x hx => le_of_ltₓ _
    rw [← div_lt omega_ne_zero, ← succ_le, le_div omega_ne_zero, mul_succ, add_le_of_limit omega_is_limit]
    intro b hb
    rcases lt_omega.1 hb with ⟨n, rfl⟩
    exact le_transₓ (add_le_add_right (mul_div_le _ _) _) (le_of_ltₓ $ lt_sub.1 $ nat_lt_limit (sub_is_limit l hx) _)
  ·
    rcases h with ⟨a0, b, rfl⟩
    refine' mul_is_limit_left omega_is_limit (Ordinal.pos_iff_ne_zero.2 $ mt _ a0)
    intro e
    simp only [e, mul_zero]

local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

theorem power_lt_omega {a b : Ordinal} (ha : a < omega) (hb : b < omega) : (a^b) < omega :=
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← nat_cast_power] <;> apply nat_lt_omega

theorem add_omega_power {a b : Ordinal} (h : a < (omega^b)) : (a+omega^b) = (omega^b) := by
  refine' le_antisymmₓ _ (le_add_left _ _)
  revert h
  apply limit_rec_on b
  ·
    intro h
    rw [power_zero, ← succ_zero, lt_succ, Ordinal.le_zero] at h
    rw [h, zero_addₓ]
  ·
    intro b _ h
    rw [power_succ] at h
    rcases(lt_mul_of_limit omega_is_limit).1 h with ⟨x, xo, ax⟩
    refine' le_transₓ (add_le_add_right (le_of_ltₓ ax) _) _
    rw [power_succ, ← mul_addₓ, add_omega xo]
  ·
    intro b l IH h
    rcases(lt_power_of_limit omega_ne_zero l).1 h with ⟨x, xb, ax⟩
    refine' (((add_is_normal a).trans (power_is_normal one_lt_omega)).limit_le l).2 fun y yb => _
    let z := max x y
    have := IH z (max_ltₓ xb yb) (lt_of_lt_of_leₓ ax $ power_le_power_right omega_pos (le_max_leftₓ _ _))
    exact
      le_transₓ (add_le_add_left (power_le_power_right omega_pos (le_max_rightₓ _ _)) _)
        (le_transₓ this (power_le_power_right omega_pos $ le_of_ltₓ $ max_ltₓ xb yb))

theorem add_lt_omega_power {a b c : Ordinal} (h₁ : a < (omega^c)) (h₂ : b < (omega^c)) : (a+b) < (omega^c) := by
  rwa [← add_omega_power h₁, add_lt_add_iff_left]

theorem add_absorp {a b c : Ordinal} (h₁ : a < (omega^b)) (h₂ : (omega^b) ≤ c) : (a+c) = c := by
  rw [← Ordinal.add_sub_cancel_of_le h₂, ← add_assocₓ, add_omega_power h₁]

theorem add_absorp_iff {o : Ordinal} (o0 : 0 < o) : (∀, ∀ a < o, ∀, (a+o) = o) ↔ ∃ a, o = (omega^a) :=
  ⟨fun H =>
    ⟨log omega o, by
      refine' ((lt_or_eq_of_leₓ (power_log_le _ o0)).resolve_left $ fun h => _).symm
      have := H _ h
      have := lt_power_succ_log one_lt_omega o
      rw [power_succ, lt_mul_of_limit omega_is_limit] at this
      rcases this with ⟨a, ao, h'⟩
      rcases lt_omega.1 ao with ⟨n, rfl⟩
      clear ao
      revert h'
      apply not_lt_of_le
      suffices e : (((omega^log omega o)*↑n)+o) = o
      ·
        simpa only [e] using le_add_right ((omega^log omega o)*↑n) o
      induction' n with n IH
      ·
        simp only [Nat.cast_zero, mul_zero, zero_addₓ]
      simp only [Nat.cast_succ, mul_add_one, add_assocₓ, this, IH]⟩,
    fun ⟨b, e⟩ => e.symm ▸ fun a => add_omega_power⟩

theorem add_mul_limit_aux {a b c : Ordinal} (ba : (b+a) = a) (l : is_limit c)
    (IH : ∀, ∀ c' < c, ∀, ((a+b)*succ c') = (a*succ c')+b) : ((a+b)*c) = a*c :=
  le_antisymmₓ
    ((mul_le_of_limit l).2 $ fun c' h => by
      apply le_transₓ (mul_le_mul_left _ (le_of_ltₓ $ lt_succ_self _))
      rw [IH _ h]
      apply le_transₓ (add_le_add_left _ _)
      ·
        rw [← mul_succ]
        exact mul_le_mul_left _ (succ_le.2 $ l.2 _ h)
      ·
        rw [← ba]
        exact le_add_right _ _)
    (mul_le_mul_right _ (le_add_right _ _))

theorem add_mul_succ {a b : Ordinal} c (ba : (b+a) = a) : ((a+b)*succ c) = (a*succ c)+b := by
  apply limit_rec_on c
  ·
    simp only [succ_zero, mul_oneₓ]
  ·
    intro c IH
    rw [mul_succ, IH, ← add_assocₓ, add_assocₓ _ b, ba, ← mul_succ]
  ·
    intro c l IH
    have := add_mul_limit_aux ba l IH
    rw [mul_succ, add_mul_limit_aux ba l IH, mul_succ, add_assocₓ]

theorem add_mul_limit {a b c : Ordinal} (ba : (b+a) = a) (l : is_limit c) : ((a+b)*c) = a*c :=
  add_mul_limit_aux ba l fun c' _ => add_mul_succ c' ba

theorem mul_omega {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : (a*omega) = omega :=
  le_antisymmₓ ((mul_le_of_limit omega_is_limit).2 $ fun b hb => le_of_ltₓ (mul_lt_omega ha hb))
    (by
      simpa only [one_mulₓ] using mul_le_mul_right omega (one_le_iff_pos.2 a0))

theorem mul_lt_omega_power {a b c : Ordinal} (c0 : 0 < c) (ha : a < (omega^c)) (hb : b < omega) : (a*b) < (omega^c) :=
  by
  rcases zero_or_succ_or_limit c with (rfl | ⟨c, rfl⟩ | l)
  ·
    exact (lt_irreflₓ _).elim c0
  ·
    rw [power_succ] at ha
    rcases((mul_is_normal $ power_pos _ omega_pos).limit_lt omega_is_limit).1 ha with ⟨n, hn, an⟩
    refine' lt_of_le_of_ltₓ (mul_le_mul_right _ (le_of_ltₓ an)) _
    rw [power_succ, mul_assocₓ, mul_lt_mul_iff_left (power_pos _ omega_pos)]
    exact mul_lt_omega hn hb
  ·
    rcases((power_is_normal one_lt_omega).limit_lt l).1 ha with ⟨x, hx, ax⟩
    refine' lt_of_le_of_ltₓ (mul_le_mul (le_of_ltₓ ax) (le_of_ltₓ hb)) _
    rw [← power_succ, power_lt_power_iff_right one_lt_omega]
    exact l.2 _ hx

theorem mul_omega_dvd {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : ∀ {b}, omega ∣ b → (a*b) = b
  | _, ⟨b, rfl⟩ => by
    rw [← mul_assocₓ, mul_omega a0 ha]

theorem mul_omega_power_power {a b : Ordinal} (a0 : 0 < a) (h : a < (omega^omega^b)) :
    (a*omega^omega^b) = (omega^omega^b) := by
  by_cases' b0 : b = 0
  ·
    rw [b0, power_zero, power_one] at h⊢
    exact mul_omega a0 h
  refine'
    le_antisymmₓ _
      (by
        simpa only [one_mulₓ] using mul_le_mul_right (omega^omega^b) (one_le_iff_pos.2 a0))
  rcases(lt_power_of_limit omega_ne_zero (power_is_limit_left omega_is_limit b0)).1 h with ⟨x, xb, ax⟩
  refine' le_transₓ (mul_le_mul_right _ (le_of_ltₓ ax)) _
  rw [← power_add, add_omega_power xb]

theorem power_omega {a : Ordinal} (a1 : 1 < a) (h : a < omega) : (a^omega) = omega :=
  le_antisymmₓ
    ((power_le_of_limit (one_le_iff_ne_zero.1 $ le_of_ltₓ a1) omega_is_limit).2 fun b hb =>
      le_of_ltₓ (power_lt_omega h hb))
    (le_power_self _ a1)

/-! ### Fixed points of normal functions -/


/--  The next fixed point function, the least fixed point of the
  normal function `f` above `a`. -/
def nfp (f : Ordinal → Ordinal) (a : Ordinal) :=
  sup fun n : ℕ => (f^[n]) a

theorem iterate_le_nfp f a n : (f^[n]) a ≤ nfp f a :=
  le_sup _ n

theorem le_nfp_self f a : a ≤ nfp f a :=
  iterate_le_nfp f a 0

theorem is_normal.lt_nfp {f} (H : is_normal f) {a b} : f b < nfp f a ↔ b < nfp f a :=
  lt_sup.trans $
    Iff.trans
      (by
        exact
          ⟨fun ⟨n, h⟩ => ⟨n, lt_of_le_of_ltₓ (H.le_self _) h⟩, fun ⟨n, h⟩ =>
            ⟨n+1, by
              rw [iterate_succ'] <;> exact H.lt_iff.2 h⟩⟩)
      lt_sup.symm

theorem is_normal.nfp_le {f} (H : is_normal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 H.lt_nfp

theorem is_normal.nfp_le_fp {f} (H : is_normal f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  sup_le.2 $ fun i => by
    induction' i with i IH generalizing a
    ·
      exact ab
    exact IH (le_transₓ (H.le_iff.2 ab) h)

theorem is_normal.nfp_fp {f} (H : is_normal f) a : f (nfp f a) = nfp f a := by
  refine' le_antisymmₓ _ (H.le_self _)
  cases' le_or_ltₓ (f a) a with aa aa
  ·
    rwa [le_antisymmₓ (H.nfp_le_fp (le_reflₓ _) aa) (le_nfp_self _ _)]
  rcases zero_or_succ_or_limit (nfp f a) with (e | ⟨b, e⟩ | l)
  ·
    refine' @le_transₓ _ _ _ (f a) _ (H.le_iff.2 _) (iterate_le_nfp f a 1)
    simp only [e, Ordinal.zero_le]
  ·
    have : f b < nfp f a :=
      H.lt_nfp.2
        (by
          simp only [e, lt_succ_self])
    rw [e, lt_succ] at this
    have ab : a ≤ b := by
      rw [← lt_succ, ← e]
      exact lt_of_lt_of_leₓ aa (iterate_le_nfp f a 1)
    refine' le_transₓ (H.le_iff.2 (H.nfp_le_fp ab this)) (le_transₓ this (le_of_ltₓ _))
    simp only [e, lt_succ_self]
  ·
    exact (H.2 _ l _).2 fun b h => le_of_ltₓ (H.lt_nfp.2 h)

theorem is_normal.le_nfp {f} (H : is_normal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨le_transₓ (H.le_self _), fun h => by
    simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : Ordinal → Ordinal} {a} (h : f a = a) : nfp f a = a :=
  le_antisymmₓ
    (sup_le.mpr $ fun i => by
      rw [iterate_fixed h])
    (le_nfp_self f a)

/--  The derivative of a normal function `f` is
  the sequence of fixed points of `f`. -/
def deriv (f : Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  limit_rec_on o (nfp f 0) (fun a IH => nfp f (succ IH)) fun a l => bsup.{u, u} a

@[simp]
theorem deriv_zero f : deriv f 0 = nfp f 0 :=
  limit_rec_on_zero _ _ _

@[simp]
theorem deriv_succ f o : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  limit_rec_on_succ _ _ _ _

theorem deriv_limit f {o} : is_limit o → deriv f o = bsup.{u, u} o fun a _ => deriv f a :=
  limit_rec_on_limit _ _ _ _

theorem deriv_is_normal f : is_normal (deriv f) :=
  ⟨fun o => by
    rw [deriv_succ, ← succ_le] <;> apply le_nfp_self, fun o l a => by
    rw [deriv_limit _ l, bsup_le]⟩

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `is_normal.deriv_fp [])
  (Command.declSig
   [(Term.implicitBinder "{" [`f] [] "}")
    (Term.explicitBinder "(" [`H] [":" (Term.app `is_normal [`f])] [] ")")
    (Term.simpleBinder [`o] [])]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `f [(Term.app (Term.explicitUniv `deriv ".{" [`u] "}") [`f `o])])
     "="
     (Term.app `deriv [`f `o]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" (Term.app `limit_rec_on [`o])) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `deriv_zero) "," (Tactic.rwRule [] `H.nfp_fp)] "]")
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`o `ih]) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `deriv_succ) "," (Tactic.rwRule [] `H.nfp_fp)] "]")
              [])
             [])])))
        [])
       (group (Tactic.intro "intro" [`o `l `IH]) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `deriv_limit [(Term.hole "_") `l]))
           ","
           (Tactic.rwRule
            []
            (Term.app
             (Term.explicitUniv `is_normal.bsup ".{" [`u "," `u "," `u] "}")
             [`H (Term.hole "_") (Term.proj `l "." (fieldIdx "1"))]))]
          "]")
         [])
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `eq_of_forall_ge_iff
          [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.hole "_")))]))
        [])
       (group
        (Tactic.simp
         "simp"
         ["("
          "config"
          ":="
          (Term.structInst
           "{"
           []
           [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
           (Term.optEllipsis [])
           []
           "}")
          ")"]
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `bsup_le) "," (Tactic.simpLemma [] [] `IH)] "]"]
         [])
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" (Term.app `limit_rec_on [`o])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `deriv_zero) "," (Tactic.rwRule [] `H.nfp_fp)] "]")
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`o `ih]) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `deriv_succ) "," (Tactic.rwRule [] `H.nfp_fp)] "]")
             [])
            [])])))
       [])
      (group (Tactic.intro "intro" [`o `l `IH]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `deriv_limit [(Term.hole "_") `l]))
          ","
          (Tactic.rwRule
           []
           (Term.app
            (Term.explicitUniv `is_normal.bsup ".{" [`u "," `u "," `u] "}")
            [`H (Term.hole "_") (Term.proj `l "." (fieldIdx "1"))]))]
         "]")
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `eq_of_forall_ge_iff
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.simp
        "simp"
        ["("
         "config"
         ":="
         (Term.structInst
          "{"
          []
          [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
          (Term.optEllipsis [])
          []
          "}")
         ")"]
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `bsup_le) "," (Tactic.simpLemma [] [] `IH)] "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   ["("
    "config"
    ":="
    (Term.structInst
     "{"
     []
     [(group (Term.structInstField (Term.structInstLVal `contextual []) ":=" `Bool.true._@._internal._hyg.0) [])]
     (Term.optEllipsis [])
     []
     "}")
    ")"]
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `bsup_le) "," (Tactic.simpLemma [] [] `IH)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IH
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `bsup_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«)»', expected 'Lean.Parser.Tactic.discharger'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  is_normal.deriv_fp
  { f } ( H : is_normal f ) o : f deriv .{ u } f o = deriv f o
  :=
    by
      apply limit_rec_on o
        · rw [ deriv_zero , H.nfp_fp ]
        · intro o ih rw [ deriv_succ , H.nfp_fp ]
        intro o l IH
        rw [ deriv_limit _ l , is_normal.bsup .{ u , u , u } H _ l . 1 ]
        refine' eq_of_forall_ge_iff fun c => _
        simp ( config := { contextual := Bool.true._@._internal._hyg.0 } ) only [ bsup_le , IH ]

theorem is_normal.fp_iff_deriv {f} (H : is_normal f) {a} : f a ≤ a ↔ ∃ o, a = deriv f o :=
  ⟨fun ha => by
    suffices : ∀ o _ : a ≤ deriv f o, ∃ o, a = deriv f o
    exact this a ((deriv_is_normal _).le_self _)
    intro o
    apply limit_rec_on o
    ·
      intro h₁
      refine' ⟨0, le_antisymmₓ h₁ _⟩
      rw [deriv_zero]
      exact H.nfp_le_fp (Ordinal.zero_le _) ha
    ·
      intro o IH h₁
      cases le_or_ltₓ a (deriv f o)
      ·
        exact IH h
      refine' ⟨succ o, le_antisymmₓ h₁ _⟩
      rw [deriv_succ]
      exact H.nfp_le_fp (succ_le.2 h) ha
    ·
      intro o l IH h₁
      cases eq_or_lt_of_le h₁
      ·
        exact ⟨_, h⟩
      rw [deriv_limit _ l, ← not_leₓ, bsup_le, not_ball] at h
      exact
        let ⟨o', h, hl⟩ := h
        IH o' h (le_of_not_leₓ hl),
    fun ⟨o, e⟩ => e.symm ▸ le_of_eqₓ (H.deriv_fp _)⟩

end Ordinal

