/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir
-/
import Mathbin.Order.Filter.Basic
import Mathbin.Algebra.Module.Pi

/-!
# Germ of a function at a filter

The germ of a function `f : α → β` at a filter `l : filter α` is the equivalence class of `f`
with respect to the equivalence relation `eventually_eq l`: `f ≈ g` means `∀ᶠ x in l, f x = g x`.

## Main definitions

We define

* `germ l β` to be the space of germs of functions `α → β` at a filter `l : filter α`;
* coercion from `α → β` to `germ l β`: `(f : germ l β)` is the germ of `f : α → β`
  at `l : filter α`; this coercion is declared as `has_coe_t`, so it does not require an explicit
  up arrow `↑`;
* coercion from `β` to `germ l β`: `(↑c : germ l β)` is the germ of the constant function
  `λ x:α, c` at a filter `l`; this coercion is declared as `has_lift_t`, so it requires an explicit
  up arrow `↑`, see [TPiL][TPiL_coe] for details.
* `map (F : β → γ) (f : germ l β)` to be the composition of a function `F` and a germ `f`;
* `map₂ (F : β → γ → δ) (f : germ l β) (g : germ l γ)` to be the germ of `λ x, F (f x) (g x)`
  at `l`;
* `f.tendsto lb`: we say that a germ `f : germ l β` tends to a filter `lb` if its representatives
  tend to `lb` along `l`;
* `f.comp_tendsto g hg` and `f.comp_tendsto' g hg`: given `f : germ l β` and a function
  `g : γ → α` (resp., a germ `g : germ lc α`), if `g` tends to `l` along `lc`, then the composition
  `f ∘ g` is a well-defined germ at `lc`;
* `germ.lift_pred`, `germ.lift_rel`: lift a predicate or a relation to the space of germs:
  `(f : germ l β).lift_pred p` means `∀ᶠ x in l, p (f x)`, and similarly for a relation.
[TPiL_coe]: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes

We also define `map (F : β → γ) : germ l β → germ l γ` sending each germ `f` to `F ∘ f`.

For each of the following structures we prove that if `β` has this structure, then so does
`germ l β`:

* one-operation algebraic structures up to `comm_group`;
* `mul_zero_class`, `distrib`, `semiring`, `comm_semiring`, `ring`, `comm_ring`;
* `mul_action`, `distrib_mul_action`, `module`;
* `preorder`, `partial_order`, and `lattice` structures, as well as `bounded_order`;
* `ordered_cancel_comm_monoid` and `ordered_cancel_add_comm_monoid`.

## Tags

filter, germ
-/


namespace Filter

variable {α β γ δ : Type _} {l : Filter α} {f g h : α → β}

theorem const_eventually_eq' [NeBot l] {a b : β} : (∀ᶠ x in l, a = b) ↔ a = b :=
  eventually_const

theorem const_eventually_eq [NeBot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventually_eq' _ _ _ _ a b

theorem EventuallyEq.comp_tendsto {f' : α → β} (H : f =ᶠ[l] f') {g : γ → α} {lc : Filter γ} (hg : Tendsto g lc l) :
    f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.Eventually H

/-- Setoid used to define the space of germs. -/
def germSetoid (l : Filter α) (β : Type _) : Setoid (α → β) where
  R := EventuallyEq l
  iseqv := ⟨EventuallyEq.refl _, fun _ _ => EventuallyEq.symm, fun _ _ _ => EventuallyEq.trans⟩

/-- The space of germs of functions `α → β` at a filter `l`. -/
def Germ (l : Filter α) (β : Type _) : Type _ :=
  Quotient (germSetoid l β)

/-- Setoid used to define the filter product. This is a dependent version of
  `filter.germ_setoid`. -/
def productSetoid (l : Filter α) (ε : α → Type _) : Setoid (∀ a, ε a) where
  R f g := ∀ᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => eventually_of_forall fun _ => rfl, fun _ _ h => h.mono fun _ => Eq.symm, fun x y z h1 h2 =>
      h1.congr (h2.mono fun x hx => hx ▸ Iff.rfl)⟩

/-- The filter product `Π (a : α), ε a` at a filter `l`. This is a dependent version of
  `filter.germ`. -/
@[protected]
def Product (l : Filter α) (ε : α → Type _) : Type _ :=
  Quotient (productSetoid l ε)

namespace Product

variable {ε : α → Type _}

instance : CoeTC (∀ a, ε a) (l.product ε) :=
  ⟨Quotient.mk'⟩

instance [∀ a, Inhabited (ε a)] : Inhabited (l.product ε) :=
  ⟨(↑fun a => (default : ε a) : l.product ε)⟩

end Product

namespace Germ

instance : CoeTC (α → β) (Germ l β) :=
  ⟨Quotient.mk'⟩

instance : HasLiftT β (Germ l β) :=
  ⟨fun c => ↑fun x : α => c⟩

@[simp]
theorem quot_mk_eq_coe (l : Filter α) (f : α → β) : Quot.mk _ f = (f : Germ l β) :=
  rfl

@[simp]
theorem mk'_eq_coe (l : Filter α) (f : α → β) : Quotient.mk' f = (f : Germ l β) :=
  rfl

@[elab_as_elim]
theorem induction_on (f : Germ l β) {p : Germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
  Quotient.induction_on' f h

@[elab_as_elim]
theorem induction_on₂ (f : Germ l β) (g : Germ l γ) {p : Germ l β → Germ l γ → Prop}
    (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
  Quotient.induction_on₂' f g h

@[elab_as_elim]
theorem induction_on₃ (f : Germ l β) (g : Germ l γ) (h : Germ l δ) {p : Germ l β → Germ l γ → Germ l δ → Prop}
    (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) : p f g h :=
  Quotient.induction_on₃' f g h H

/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `germ l β` to `germ lc δ`. -/
def map' {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) : Germ l β → Germ lc δ :=
  Quotient.map' F hF

/-- Given a germ `f : germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
def liftOn {γ : Sort _} (f : Germ l β) (F : (α → β) → γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F) : γ :=
  Quotient.liftOn' f F hF

@[simp]
theorem map'_coe {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) (f : α → β) :
    map' F hF f = F f :=
  rfl

@[simp, norm_cast]
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g :=
  Quotient.eq'

alias coe_eq ↔ _ _root_.filter.eventually_eq.germ_eq

/-- Lift a function `β → γ` to a function `germ l β → germ l γ`. -/
def map (op : β → γ) : Germ l β → Germ l γ :=
  (map' ((· ∘ ·) op)) fun f g H => H.mono fun x H => congr_arg op H

@[simp]
theorem map_coe (op : β → γ) (f : α → β) : map op (f : Germ l β) = op ∘ f :=
  rfl

@[simp]
theorem map_id : map id = (id : Germ l β → Germ l β) := by
  ext ⟨f⟩
  rfl

theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : Germ l β) : map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  (induction_on f) fun f => rfl

/-- Lift a binary function `β → γ → δ` to a function `germ l β → germ l γ → germ l δ`. -/
def map₂ (op : β → γ → δ) : Germ l β → Germ l γ → Germ l δ :=
  (Quotient.map₂' fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
    Hg.mp <| Hf.mono fun x Hf Hg => by simp only [Hf, Hg]

@[simp]
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) : map₂ op (f : Germ l β) g = fun x => op (f x) (g x) :=
  rfl

/-- A germ at `l` of maps from `α` to `β` tends to `lb : filter β` if it is represented by a map
which tends to `lb` along `l`. -/
protected def Tendsto (f : Germ l β) (lb : Filter β) : Prop :=
  (liftOn f fun f => Tendsto f l lb) fun f g H => propext (tendsto_congr' H)

@[simp, norm_cast]
theorem coe_tendsto {f : α → β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Tendsto f l lb :=
  Iff.rfl

alias coe_tendsto ↔ _ _root_.filter.tendsto.germ_tendsto

/-- Given two germs `f : germ l β`, and `g : germ lc α`, where `l : filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendsto l) : Germ lc β :=
  (liftOn f fun f => g.map f) fun f₁ f₂ hF => ((induction_on g) fun g hg => coe_eq.2 <| hg.Eventually hF) hg

@[simp]
theorem coe_comp_tendsto' (f : α → β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f :=
  rfl

/-- Given a germ `f : germ l β` and a function `g : γ → α`, where `l : filter α`, if `g` tends
to `l` along `lc : filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ → α) (hg : Tendsto g lc l) : Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto

@[simp]
theorem coe_comp_tendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (f : Germ l β).comp_tendsto g hg = f ∘ g :=
  rfl

@[simp]
theorem comp_tendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.comp_tendsto g hg :=
  rfl

@[simp, norm_cast]
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans <| const_eventually_eq

@[simp]
theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : Germ l β).map f = ↑(f a) :=
  rfl

@[simp]
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) : map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  rfl

@[simp]
theorem const_comp_tendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).comp_tendsto g hg = ↑b :=
  rfl

@[simp]
theorem const_comp_tendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (↑b : Germ l β).compTendsto' g hg = ↑b :=
  induction_on g (fun _ _ => rfl) hg

/-- Lift a predicate on `β` to `germ l β`. -/
def LiftPred (p : β → Prop) (f : Germ l β) : Prop :=
  (liftOn f fun f => ∀ᶠ x in l, p (f x)) fun f g H => propext <| eventually_congr <| H.mono fun x hx => hx ▸ Iff.rfl

@[simp]
theorem lift_pred_coe {p : β → Prop} {f : α → β} : LiftPred p (f : Germ l β) ↔ ∀ᶠ x in l, p (f x) :=
  Iff.rfl

theorem lift_pred_const {p : β → Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  eventually_of_forall fun y => hx

@[simp]
theorem lift_pred_const_iff [NeBot l] {p : β → Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)

/-- Lift a relation `r : β → γ → Prop` to `germ l β → germ l γ → Prop`. -/
def LiftRel (r : β → γ → Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  (Quotient.liftOn₂' f g fun f g => ∀ᶠ x in l, r (f x) (g x)) fun f g f' g' Hf Hg =>
    propext <| eventually_congr <| Hg.mp <| Hf.mono fun x hf hg => hf ▸ hg ▸ Iff.rfl

@[simp]
theorem lift_rel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    LiftRel r (f : Germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
  Iff.rfl

theorem lift_rel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) : LiftRel r (↑x : Germ l β) ↑y :=
  eventually_of_forall fun _ => h

@[simp]
theorem lift_rel_const_iff [NeBot l] {r : β → γ → Prop} {x : β} {y : γ} : LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  @eventually_const _ _ _ (r x y)

instance [Inhabited β] : Inhabited (Germ l β) :=
  ⟨↑(default : β)⟩

section Monoid

variable {M : Type _} {G : Type _}

@[to_additive]
instance [Mul M] : Mul (Germ l M) :=
  ⟨map₂ (· * ·)⟩

@[simp, norm_cast, to_additive]
theorem coe_mul [Mul M] (f g : α → M) : ↑(f * g) = (f * g : Germ l M) :=
  rfl

@[to_additive]
instance [One M] : One (Germ l M) :=
  ⟨↑(1 : M)⟩

@[simp, norm_cast, to_additive]
theorem coe_one [One M] : ↑(1 : α → M) = (1 : Germ l M) :=
  rfl

@[to_additive]
instance [Semigroup M] : Semigroup (Germ l M) :=
  Function.Surjective.semigroup coe (surjective_quot_mk _) fun a b => coe_mul a b

@[to_additive]
instance [CommSemigroup M] : CommSemigroup (Germ l M) :=
  Function.Surjective.commSemigroup coe (surjective_quot_mk _) fun a b => coe_mul a b

@[to_additive AddLeftCancelSemigroup]
instance [LeftCancelSemigroup M] : LeftCancelSemigroup (Germ l M) :=
  { Germ.semigroup with mul := (· * ·),
    mul_left_cancel := fun f₁ f₂ f₃ =>
      (induction_on₃ f₁ f₂ f₃) fun f₁ f₂ f₃ H => coe_eq.2 ((coe_eq.1 H).mono fun x => mul_left_cancel) }

@[to_additive AddRightCancelSemigroup]
instance [RightCancelSemigroup M] : RightCancelSemigroup (Germ l M) :=
  { Germ.semigroup with mul := (· * ·),
    mul_right_cancel := fun f₁ f₂ f₃ =>
      (induction_on₃ f₁ f₂ f₃) fun f₁ f₂ f₃ H => coe_eq.2 <| (coe_eq.1 H).mono fun x => mul_right_cancel }

instance [HasVadd M G] : HasVadd M (Germ l G) :=
  ⟨fun n => map ((· +ᵥ ·) n)⟩

@[to_additive]
instance [HasSmul M G] : HasSmul M (Germ l G) :=
  ⟨fun n => map ((· • ·) n)⟩

@[to_additive HasSmul]
instance [Pow G M] : Pow (Germ l G) M :=
  ⟨fun f n => map (· ^ n) f⟩

@[simp, norm_cast, to_additive]
theorem coe_smul [HasSmul M G] (n : M) (f : α → G) : ↑(n • f) = (n • f : Germ l G) :=
  rfl

@[simp, norm_cast, to_additive]
theorem const_smul [HasSmul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • ↑a :=
  rfl

@[simp, norm_cast, to_additive coe_smul]
theorem coe_pow [Pow G M] (f : α → G) (n : M) : ↑(f ^ n) = (f ^ n : Germ l G) :=
  rfl

@[simp, norm_cast, to_additive const_smul]
theorem const_pow [Pow G M] (a : G) (n : M) : (↑(a ^ n) : Germ l G) = ↑a ^ n :=
  rfl

@[to_additive]
instance [Monoid M] : Monoid (Germ l M) :=
  Function.Surjective.monoid coe (surjective_quot_mk _) rfl (fun _ _ => rfl) fun _ _ => rfl

/-- Coercion from functions to germs as a monoid homomorphism. -/
@[to_additive "Coercion from functions to germs as an additive monoid homomorphism."]
def coeMulHom [Monoid M] (l : Filter α) : (α → M) →* Germ l M :=
  ⟨coe, rfl, fun f g => rfl⟩

@[simp, to_additive]
theorem coe_coe_mul_hom [Monoid M] : (coeMulHom l : (α → M) → Germ l M) = coe :=
  rfl

@[to_additive]
instance [CommMonoid M] : CommMonoid (Germ l M) :=
  { Germ.commSemigroup, Germ.monoid with mul := (· * ·), one := 1 }

instance [AddMonoidWithOne M] : AddMonoidWithOne (Germ l M) :=
  { Germ.hasOne, Germ.addMonoid with natCast := fun n => ↑(n : M), nat_cast_zero := congr_arg coe Nat.cast_zero,
    nat_cast_succ := fun n => congr_arg coe (Nat.cast_succ _) }

@[to_additive]
instance [Inv G] : Inv (Germ l G) :=
  ⟨map Inv.inv⟩

@[simp, norm_cast, to_additive]
theorem coe_inv [Inv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : Germ l G) :=
  rfl

@[simp, norm_cast, to_additive]
theorem const_inv [Inv G] (a : G) : (↑a⁻¹ : Germ l G) = (↑a)⁻¹ :=
  rfl

@[to_additive]
instance [Div M] : Div (Germ l M) :=
  ⟨map₂ (· / ·)⟩

@[simp, norm_cast, to_additive]
theorem coe_div [Div M] (f g : α → M) : ↑(f / g) = (f / g : Germ l M) :=
  rfl

@[simp, norm_cast, to_additive]
theorem const_div [Div M] (a b : M) : (↑(a / b) : Germ l M) = ↑a / ↑b :=
  rfl

@[to_additive SubNegMonoid]
instance [DivInvMonoid G] : DivInvMonoid (Germ l G) :=
  Function.Surjective.divInvMonoid coe (surjective_quot_mk _) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance [Group G] : Group (Germ l G) :=
  { Germ.divInvMonoid with mul := (· * ·), one := 1,
    mul_left_inv := by
      rintro ⟨f⟩
      exact congr_arg (Quot.mk _) (mul_left_inv f) }

@[to_additive]
instance [CommGroup G] : CommGroup (Germ l G) :=
  { Germ.group, Germ.commMonoid with mul := (· * ·), one := 1, inv := Inv.inv }

end Monoid

section Ring

variable {R : Type _}

instance nontrivial [Nontrivial R] [NeBot l] : Nontrivial (Germ l R) :=
  let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩

instance [MulZeroClass R] : MulZeroClass (Germ l R) where
  zero := 0
  mul := (· * ·)
  mul_zero f :=
    (induction_on f) fun f => by
      norm_cast
      rw [mul_zero]
  zero_mul f :=
    (induction_on f) fun f => by
      norm_cast
      rw [zero_mul]

instance [Distrib R] : Distrib (Germ l R) where
  mul := (· * ·)
  add := (· + ·)
  left_distrib f g h :=
    (induction_on₃ f g h) fun f g h => by
      norm_cast
      rw [left_distrib]
  right_distrib f g h :=
    (induction_on₃ f g h) fun f g h => by
      norm_cast
      rw [right_distrib]

instance [Semiring R] : Semiring (Germ l R) :=
  { Germ.addCommMonoid, Germ.monoid, Germ.distrib, Germ.mulZeroClass, Germ.addMonoidWithOne with }

/-- Coercion `(α → R) → germ l R` as a `ring_hom`. -/
def coeRingHom [Semiring R] (l : Filter α) : (α → R) →+* Germ l R :=
  { (coeMulHom l : _ →* Germ l R), (coeAddHom l : _ →+ Germ l R) with toFun := coe }

@[simp]
theorem coe_coe_ring_hom [Semiring R] : (coeRingHom l : (α → R) → Germ l R) = coe :=
  rfl

instance [Ring R] : Ring (Germ l R) :=
  { Germ.addCommGroup, Germ.semiring with }

instance [CommSemiring R] : CommSemiring (Germ l R) :=
  { Germ.semiring, Germ.commMonoid with }

instance [CommRing R] : CommRing (Germ l R) :=
  { Germ.ring, Germ.commMonoid with }

end Ring

section Module

variable {M N R : Type _}

@[to_additive]
instance hasSmul' [HasSmul M β] : HasSmul (Germ l M) (Germ l β) :=
  ⟨map₂ (· • ·)⟩

@[simp, norm_cast, to_additive]
theorem coe_smul' [HasSmul M β] (c : α → M) (f : α → β) : ↑(c • f) = (c : Germ l M) • (f : Germ l β) :=
  rfl

@[to_additive]
instance [Monoid M] [MulAction M β] : MulAction M (Germ l β) where
  one_smul f :=
    (induction_on f) fun f => by
      norm_cast
      simp only [one_smul]
  mul_smul c₁ c₂ f :=
    (induction_on f) fun f => by
      norm_cast
      simp only [mul_smul]

@[to_additive]
instance mulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β) where
  one_smul f := (induction_on f) fun f => by simp only [← coe_one, ← coe_smul', one_smul]
  mul_smul c₁ c₂ f :=
    (induction_on₃ c₁ c₂ f) fun c₁ c₂ f => by
      norm_cast
      simp only [mul_smul]

instance [Monoid M] [AddMonoid N] [DistribMulAction M N] : DistribMulAction M (Germ l N) where
  smul_add c f g :=
    (induction_on₂ f g) fun f g => by
      norm_cast
      simp only [smul_add]
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]

instance distribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction (Germ l M) (Germ l N) where
  smul_add c f g :=
    (induction_on₃ c f g) fun c f g => by
      norm_cast
      simp only [smul_add]
  smul_zero c := (induction_on c) fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]

instance [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Germ l M) where
  add_smul c₁ c₂ f :=
    (induction_on f) fun f => by
      norm_cast
      simp only [add_smul]
  zero_smul f :=
    (induction_on f) fun f => by
      norm_cast
      simp only [zero_smul, coe_zero]

instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module (Germ l R) (Germ l M) where
  add_smul c₁ c₂ f :=
    (induction_on₃ c₁ c₂ f) fun c₁ c₂ f => by
      norm_cast
      simp only [add_smul]
  zero_smul f := (induction_on f) fun f => by simp only [← coe_zero, ← coe_smul', zero_smul]

end Module

instance [LE β] : LE (Germ l β) :=
  ⟨LiftRel (· ≤ ·)⟩

theorem le_def [LE β] : ((· ≤ ·) : Germ l β → Germ l β → Prop) = LiftRel (· ≤ ·) :=
  rfl

@[simp]
theorem coe_le [LE β] : (f : Germ l β) ≤ g ↔ f ≤ᶠ[l] g :=
  Iff.rfl

theorem coe_nonneg [LE β] [Zero β] {f : α → β} : 0 ≤ (f : Germ l β) ↔ ∀ᶠ x in l, 0 ≤ f x :=
  Iff.rfl

theorem const_le [LE β] {x y : β} : x ≤ y → (↑x : Germ l β) ≤ ↑y :=
  lift_rel_const

@[simp, norm_cast]
theorem const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) ≤ ↑y ↔ x ≤ y :=
  lift_rel_const_iff

instance [Preorder β] : Preorder (Germ l β) where
  le := (· ≤ ·)
  le_refl f := induction_on f <| EventuallyLe.refl l
  le_trans f₁ f₂ f₃ := (induction_on₃ f₁ f₂ f₃) fun f₁ f₂ f₃ => EventuallyLe.trans

instance [PartialOrder β] : PartialOrder (Germ l β) :=
  { Germ.preorder with le := (· ≤ ·),
    le_antisymm := fun f g => (induction_on₂ f g) fun f g h₁ h₂ => (EventuallyLe.antisymm h₁ h₂).germ_eq }

instance [HasBot β] : HasBot (Germ l β) :=
  ⟨↑(⊥ : β)⟩

instance [HasTop β] : HasTop (Germ l β) :=
  ⟨↑(⊤ : β)⟩

@[simp, norm_cast]
theorem const_bot [HasBot β] : (↑(⊥ : β) : Germ l β) = ⊥ :=
  rfl

@[simp, norm_cast]
theorem const_top [HasTop β] : (↑(⊤ : β) : Germ l β) = ⊤ :=
  rfl

instance [LE β] [OrderBot β] : OrderBot (Germ l β) where
  bot := ⊥
  bot_le f := (induction_on f) fun f => eventually_of_forall fun x => bot_le

instance [LE β] [OrderTop β] : OrderTop (Germ l β) where
  top := ⊤
  le_top f := (induction_on f) fun f => eventually_of_forall fun x => le_top

instance [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) :=
  { Germ.orderBot, Germ.orderTop with }

end Germ

end Filter

