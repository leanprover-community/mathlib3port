/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir
-/
import Mathbin.Order.Filter.Basic
import Mathbin.Algebra.Module.Pi

#align_import order.filter.germ from "leanprover-community/mathlib"@"e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b"

/-!
# Germ of a function at a filter

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print Filter.const_eventuallyEq' /-
theorem const_eventuallyEq' [NeBot l] {a b : β} : (∀ᶠ x in l, a = b) ↔ a = b :=
  eventually_const
#align filter.const_eventually_eq' Filter.const_eventuallyEq'
-/

#print Filter.const_eventuallyEq /-
theorem const_eventuallyEq [NeBot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventuallyEq' _ _ _ _ a b
#align filter.const_eventually_eq Filter.const_eventuallyEq
-/

#print Filter.EventuallyEq.comp_tendsto /-
theorem EventuallyEq.comp_tendsto {f' : α → β} (H : f =ᶠ[l] f') {g : γ → α} {lc : Filter γ}
    (hg : Tendsto g lc l) : f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.Eventually H
#align filter.eventually_eq.comp_tendsto Filter.EventuallyEq.comp_tendsto
-/

#print Filter.germSetoid /-
/-- Setoid used to define the space of germs. -/
def germSetoid (l : Filter α) (β : Type _) : Setoid (α → β)
    where
  R := EventuallyEq l
  iseqv := ⟨EventuallyEq.refl _, fun _ _ => EventuallyEq.symm, fun _ _ _ => EventuallyEq.trans⟩
#align filter.germ_setoid Filter.germSetoid
-/

#print Filter.Germ /-
/-- The space of germs of functions `α → β` at a filter `l`. -/
def Germ (l : Filter α) (β : Type _) : Type _ :=
  Quotient (germSetoid l β)
#align filter.germ Filter.Germ
-/

#print Filter.productSetoid /-
/-- Setoid used to define the filter product. This is a dependent version of
  `filter.germ_setoid`. -/
def productSetoid (l : Filter α) (ε : α → Type _) : Setoid (∀ a, ε a)
    where
  R f g := ∀ᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => eventually_of_forall fun _ => rfl, fun _ _ h => h.mono fun _ => Eq.symm,
      fun x y z h1 h2 => h1.congr (h2.mono fun x hx => hx ▸ Iff.rfl)⟩
#align filter.product_setoid Filter.productSetoid
-/

#print Filter.Product /-
/-- The filter product `Π (a : α), ε a` at a filter `l`. This is a dependent version of
  `filter.germ`. -/
@[protected]
def Product (l : Filter α) (ε : α → Type _) : Type _ :=
  Quotient (productSetoid l ε)
#align filter.product Filter.Product
-/

namespace Product

variable {ε : α → Type _}

instance : CoeTC (∀ a, ε a) (l.product ε) :=
  ⟨Quotient.mk''⟩

instance [∀ a, Inhabited (ε a)] : Inhabited (l.product ε) :=
  ⟨(↑fun a => (default : ε a) : l.product ε)⟩

end Product

namespace Germ

instance : CoeTC (α → β) (Germ l β) :=
  ⟨Quotient.mk''⟩

instance : HasLiftT β (Germ l β) :=
  ⟨fun c => ↑fun x : α => c⟩

#print Filter.Germ.quot_mk_eq_coe /-
@[simp]
theorem quot_mk_eq_coe (l : Filter α) (f : α → β) : Quot.mk _ f = (f : Germ l β) :=
  rfl
#align filter.germ.quot_mk_eq_coe Filter.Germ.quot_mk_eq_coe
-/

#print Filter.Germ.mk'_eq_coe /-
@[simp]
theorem mk'_eq_coe (l : Filter α) (f : α → β) : Quotient.mk'' f = (f : Germ l β) :=
  rfl
#align filter.germ.mk'_eq_coe Filter.Germ.mk'_eq_coe
-/

#print Filter.Germ.inductionOn /-
@[elab_as_elim]
theorem inductionOn (f : Germ l β) {p : Germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
  Quotient.inductionOn' f h
#align filter.germ.induction_on Filter.Germ.inductionOn
-/

#print Filter.Germ.inductionOn₂ /-
@[elab_as_elim]
theorem inductionOn₂ (f : Germ l β) (g : Germ l γ) {p : Germ l β → Germ l γ → Prop}
    (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
  Quotient.inductionOn₂' f g h
#align filter.germ.induction_on₂ Filter.Germ.inductionOn₂
-/

#print Filter.Germ.inductionOn₃ /-
@[elab_as_elim]
theorem inductionOn₃ (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
    {p : Germ l β → Germ l γ → Germ l δ → Prop}
    (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) : p f g h :=
  Quotient.inductionOn₃' f g h H
#align filter.germ.induction_on₃ Filter.Germ.inductionOn₃
-/

#print Filter.Germ.map' /-
/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `germ l β` to `germ lc δ`. -/
def map' {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) :
    Germ l β → Germ lc δ :=
  Quotient.map' F hF
#align filter.germ.map' Filter.Germ.map'
-/

#print Filter.Germ.liftOn /-
/-- Given a germ `f : germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
def liftOn {γ : Sort _} (f : Germ l β) (F : (α → β) → γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F) :
    γ :=
  Quotient.liftOn' f F hF
#align filter.germ.lift_on Filter.Germ.liftOn
-/

#print Filter.Germ.map'_coe /-
@[simp]
theorem map'_coe {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
    (f : α → β) : map' F hF f = F f :=
  rfl
#align filter.germ.map'_coe Filter.Germ.map'_coe
-/

#print Filter.Germ.coe_eq /-
@[simp, norm_cast]
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g :=
  Quotient.eq''
#align filter.germ.coe_eq Filter.Germ.coe_eq
-/

alias coe_eq ↔ _ _root_.filter.eventually_eq.germ_eq
#align filter.eventually_eq.germ_eq Filter.EventuallyEq.germ_eq

#print Filter.Germ.map /-
/-- Lift a function `β → γ` to a function `germ l β → germ l γ`. -/
def map (op : β → γ) : Germ l β → Germ l γ :=
  map' ((· ∘ ·) op) fun f g H => H.mono fun x H => congr_arg op H
#align filter.germ.map Filter.Germ.map
-/

#print Filter.Germ.map_coe /-
@[simp]
theorem map_coe (op : β → γ) (f : α → β) : map op (f : Germ l β) = op ∘ f :=
  rfl
#align filter.germ.map_coe Filter.Germ.map_coe
-/

#print Filter.Germ.map_id /-
@[simp]
theorem map_id : map id = (id : Germ l β → Germ l β) := by ext ⟨f⟩; rfl
#align filter.germ.map_id Filter.Germ.map_id
-/

#print Filter.Germ.map_map /-
theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : Germ l β) :
    map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  inductionOn f fun f => rfl
#align filter.germ.map_map Filter.Germ.map_map
-/

#print Filter.Germ.map₂ /-
/-- Lift a binary function `β → γ → δ` to a function `germ l β → germ l γ → germ l δ`. -/
def map₂ (op : β → γ → δ) : Germ l β → Germ l γ → Germ l δ :=
  Quotient.map₂' (fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
    Hg.mp <| Hf.mono fun x Hf Hg => by simp only [Hf, Hg]
#align filter.germ.map₂ Filter.Germ.map₂
-/

#print Filter.Germ.map₂_coe /-
@[simp]
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) :
    map₂ op (f : Germ l β) g = fun x => op (f x) (g x) :=
  rfl
#align filter.germ.map₂_coe Filter.Germ.map₂_coe
-/

#print Filter.Germ.Tendsto /-
/-- A germ at `l` of maps from `α` to `β` tends to `lb : filter β` if it is represented by a map
which tends to `lb` along `l`. -/
protected def Tendsto (f : Germ l β) (lb : Filter β) : Prop :=
  liftOn f (fun f => Tendsto f l lb) fun f g H => propext (tendsto_congr' H)
#align filter.germ.tendsto Filter.Germ.Tendsto
-/

#print Filter.Germ.coe_tendsto /-
@[simp, norm_cast]
theorem coe_tendsto {f : α → β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Tendsto f l lb :=
  Iff.rfl
#align filter.germ.coe_tendsto Filter.Germ.coe_tendsto
-/

alias coe_tendsto ↔ _ _root_.filter.tendsto.germ_tendsto
#align filter.tendsto.germ_tendsto Filter.Tendsto.germ_tendsto

#print Filter.Germ.compTendsto' /-
/-- Given two germs `f : germ l β`, and `g : germ lc α`, where `l : filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendsto l) : Germ lc β :=
  liftOn f (fun f => g.map f) fun f₁ f₂ hF =>
    (inductionOn g fun g hg => coe_eq.2 <| hg.Eventually hF) hg
#align filter.germ.comp_tendsto' Filter.Germ.compTendsto'
-/

#print Filter.Germ.coe_compTendsto' /-
@[simp]
theorem coe_compTendsto' (f : α → β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f :=
  rfl
#align filter.germ.coe_comp_tendsto' Filter.Germ.coe_compTendsto'
-/

#print Filter.Germ.compTendsto /-
/-- Given a germ `f : germ l β` and a function `g : γ → α`, where `l : filter α`, if `g` tends
to `l` along `lc : filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ → α) (hg : Tendsto g lc l) : Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto
#align filter.germ.comp_tendsto Filter.Germ.compTendsto
-/

#print Filter.Germ.coe_compTendsto /-
@[simp]
theorem coe_compTendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (f : Germ l β).comp_tendsto g hg = f ∘ g :=
  rfl
#align filter.germ.coe_comp_tendsto Filter.Germ.coe_compTendsto
-/

#print Filter.Germ.compTendsto'_coe /-
@[simp]
theorem compTendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.comp_tendsto g hg :=
  rfl
#align filter.germ.comp_tendsto'_coe Filter.Germ.compTendsto'_coe
-/

#print Filter.Germ.const_inj /-
@[simp, norm_cast]
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans <| const_eventuallyEq
#align filter.germ.const_inj Filter.Germ.const_inj
-/

#print Filter.Germ.map_const /-
@[simp]
theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : Germ l β).map f = ↑(f a) :=
  rfl
#align filter.germ.map_const Filter.Germ.map_const
-/

#print Filter.Germ.map₂_const /-
@[simp]
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) :
    map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  rfl
#align filter.germ.map₂_const Filter.Germ.map₂_const
-/

#print Filter.Germ.const_compTendsto /-
@[simp]
theorem const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).comp_tendsto g hg = ↑b :=
  rfl
#align filter.germ.const_comp_tendsto Filter.Germ.const_compTendsto
-/

#print Filter.Germ.const_compTendsto' /-
@[simp]
theorem const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
    (hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b :=
  inductionOn g (fun _ _ => rfl) hg
#align filter.germ.const_comp_tendsto' Filter.Germ.const_compTendsto'
-/

#print Filter.Germ.LiftPred /-
/-- Lift a predicate on `β` to `germ l β`. -/
def LiftPred (p : β → Prop) (f : Germ l β) : Prop :=
  liftOn f (fun f => ∀ᶠ x in l, p (f x)) fun f g H =>
    propext <| eventually_congr <| H.mono fun x hx => hx ▸ Iff.rfl
#align filter.germ.lift_pred Filter.Germ.LiftPred
-/

#print Filter.Germ.liftPred_coe /-
@[simp]
theorem liftPred_coe {p : β → Prop} {f : α → β} : LiftPred p (f : Germ l β) ↔ ∀ᶠ x in l, p (f x) :=
  Iff.rfl
#align filter.germ.lift_pred_coe Filter.Germ.liftPred_coe
-/

#print Filter.Germ.liftPred_const /-
theorem liftPred_const {p : β → Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  eventually_of_forall fun y => hx
#align filter.germ.lift_pred_const Filter.Germ.liftPred_const
-/

#print Filter.Germ.liftPred_const_iff /-
@[simp]
theorem liftPred_const_iff [NeBot l] {p : β → Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)
#align filter.germ.lift_pred_const_iff Filter.Germ.liftPred_const_iff
-/

#print Filter.Germ.LiftRel /-
/-- Lift a relation `r : β → γ → Prop` to `germ l β → germ l γ → Prop`. -/
def LiftRel (r : β → γ → Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  Quotient.liftOn₂' f g (fun f g => ∀ᶠ x in l, r (f x) (g x)) fun f g f' g' Hf Hg =>
    propext <| eventually_congr <| Hg.mp <| Hf.mono fun x hf hg => hf ▸ hg ▸ Iff.rfl
#align filter.germ.lift_rel Filter.Germ.LiftRel
-/

#print Filter.Germ.liftRel_coe /-
@[simp]
theorem liftRel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    LiftRel r (f : Germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
  Iff.rfl
#align filter.germ.lift_rel_coe Filter.Germ.liftRel_coe
-/

#print Filter.Germ.liftRel_const /-
theorem liftRel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) :
    LiftRel r (↑x : Germ l β) ↑y :=
  eventually_of_forall fun _ => h
#align filter.germ.lift_rel_const Filter.Germ.liftRel_const
-/

#print Filter.Germ.liftRel_const_iff /-
@[simp]
theorem liftRel_const_iff [NeBot l] {r : β → γ → Prop} {x : β} {y : γ} :
    LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  @eventually_const _ _ _ (r x y)
#align filter.germ.lift_rel_const_iff Filter.Germ.liftRel_const_iff
-/

instance [Inhabited β] : Inhabited (Germ l β) :=
  ⟨↑(default : β)⟩

section Monoid

variable {M : Type _} {G : Type _}

@[to_additive]
instance [Mul M] : Mul (Germ l M) :=
  ⟨map₂ (· * ·)⟩

#print Filter.Germ.coe_mul /-
@[simp, norm_cast, to_additive]
theorem coe_mul [Mul M] (f g : α → M) : ↑(f * g) = (f * g : Germ l M) :=
  rfl
#align filter.germ.coe_mul Filter.Germ.coe_mul
#align filter.germ.coe_add Filter.Germ.coe_add
-/

@[to_additive]
instance [One M] : One (Germ l M) :=
  ⟨↑(1 : M)⟩

#print Filter.Germ.coe_one /-
@[simp, norm_cast, to_additive]
theorem coe_one [One M] : ↑(1 : α → M) = (1 : Germ l M) :=
  rfl
#align filter.germ.coe_one Filter.Germ.coe_one
#align filter.germ.coe_zero Filter.Germ.coe_zero
-/

@[to_additive]
instance [Semigroup M] : Semigroup (Germ l M) :=
  Function.Surjective.semigroup coe (surjective_quot_mk _) fun a b => coe_mul a b

@[to_additive]
instance [CommSemigroup M] : CommSemigroup (Germ l M) :=
  Function.Surjective.commSemigroup coe (surjective_quot_mk _) fun a b => coe_mul a b

@[to_additive AddLeftCancelSemigroup]
instance [LeftCancelSemigroup M] : LeftCancelSemigroup (Germ l M) :=
  { Germ.semigroup with
    mul := (· * ·)
    hMul_left_cancel := fun f₁ f₂ f₃ =>
      inductionOn₃ f₁ f₂ f₃ fun f₁ f₂ f₃ H =>
        coe_eq.2 ((coe_eq.1 H).mono fun x => mul_left_cancel) }

@[to_additive AddRightCancelSemigroup]
instance [RightCancelSemigroup M] : RightCancelSemigroup (Germ l M) :=
  { Germ.semigroup with
    mul := (· * ·)
    hMul_right_cancel := fun f₁ f₂ f₃ =>
      inductionOn₃ f₁ f₂ f₃ fun f₁ f₂ f₃ H =>
        coe_eq.2 <| (coe_eq.1 H).mono fun x => mul_right_cancel }

instance [VAdd M G] : VAdd M (Germ l G) :=
  ⟨fun n => map ((· +ᵥ ·) n)⟩

@[to_additive]
instance [SMul M G] : SMul M (Germ l G) :=
  ⟨fun n => map ((· • ·) n)⟩

@[to_additive SMul]
instance [Pow G M] : Pow (Germ l G) M :=
  ⟨fun f n => map (· ^ n) f⟩

#print Filter.Germ.coe_smul /-
@[simp, norm_cast, to_additive]
theorem coe_smul [SMul M G] (n : M) (f : α → G) : ↑(n • f) = (n • f : Germ l G) :=
  rfl
#align filter.germ.coe_smul Filter.Germ.coe_smul
#align filter.germ.coe_vadd Filter.Germ.coe_vadd
-/

#print Filter.Germ.const_smul /-
@[simp, norm_cast, to_additive]
theorem const_smul [SMul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • ↑a :=
  rfl
#align filter.germ.const_smul Filter.Germ.const_smul
#align filter.germ.const_vadd Filter.Germ.const_vadd
-/

#print Filter.Germ.coe_pow /-
@[simp, norm_cast, to_additive coe_smul]
theorem coe_pow [Pow G M] (f : α → G) (n : M) : ↑(f ^ n) = (f ^ n : Germ l G) :=
  rfl
#align filter.germ.coe_pow Filter.Germ.coe_pow
-/

#print Filter.Germ.const_pow /-
@[simp, norm_cast, to_additive const_smul]
theorem const_pow [Pow G M] (a : G) (n : M) : (↑(a ^ n) : Germ l G) = ↑a ^ n :=
  rfl
#align filter.germ.const_pow Filter.Germ.const_pow
-/

@[to_additive]
instance [Monoid M] : Monoid (Germ l M) :=
  Function.Surjective.monoid coe (surjective_quot_mk _) rfl (fun _ _ => rfl) fun _ _ => rfl

#print Filter.Germ.coeMulHom /-
/-- Coercion from functions to germs as a monoid homomorphism. -/
@[to_additive "Coercion from functions to germs as an additive monoid homomorphism."]
def coeMulHom [Monoid M] (l : Filter α) : (α → M) →* Germ l M :=
  ⟨coe, rfl, fun f g => rfl⟩
#align filter.germ.coe_mul_hom Filter.Germ.coeMulHom
#align filter.germ.coe_add_hom Filter.Germ.coeAddHom
-/

#print Filter.Germ.coe_coeMulHom /-
@[simp, to_additive]
theorem coe_coeMulHom [Monoid M] : (coeMulHom l : (α → M) → Germ l M) = coe :=
  rfl
#align filter.germ.coe_coe_mul_hom Filter.Germ.coe_coeMulHom
#align filter.germ.coe_coe_add_hom Filter.Germ.coe_coeAddHom
-/

@[to_additive]
instance [CommMonoid M] : CommMonoid (Germ l M) :=
  { Germ.commSemigroup, Germ.monoid with
    mul := (· * ·)
    one := 1 }

instance [AddMonoidWithOne M] : AddMonoidWithOne (Germ l M) :=
  { Germ.hasOne, Germ.addMonoid with
    natCast := fun n => ↑(n : M)
    natCast_zero := congr_arg coe Nat.cast_zero
    natCast_succ := fun n => congr_arg coe (Nat.cast_succ _) }

@[to_additive]
instance [Inv G] : Inv (Germ l G) :=
  ⟨map Inv.inv⟩

#print Filter.Germ.coe_inv /-
@[simp, norm_cast, to_additive]
theorem coe_inv [Inv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : Germ l G) :=
  rfl
#align filter.germ.coe_inv Filter.Germ.coe_inv
#align filter.germ.coe_neg Filter.Germ.coe_neg
-/

#print Filter.Germ.const_inv /-
@[simp, norm_cast, to_additive]
theorem const_inv [Inv G] (a : G) : (↑a⁻¹ : Germ l G) = (↑a)⁻¹ :=
  rfl
#align filter.germ.const_inv Filter.Germ.const_inv
#align filter.germ.const_neg Filter.Germ.const_neg
-/

@[to_additive]
instance [Div M] : Div (Germ l M) :=
  ⟨map₂ (· / ·)⟩

#print Filter.Germ.coe_div /-
@[simp, norm_cast, to_additive]
theorem coe_div [Div M] (f g : α → M) : ↑(f / g) = (f / g : Germ l M) :=
  rfl
#align filter.germ.coe_div Filter.Germ.coe_div
#align filter.germ.coe_sub Filter.Germ.coe_sub
-/

#print Filter.Germ.const_div /-
@[simp, norm_cast, to_additive]
theorem const_div [Div M] (a b : M) : (↑(a / b) : Germ l M) = ↑a / ↑b :=
  rfl
#align filter.germ.const_div Filter.Germ.const_div
#align filter.germ.const_sub Filter.Germ.const_sub
-/

@[to_additive SubNegMonoid]
instance [DivInvMonoid G] : DivInvMonoid (Germ l G) :=
  Function.Surjective.divInvMonoid coe (surjective_quot_mk _) rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance [Group G] : Group (Germ l G) :=
  { Germ.divInvMonoid with
    mul := (· * ·)
    one := 1
    hMul_left_inv := by rintro ⟨f⟩; exact congr_arg (Quot.mk _) (mul_left_inv f) }

@[to_additive]
instance [CommGroup G] : CommGroup (Germ l G) :=
  { Germ.group, Germ.commMonoid with
    mul := (· * ·)
    one := 1
    inv := Inv.inv }

end Monoid

section Ring

variable {R : Type _}

#print Filter.Germ.nontrivial /-
instance nontrivial [Nontrivial R] [NeBot l] : Nontrivial (Germ l R) :=
  let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩
#align filter.germ.nontrivial Filter.Germ.nontrivial
-/

instance [MulZeroClass R] : MulZeroClass (Germ l R)
    where
  zero := 0
  mul := (· * ·)
  mul_zero f := inductionOn f fun f => by norm_cast; rw [MulZeroClass.mul_zero]
  zero_mul f := inductionOn f fun f => by norm_cast; rw [MulZeroClass.zero_mul]

instance [Distrib R] : Distrib (Germ l R)
    where
  mul := (· * ·)
  add := (· + ·)
  left_distrib f g h := inductionOn₃ f g h fun f g h => by norm_cast; rw [left_distrib]
  right_distrib f g h := inductionOn₃ f g h fun f g h => by norm_cast; rw [right_distrib]

instance [Semiring R] : Semiring (Germ l R) :=
  { Germ.addCommMonoid, Germ.monoid, Germ.distrib, Germ.mulZeroClass, Germ.addMonoidWithOne with }

#print Filter.Germ.coeRingHom /-
/-- Coercion `(α → R) → germ l R` as a `ring_hom`. -/
def coeRingHom [Semiring R] (l : Filter α) : (α → R) →+* Germ l R :=
  { (coeMulHom l : _ →* Germ l R), (coeAddHom l : _ →+ Germ l R) with toFun := coe }
#align filter.germ.coe_ring_hom Filter.Germ.coeRingHom
-/

#print Filter.Germ.coe_coeRingHom /-
@[simp]
theorem coe_coeRingHom [Semiring R] : (coeRingHom l : (α → R) → Germ l R) = coe :=
  rfl
#align filter.germ.coe_coe_ring_hom Filter.Germ.coe_coeRingHom
-/

instance [Ring R] : Ring (Germ l R) :=
  { Germ.addCommGroup, Germ.semiring with }

instance [CommSemiring R] : CommSemiring (Germ l R) :=
  { Germ.semiring, Germ.commMonoid with }

instance [CommRing R] : CommRing (Germ l R) :=
  { Germ.ring, Germ.commMonoid with }

end Ring

section Module

variable {M N R : Type _}

#print Filter.Germ.instSMul' /-
@[to_additive]
instance instSMul' [SMul M β] : SMul (Germ l M) (Germ l β) :=
  ⟨map₂ (· • ·)⟩
#align filter.germ.has_smul' Filter.Germ.instSMul'
#align filter.germ.has_vadd' Filter.Germ.instVAdd'
-/

#print Filter.Germ.coe_smul' /-
@[simp, norm_cast, to_additive]
theorem coe_smul' [SMul M β] (c : α → M) (f : α → β) : ↑(c • f) = (c : Germ l M) • (f : Germ l β) :=
  rfl
#align filter.germ.coe_smul' Filter.Germ.coe_smul'
#align filter.germ.coe_vadd' Filter.Germ.coe_vadd'
-/

@[to_additive]
instance [Monoid M] [MulAction M β] : MulAction M (Germ l β)
    where
  one_smul f := inductionOn f fun f => by norm_cast; simp only [one_smul]
  hMul_smul c₁ c₂ f := inductionOn f fun f => by norm_cast; simp only [mul_smul]

#print Filter.Germ.mulAction' /-
@[to_additive]
instance mulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β)
    where
  one_smul f := inductionOn f fun f => by simp only [← coe_one, ← coe_smul', one_smul]
  hMul_smul c₁ c₂ f := inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by norm_cast; simp only [mul_smul]
#align filter.germ.mul_action' Filter.Germ.mulAction'
#align filter.germ.add_action' Filter.Germ.addAction'
-/

instance [Monoid M] [AddMonoid N] [DistribMulAction M N] : DistribMulAction M (Germ l N)
    where
  smul_add c f g := inductionOn₂ f g fun f g => by norm_cast; simp only [smul_add]
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]

#print Filter.Germ.distribMulAction' /-
instance distribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction (Germ l M) (Germ l N)
    where
  smul_add c f g := inductionOn₃ c f g fun c f g => by norm_cast; simp only [smul_add]
  smul_zero c := inductionOn c fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]
#align filter.germ.distrib_mul_action' Filter.Germ.distribMulAction'
-/

instance [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Germ l M)
    where
  add_smul c₁ c₂ f := inductionOn f fun f => by norm_cast; simp only [add_smul]
  zero_smul f := inductionOn f fun f => by norm_cast; simp only [zero_smul, coe_zero]

#print Filter.Germ.module' /-
instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module (Germ l R) (Germ l M)
    where
  add_smul c₁ c₂ f := inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by norm_cast; simp only [add_smul]
  zero_smul f := inductionOn f fun f => by simp only [← coe_zero, ← coe_smul', zero_smul]
#align filter.germ.module' Filter.Germ.module'
-/

end Module

instance [LE β] : LE (Germ l β) :=
  ⟨LiftRel (· ≤ ·)⟩

#print Filter.Germ.le_def /-
theorem le_def [LE β] : ((· ≤ ·) : Germ l β → Germ l β → Prop) = LiftRel (· ≤ ·) :=
  rfl
#align filter.germ.le_def Filter.Germ.le_def
-/

#print Filter.Germ.coe_le /-
@[simp]
theorem coe_le [LE β] : (f : Germ l β) ≤ g ↔ f ≤ᶠ[l] g :=
  Iff.rfl
#align filter.germ.coe_le Filter.Germ.coe_le
-/

#print Filter.Germ.coe_nonneg /-
theorem coe_nonneg [LE β] [Zero β] {f : α → β} : 0 ≤ (f : Germ l β) ↔ ∀ᶠ x in l, 0 ≤ f x :=
  Iff.rfl
#align filter.germ.coe_nonneg Filter.Germ.coe_nonneg
-/

#print Filter.Germ.const_le /-
theorem const_le [LE β] {x y : β} : x ≤ y → (↑x : Germ l β) ≤ ↑y :=
  liftRel_const
#align filter.germ.const_le Filter.Germ.const_le
-/

#print Filter.Germ.const_le_iff /-
@[simp, norm_cast]
theorem const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) ≤ ↑y ↔ x ≤ y :=
  liftRel_const_iff
#align filter.germ.const_le_iff Filter.Germ.const_le_iff
-/

instance [Preorder β] : Preorder (Germ l β)
    where
  le := (· ≤ ·)
  le_refl f := inductionOn f <| EventuallyLE.refl l
  le_trans f₁ f₂ f₃ := inductionOn₃ f₁ f₂ f₃ fun f₁ f₂ f₃ => EventuallyLE.trans

instance [PartialOrder β] : PartialOrder (Germ l β) :=
  { Germ.preorder with
    le := (· ≤ ·)
    le_antisymm := fun f g =>
      inductionOn₂ f g fun f g h₁ h₂ => (EventuallyLE.antisymm h₁ h₂).germ_eq }

instance [Bot β] : Bot (Germ l β) :=
  ⟨↑(⊥ : β)⟩

instance [Top β] : Top (Germ l β) :=
  ⟨↑(⊤ : β)⟩

#print Filter.Germ.const_bot /-
@[simp, norm_cast]
theorem const_bot [Bot β] : (↑(⊥ : β) : Germ l β) = ⊥ :=
  rfl
#align filter.germ.const_bot Filter.Germ.const_bot
-/

#print Filter.Germ.const_top /-
@[simp, norm_cast]
theorem const_top [Top β] : (↑(⊤ : β) : Germ l β) = ⊤ :=
  rfl
#align filter.germ.const_top Filter.Germ.const_top
-/

instance [LE β] [OrderBot β] : OrderBot (Germ l β)
    where
  bot := ⊥
  bot_le f := inductionOn f fun f => eventually_of_forall fun x => bot_le

instance [LE β] [OrderTop β] : OrderTop (Germ l β)
    where
  top := ⊤
  le_top f := inductionOn f fun f => eventually_of_forall fun x => le_top

instance [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) :=
  { Germ.orderBot, Germ.orderTop with }

end Germ

end Filter

