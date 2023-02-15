/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir

! This file was ported from Lean 3 source module order.filter.germ
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
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

/- warning: filter.const_eventually_eq' -> Filter.const_eventuallyEq' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} [_inst_1 : Filter.NeBot.{u1} α l] {a : β} {b : β}, Iff (Filter.Eventually.{u1} α (fun (x : α) => Eq.{succ u2} β a b) l) (Eq.{succ u2} β a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} [_inst_1 : Filter.NeBot.{u2} α l] {a : β} {b : β}, Iff (Filter.Eventually.{u2} α (fun (x : α) => Eq.{succ u1} β a b) l) (Eq.{succ u1} β a b)
Case conversion may be inaccurate. Consider using '#align filter.const_eventually_eq' Filter.const_eventuallyEq'ₓ'. -/
theorem const_eventuallyEq' [NeBot l] {a b : β} : (∀ᶠ x in l, a = b) ↔ a = b :=
  eventually_const
#align filter.const_eventually_eq' Filter.const_eventuallyEq'

/- warning: filter.const_eventually_eq -> Filter.const_eventuallyEq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} [_inst_1 : Filter.NeBot.{u1} α l] {a : β} {b : β}, Iff (Filter.EventuallyEq.{u1, u2} α β l (fun (_x : α) => a) (fun (_x : α) => b)) (Eq.{succ u2} β a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} [_inst_1 : Filter.NeBot.{u2} α l] {a : β} {b : β}, Iff (Filter.EventuallyEq.{u2, u1} α β l (fun (_x : α) => a) (fun (_x : α) => b)) (Eq.{succ u1} β a b)
Case conversion may be inaccurate. Consider using '#align filter.const_eventually_eq Filter.const_eventuallyEqₓ'. -/
theorem const_eventuallyEq [NeBot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventuallyEq' _ _ _ _ a b
#align filter.const_eventually_eq Filter.const_eventuallyEq

/- warning: filter.eventually_eq.comp_tendsto -> Filter.EventuallyEq.comp_tendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} {f : α -> β} {f' : α -> β}, (Filter.EventuallyEq.{u1, u2} α β l f f') -> (forall {g : γ -> α} {lc : Filter.{u3} γ}, (Filter.Tendsto.{u3, u1} γ α g lc l) -> (Filter.EventuallyEq.{u3, u2} γ β lc (Function.comp.{succ u3, succ u1, succ u2} γ α β f g) (Function.comp.{succ u3, succ u1, succ u2} γ α β f' g)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {l : Filter.{u3} α} {f : α -> β} {f' : α -> β}, (Filter.EventuallyEq.{u3, u2} α β l f f') -> (forall {g : γ -> α} {lc : Filter.{u1} γ}, (Filter.Tendsto.{u1, u3} γ α g lc l) -> (Filter.EventuallyEq.{u1, u2} γ β lc (Function.comp.{succ u1, succ u3, succ u2} γ α β f g) (Function.comp.{succ u1, succ u3, succ u2} γ α β f' g)))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.comp_tendsto Filter.EventuallyEq.comp_tendstoₓ'. -/
theorem EventuallyEq.comp_tendsto {f' : α → β} (H : f =ᶠ[l] f') {g : γ → α} {lc : Filter γ}
    (hg : Tendsto g lc l) : f ∘ g =ᶠ[lc] f' ∘ g :=
  hg.Eventually H
#align filter.eventually_eq.comp_tendsto Filter.EventuallyEq.comp_tendsto

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

/- warning: filter.germ.quot_mk_eq_coe -> Filter.Germ.quot_mk_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : Filter.{u1} α) (f : α -> β), Eq.{max (succ u1) (succ u2)} (Quot.{max (succ u1) (succ u2)} (α -> β) (Setoid.r.{succ (max u1 u2)} (α -> β) (Filter.germSetoid.{u1, u2} α l β))) (Quot.mk.{max (succ u1) (succ u2)} (α -> β) (Setoid.r.{succ (max u1 u2)} (α -> β) (Filter.germSetoid.{u1, u2} α l β)) f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : Filter.{u2} α) (f : α -> β), Eq.{max (succ u2) (succ u1)} (Quot.{max (succ u2) (succ u1)} (α -> β) (Setoid.r.{succ (max u2 u1)} (α -> β) (Filter.germSetoid.{u2, u1} α l β))) (Quot.mk.{max (succ u2) (succ u1)} (α -> β) (Setoid.r.{succ (max u2 u1)} (α -> β) (Filter.germSetoid.{u2, u1} α l β)) f) (Filter.Germ.ofFun.{u2, u1} α β l f)
Case conversion may be inaccurate. Consider using '#align filter.germ.quot_mk_eq_coe Filter.Germ.quot_mk_eq_coeₓ'. -/
@[simp]
theorem quot_mk_eq_coe (l : Filter α) (f : α → β) : Quot.mk _ f = (f : Germ l β) :=
  rfl
#align filter.germ.quot_mk_eq_coe Filter.Germ.quot_mk_eq_coe

/- warning: filter.germ.mk'_eq_coe -> Filter.Germ.mk'_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (l : Filter.{u1} α) (f : α -> β), Eq.{max (succ u1) (succ u2)} (Quotient.{max (succ u1) (succ u2)} (α -> β) (Filter.germSetoid.{u1, u2} α l β)) (Quotient.mk''.{max (succ u1) (succ u2)} (α -> β) (Filter.germSetoid.{u1, u2} α l β) f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (l : Filter.{u2} α) (f : α -> β), Eq.{max (succ u2) (succ u1)} (Quotient.{max (succ u1) (succ u2)} (α -> β) (Filter.germSetoid.{u2, u1} α l β)) (Quotient.mk'.{max (succ u1) (succ u2)} (α -> β) (Filter.germSetoid.{u2, u1} α l β) f) (Filter.Germ.ofFun.{u2, u1} α β l f)
Case conversion may be inaccurate. Consider using '#align filter.germ.mk'_eq_coe Filter.Germ.mk'_eq_coeₓ'. -/
@[simp]
theorem mk'_eq_coe (l : Filter α) (f : α → β) : Quotient.mk'' f = (f : Germ l β) :=
  rfl
#align filter.germ.mk'_eq_coe Filter.Germ.mk'_eq_coe

/- warning: filter.germ.induction_on -> Filter.Germ.inductionOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} (f : Filter.Germ.{u1, u2} α l β) {p : (Filter.Germ.{u1, u2} α l β) -> Prop}, (forall (f : α -> β), p ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f)) -> (p f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} (f : Filter.Germ.{u2, u1} α l β) {p : (Filter.Germ.{u2, u1} α l β) -> Prop}, (forall (f : α -> β), p (Filter.Germ.ofFun.{u2, u1} α β l f)) -> (p f)
Case conversion may be inaccurate. Consider using '#align filter.germ.induction_on Filter.Germ.inductionOnₓ'. -/
@[elab_as_elim]
theorem inductionOn (f : Germ l β) {p : Germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
  Quotient.inductionOn' f h
#align filter.germ.induction_on Filter.Germ.inductionOn

/- warning: filter.germ.induction_on₂ -> Filter.Germ.inductionOn₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} (f : Filter.Germ.{u1, u2} α l β) (g : Filter.Germ.{u1, u3} α l γ) {p : (Filter.Germ.{u1, u2} α l β) -> (Filter.Germ.{u1, u3} α l γ) -> Prop}, (forall (f : α -> β) (g : α -> γ), p ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Type.{max u1 u3}) [self : HasLiftT.{max (succ u1) (succ u3), succ (max u1 u3)} a b] => self.0) (α -> γ) (Filter.Germ.{u1, u3} α l γ) (HasLiftT.mk.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (CoeTCₓ.coe.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasCoeT.{u1, u3} α γ l))) g)) -> (p f g)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {l : Filter.{u3} α} (f : Filter.Germ.{u3, u2} α l β) (g : Filter.Germ.{u3, u1} α l γ) {p : (Filter.Germ.{u3, u2} α l β) -> (Filter.Germ.{u3, u1} α l γ) -> Prop}, (forall (f : α -> β) (g : α -> γ), p (Filter.Germ.ofFun.{u3, u2} α β l f) (Filter.Germ.ofFun.{u3, u1} α γ l g)) -> (p f g)
Case conversion may be inaccurate. Consider using '#align filter.germ.induction_on₂ Filter.Germ.inductionOn₂ₓ'. -/
@[elab_as_elim]
theorem inductionOn₂ (f : Germ l β) (g : Germ l γ) {p : Germ l β → Germ l γ → Prop}
    (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
  Quotient.inductionOn₂' f g h
#align filter.germ.induction_on₂ Filter.Germ.inductionOn₂

/- warning: filter.germ.induction_on₃ -> Filter.Germ.inductionOn₃ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {l : Filter.{u1} α} (f : Filter.Germ.{u1, u2} α l β) (g : Filter.Germ.{u1, u3} α l γ) (h : Filter.Germ.{u1, u4} α l δ) {p : (Filter.Germ.{u1, u2} α l β) -> (Filter.Germ.{u1, u3} α l γ) -> (Filter.Germ.{u1, u4} α l δ) -> Prop}, (forall (f : α -> β) (g : α -> γ) (h : α -> δ), p ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Type.{max u1 u3}) [self : HasLiftT.{max (succ u1) (succ u3), succ (max u1 u3)} a b] => self.0) (α -> γ) (Filter.Germ.{u1, u3} α l γ) (HasLiftT.mk.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (CoeTCₓ.coe.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasCoeT.{u1, u3} α γ l))) g) ((fun (a : Sort.{max (succ u1) (succ u4)}) (b : Type.{max u1 u4}) [self : HasLiftT.{max (succ u1) (succ u4), succ (max u1 u4)} a b] => self.0) (α -> δ) (Filter.Germ.{u1, u4} α l δ) (HasLiftT.mk.{max (succ u1) (succ u4), succ (max u1 u4)} (α -> δ) (Filter.Germ.{u1, u4} α l δ) (CoeTCₓ.coe.{max (succ u1) (succ u4), succ (max u1 u4)} (α -> δ) (Filter.Germ.{u1, u4} α l δ) (Filter.Germ.hasCoeT.{u1, u4} α δ l))) h)) -> (p f g h)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} {l : Filter.{u4} α} (f : Filter.Germ.{u4, u3} α l β) (g : Filter.Germ.{u4, u2} α l γ) (h : Filter.Germ.{u4, u1} α l δ) {p : (Filter.Germ.{u4, u3} α l β) -> (Filter.Germ.{u4, u2} α l γ) -> (Filter.Germ.{u4, u1} α l δ) -> Prop}, (forall (f : α -> β) (g : α -> γ) (h : α -> δ), p (Filter.Germ.ofFun.{u4, u3} α β l f) (Filter.Germ.ofFun.{u4, u2} α γ l g) (Filter.Germ.ofFun.{u4, u1} α δ l h)) -> (p f g h)
Case conversion may be inaccurate. Consider using '#align filter.germ.induction_on₃ Filter.Germ.inductionOn₃ₓ'. -/
@[elab_as_elim]
theorem inductionOn₃ (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
    {p : Germ l β → Germ l γ → Germ l δ → Prop}
    (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) : p f g h :=
  Quotient.inductionOn₃' f g h H
#align filter.germ.induction_on₃ Filter.Germ.inductionOn₃

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

/- warning: filter.germ.map'_coe -> Filter.Germ.map'_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {l : Filter.{u1} α} {lc : Filter.{u3} γ} (F : (α -> β) -> γ -> δ) (hF : Relator.LiftFun.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u3) (succ u4), max (succ u3) (succ u4)} (α -> β) (α -> β) (γ -> δ) (γ -> δ) (Filter.EventuallyEq.{u1, u2} α β l) (Filter.EventuallyEq.{u3, u4} γ δ lc) F F) (f : α -> β), Eq.{succ (max u3 u4)} (Filter.Germ.{u3, u4} γ lc δ) (Filter.Germ.map'.{u1, u2, u3, u4} α β γ δ l lc F hF ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f)) ((fun (a : Sort.{max (succ u3) (succ u4)}) (b : Type.{max u3 u4}) [self : HasLiftT.{max (succ u3) (succ u4), succ (max u3 u4)} a b] => self.0) (γ -> δ) (Filter.Germ.{u3, u4} γ lc δ) (HasLiftT.mk.{max (succ u3) (succ u4), succ (max u3 u4)} (γ -> δ) (Filter.Germ.{u3, u4} γ lc δ) (CoeTCₓ.coe.{max (succ u3) (succ u4), succ (max u3 u4)} (γ -> δ) (Filter.Germ.{u3, u4} γ lc δ) (Filter.Germ.hasCoeT.{u3, u4} γ δ lc))) (F f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u1}} {l : Filter.{u3} α} {lc : Filter.{u4} γ} (F : (α -> β) -> γ -> δ) (hF : Relator.LiftFun.{max (succ u3) (succ u2), max (succ u3) (succ u2), max (succ u4) (succ u1), max (succ u4) (succ u1)} (α -> β) (α -> β) (γ -> δ) (γ -> δ) (Filter.EventuallyEq.{u3, u2} α β l) (Filter.EventuallyEq.{u4, u1} γ δ lc) F F) (f : α -> β), Eq.{max (succ u4) (succ u1)} (Filter.Germ.{u4, u1} γ lc δ) (Filter.Germ.map'.{u3, u2, u4, u1} α β γ δ l lc F hF (Filter.Germ.ofFun.{u3, u2} α β l f)) (Filter.Germ.ofFun.{u4, u1} γ δ lc (F f))
Case conversion may be inaccurate. Consider using '#align filter.germ.map'_coe Filter.Germ.map'_coeₓ'. -/
@[simp]
theorem map'_coe {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
    (f : α → β) : map' F hF f = F f :=
  rfl
#align filter.germ.map'_coe Filter.Germ.map'_coe

/- warning: filter.germ.coe_eq -> Filter.Germ.coe_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, Iff (Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α l β) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) g)) (Filter.EventuallyEq.{u1, u2} α β l f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} {f : α -> β} {g : α -> β}, Iff (Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α l β) (Filter.Germ.ofFun.{u2, u1} α β l f) (Filter.Germ.ofFun.{u2, u1} α β l g)) (Filter.EventuallyEq.{u2, u1} α β l f g)
Case conversion may be inaccurate. Consider using '#align filter.germ.coe_eq Filter.Germ.coe_eqₓ'. -/
@[simp, norm_cast]
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g :=
  Quotient.eq''
#align filter.germ.coe_eq Filter.Germ.coe_eq

/- warning: filter.eventually_eq.germ_eq -> Filter.EventuallyEq.germ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u1, u2} α β l f g) -> (Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α l β) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} {f : α -> β} {g : α -> β}, (Filter.EventuallyEq.{u2, u1} α β l f g) -> (Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α l β) (Filter.Germ.ofFun.{u2, u1} α β l f) (Filter.Germ.ofFun.{u2, u1} α β l g))
Case conversion may be inaccurate. Consider using '#align filter.eventually_eq.germ_eq Filter.EventuallyEq.germ_eqₓ'. -/
alias coe_eq ↔ _ _root_.filter.eventually_eq.germ_eq
#align filter.eventually_eq.germ_eq Filter.EventuallyEq.germ_eq

#print Filter.Germ.map /-
/-- Lift a function `β → γ` to a function `germ l β → germ l γ`. -/
def map (op : β → γ) : Germ l β → Germ l γ :=
  map' ((· ∘ ·) op) fun f g H => H.mono fun x H => congr_arg op H
#align filter.germ.map Filter.Germ.map
-/

/- warning: filter.germ.map_coe -> Filter.Germ.map_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} (op : β -> γ) (f : α -> β), Eq.{succ (max u1 u3)} (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.map.{u1, u2, u3} α β γ l op ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f)) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Type.{max u1 u3}) [self : HasLiftT.{max (succ u1) (succ u3), succ (max u1 u3)} a b] => self.0) (α -> γ) (Filter.Germ.{u1, u3} α l γ) (HasLiftT.mk.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (CoeTCₓ.coe.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasCoeT.{u1, u3} α γ l))) (Function.comp.{succ u1, succ u2, succ u3} α β γ op f))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {l : Filter.{u3} α} (op : β -> γ) (f : α -> β), Eq.{max (succ u3) (succ u2)} (Filter.Germ.{u3, u2} α l γ) (Filter.Germ.map.{u3, u1, u2} α β γ l op (Filter.Germ.ofFun.{u3, u1} α β l f)) (Filter.Germ.ofFun.{u3, u2} α γ l (Function.comp.{succ u3, succ u1, succ u2} α β γ op f))
Case conversion may be inaccurate. Consider using '#align filter.germ.map_coe Filter.Germ.map_coeₓ'. -/
@[simp]
theorem map_coe (op : β → γ) (f : α → β) : map op (f : Germ l β) = op ∘ f :=
  rfl
#align filter.germ.map_coe Filter.Germ.map_coe

/- warning: filter.germ.map_id -> Filter.Germ.map_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α}, Eq.{succ (max u1 u2)} ((Filter.Germ.{u1, u2} α l β) -> (Filter.Germ.{u1, u2} α l β)) (Filter.Germ.map.{u1, u2, u2} α β β l (id.{succ u2} β)) (id.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α l β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α}, Eq.{max (succ u2) (succ u1)} ((Filter.Germ.{u2, u1} α l β) -> (Filter.Germ.{u2, u1} α l β)) (Filter.Germ.map.{u2, u1, u1} α β β l (id.{succ u1} β)) (id.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α l β))
Case conversion may be inaccurate. Consider using '#align filter.germ.map_id Filter.Germ.map_idₓ'. -/
@[simp]
theorem map_id : map id = (id : Germ l β → Germ l β) :=
  by
  ext ⟨f⟩
  rfl
#align filter.germ.map_id Filter.Germ.map_id

/- warning: filter.germ.map_map -> Filter.Germ.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {l : Filter.{u1} α} (op₁ : γ -> δ) (op₂ : β -> γ) (f : Filter.Germ.{u1, u2} α l β), Eq.{succ (max u1 u4)} (Filter.Germ.{u1, u4} α l δ) (Filter.Germ.map.{u1, u3, u4} α γ δ l op₁ (Filter.Germ.map.{u1, u2, u3} α β γ l op₂ f)) (Filter.Germ.map.{u1, u2, u4} α β δ l (Function.comp.{succ u2, succ u3, succ u4} β γ δ op₁ op₂) f)
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u1}} {δ : Type.{u2}} {l : Filter.{u4} α} (op₁ : γ -> δ) (op₂ : β -> γ) (f : Filter.Germ.{u4, u3} α l β), Eq.{max (succ u4) (succ u2)} (Filter.Germ.{u4, u2} α l δ) (Filter.Germ.map.{u4, u1, u2} α γ δ l op₁ (Filter.Germ.map.{u4, u3, u1} α β γ l op₂ f)) (Filter.Germ.map.{u4, u3, u2} α β δ l (Function.comp.{succ u3, succ u1, succ u2} β γ δ op₁ op₂) f)
Case conversion may be inaccurate. Consider using '#align filter.germ.map_map Filter.Germ.map_mapₓ'. -/
theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : Germ l β) :
    map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  inductionOn f fun f => rfl
#align filter.germ.map_map Filter.Germ.map_map

#print Filter.Germ.map₂ /-
/-- Lift a binary function `β → γ → δ` to a function `germ l β → germ l γ → germ l δ`. -/
def map₂ (op : β → γ → δ) : Germ l β → Germ l γ → Germ l δ :=
  Quotient.map₂' (fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
    Hg.mp <| Hf.mono fun x Hf Hg => by simp only [Hf, Hg]
#align filter.germ.map₂ Filter.Germ.map₂
-/

/- warning: filter.germ.map₂_coe -> Filter.Germ.map₂_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {l : Filter.{u1} α} (op : β -> γ -> δ) (f : α -> β) (g : α -> γ), Eq.{succ (max u1 u4)} (Filter.Germ.{u1, u4} α l δ) (Filter.Germ.map₂.{u1, u2, u3, u4} α β γ δ l op ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Type.{max u1 u3}) [self : HasLiftT.{max (succ u1) (succ u3), succ (max u1 u3)} a b] => self.0) (α -> γ) (Filter.Germ.{u1, u3} α l γ) (HasLiftT.mk.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (CoeTCₓ.coe.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasCoeT.{u1, u3} α γ l))) g)) ((fun (a : Sort.{max (succ u1) (succ u4)}) (b : Type.{max u1 u4}) [self : HasLiftT.{max (succ u1) (succ u4), succ (max u1 u4)} a b] => self.0) (α -> δ) (Filter.Germ.{u1, u4} α l δ) (HasLiftT.mk.{max (succ u1) (succ u4), succ (max u1 u4)} (α -> δ) (Filter.Germ.{u1, u4} α l δ) (CoeTCₓ.coe.{max (succ u1) (succ u4), succ (max u1 u4)} (α -> δ) (Filter.Germ.{u1, u4} α l δ) (Filter.Germ.hasCoeT.{u1, u4} α δ l))) (fun (x : α) => op (f x) (g x)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u3}} {l : Filter.{u4} α} (op : β -> γ -> δ) (f : α -> β) (g : α -> γ), Eq.{max (succ u4) (succ u3)} (Filter.Germ.{u4, u3} α l δ) (Filter.Germ.map₂.{u4, u2, u1, u3} α β γ δ l op (Filter.Germ.ofFun.{u4, u2} α β l f) (Filter.Germ.ofFun.{u4, u1} α γ l g)) (Filter.Germ.ofFun.{u4, u3} α δ l (fun (x : α) => op (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align filter.germ.map₂_coe Filter.Germ.map₂_coeₓ'. -/
@[simp]
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) :
    map₂ op (f : Germ l β) g = fun x => op (f x) (g x) :=
  rfl
#align filter.germ.map₂_coe Filter.Germ.map₂_coe

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

/- warning: filter.germ.coe_comp_tendsto' -> Filter.Germ.coe_compTendsto' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} (f : α -> β) {lc : Filter.{u3} γ} {g : Filter.Germ.{u3, u1} γ lc α} (hg : Filter.Germ.Tendsto.{u3, u1} γ α lc g l), Eq.{succ (max u3 u2)} (Filter.Germ.{u3, u2} γ lc β) (Filter.Germ.compTendsto'.{u1, u2, u3} α β γ l ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f) lc g hg) (Filter.Germ.map.{u3, u1, u2} γ α β lc f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {l : Filter.{u2} α} (f : α -> β) {lc : Filter.{u3} γ} {g : Filter.Germ.{u3, u2} γ lc α} (hg : Filter.Germ.Tendsto.{u3, u2} γ α lc g l), Eq.{max (succ u1) (succ u3)} (Filter.Germ.{u3, u1} γ lc β) (Filter.Germ.compTendsto'.{u2, u1, u3} α β γ l (Filter.Germ.ofFun.{u2, u1} α β l f) lc g hg) (Filter.Germ.map.{u3, u2, u1} γ α β lc f g)
Case conversion may be inaccurate. Consider using '#align filter.germ.coe_comp_tendsto' Filter.Germ.coe_compTendsto'ₓ'. -/
@[simp]
theorem coe_compTendsto' (f : α → β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f :=
  rfl
#align filter.germ.coe_comp_tendsto' Filter.Germ.coe_compTendsto'

#print Filter.Germ.compTendsto /-
/-- Given a germ `f : germ l β` and a function `g : γ → α`, where `l : filter α`, if `g` tends
to `l` along `lc : filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ → α) (hg : Tendsto g lc l) : Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto
#align filter.germ.comp_tendsto Filter.Germ.compTendsto
-/

/- warning: filter.germ.coe_comp_tendsto -> Filter.Germ.coe_compTendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} (f : α -> β) {lc : Filter.{u3} γ} {g : γ -> α} (hg : Filter.Tendsto.{u3, u1} γ α g lc l), Eq.{succ (max u3 u2)} (Filter.Germ.{u3, u2} γ lc β) (Filter.Germ.compTendsto.{u1, u2, u3} α β γ l ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f) lc g hg) ((fun (a : Sort.{max (succ u3) (succ u2)}) (b : Type.{max u3 u2}) [self : HasLiftT.{max (succ u3) (succ u2), succ (max u3 u2)} a b] => self.0) (γ -> β) (Filter.Germ.{u3, u2} γ lc β) (HasLiftT.mk.{max (succ u3) (succ u2), succ (max u3 u2)} (γ -> β) (Filter.Germ.{u3, u2} γ lc β) (CoeTCₓ.coe.{max (succ u3) (succ u2), succ (max u3 u2)} (γ -> β) (Filter.Germ.{u3, u2} γ lc β) (Filter.Germ.hasCoeT.{u3, u2} γ β lc))) (Function.comp.{succ u3, succ u1, succ u2} γ α β f g))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {l : Filter.{u2} α} (f : α -> β) {lc : Filter.{u3} γ} {g : γ -> α} (hg : Filter.Tendsto.{u3, u2} γ α g lc l), Eq.{max (succ u1) (succ u3)} (Filter.Germ.{u3, u1} γ lc β) (Filter.Germ.compTendsto.{u2, u1, u3} α β γ l (Filter.Germ.ofFun.{u2, u1} α β l f) lc g hg) (Filter.Germ.ofFun.{u3, u1} γ β lc (Function.comp.{succ u3, succ u2, succ u1} γ α β f g))
Case conversion may be inaccurate. Consider using '#align filter.germ.coe_comp_tendsto Filter.Germ.coe_compTendstoₓ'. -/
@[simp]
theorem coe_compTendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (f : Germ l β).comp_tendsto g hg = f ∘ g :=
  rfl
#align filter.germ.coe_comp_tendsto Filter.Germ.coe_compTendsto

/- warning: filter.germ.comp_tendsto'_coe -> Filter.Germ.compTendsto'_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} (f : Filter.Germ.{u1, u2} α l β) {lc : Filter.{u3} γ} {g : γ -> α} (hg : Filter.Tendsto.{u3, u1} γ α g lc l), Eq.{succ (max u3 u2)} (Filter.Germ.{u3, u2} γ lc β) (Filter.Germ.compTendsto'.{u1, u2, u3} α β γ l f lc ((fun (a : Sort.{max (succ u3) (succ u1)}) (b : Type.{max u3 u1}) [self : HasLiftT.{max (succ u3) (succ u1), succ (max u3 u1)} a b] => self.0) (γ -> α) (Filter.Germ.{u3, u1} γ lc α) (HasLiftT.mk.{max (succ u3) (succ u1), succ (max u3 u1)} (γ -> α) (Filter.Germ.{u3, u1} γ lc α) (CoeTCₓ.coe.{max (succ u3) (succ u1), succ (max u3 u1)} (γ -> α) (Filter.Germ.{u3, u1} γ lc α) (Filter.Germ.hasCoeT.{u3, u1} γ α lc))) g) (Filter.Tendsto.germ_tendsto.{u3, u1} γ α lc g l hg)) (Filter.Germ.compTendsto.{u1, u2, u3} α β γ l f lc g hg)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {l : Filter.{u3} α} (f : Filter.Germ.{u3, u2} α l β) {lc : Filter.{u1} γ} {g : γ -> α} (hg : Filter.Tendsto.{u1, u3} γ α g lc l), Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u1, u2} γ lc β) (Filter.Germ.compTendsto'.{u3, u2, u1} α β γ l f lc (Filter.Germ.ofFun.{u1, u3} γ α lc g) (Filter.Tendsto.germ_tendsto.{u1, u3} γ α lc g l hg)) (Filter.Germ.compTendsto.{u3, u2, u1} α β γ l f lc g hg)
Case conversion may be inaccurate. Consider using '#align filter.germ.comp_tendsto'_coe Filter.Germ.compTendsto'_coeₓ'. -/
@[simp]
theorem compTendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.comp_tendsto g hg :=
  rfl
#align filter.germ.comp_tendsto'_coe Filter.Germ.compTendsto'_coe

/- warning: filter.germ.const_inj -> Filter.Germ.const_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} [_inst_1 : Filter.NeBot.{u1} α l] {a : β} {b : β}, Iff (Eq.{succ (max u1 u2)} (Filter.Germ.{u1, u2} α l β) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) a) ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) b)) (Eq.{succ u2} β a b)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} [_inst_1 : Filter.NeBot.{u2} α l] {a : β} {b : β}, Iff (Eq.{max (succ u2) (succ u1)} (Filter.Germ.{u2, u1} α l β) (Filter.Germ.const.{u2, u1} α β l a) (Filter.Germ.const.{u2, u1} α β l b)) (Eq.{succ u1} β a b)
Case conversion may be inaccurate. Consider using '#align filter.germ.const_inj Filter.Germ.const_injₓ'. -/
@[simp, norm_cast]
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans <| const_eventuallyEq
#align filter.germ.const_inj Filter.Germ.const_inj

/- warning: filter.germ.map_const -> Filter.Germ.map_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (l : Filter.{u1} α) (a : β) (f : β -> γ), Eq.{succ (max u1 u3)} (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.map.{u1, u2, u3} α β γ l f ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) a)) ((fun (a : Type.{u3}) (b : Type.{max u1 u3}) [self : HasLiftT.{succ u3, succ (max u1 u3)} a b] => self.0) γ (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasLiftT.{u1, u3} α γ l) (f a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (l : Filter.{u3} α) (a : β) (f : β -> γ), Eq.{max (succ u3) (succ u2)} (Filter.Germ.{u3, u2} α l γ) (Filter.Germ.map.{u3, u1, u2} α β γ l f (Filter.Germ.const.{u3, u1} α β l a)) (Filter.Germ.const.{u3, u2} α γ l (f a))
Case conversion may be inaccurate. Consider using '#align filter.germ.map_const Filter.Germ.map_constₓ'. -/
@[simp]
theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : Germ l β).map f = ↑(f a) :=
  rfl
#align filter.germ.map_const Filter.Germ.map_const

/- warning: filter.germ.map₂_const -> Filter.Germ.map₂_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (l : Filter.{u1} α) (b : β) (c : γ) (f : β -> γ -> δ), Eq.{succ (max u1 u4)} (Filter.Germ.{u1, u4} α l δ) (Filter.Germ.map₂.{u1, u2, u3, u4} α β γ δ l f ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) b) ((fun (a : Type.{u3}) (b : Type.{max u1 u3}) [self : HasLiftT.{succ u3, succ (max u1 u3)} a b] => self.0) γ (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasLiftT.{u1, u3} α γ l) c)) ((fun (a : Type.{u4}) (b : Type.{max u1 u4}) [self : HasLiftT.{succ u4, succ (max u1 u4)} a b] => self.0) δ (Filter.Germ.{u1, u4} α l δ) (Filter.Germ.hasLiftT.{u1, u4} α δ l) (f b c))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {γ : Type.{u1}} {δ : Type.{u3}} (l : Filter.{u4} α) (b : β) (c : γ) (f : β -> γ -> δ), Eq.{max (succ u4) (succ u3)} (Filter.Germ.{u4, u3} α l δ) (Filter.Germ.map₂.{u4, u2, u1, u3} α β γ δ l f (Filter.Germ.const.{u4, u2} α β l b) (Filter.Germ.const.{u4, u1} α γ l c)) (Filter.Germ.const.{u4, u3} α δ l (f b c))
Case conversion may be inaccurate. Consider using '#align filter.germ.map₂_const Filter.Germ.map₂_constₓ'. -/
@[simp]
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) :
    map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  rfl
#align filter.germ.map₂_const Filter.Germ.map₂_const

/- warning: filter.germ.const_comp_tendsto -> Filter.Germ.const_compTendsto is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} (b : β) {lc : Filter.{u3} γ} {g : γ -> α} (hg : Filter.Tendsto.{u3, u1} γ α g lc l), Eq.{succ (max u3 u2)} (Filter.Germ.{u3, u2} γ lc β) (Filter.Germ.compTendsto.{u1, u2, u3} α β γ l ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) b) lc g hg) ((fun (a : Type.{u2}) (b : Type.{max u3 u2}) [self : HasLiftT.{succ u2, succ (max u3 u2)} a b] => self.0) β (Filter.Germ.{u3, u2} γ lc β) (Filter.Germ.hasLiftT.{u3, u2} γ β lc) b)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {l : Filter.{u3} α} (b : β) {lc : Filter.{u2} γ} {g : γ -> α} (hg : Filter.Tendsto.{u2, u3} γ α g lc l), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u2, u1} γ lc β) (Filter.Germ.compTendsto.{u3, u1, u2} α β γ l (Filter.Germ.const.{u3, u1} α β l b) lc g hg) (Filter.Germ.const.{u2, u1} γ β lc b)
Case conversion may be inaccurate. Consider using '#align filter.germ.const_comp_tendsto Filter.Germ.const_compTendstoₓ'. -/
@[simp]
theorem const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).comp_tendsto g hg = ↑b :=
  rfl
#align filter.germ.const_comp_tendsto Filter.Germ.const_compTendsto

/- warning: filter.germ.const_comp_tendsto' -> Filter.Germ.const_compTendsto' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} (b : β) {lc : Filter.{u3} γ} {g : Filter.Germ.{u3, u1} γ lc α} (hg : Filter.Germ.Tendsto.{u3, u1} γ α lc g l), Eq.{succ (max u3 u2)} (Filter.Germ.{u3, u2} γ lc β) (Filter.Germ.compTendsto'.{u1, u2, u3} α β γ l ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) b) lc g hg) ((fun (a : Type.{u2}) (b : Type.{max u3 u2}) [self : HasLiftT.{succ u2, succ (max u3 u2)} a b] => self.0) β (Filter.Germ.{u3, u2} γ lc β) (Filter.Germ.hasLiftT.{u3, u2} γ β lc) b)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {l : Filter.{u3} α} (b : β) {lc : Filter.{u2} γ} {g : Filter.Germ.{u2, u3} γ lc α} (hg : Filter.Germ.Tendsto.{u2, u3} γ α lc g l), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u2, u1} γ lc β) (Filter.Germ.compTendsto'.{u3, u1, u2} α β γ l (Filter.Germ.const.{u3, u1} α β l b) lc g hg) (Filter.Germ.const.{u2, u1} γ β lc b)
Case conversion may be inaccurate. Consider using '#align filter.germ.const_comp_tendsto' Filter.Germ.const_compTendsto'ₓ'. -/
@[simp]
theorem const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
    (hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b :=
  inductionOn g (fun _ _ => rfl) hg
#align filter.germ.const_comp_tendsto' Filter.Germ.const_compTendsto'

#print Filter.Germ.LiftPred /-
/-- Lift a predicate on `β` to `germ l β`. -/
def LiftPred (p : β → Prop) (f : Germ l β) : Prop :=
  liftOn f (fun f => ∀ᶠ x in l, p (f x)) fun f g H =>
    propext <| eventually_congr <| H.mono fun x hx => hx ▸ Iff.rfl
#align filter.germ.lift_pred Filter.Germ.LiftPred
-/

/- warning: filter.germ.lift_pred_coe -> Filter.Germ.liftPred_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {p : β -> Prop} {f : α -> β}, Iff (Filter.Germ.LiftPred.{u1, u2} α β l p ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f)) (Filter.Eventually.{u1} α (fun (x : α) => p (f x)) l)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} {p : β -> Prop} {f : α -> β}, Iff (Filter.Germ.LiftPred.{u2, u1} α β l p (Filter.Germ.ofFun.{u2, u1} α β l f)) (Filter.Eventually.{u2} α (fun (x : α) => p (f x)) l)
Case conversion may be inaccurate. Consider using '#align filter.germ.lift_pred_coe Filter.Germ.liftPred_coeₓ'. -/
@[simp]
theorem liftPred_coe {p : β → Prop} {f : α → β} : LiftPred p (f : Germ l β) ↔ ∀ᶠ x in l, p (f x) :=
  Iff.rfl
#align filter.germ.lift_pred_coe Filter.Germ.liftPred_coe

/- warning: filter.germ.lift_pred_const -> Filter.Germ.liftPred_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} {p : β -> Prop} {x : β}, (p x) -> (Filter.Germ.LiftPred.{u1, u2} α β l p ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) x))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} {p : β -> Prop} {x : β}, (p x) -> (Filter.Germ.LiftPred.{u2, u1} α β l p (Filter.Germ.const.{u2, u1} α β l x))
Case conversion may be inaccurate. Consider using '#align filter.germ.lift_pred_const Filter.Germ.liftPred_constₓ'. -/
theorem liftPred_const {p : β → Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  eventually_of_forall fun y => hx
#align filter.germ.lift_pred_const Filter.Germ.liftPred_const

/- warning: filter.germ.lift_pred_const_iff -> Filter.Germ.liftPred_const_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {l : Filter.{u1} α} [_inst_1 : Filter.NeBot.{u1} α l] {p : β -> Prop} {x : β}, Iff (Filter.Germ.LiftPred.{u1, u2} α β l p ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) x)) (p x)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {l : Filter.{u2} α} [_inst_1 : Filter.NeBot.{u2} α l] {p : β -> Prop} {x : β}, Iff (Filter.Germ.LiftPred.{u2, u1} α β l p (Filter.Germ.const.{u2, u1} α β l x)) (p x)
Case conversion may be inaccurate. Consider using '#align filter.germ.lift_pred_const_iff Filter.Germ.liftPred_const_iffₓ'. -/
@[simp]
theorem liftPred_const_iff [NeBot l] {p : β → Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)
#align filter.germ.lift_pred_const_iff Filter.Germ.liftPred_const_iff

#print Filter.Germ.LiftRel /-
/-- Lift a relation `r : β → γ → Prop` to `germ l β → germ l γ → Prop`. -/
def LiftRel (r : β → γ → Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  Quotient.liftOn₂' f g (fun f g => ∀ᶠ x in l, r (f x) (g x)) fun f g f' g' Hf Hg =>
    propext <| eventually_congr <| Hg.mp <| Hf.mono fun x hf hg => hf ▸ hg ▸ Iff.rfl
#align filter.germ.lift_rel Filter.Germ.LiftRel
-/

/- warning: filter.germ.lift_rel_coe -> Filter.Germ.liftRel_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ}, Iff (Filter.Germ.LiftRel.{u1, u2, u3} α β γ l r ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> β) (Filter.Germ.{u1, u2} α l β) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> β) (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasCoeT.{u1, u2} α β l))) f) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Type.{max u1 u3}) [self : HasLiftT.{max (succ u1) (succ u3), succ (max u1 u3)} a b] => self.0) (α -> γ) (Filter.Germ.{u1, u3} α l γ) (HasLiftT.mk.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (CoeTCₓ.coe.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> γ) (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasCoeT.{u1, u3} α γ l))) g)) (Filter.Eventually.{u1} α (fun (x : α) => r (f x) (g x)) l)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {l : Filter.{u3} α} {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ}, Iff (Filter.Germ.LiftRel.{u3, u2, u1} α β γ l r (Filter.Germ.ofFun.{u3, u2} α β l f) (Filter.Germ.ofFun.{u3, u1} α γ l g)) (Filter.Eventually.{u3} α (fun (x : α) => r (f x) (g x)) l)
Case conversion may be inaccurate. Consider using '#align filter.germ.lift_rel_coe Filter.Germ.liftRel_coeₓ'. -/
@[simp]
theorem liftRel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    LiftRel r (f : Germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
  Iff.rfl
#align filter.germ.lift_rel_coe Filter.Germ.liftRel_coe

/- warning: filter.germ.lift_rel_const -> Filter.Germ.liftRel_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} {r : β -> γ -> Prop} {x : β} {y : γ}, (r x y) -> (Filter.Germ.LiftRel.{u1, u2, u3} α β γ l r ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) x) ((fun (a : Type.{u3}) (b : Type.{max u1 u3}) [self : HasLiftT.{succ u3, succ (max u1 u3)} a b] => self.0) γ (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasLiftT.{u1, u3} α γ l) y))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {l : Filter.{u3} α} {r : β -> γ -> Prop} {x : β} {y : γ}, (r x y) -> (Filter.Germ.LiftRel.{u3, u2, u1} α β γ l r (Filter.Germ.const.{u3, u2} α β l x) (Filter.Germ.const.{u3, u1} α γ l y))
Case conversion may be inaccurate. Consider using '#align filter.germ.lift_rel_const Filter.Germ.liftRel_constₓ'. -/
theorem liftRel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) :
    LiftRel r (↑x : Germ l β) ↑y :=
  eventually_of_forall fun _ => h
#align filter.germ.lift_rel_const Filter.Germ.liftRel_const

/- warning: filter.germ.lift_rel_const_iff -> Filter.Germ.liftRel_const_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {l : Filter.{u1} α} [_inst_1 : Filter.NeBot.{u1} α l] {r : β -> γ -> Prop} {x : β} {y : γ}, Iff (Filter.Germ.LiftRel.{u1, u2, u3} α β γ l r ((fun (a : Type.{u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ u2, succ (max u1 u2)} a b] => self.0) β (Filter.Germ.{u1, u2} α l β) (Filter.Germ.hasLiftT.{u1, u2} α β l) x) ((fun (a : Type.{u3}) (b : Type.{max u1 u3}) [self : HasLiftT.{succ u3, succ (max u1 u3)} a b] => self.0) γ (Filter.Germ.{u1, u3} α l γ) (Filter.Germ.hasLiftT.{u1, u3} α γ l) y)) (r x y)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {l : Filter.{u3} α} [_inst_1 : Filter.NeBot.{u3} α l] {r : β -> γ -> Prop} {x : β} {y : γ}, Iff (Filter.Germ.LiftRel.{u3, u2, u1} α β γ l r (Filter.Germ.const.{u3, u2} α β l x) (Filter.Germ.const.{u3, u1} α γ l y)) (r x y)
Case conversion may be inaccurate. Consider using '#align filter.germ.lift_rel_const_iff Filter.Germ.liftRel_const_iffₓ'. -/
@[simp]
theorem liftRel_const_iff [NeBot l] {r : β → γ → Prop} {x : β} {y : γ} :
    LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  @eventually_const _ _ _ (r x y)
#align filter.germ.lift_rel_const_iff Filter.Germ.liftRel_const_iff

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
    mul_left_cancel := fun f₁ f₂ f₃ =>
      inductionOn₃ f₁ f₂ f₃ fun f₁ f₂ f₃ H =>
        coe_eq.2 ((coe_eq.1 H).mono fun x => mul_left_cancel) }

@[to_additive AddRightCancelSemigroup]
instance [RightCancelSemigroup M] : RightCancelSemigroup (Germ l M) :=
  { Germ.semigroup with
    mul := (· * ·)
    mul_right_cancel := fun f₁ f₂ f₃ =>
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

/- warning: filter.germ.coe_smul -> Filter.Germ.coe_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {M : Type.{u2}} {G : Type.{u3}} [_inst_1 : SMul.{u2, u3} M G] (n : M) (f : α -> G), Eq.{succ (max u1 u3)} (Filter.Germ.{u1, u3} α l G) ((fun (a : Type.{max u1 u3}) (b : Type.{max u1 u3}) [self : HasLiftT.{succ (max u1 u3), succ (max u1 u3)} a b] => self.0) (α -> G) (Filter.Germ.{u1, u3} α l G) (HasLiftT.mk.{succ (max u1 u3), succ (max u1 u3)} (α -> G) (Filter.Germ.{u1, u3} α l G) (CoeTCₓ.coe.{succ (max u1 u3), succ (max u1 u3)} (α -> G) (Filter.Germ.{u1, u3} α l G) (Filter.Germ.hasCoeT.{u1, u3} α G l))) (SMul.smul.{u2, max u1 u3} M (α -> G) (Function.hasSMul.{u1, u2, u3} α M G _inst_1) n f)) (SMul.smul.{u2, max u1 u3} M (Filter.Germ.{u1, u3} α l G) (Filter.Germ.hasSmul.{u1, u2, u3} α l M G _inst_1) n ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Type.{max u1 u3}) [self : HasLiftT.{max (succ u1) (succ u3), succ (max u1 u3)} a b] => self.0) (α -> G) (Filter.Germ.{u1, u3} α l G) (HasLiftT.mk.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> G) (Filter.Germ.{u1, u3} α l G) (CoeTCₓ.coe.{max (succ u1) (succ u3), succ (max u1 u3)} (α -> G) (Filter.Germ.{u1, u3} α l G) (Filter.Germ.hasCoeT.{u1, u3} α G l))) f))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {M : Type.{u3}} {G : Type.{u2}} [_inst_1 : SMul.{u3, u2} M G] (n : M) (f : α -> G), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α l G) (Filter.Germ.ofFun.{u1, u2} α G l (HSMul.hSMul.{u3, max u1 u2, max u1 u2} M (α -> G) (α -> G) (instHSMul.{u3, max u1 u2} M (α -> G) (Pi.instSMul.{u1, u2, u3} α M (fun (a._@.Mathlib.Order.Filter.Germ._hyg.3271 : α) => G) (fun (i : α) => _inst_1))) n f)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} M (Filter.Germ.{u1, u2} α l G) (Filter.Germ.{u1, u2} α l G) (instHSMul.{u3, max u1 u2} M (Filter.Germ.{u1, u2} α l G) (Filter.Germ.instSMulGerm.{u1, u3, u2} α l M G _inst_1)) n (Filter.Germ.ofFun.{u1, u2} α G l f))
Case conversion may be inaccurate. Consider using '#align filter.germ.coe_smul Filter.Germ.coe_smulₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_smul [SMul M G] (n : M) (f : α → G) : ↑(n • f) = (n • f : Germ l G) :=
  rfl
#align filter.germ.coe_smul Filter.Germ.coe_smul
#align filter.germ.coe_vadd Filter.Germ.coe_vadd

/- warning: filter.germ.const_smul -> Filter.Germ.const_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {M : Type.{u2}} {G : Type.{u3}} [_inst_1 : SMul.{u2, u3} M G] (n : M) (a : G), Eq.{succ (max u1 u3)} (Filter.Germ.{u1, u3} α l G) ((fun (a : Type.{u3}) (b : Type.{max u1 u3}) [self : HasLiftT.{succ u3, succ (max u1 u3)} a b] => self.0) G (Filter.Germ.{u1, u3} α l G) (Filter.Germ.hasLiftT.{u1, u3} α G l) (SMul.smul.{u2, u3} M G _inst_1 n a)) (SMul.smul.{u2, max u1 u3} M (Filter.Germ.{u1, u3} α l G) (Filter.Germ.hasSmul.{u1, u2, u3} α l M G _inst_1) n ((fun (a : Type.{u3}) (b : Type.{max u1 u3}) [self : HasLiftT.{succ u3, succ (max u1 u3)} a b] => self.0) G (Filter.Germ.{u1, u3} α l G) (Filter.Germ.hasLiftT.{u1, u3} α G l) a))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {M : Type.{u3}} {G : Type.{u2}} [_inst_1 : SMul.{u3, u2} M G] (n : M) (a : G), Eq.{max (succ u1) (succ u2)} (Filter.Germ.{u1, u2} α l G) (Filter.Germ.const.{u1, u2} α G l (HSMul.hSMul.{u3, u2, u2} M G G (instHSMul.{u3, u2} M G _inst_1) n a)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} M (Filter.Germ.{u1, u2} α l G) (Filter.Germ.{u1, u2} α l G) (instHSMul.{u3, max u1 u2} M (Filter.Germ.{u1, u2} α l G) (Filter.Germ.instSMulGerm.{u1, u3, u2} α l M G _inst_1)) n (Filter.Germ.const.{u1, u2} α G l a))
Case conversion may be inaccurate. Consider using '#align filter.germ.const_smul Filter.Germ.const_smulₓ'. -/
@[simp, norm_cast, to_additive]
theorem const_smul [SMul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • ↑a :=
  rfl
#align filter.germ.const_smul Filter.Germ.const_smul
#align filter.germ.const_vadd Filter.Germ.const_vadd

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

/- warning: filter.germ.coe_coe_mul_hom -> Filter.Germ.coe_coeMulHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M], Eq.{max (max (succ u1) (succ u2)) (succ (max u1 u2))} ((fun (_x : MonoidHom.{max u1 u2, max u1 u2} (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))) => (α -> M) -> (Filter.Germ.{u1, u2} α l M)) (Filter.Germ.coeMulHom.{u1, u2} α M _inst_1 l)) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (MonoidHom.{max u1 u2, max u1 u2} (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))) (fun (_x : MonoidHom.{max u1 u2, max u1 u2} (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))) => (α -> M) -> (Filter.Germ.{u1, u2} α l M)) (MonoidHom.hasCoeToFun.{max u1 u2, max u1 u2} (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (ᾰ : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))) (Filter.Germ.coeMulHom.{u1, u2} α M _inst_1 l)) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> M) (Filter.Germ.{u1, u2} α l M) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> M) (Filter.Germ.{u1, u2} α l M) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> M) (Filter.Germ.{u1, u2} α l M) (Filter.Germ.hasCoeT.{u1, u2} α M l))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {M : Type.{u2}} [_inst_1 : Monoid.{u2} M], Eq.{max (succ u1) (succ u2)} (forall (a : α -> M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α -> M) => Filter.Germ.{u1, u2} α l M) a) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (MonoidHom.{max u1 u2, max u2 u1} (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.3586 : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))) (α -> M) (fun (_x : α -> M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α -> M) => Filter.Germ.{u1, u2} α l M) _x) (MulHomClass.toFunLike.{max u1 u2, max u1 u2, max u1 u2} (MonoidHom.{max u1 u2, max u2 u1} (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.3586 : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))) (α -> M) (Filter.Germ.{u1, u2} α l M) (MulOneClass.toMul.{max u1 u2} (α -> M) (Pi.mulOneClass.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.3586 : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1))) (MulOneClass.toMul.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))) (MonoidHomClass.toMulHomClass.{max u1 u2, max u1 u2, max u1 u2} (MonoidHom.{max u1 u2, max u2 u1} (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.3586 : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))) (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.3586 : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1)) (MonoidHom.monoidHomClass.{max u1 u2, max u1 u2} (α -> M) (Filter.Germ.{u1, u2} α l M) (Pi.mulOneClass.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.3586 : α) => M) (fun (i : α) => Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toMulOneClass.{max u1 u2} (Filter.Germ.{u1, u2} α l M) (Filter.Germ.monoid.{u1, u2} α l M _inst_1))))) (Filter.Germ.coeMulHom.{u1, u2} α M _inst_1 l)) (Filter.Germ.ofFun.{u1, u2} α M l)
Case conversion may be inaccurate. Consider using '#align filter.germ.coe_coe_mul_hom Filter.Germ.coe_coeMulHomₓ'. -/
@[simp, to_additive]
theorem coe_coeMulHom [Monoid M] : (coeMulHom l : (α → M) → Germ l M) = coe :=
  rfl
#align filter.germ.coe_coe_mul_hom Filter.Germ.coe_coeMulHom
#align filter.germ.coe_coe_add_hom Filter.Germ.coe_coeAddHom

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
    mul_left_inv := by
      rintro ⟨f⟩
      exact congr_arg (Quot.mk _) (mul_left_inv f) }

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
  mul_zero f :=
    inductionOn f fun f => by
      norm_cast
      rw [mul_zero]
  zero_mul f :=
    inductionOn f fun f => by
      norm_cast
      rw [zero_mul]

instance [Distrib R] : Distrib (Germ l R)
    where
  mul := (· * ·)
  add := (· + ·)
  left_distrib f g h :=
    inductionOn₃ f g h fun f g h => by
      norm_cast
      rw [left_distrib]
  right_distrib f g h :=
    inductionOn₃ f g h fun f g h => by
      norm_cast
      rw [right_distrib]

instance [Semiring R] : Semiring (Germ l R) :=
  { Germ.addCommMonoid, Germ.monoid, Germ.distrib, Germ.mulZeroClass, Germ.addMonoidWithOne with }

#print Filter.Germ.coeRingHom /-
/-- Coercion `(α → R) → germ l R` as a `ring_hom`. -/
def coeRingHom [Semiring R] (l : Filter α) : (α → R) →+* Germ l R :=
  { (coeMulHom l : _ →* Germ l R), (coeAddHom l : _ →+ Germ l R) with toFun := coe }
#align filter.germ.coe_ring_hom Filter.Germ.coeRingHom
-/

/- warning: filter.germ.coe_coe_ring_hom -> Filter.Germ.coe_coeRingHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : Filter.{u1} α} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R], Eq.{max (max (succ u1) (succ u2)) (succ (max u1 u2))} ((fun (_x : RingHom.{max u1 u2, max u1 u2} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) => (α -> R) -> (Filter.Germ.{u1, u2} α l R)) (Filter.Germ.coeRingHom.{u1, u2} α R _inst_1 l)) (coeFn.{succ (max u1 u2), succ (max u1 u2)} (RingHom.{max u1 u2, max u1 u2} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) (fun (_x : RingHom.{max u1 u2, max u1 u2} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) => (α -> R) -> (Filter.Germ.{u1, u2} α l R)) (RingHom.hasCoeToFun.{max u1 u2, max u1 u2} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (ᾰ : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) (Filter.Germ.coeRingHom.{u1, u2} α R _inst_1 l)) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Type.{max u1 u2}) [self : HasLiftT.{max (succ u1) (succ u2), succ (max u1 u2)} a b] => self.0) (α -> R) (Filter.Germ.{u1, u2} α l R) (HasLiftT.mk.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> R) (Filter.Germ.{u1, u2} α l R) (CoeTCₓ.coe.{max (succ u1) (succ u2), succ (max u1 u2)} (α -> R) (Filter.Germ.{u1, u2} α l R) (Filter.Germ.hasCoeT.{u1, u2} α R l))))
but is expected to have type
  forall {α : Type.{u1}} {l : Filter.{u1} α} {R : Type.{u2}} [_inst_1 : Semiring.{u2} R], Eq.{max (succ u1) (succ u2)} (forall (a : α -> R), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α -> R) => Filter.Germ.{u1, u2} α l R) a) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{max u1 u2, max u2 u1} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.4987 : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) (α -> R) (fun (_x : α -> R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : α -> R) => Filter.Germ.{u1, u2} α l R) _x) (MulHomClass.toFunLike.{max u1 u2, max u1 u2, max u1 u2} (RingHom.{max u1 u2, max u2 u1} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.4987 : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) (α -> R) (Filter.Germ.{u1, u2} α l R) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (α -> R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (α -> R) (Pi.nonAssocSemiring.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.4987 : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)))) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, max u1 u2, max u1 u2} (RingHom.{max u1 u2, max u2 u1} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.4987 : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) (α -> R) (Filter.Germ.{u1, u2} α l R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (α -> R) (Pi.nonAssocSemiring.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.4987 : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, max u1 u2, max u1 u2} (RingHom.{max u1 u2, max u2 u1} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.4987 : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1))) (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.4987 : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1)) (RingHom.instRingHomClassRingHom.{max u1 u2, max u1 u2} (α -> R) (Filter.Germ.{u1, u2} α l R) (Pi.nonAssocSemiring.{u1, u2} α (fun (a._@.Mathlib.Order.Filter.Germ._hyg.4987 : α) => R) (fun (i : α) => Semiring.toNonAssocSemiring.{u2} R _inst_1)) (Semiring.toNonAssocSemiring.{max u1 u2} (Filter.Germ.{u1, u2} α l R) (Filter.Germ.semiring.{u1, u2} α l R _inst_1)))))) (Filter.Germ.coeRingHom.{u1, u2} α R _inst_1 l)) (Filter.Germ.ofFun.{u1, u2} α R l)
Case conversion may be inaccurate. Consider using '#align filter.germ.coe_coe_ring_hom Filter.Germ.coe_coeRingHomₓ'. -/
@[simp]
theorem coe_coeRingHom [Semiring R] : (coeRingHom l : (α → R) → Germ l R) = coe :=
  rfl
#align filter.germ.coe_coe_ring_hom Filter.Germ.coe_coeRingHom

instance [Ring R] : Ring (Germ l R) :=
  { Germ.addCommGroup, Germ.semiring with }

instance [CommSemiring R] : CommSemiring (Germ l R) :=
  { Germ.semiring, Germ.commMonoid with }

instance [CommRing R] : CommRing (Germ l R) :=
  { Germ.ring, Germ.commMonoid with }

end Ring

section Module

variable {M N R : Type _}

#print Filter.Germ.hasSmul' /-
@[to_additive]
instance hasSmul' [SMul M β] : SMul (Germ l M) (Germ l β) :=
  ⟨map₂ (· • ·)⟩
#align filter.germ.has_smul' Filter.Germ.hasSmul'
#align filter.germ.has_vadd' Filter.Germ.hasVadd'
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
  one_smul f :=
    inductionOn f fun f => by
      norm_cast
      simp only [one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      simp only [mul_smul]

#print Filter.Germ.mulAction' /-
@[to_additive]
instance mulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β)
    where
  one_smul f := inductionOn f fun f => by simp only [← coe_one, ← coe_smul', one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp only [mul_smul]
#align filter.germ.mul_action' Filter.Germ.mulAction'
#align filter.germ.add_action' Filter.Germ.addAction'
-/

instance [Monoid M] [AddMonoid N] [DistribMulAction M N] : DistribMulAction M (Germ l N)
    where
  smul_add c f g :=
    inductionOn₂ f g fun f g => by
      norm_cast
      simp only [smul_add]
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]

#print Filter.Germ.distribMulAction' /-
instance distribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction (Germ l M) (Germ l N)
    where
  smul_add c f g :=
    inductionOn₃ c f g fun c f g => by
      norm_cast
      simp only [smul_add]
  smul_zero c := inductionOn c fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]
#align filter.germ.distrib_mul_action' Filter.Germ.distribMulAction'
-/

instance [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Germ l M)
    where
  add_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      simp only [add_smul]
  zero_smul f :=
    inductionOn f fun f => by
      norm_cast
      simp only [zero_smul, coe_zero]

#print Filter.Germ.module' /-
instance module' [Semiring R] [AddCommMonoid M] [Module R M] : Module (Germ l R) (Germ l M)
    where
  add_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp only [add_smul]
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
  le_refl f := inductionOn f <| EventuallyLe.refl l
  le_trans f₁ f₂ f₃ := inductionOn₃ f₁ f₂ f₃ fun f₁ f₂ f₃ => EventuallyLe.trans

instance [PartialOrder β] : PartialOrder (Germ l β) :=
  { Germ.preorder with
    le := (· ≤ ·)
    le_antisymm := fun f g =>
      inductionOn₂ f g fun f g h₁ h₂ => (EventuallyLe.antisymm h₁ h₂).germ_eq }

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

