import Mathbin.Data.Option.Basic 
import Mathbin.Data.Sum 
import Mathbin.Logic.Unique 
import Mathbin.Logic.Function.Basic 
import Mathbin.Data.Quot 
import Mathbin.Tactic.Simps 
import Mathbin.Logic.Function.Conjugate 
import Mathbin.Data.Prod 
import Mathbin.Tactic.NormCast 
import Mathbin.Data.Sigma.Basic 
import Mathbin.Data.Subtype

/-!
# Equivalence between types

In this file we define two types:

* `equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `equiv.perm α`: the group of permutations `α ≃ α`. More lemmas about `equiv.perm` can be found in
  `group_theory/perm`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `equiv.refl α` is the identity map interpreted as `α ≃ α`;

  - `equiv.sum_equiv_sigma_bool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b : bool, cond b α β`;

  - `equiv.prod_sum_distrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

* operations on equivalences: e.g.,

  - `equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

  - `equiv.prod_congr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `prod.map`.

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `equiv.inhabited` takes `e : α ≃ β` and `[inhabited β]` and returns `inhabited α`;
  - `equiv.unique` takes `e : α ≃ β` and `[unique β]` and returns `unique α`;
  - `equiv.decidable_eq` takes `e : α ≃ β` and `[decidable_eq β]` and returns `decidable_eq α`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

## Tags

equivalence, congruence, bijective map
-/


open Function

universe u v w z

variable {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
@[nolint has_inhabited_instance]
structure Equiv (α : Sort _) (β : Sort _) where 
  toFun : α → β 
  invFun : β → α 
  left_inv : left_inverse inv_fun to_fun 
  right_inv : RightInverse inv_fun to_fun

infixl:25 " ≃ " => Equiv

/-- Convert an involutive function `f` to an equivalence with `to_fun = inv_fun = f`. -/
def Function.Involutive.toEquiv (f : α → α) (h : involutive f) : α ≃ α :=
  ⟨f, f, h.left_inverse, h.right_inverse⟩

namespace Equiv

/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible]
def perm (α : Sort _) :=
  Equiv α α

instance : CoeFun (α ≃ β) fun _ => α → β :=
  ⟨to_fun⟩

@[simp]
theorem coe_fn_mk (f : α → β) g l r : (Equiv.mk f g l r : α → β) = f :=
  rfl

/-- The map `coe_fn : (r ≃ s) → (r → s)` is injective. -/
theorem coe_fn_injective : @Function.Injective (α ≃ β) (α → β) coeFn
| ⟨f₁, g₁, l₁, r₁⟩, ⟨f₂, g₂, l₂, r₂⟩, h =>
  have  : f₁ = f₂ := h 
  have  : g₁ = g₂ := l₁.eq_right_inverse (this.symm ▸ r₂)
  by 
    simp 

@[simp, normCast]
protected theorem coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ :=
  coe_fn_injective.eq_iff

@[ext]
theorem ext {f g : Equiv α β} (H : ∀ x, f x = g x) : f = g :=
  coe_fn_injective (funext H)

protected theorem congr_argₓ {f : Equiv α β} : ∀ {x x' : α}, x = x' → f x = f x'
| _, _, rfl => rfl

protected theorem congr_funₓ {f g : Equiv α β} (h : f = g) (x : α) : f x = g x :=
  h ▸ rfl

theorem ext_iff {f g : Equiv α β} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, ext⟩

@[ext]
theorem perm.ext {σ τ : Equiv.Perm α} (H : ∀ x, σ x = τ x) : σ = τ :=
  Equiv.ext H

protected theorem perm.congr_arg {f : Equiv.Perm α} {x x' : α} : x = x' → f x = f x' :=
  Equiv.congr_arg

protected theorem perm.congr_fun {f g : Equiv.Perm α} (h : f = g) (x : α) : f x = g x :=
  Equiv.congr_fun h x

theorem perm.ext_iff {σ τ : Equiv.Perm α} : σ = τ ↔ ∀ x, σ x = τ x :=
  ext_iff

/-- Any type is equivalent to itself. -/
@[refl]
protected def refl (α : Sort _) : α ≃ α :=
  ⟨id, id, fun x => rfl, fun x => rfl⟩

instance inhabited' : Inhabited (α ≃ α) :=
  ⟨Equiv.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm]
protected def symm (e : α ≃ β) : β ≃ α :=
  ⟨e.inv_fun, e.to_fun, e.right_inv, e.left_inv⟩

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : α ≃ β) : β → α :=
  e.symm

initialize_simps_projections Equiv (toFun → apply, invFun → symmApply)

attribute [simps] Function.Involutive.toEquiv

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans]
protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm, e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simp]
theorem to_fun_as_coe (e : α ≃ β) : e.to_fun = e :=
  rfl

@[simp]
theorem inv_fun_as_coe (e : α ≃ β) : e.inv_fun = e.symm :=
  rfl

protected theorem injective (e : α ≃ β) : injective e :=
  e.left_inv.injective

protected theorem surjective (e : α ≃ β) : surjective e :=
  e.right_inv.surjective

protected theorem bijective (f : α ≃ β) : bijective f :=
  ⟨f.injective, f.surjective⟩

protected theorem Subsingleton (e : α ≃ β) [Subsingleton β] : Subsingleton α :=
  e.injective.subsingleton

protected theorem subsingleton.symm (e : α ≃ β) [Subsingleton α] : Subsingleton β :=
  e.symm.injective.subsingleton

theorem subsingleton_congr (e : α ≃ β) : Subsingleton α ↔ Subsingleton β :=
  ⟨fun h =>
      by 
        exact e.symm.subsingleton,
    fun h =>
      by 
        exact e.subsingleton⟩

instance equiv_subsingleton_cod [Subsingleton β] : Subsingleton (α ≃ β) :=
  ⟨fun f g => Equiv.ext$ fun x => Subsingleton.elimₓ _ _⟩

instance equiv_subsingleton_dom [Subsingleton α] : Subsingleton (α ≃ β) :=
  ⟨fun f g => Equiv.ext$ fun x => @Subsingleton.elimₓ _ (Equiv.subsingleton.symm f) _ _⟩

instance perm_unique [Subsingleton α] : Unique (perm α) :=
  uniqueOfSubsingleton (Equiv.refl α)

theorem perm.subsingleton_eq_refl [Subsingleton α] (e : perm α) : e = Equiv.refl α :=
  Subsingleton.elimₓ _ _

/-- Transfer `decidable_eq` across an equivalence. -/
protected def DecidableEq (e : α ≃ β) [DecidableEq β] : DecidableEq α :=
  e.injective.decidable_eq

theorem nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty β :=
  Nonempty.congr e e.symm

protected theorem Nonempty (e : α ≃ β) [Nonempty β] : Nonempty α :=
  e.nonempty_congr.mpr ‹_›

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def Inhabited [Inhabited β] (e : α ≃ β) : Inhabited α :=
  ⟨e.symm (default _)⟩

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def Unique [Unique β] (e : α ≃ β) : Unique α :=
  e.symm.surjective.unique

/-- Equivalence between equal types. -/
protected def cast {α β : Sort _} (h : α = β) : α ≃ β :=
  ⟨cast h, cast h.symm,
    fun x =>
      by 
        cases h 
        rfl,
    fun x =>
      by 
        cases h 
        rfl⟩

@[simp]
theorem coe_fn_symm_mk (f : α → β) g l r : ((Equiv.mk f g l r).symm : β → α) = g :=
  rfl

@[simp]
theorem coe_refl : «expr⇑ » (Equiv.refl α) = id :=
  rfl

@[simp]
theorem perm.coe_subsingleton {α : Type _} [Subsingleton α] (e : perm α) : «expr⇑ » e = id :=
  by 
    rw [perm.subsingleton_eq_refl e, coe_refl]

theorem refl_apply (x : α) : Equiv.refl α x = x :=
  rfl

@[simp]
theorem coeTransₓ (f : α ≃ β) (g : β ≃ γ) : «expr⇑ » (f.trans g) = g ∘ f :=
  rfl

theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[simp]
theorem apply_symm_apply (e : α ≃ β) (x : β) : e (e.symm x) = x :=
  e.right_inv x

@[simp]
theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
  e.left_inv x

@[simp]
theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[simp]
theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[simp]
theorem symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) : (f.trans g).symm a = f.symm (g.symm a) :=
  rfl

@[simp, nolint simp_nf]
theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b :=
  rfl

@[simp]
theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y :=
  f.injective.eq_iff

theorem apply_eq_iff_eq_symm_apply {α β : Sort _} (f : α ≃ β) {x : α} {y : β} : f x = y ↔ x = f.symm y :=
  by 
    convLHS => rw [←apply_symm_apply f y]
    rw [apply_eq_iff_eq]

@[simp]
theorem cast_apply {α β} (h : α = β) (x : α) : Equiv.cast h x = cast h x :=
  rfl

@[simp]
theorem cast_symm {α β} (h : α = β) : (Equiv.cast h).symm = Equiv.cast h.symm :=
  rfl

@[simp]
theorem cast_refl {α} (h : α = α := rfl) : Equiv.cast h = Equiv.refl α :=
  rfl

@[simp]
theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) : (Equiv.cast h).trans (Equiv.cast h2) = Equiv.cast (h.trans h2) :=
  ext$
    fun x =>
      by 
        substs h h2 
        rfl

theorem cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : Equiv.cast h a = b ↔ HEq a b :=
  by 
    subst h 
    simp 

theorem symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
  ⟨fun H =>
      by 
        simp [H.symm],
    fun H =>
      by 
        simp [H]⟩

theorem eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x :=
  (eq_comm.trans e.symm_apply_eq).trans eq_comm

@[simp]
theorem symm_symm (e : α ≃ β) : e.symm.symm = e :=
  by 
    cases e 
    rfl

@[simp]
theorem trans_refl (e : α ≃ β) : e.trans (Equiv.refl β) = e :=
  by 
    cases e 
    rfl

@[simp]
theorem refl_symm : (Equiv.refl α).symm = Equiv.refl α :=
  rfl

@[simp]
theorem refl_trans (e : α ≃ β) : (Equiv.refl α).trans e = e :=
  by 
    cases e 
    rfl

@[simp]
theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = Equiv.refl β :=
  ext
    (by 
      simp )

@[simp]
theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = Equiv.refl α :=
  ext
    (by 
      simp )

theorem trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) : (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
  Equiv.ext$ fun a => rfl

theorem left_inverse_symm (f : Equiv α β) : left_inverse f.symm f :=
  f.left_inv

theorem right_inverse_symm (f : Equiv α β) : Function.RightInverse f.symm f :=
  f.right_inv

@[simp]
theorem injective_comp (e : α ≃ β) (f : β → γ) : injective (f ∘ e) ↔ injective f :=
  injective.of_comp_iff' f e.bijective

@[simp]
theorem comp_injective (f : α → β) (e : β ≃ γ) : injective (e ∘ f) ↔ injective f :=
  e.injective.of_comp_iff f

@[simp]
theorem surjective_comp (e : α ≃ β) (f : β → γ) : surjective (f ∘ e) ↔ surjective f :=
  e.surjective.of_comp_iff f

@[simp]
theorem comp_surjective (f : α → β) (e : β ≃ γ) : surjective (e ∘ f) ↔ surjective f :=
  surjective.of_comp_iff' e.bijective f

@[simp]
theorem bijective_comp (e : α ≃ β) (f : β → γ) : bijective (f ∘ e) ↔ bijective f :=
  e.bijective.of_comp_iff f

@[simp]
theorem comp_bijective (f : α → β) (e : β ≃ γ) : bijective (e ∘ f) ↔ bijective f :=
  bijective.of_comp_iff' e.bijective f

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equiv_congr {δ} (ab : α ≃ β) (cd : γ ≃ δ) : α ≃ γ ≃ (β ≃ δ) :=
  ⟨fun ac => (ab.symm.trans ac).trans cd, fun bd => ab.trans$ bd.trans$ cd.symm,
    fun ac =>
      by 
        ext x 
        simp ,
    fun ac =>
      by 
        ext x 
        simp ⟩

@[simp]
theorem equiv_congr_refl {α β} : (Equiv.refl α).equivCongr (Equiv.refl β) = Equiv.refl (α ≃ β) :=
  by 
    ext 
    rfl

@[simp]
theorem equiv_congr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) : (ab.equiv_congr cd).symm = ab.symm.equiv_congr cd.symm :=
  by 
    ext 
    rfl

@[simp]
theorem equiv_congr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
  (ab.equiv_congr de).trans (bc.equiv_congr ef) = (ab.trans bc).equivCongr (de.trans ef) :=
  by 
    ext 
    rfl

@[simp]
theorem equiv_congr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) : (Equiv.refl α).equivCongr bg e = e.trans bg :=
  rfl

@[simp]
theorem equiv_congr_refl_right {α β} (ab e : α ≃ β) : ab.equiv_congr (Equiv.refl β) e = ab.symm.trans e :=
  rfl

@[simp]
theorem equiv_congr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) x :
  ab.equiv_congr cd e x = cd (e (ab.symm x)) :=
  rfl

section PermCongr

variable {α' β' : Type _} (e : α' ≃ β')

/-- If `α` is equivalent to `β`, then `perm α` is equivalent to `perm β`. -/
def perm_congr : perm α' ≃ perm β' :=
  equiv_congr e e

theorem perm_congr_def (p : Equiv.Perm α') : e.perm_congr p = (e.symm.trans p).trans e :=
  rfl

@[simp]
theorem perm_congr_refl : e.perm_congr (Equiv.refl _) = Equiv.refl _ :=
  by 
    simp [perm_congr_def]

@[simp]
theorem perm_congr_symm : e.perm_congr.symm = e.symm.perm_congr :=
  rfl

@[simp]
theorem perm_congr_apply (p : Equiv.Perm α') x : e.perm_congr p x = e (p (e.symm x)) :=
  rfl

theorem perm_congr_symm_apply (p : Equiv.Perm β') x : e.perm_congr.symm p x = e.symm (p (e x)) :=
  rfl

theorem perm_congr_trans (p p' : Equiv.Perm α') :
  (e.perm_congr p).trans (e.perm_congr p') = e.perm_congr (p.trans p') :=
  by 
    ext 
    simp 

end PermCongr

/-- If `α` is an empty type, then it is equivalent to the `empty` type. -/
def equiv_empty (α : Sort u) [IsEmpty α] : α ≃ Empty :=
  ⟨isEmptyElim, fun e => e.rec _, isEmptyElim, fun e => e.rec _⟩

/-- `α` is equivalent to an empty type iff `α` is empty. -/
def equiv_empty_equiv (α : Sort u) : α ≃ Empty ≃ IsEmpty α :=
  ⟨fun e => Function.is_empty e, @equiv_empty α, fun e => ext$ fun x => (e x).elim, fun p => rfl⟩

/-- `false` is equivalent to `empty`. -/
def false_equiv_empty : False ≃ Empty :=
  equiv_empty _

/-- If `α` is an empty type, then it is equivalent to the `pempty` type in any universe. -/
def equiv_pempty.{u', v'} (α : Sort v') [IsEmpty α] : α ≃ Pempty.{u'} :=
  ⟨isEmptyElim, fun e => e.rec _, isEmptyElim, fun e => e.rec _⟩

/-- `false` is equivalent to `pempty`. -/
def false_equiv_pempty : False ≃ Pempty :=
  equiv_pempty _

/-- `empty` is equivalent to `pempty`. -/
def empty_equiv_pempty : Empty ≃ Pempty :=
  equiv_pempty _

/-- `pempty` types from any two universes are equivalent. -/
def pempty_equiv_pempty : Pempty.{v} ≃ Pempty.{w} :=
  equiv_pempty _

/-- The `Sort` of proofs of a true proposition is equivalent to `punit`. -/
def prop_equiv_punit {p : Prop} (h : p) : p ≃ PUnit :=
  ⟨fun x => (), fun x => h, fun _ => rfl, fun ⟨⟩ => rfl⟩

/-- The `Sort` of proofs of a false proposition is equivalent to `pempty`. -/
def prop_equiv_pempty {p : Prop} (h : ¬p) : p ≃ Pempty :=
  ⟨fun x => absurd x h,
    fun x =>
      by 
        cases x,
    fun x => absurd x h,
    fun x =>
      by 
        cases x⟩

/-- `true` is equivalent to `punit`. -/
def true_equiv_punit : True ≃ PUnit :=
  prop_equiv_punit trivialₓ

/-- `ulift α` is equivalent to `α`. -/
@[simps (config := { fullyApplied := ff }) apply symmApply]
protected def Ulift {α : Type v} : Ulift.{u} α ≃ α :=
  ⟨Ulift.down, Ulift.up, Ulift.up_down, fun a => rfl⟩

/-- `plift α` is equivalent to `α`. -/
@[simps (config := { fullyApplied := ff }) apply symmApply]
protected def Plift : Plift α ≃ α :=
  ⟨Plift.down, Plift.up, Plift.up_down, Plift.down_up⟩

/-- equivalence of propositions is the same as iff -/
def of_iff {P Q : Prop} (h : P ↔ Q) : P ≃ Q :=
  { toFun := h.mp, invFun := h.mpr, left_inv := fun x => rfl, right_inv := fun y => rfl }

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[congr, simps apply]
def arrow_congr {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  { toFun := fun f => e₂ ∘ f ∘ e₁.symm, invFun := fun f => e₂.symm ∘ f ∘ e₁,
    left_inv :=
      fun f =>
        funext$
          fun x =>
            by 
              simp ,
    right_inv :=
      fun f =>
        funext$
          fun x =>
            by 
              simp  }

theorem arrow_congr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ → β₁)
  (g : β₁ → γ₁) : arrow_congr ea ec (g ∘ f) = arrow_congr eb ec g ∘ arrow_congr ea eb f :=
  by 
    ext 
    simp only [comp, arrow_congr_apply, eb.symm_apply_apply]

@[simp]
theorem arrow_congr_refl {α β : Sort _} : arrow_congr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) :=
  rfl

@[simp]
theorem arrow_congr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
  arrow_congr (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr e₁ e₁').trans (arrow_congr e₂ e₂') :=
  rfl

@[simp]
theorem arrow_congr_symm {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (arrow_congr e₁ e₂).symm = arrow_congr e₁.symm e₂.symm :=
  rfl

/--
A version of `equiv.arrow_congr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `equiv.arrow_congr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[congr, simps apply]
def arrow_congr' {α₁ β₁ α₂ β₂ : Type _} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
  Equiv.arrowCongr hα hβ

@[simp]
theorem arrow_congr'_refl {α β : Type _} : arrow_congr' (Equiv.refl α) (Equiv.refl β) = Equiv.refl (α → β) :=
  rfl

@[simp]
theorem arrow_congr'_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Type _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
  arrow_congr' (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr' e₁ e₁').trans (arrow_congr' e₂ e₂') :=
  rfl

@[simp]
theorem arrow_congr'_symm {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (arrow_congr' e₁ e₂).symm = arrow_congr' e₁.symm e₂.symm :=
  rfl

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
@[simps apply]
def conj (e : α ≃ β) : (α → α) ≃ (β → β) :=
  arrow_congr e e

@[simp]
theorem conj_refl : conj (Equiv.refl α) = Equiv.refl (α → α) :=
  rfl

@[simp]
theorem conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj :=
  rfl

@[simp]
theorem conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : (e₁.trans e₂).conj = e₁.conj.trans e₂.conj :=
  rfl

theorem conj_comp (e : α ≃ β) (f₁ f₂ : α → α) : e.conj (f₁ ∘ f₂) = e.conj f₁ ∘ e.conj f₂ :=
  by 
    apply arrow_congr_comp

section BinaryOp

variable {α₁ β₁ : Type _} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

theorem semiconj_conj (f : α₁ → α₁) : semiconj e f (e.conj f) :=
  fun x =>
    by 
      simp 

theorem semiconj₂_conj : semiconj₂ e f (e.arrow_congr e.conj f) :=
  fun x y =>
    by 
      simp 

instance [IsAssociative α₁ f] : IsAssociative β₁ (e.arrow_congr (e.arrow_congr e) f) :=
  (e.semiconj₂_conj f).is_associative_right e.surjective

instance [IsIdempotent α₁ f] : IsIdempotent β₁ (e.arrow_congr (e.arrow_congr e) f) :=
  (e.semiconj₂_conj f).is_idempotent_right e.surjective

instance [IsLeftCancel α₁ f] : IsLeftCancel β₁ (e.arrow_congr (e.arrow_congr e) f) :=
  ⟨e.surjective.forall₃.2$
      fun x y z =>
        by 
          simpa using @IsLeftCancel.left_cancel _ f _ x y z⟩

instance [IsRightCancel α₁ f] : IsRightCancel β₁ (e.arrow_congr (e.arrow_congr e) f) :=
  ⟨e.surjective.forall₃.2$
      fun x y z =>
        by 
          simpa using @IsRightCancel.right_cancel _ f _ x y z⟩

end BinaryOp

/-- `punit` sorts in any two universes are equivalent. -/
def punit_equiv_punit : PUnit.{v} ≃ PUnit.{w} :=
  ⟨fun _ => PUnit.unit, fun _ => PUnit.unit,
    fun u =>
      by 
        cases u 
        rfl,
    fun u =>
      by 
        cases u 
        rfl⟩

section 

/-- The sort of maps to `punit.{v}` is equivalent to `punit.{w}`. -/
def arrow_punit_equiv_punit (α : Sort _) : (α → PUnit.{v}) ≃ PUnit.{w} :=
  ⟨fun f => PUnit.unit, fun u f => PUnit.unit,
    fun f =>
      by 
        funext x 
        cases f x 
        rfl,
    fun u =>
      by 
        cases u 
        rfl⟩

/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps (config := { fullyApplied := ff })]
def fun_unique α β [Unique α] : (α → β) ≃ β :=
  { toFun := eval (default α), invFun := const α,
    left_inv := fun f => funext$ fun a => congr_argₓ f$ Subsingleton.elimₓ _ _, right_inv := fun b => rfl }

/-- The sort of maps from `punit` is equivalent to the codomain. -/
def punit_arrow_equiv (α : Sort _) : (PUnit.{u} → α) ≃ α :=
  fun_unique _ _

/-- The sort of maps from `true` is equivalent to the codomain. -/
def true_arrow_equiv (α : Sort _) : (True → α) ≃ α :=
  fun_unique _ _

/-- The sort of maps from a type that `is_empty` is equivalent to `punit`. -/
def arrow_punit_of_is_empty (α β : Sort _) [IsEmpty α] : (α → β) ≃ PUnit.{u} :=
  ⟨fun f => PUnit.unit, fun u => isEmptyElim, fun f => funext isEmptyElim,
    fun u =>
      by 
        cases u 
        rfl⟩

/-- The sort of maps from `empty` is equivalent to `punit`. -/
def empty_arrow_equiv_punit (α : Sort _) : (Empty → α) ≃ PUnit.{u} :=
  arrow_punit_of_is_empty _ _

/-- The sort of maps from `pempty` is equivalent to `punit`. -/
def pempty_arrow_equiv_punit (α : Sort _) : (Pempty → α) ≃ PUnit.{u} :=
  arrow_punit_of_is_empty _ _

/-- The sort of maps from `false` is equivalent to `punit`. -/
def false_arrow_equiv_punit (α : Sort _) : (False → α) ≃ PUnit.{u} :=
  arrow_punit_of_is_empty _ _

end 

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. -/
@[congr, simps apply]
def prod_congr {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
  ⟨Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm,
    fun ⟨a, b⟩ =>
      by 
        simp ,
    fun ⟨a, b⟩ =>
      by 
        simp ⟩

@[simp]
theorem prod_congr_symm {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (prod_congr e₁ e₂).symm = prod_congr e₁.symm e₂.symm :=
  rfl

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. -/
@[simps apply]
def prod_comm (α β : Type _) : α × β ≃ β × α :=
  ⟨Prod.swap, Prod.swap, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

@[simp]
theorem prod_comm_symm α β : (prod_comm α β).symm = prod_comm β α :=
  rfl

/-- Type product is associative up to an equivalence. -/
@[simps]
def prod_assoc (α β γ : Sort _) : (α × β) × γ ≃ α × β × γ :=
  ⟨fun p => (p.1.1, p.1.2, p.2), fun p => ((p.1, p.2.1), p.2.2), fun ⟨⟨a, b⟩, c⟩ => rfl, fun ⟨a, ⟨b, c⟩⟩ => rfl⟩

/-- Functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps (config := { fullyApplied := ff })]
def curry (α β γ : Type _) : (α × β → γ) ≃ (α → β → γ) :=
  { toFun := curry, invFun := uncurry, left_inv := uncurry_curry, right_inv := curry_uncurry }

section 

/-- `punit` is a right identity for type product up to an equivalence. -/
@[simps]
def prod_punit (α : Type _) : α × PUnit.{u + 1} ≃ α :=
  ⟨fun p => p.1, fun a => (a, PUnit.unit), fun ⟨_, PUnit.unit⟩ => rfl, fun a => rfl⟩

/-- `punit` is a left identity for type product up to an equivalence. -/
@[simps]
def punit_prod (α : Type _) : PUnit.{u + 1} × α ≃ α :=
  calc PUnit × α ≃ α × PUnit := prod_comm _ _ 
    _ ≃ α := prod_punit _
    

/-- `empty` type is a right absorbing element for type product up to an equivalence. -/
def prod_empty (α : Type _) : α × Empty ≃ Empty :=
  equiv_empty _

/-- `empty` type is a left absorbing element for type product up to an equivalence. -/
def empty_prod (α : Type _) : Empty × α ≃ Empty :=
  equiv_empty _

/-- `pempty` type is a right absorbing element for type product up to an equivalence. -/
def prod_pempty (α : Type _) : α × Pempty ≃ Pempty :=
  equiv_pempty _

/-- `pempty` type is a left absorbing element for type product up to an equivalence. -/
def pempty_prod (α : Type _) : Pempty × α ≃ Pempty :=
  equiv_pempty _

end 

section 

open Sum

/-- `psum` is equivalent to `sum`. -/
def psum_equiv_sum (α β : Type _) : Psum α β ≃ Sum α β :=
  ⟨fun s => Psum.casesOn s inl inr, fun s => Sum.casesOn s Psum.inl Psum.inr,
    fun s =>
      by 
        cases s <;> rfl,
    fun s =>
      by 
        cases s <;> rfl⟩

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. -/
@[simps apply]
def sum_congr {α₁ β₁ α₂ β₂ : Type _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : Sum α₁ β₁ ≃ Sum α₂ β₂ :=
  ⟨Sum.map ea eb, Sum.map ea.symm eb.symm,
    fun x =>
      by 
        simp ,
    fun x =>
      by 
        simp ⟩

@[simp]
theorem sum_congr_trans {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort _} (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) :
  (Equiv.sumCongr e f).trans (Equiv.sumCongr g h) = Equiv.sumCongr (e.trans g) (f.trans h) :=
  by 
    ext i 
    cases i <;> rfl

@[simp]
theorem sum_congr_symm {α β γ δ : Sort _} (e : α ≃ β) (f : γ ≃ δ) :
  (Equiv.sumCongr e f).symm = Equiv.sumCongr e.symm f.symm :=
  rfl

@[simp]
theorem sum_congr_refl {α β : Sort _} : Equiv.sumCongr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (Sum α β) :=
  by 
    ext i 
    cases i <;> rfl

namespace Perm

/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
@[reducible]
def sum_congr {α β : Type _} (ea : Equiv.Perm α) (eb : Equiv.Perm β) : Equiv.Perm (Sum α β) :=
  Equiv.sumCongr ea eb

@[simp]
theorem sum_congr_apply {α β : Type _} (ea : Equiv.Perm α) (eb : Equiv.Perm β) (x : Sum α β) :
  sum_congr ea eb x = Sum.map («expr⇑ » ea) («expr⇑ » eb) x :=
  Equiv.sum_congr_apply ea eb x

@[simp]
theorem sum_congr_trans {α β : Sort _} (e : Equiv.Perm α) (f : Equiv.Perm β) (g : Equiv.Perm α) (h : Equiv.Perm β) :
  (sum_congr e f).trans (sum_congr g h) = sum_congr (e.trans g) (f.trans h) :=
  Equiv.sum_congr_trans e f g h

@[simp]
theorem sum_congr_symm {α β : Sort _} (e : Equiv.Perm α) (f : Equiv.Perm β) :
  (sum_congr e f).symm = sum_congr e.symm f.symm :=
  Equiv.sum_congr_symm e f

@[simp]
theorem sum_congr_refl {α β : Sort _} : sum_congr (Equiv.refl α) (Equiv.refl β) = Equiv.refl (Sum α β) :=
  Equiv.sum_congr_refl

end Perm

/-- `bool` is equivalent the sum of two `punit`s. -/
def bool_equiv_punit_sum_punit : Bool ≃ Sum PUnit.{u + 1} PUnit.{v + 1} :=
  ⟨fun b => cond b (inr PUnit.unit) (inl PUnit.unit), fun s => Sum.recOn s (fun _ => ff) fun _ => tt,
    fun b =>
      by 
        cases b <;> rfl,
    fun s =>
      by 
        rcases s with (⟨⟨⟩⟩ | ⟨⟨⟩⟩) <;> rfl⟩

/-- `Prop` is noncomputably equivalent to `bool`. -/
noncomputable def Prop_equiv_bool : Prop ≃ Bool :=
  ⟨fun p => @to_bool p (Classical.propDecidable _), fun b => b,
    fun p =>
      by 
        simp ,
    fun b =>
      by 
        simp ⟩

/-- Sum of types is commutative up to an equivalence. -/
@[simps apply]
def sum_comm (α β : Sort _) : Sum α β ≃ Sum β α :=
  ⟨Sum.swap, Sum.swap, Sum.swap_swap, Sum.swap_swap⟩

@[simp]
theorem sum_comm_symm α β : (sum_comm α β).symm = sum_comm β α :=
  rfl

/-- Sum of types is associative up to an equivalence. -/
def sum_assoc (α β γ : Sort _) : Sum (Sum α β) γ ≃ Sum α (Sum β γ) :=
  ⟨Sum.elim (Sum.elim Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr),
    Sum.elim (Sum.inl ∘ Sum.inl)$ Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr,
    by 
      rintro (⟨_ | _⟩ | _) <;> rfl,
    by 
      rintro (_ | ⟨_ | _⟩) <;> rfl⟩

@[simp]
theorem sum_assoc_apply_in1 {α β γ} a : sum_assoc α β γ (inl (inl a)) = inl a :=
  rfl

@[simp]
theorem sum_assoc_apply_in2 {α β γ} b : sum_assoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl

@[simp]
theorem sum_assoc_apply_in3 {α β γ} c : sum_assoc α β γ (inr c) = inr (inr c) :=
  rfl

/-- Sum with `empty` is equivalent to the original type. -/
@[simps symmApply]
def sum_empty (α β : Type _) [IsEmpty β] : Sum α β ≃ α :=
  ⟨Sum.elim id isEmptyElim, inl,
    fun s =>
      by 
        rcases s with (_ | x)
        rfl 
        exact isEmptyElim x,
    fun a => rfl⟩

@[simp]
theorem sum_empty_apply_inl {α β : Type _} [IsEmpty β] (a : α) : sum_empty α β (Sum.inl a) = a :=
  rfl

/-- The sum of `empty` with any `Sort*` is equivalent to the right summand. -/
@[simps symmApply]
def empty_sum (α β : Type _) [IsEmpty α] : Sum α β ≃ β :=
  (sum_comm _ _).trans$ sum_empty _ _

@[simp]
theorem empty_sum_apply_inr {α β : Type _} [IsEmpty α] (b : β) : empty_sum α β (Sum.inr b) = b :=
  rfl

/-- `option α` is equivalent to `α ⊕ punit` -/
def option_equiv_sum_punit (α : Type _) : Option α ≃ Sum α PUnit.{u + 1} :=
  ⟨fun o =>
      match o with 
      | none => inr PUnit.unit
      | some a => inl a,
    fun s =>
      match s with 
      | inr _ => none
      | inl a => some a,
    fun o =>
      by 
        cases o <;> rfl,
    fun s =>
      by 
        rcases s with (_ | ⟨⟨⟩⟩) <;> rfl⟩

@[simp]
theorem option_equiv_sum_punit_none {α} : option_equiv_sum_punit α none = Sum.inr PUnit.unit :=
  rfl

@[simp]
theorem option_equiv_sum_punit_some {α} a : option_equiv_sum_punit α (some a) = Sum.inl a :=
  rfl

@[simp]
theorem option_equiv_sum_punit_coe {α} (a : α) : option_equiv_sum_punit α a = Sum.inl a :=
  rfl

@[simp]
theorem option_equiv_sum_punit_symm_inl {α} a : (option_equiv_sum_punit α).symm (Sum.inl a) = a :=
  rfl

@[simp]
theorem option_equiv_sum_punit_symm_inr {α} a : (option_equiv_sum_punit α).symm (Sum.inr a) = none :=
  rfl

/-- The set of `x : option α` such that `is_some x` is equivalent to `α`. -/
@[simps]
def option_is_some_equiv (α : Type _) : { x : Option α // x.is_some } ≃ α :=
  { toFun := fun o => Option.get o.2,
    invFun :=
      fun x =>
        ⟨some x,
          by 
            decide⟩,
    left_inv := fun o => Subtype.eq$ Option.some_get _, right_inv := fun x => Option.get_some _ _ }

/-- The product over `option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps]
def pi_option_equiv_prod {α : Type _} {β : Option α → Type _} : (∀ a : Option α, β a) ≃ β none × ∀ a : α, β (some a) :=
  { toFun := fun f => (f none, fun a => f (some a)), invFun := fun x a => Option.casesOn a x.fst x.snd,
    left_inv :=
      fun f =>
        funext$
          fun a =>
            by 
              cases a <;> rfl,
    right_inv :=
      fun x =>
        by 
          simp  }

/-- `α ⊕ β` is equivalent to a `sigma`-type over `bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot by used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ulift` to work around this
difficulty. -/
def sum_equiv_sigma_bool (α β : Type u) : Sum α β ≃ Σb : Bool, cond b α β :=
  ⟨fun s => s.elim (fun x => ⟨tt, x⟩) fun x => ⟨ff, x⟩,
    fun s =>
      match s with 
      | ⟨tt, a⟩ => inl a
      | ⟨ff, b⟩ => inr b,
    fun s =>
      by 
        cases s <;> rfl,
    fun s =>
      by 
        rcases s with ⟨_ | _, _⟩ <;> rfl⟩

/-- `sigma_preimage_equiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simps]
def sigma_preimage_equiv {α β : Type _} (f : α → β) : (Σy : β, { x // f x = y }) ≃ α :=
  ⟨fun x => «expr↑ » x.2, fun x => ⟨f x, x, rfl⟩, fun ⟨y, x, rfl⟩ => rfl, fun x => rfl⟩

end 

section SumCompl

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtype_or_equiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `is_compl p q`.  -/
def sum_compl {α : Type _} (p : α → Prop) [DecidablePred p] : Sum { a // p a } { a // ¬p a } ≃ α :=
  { toFun := Sum.elim coeₓ coeₓ, invFun := fun a => if h : p a then Sum.inl ⟨a, h⟩ else Sum.inr ⟨a, h⟩,
    left_inv :=
      by 
        rintro (⟨x, hx⟩ | ⟨x, hx⟩) <;> dsimp <;> [rw [dif_pos], rw [dif_neg]],
    right_inv :=
      fun a =>
        by 
          dsimp 
          splitIfs <;> rfl }

@[simp]
theorem sum_compl_apply_inl {α : Type _} (p : α → Prop) [DecidablePred p] (x : { a // p a }) :
  sum_compl p (Sum.inl x) = x :=
  rfl

@[simp]
theorem sum_compl_apply_inr {α : Type _} (p : α → Prop) [DecidablePred p] (x : { a // ¬p a }) :
  sum_compl p (Sum.inr x) = x :=
  rfl

@[simp]
theorem sum_compl_apply_symm_of_pos {α : Type _} (p : α → Prop) [DecidablePred p] (a : α) (h : p a) :
  (sum_compl p).symm a = Sum.inl ⟨a, h⟩ :=
  dif_pos h

@[simp]
theorem sum_compl_apply_symm_of_neg {α : Type _} (p : α → Prop) [DecidablePred p] (a : α) (h : ¬p a) :
  (sum_compl p).symm a = Sum.inr ⟨a, h⟩ :=
  dif_neg h

/-- Combines an `equiv` between two subtypes with an `equiv` between their complements to form a
  permutation. -/
def subtype_congr {α : Type _} {p q : α → Prop} [DecidablePred p] [DecidablePred q] (e : { x // p x } ≃ { x // q x })
  (f : { x // ¬p x } ≃ { x // ¬q x }) : perm α :=
  (sum_compl p).symm.trans ((sum_congr e f).trans (sum_compl q))

open Equiv

variable {ε : Type _} {p : ε → Prop} [DecidablePred p]

variable (ep ep' : perm { a // p a }) (en en' : perm { a // ¬p a })

/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
def perm.subtype_congr : Equiv.Perm ε :=
  perm_congr (sum_compl p) (sum_congr ep en)

theorem perm.subtype_congr.apply (a : ε) : ep.subtype_congr en a = if h : p a then ep ⟨a, h⟩ else en ⟨a, h⟩ :=
  by 
    byCases' h : p a <;> simp [perm.subtype_congr, h]

@[simp]
theorem perm.subtype_congr.left_apply {a : ε} (h : p a) : ep.subtype_congr en a = ep ⟨a, h⟩ :=
  by 
    simp [perm.subtype_congr.apply, h]

@[simp]
theorem perm.subtype_congr.left_apply_subtype (a : { a // p a }) : ep.subtype_congr en a = ep a :=
  by 
    convert perm.subtype_congr.left_apply _ _ a.property 
    simp 

@[simp]
theorem perm.subtype_congr.right_apply {a : ε} (h : ¬p a) : ep.subtype_congr en a = en ⟨a, h⟩ :=
  by 
    simp [perm.subtype_congr.apply, h]

@[simp]
theorem perm.subtype_congr.right_apply_subtype (a : { a // ¬p a }) : ep.subtype_congr en a = en a :=
  by 
    convert perm.subtype_congr.right_apply _ _ a.property 
    simp 

@[simp]
theorem perm.subtype_congr.refl :
  perm.subtype_congr (Equiv.refl { a // p a }) (Equiv.refl { a // ¬p a }) = Equiv.refl ε :=
  by 
    ext x 
    byCases' h : p x <;> simp [h]

-- error in Data.Equiv.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem perm.subtype_congr.symm : «expr = »((ep.subtype_congr en).symm, perm.subtype_congr ep.symm en.symm) :=
begin
  ext [] [ident x] [],
  by_cases [expr h, ":", expr p x],
  { have [] [":", expr p (ep.symm ⟨x, h⟩)] [":=", expr subtype.property _],
    simp [] [] [] ["[", expr perm.subtype_congr.apply, ",", expr h, ",", expr symm_apply_eq, ",", expr this, "]"] [] [] },
  { have [] [":", expr «expr¬ »(p (en.symm ⟨x, h⟩))] [":=", expr subtype.property (en.symm _)],
    simp [] [] [] ["[", expr perm.subtype_congr.apply, ",", expr h, ",", expr symm_apply_eq, ",", expr this, "]"] [] [] }
end

-- error in Data.Equiv.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem perm.subtype_congr.trans : «expr = »((ep.subtype_congr en).trans (ep'.subtype_congr en'), perm.subtype_congr (ep.trans ep') (en.trans en')) :=
begin
  ext [] [ident x] [],
  by_cases [expr h, ":", expr p x],
  { have [] [":", expr p (ep ⟨x, h⟩)] [":=", expr subtype.property _],
    simp [] [] [] ["[", expr perm.subtype_congr.apply, ",", expr h, ",", expr this, "]"] [] [] },
  { have [] [":", expr «expr¬ »(p (en ⟨x, h⟩))] [":=", expr subtype.property (en _)],
    simp [] [] [] ["[", expr perm.subtype_congr.apply, ",", expr h, ",", expr symm_apply_eq, ",", expr this, "]"] [] [] }
end

end SumCompl

section SubtypePreimage

variable (p : α → Prop) [DecidablePred p] (x₀ : { a // p a } → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtype_preimage : { x : α → β // x ∘ coeₓ = x₀ } ≃ ({ a // ¬p a } → β) :=
  { toFun := fun x : { x : α → β // x ∘ coeₓ = x₀ } a => (x : α → β) a,
    invFun := fun x => ⟨fun a => if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩, funext$ fun ⟨a, h⟩ => dif_pos h⟩,
    left_inv :=
      fun ⟨x, hx⟩ =>
        Subtype.val_injective$
          funext$
            fun a =>
              by 
                dsimp 
                splitIfs <;> [rw [←hx], skip] <;> rfl,
    right_inv :=
      fun x =>
        funext$
          fun ⟨a, h⟩ =>
            show dite (p a) _ _ = _ by 
              dsimp 
              rw [dif_neg h] }

theorem subtype_preimage_symm_apply_coe_pos (x : { a // ¬p a } → β) (a : α) (h : p a) :
  ((subtype_preimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
  dif_pos h

theorem subtype_preimage_symm_apply_coe_neg (x : { a // ¬p a } → β) (a : α) (h : ¬p a) :
  ((subtype_preimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
  dif_neg h

end SubtypePreimage

section 

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Π a, β₁ a` and
`Π a, β₂ a`. -/
def Pi_congr_right {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) : (∀ a, β₁ a) ≃ ∀ a, β₂ a :=
  ⟨fun H a => F a (H a), fun H a => (F a).symm (H a),
    fun H =>
      funext$
        by 
          simp ,
    fun H =>
      funext$
        by 
          simp ⟩

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `sigma.curry` and `sigma.uncurry` together as an equiv. -/
def Pi_curry {α} {β : α → Sort _} (γ : ∀ a, β a → Sort _) : (∀ x : Σi, β i, γ x.1 x.2) ≃ ∀ a b, γ a b :=
  { toFun := Sigma.curry, invFun := Sigma.uncurry, left_inv := Sigma.uncurry_curry, right_inv := Sigma.curry_uncurry }

end 

section 

/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symmApply]
def psigma_equiv_sigma {α} (β : α → Type _) : (Σ'i, β i) ≃ Σi, β i :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps apply]
def psigma_congr_right {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) : (Σ'a, β₁ a) ≃ Σ'a, β₂ a :=
  ⟨fun a => ⟨a.1, F a.1 a.2⟩, fun a => ⟨a.1, (F a.1).symm a.2⟩,
    fun ⟨a, b⟩ => congr_argₓ (Psigma.mk a)$ symm_apply_apply (F a) b,
    fun ⟨a, b⟩ => congr_argₓ (Psigma.mk a)$ apply_symm_apply (F a) b⟩

@[simp]
theorem psigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
  (psigma_congr_right F).trans (psigma_congr_right G) = psigma_congr_right fun a => (F a).trans (G a) :=
  by 
    ext1 x 
    cases x 
    rfl

@[simp]
theorem psigma_congr_right_symm {α} {β₁ β₂ : α → Sort _} (F : ∀ a, β₁ a ≃ β₂ a) :
  (psigma_congr_right F).symm = psigma_congr_right fun a => (F a).symm :=
  by 
    ext1 x 
    cases x 
    rfl

@[simp]
theorem psigma_congr_right_refl {α} {β : α → Sort _} :
  (psigma_congr_right fun a => Equiv.refl (β a)) = Equiv.refl (Σ'a, β a) :=
  by 
    ext1 x 
    cases x 
    rfl

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps apply]
def sigma_congr_right {α} {β₁ β₂ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) : (Σa, β₁ a) ≃ Σa, β₂ a :=
  ⟨fun a => ⟨a.1, F a.1 a.2⟩, fun a => ⟨a.1, (F a.1).symm a.2⟩,
    fun ⟨a, b⟩ => congr_argₓ (Sigma.mk a)$ symm_apply_apply (F a) b,
    fun ⟨a, b⟩ => congr_argₓ (Sigma.mk a)$ apply_symm_apply (F a) b⟩

@[simp]
theorem sigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) (G : ∀ a, β₂ a ≃ β₃ a) :
  (sigma_congr_right F).trans (sigma_congr_right G) = sigma_congr_right fun a => (F a).trans (G a) :=
  by 
    ext1 x 
    cases x 
    rfl

@[simp]
theorem sigma_congr_right_symm {α} {β₁ β₂ : α → Type _} (F : ∀ a, β₁ a ≃ β₂ a) :
  (sigma_congr_right F).symm = sigma_congr_right fun a => (F a).symm :=
  by 
    ext1 x 
    cases x 
    rfl

@[simp]
theorem sigma_congr_right_refl {α} {β : α → Type _} :
  (sigma_congr_right fun a => Equiv.refl (β a)) = Equiv.refl (Σa, β a) :=
  by 
    ext1 x 
    cases x 
    rfl

/-- A `psigma` with `Prop` fibers is equivalent to the subtype.  -/
def psigma_equiv_subtype {α : Type v} (P : α → Prop) : (Σ'i, P i) ≃ Subtype P :=
  { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩,
    left_inv :=
      fun x =>
        by 
          cases x 
          rfl,
    right_inv :=
      fun x =>
        by 
          cases x 
          rfl }

/-- A `sigma` with `plift` fibers is equivalent to the subtype. -/
def sigma_plift_equiv_subtype {α : Type v} (P : α → Prop) : (Σi, Plift (P i)) ≃ Subtype P :=
  ((psigma_equiv_sigma _).symm.trans (psigma_congr_right fun a => Equiv.plift)).trans (psigma_equiv_subtype P)

/--
A `sigma` with `λ i, ulift (plift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigma_plift_equiv_subtype`.
-/
def sigma_ulift_plift_equiv_subtype {α : Type v} (P : α → Prop) : (Σi, Ulift (Plift (P i))) ≃ Subtype P :=
  (sigma_congr_right fun a => Equiv.ulift).trans (sigma_plift_equiv_subtype P)

namespace Perm

/-- A family of permutations `Π a, perm (β a)` generates a permuation `perm (Σ a, β₁ a)`. -/
@[reducible]
def sigma_congr_right {α} {β : α → Sort _} (F : ∀ a, perm (β a)) : perm (Σa, β a) :=
  Equiv.sigmaCongrRight F

@[simp]
theorem sigma_congr_right_trans {α} {β : α → Sort _} (F : ∀ a, perm (β a)) (G : ∀ a, perm (β a)) :
  (sigma_congr_right F).trans (sigma_congr_right G) = sigma_congr_right fun a => (F a).trans (G a) :=
  Equiv.sigma_congr_right_trans F G

@[simp]
theorem sigma_congr_right_symm {α} {β : α → Sort _} (F : ∀ a, perm (β a)) :
  (sigma_congr_right F).symm = sigma_congr_right fun a => (F a).symm :=
  Equiv.sigma_congr_right_symm F

@[simp]
theorem sigma_congr_right_refl {α} {β : α → Sort _} :
  (sigma_congr_right fun a => Equiv.refl (β a)) = Equiv.refl (Σa, β a) :=
  Equiv.sigma_congr_right_refl

end Perm

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps apply]
def sigma_congr_left {α₁ α₂} {β : α₂ → Sort _} (e : α₁ ≃ α₂) : (Σa : α₁, β (e a)) ≃ Σa : α₂, β a :=
  ⟨fun a => ⟨e a.1, a.2⟩, fun a => ⟨e.symm a.1, @Eq.ndrec β a.2 (e.right_inv a.1).symm⟩,
    fun ⟨a, b⟩ =>
      match e.symm (e a), e.left_inv a with 
      | _, rfl => rfl,
    fun ⟨a, b⟩ =>
      match e (e.symm a), _ with 
      | _, rfl => rfl⟩

/-- Transporting a sigma type through an equivalence of the base -/
def sigma_congr_left' {α₁ α₂} {β : α₁ → Sort _} (f : α₁ ≃ α₂) : (Σa : α₁, β a) ≃ Σa : α₂, β (f.symm a) :=
  (sigma_congr_left f.symm).symm

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigma_congr {α₁ α₂} {β₁ : α₁ → Sort _} {β₂ : α₂ → Sort _} (f : α₁ ≃ α₂) (F : ∀ a, β₁ a ≃ β₂ (f a)) :
  Sigma β₁ ≃ Sigma β₂ :=
  (sigma_congr_right F).trans (sigma_congr_left f)

/-- `sigma` type with a constant fiber is equivalent to the product. -/
@[simps apply symmApply]
def sigma_equiv_prod (α β : Type _) : (Σ_ : α, β) ≃ α × β :=
  ⟨fun a => ⟨a.1, a.2⟩, fun a => ⟨a.1, a.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- If each fiber of a `sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigma_equiv_prod_of_equiv {α β} {β₁ : α → Sort _} (F : ∀ a, β₁ a ≃ β) : Sigma β₁ ≃ α × β :=
  (sigma_congr_right F).trans (sigma_equiv_prod α β)

/-- Dependent product of types is associative up to an equivalence. -/
def sigma_assoc {α : Type _} {β : α → Type _} (γ : ∀ a : α, β a → Type _) :
  (Σab : Σa : α, β a, γ ab.1 ab.2) ≃ Σa : α, Σb : β a, γ a b :=
  { toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩, invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
    left_inv := fun ⟨⟨a, b⟩, c⟩ => rfl, right_inv := fun ⟨a, ⟨b, c⟩⟩ => rfl }

end 

section ProdCongr

variable {α₁ β₁ β₂ : Type _} (e : α₁ → β₁ ≃ β₂)

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
def prod_congr_left : β₁ × α₁ ≃ β₂ × α₁ :=
  { toFun := fun ab => ⟨e ab.2 ab.1, ab.2⟩, invFun := fun ab => ⟨(e ab.2).symm ab.1, ab.2⟩,
    left_inv :=
      by 
        rintro ⟨a, b⟩
        simp ,
    right_inv :=
      by 
        rintro ⟨a, b⟩
        simp  }

@[simp]
theorem prod_congr_left_apply (b : β₁) (a : α₁) : prod_congr_left e (b, a) = (e a b, a) :=
  rfl

theorem prod_congr_refl_right (e : β₁ ≃ β₂) : prod_congr e (Equiv.refl α₁) = prod_congr_left fun _ => e :=
  by 
    ext ⟨a, b⟩ : 1
    simp 

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
def prod_congr_right : α₁ × β₁ ≃ α₁ × β₂ :=
  { toFun := fun ab => ⟨ab.1, e ab.1 ab.2⟩, invFun := fun ab => ⟨ab.1, (e ab.1).symm ab.2⟩,
    left_inv :=
      by 
        rintro ⟨a, b⟩
        simp ,
    right_inv :=
      by 
        rintro ⟨a, b⟩
        simp  }

@[simp]
theorem prod_congr_right_apply (a : α₁) (b : β₁) : prod_congr_right e (a, b) = (a, e a b) :=
  rfl

theorem prod_congr_refl_left (e : β₁ ≃ β₂) : prod_congr (Equiv.refl α₁) e = prod_congr_right fun _ => e :=
  by 
    ext ⟨a, b⟩ : 1
    simp 

@[simp]
theorem prod_congr_left_trans_prod_comm :
  (prod_congr_left e).trans (prod_comm _ _) = (prod_comm _ _).trans (prod_congr_right e) :=
  by 
    ext ⟨a, b⟩ : 1
    simp 

@[simp]
theorem prod_congr_right_trans_prod_comm :
  (prod_congr_right e).trans (prod_comm _ _) = (prod_comm _ _).trans (prod_congr_left e) :=
  by 
    ext ⟨a, b⟩ : 1
    simp 

theorem sigma_congr_right_sigma_equiv_prod :
  (sigma_congr_right e).trans (sigma_equiv_prod α₁ β₂) = (sigma_equiv_prod α₁ β₁).trans (prod_congr_right e) :=
  by 
    ext ⟨a, b⟩ : 1
    simp 

theorem sigma_equiv_prod_sigma_congr_right :
  (sigma_equiv_prod α₁ β₁).symm.trans (sigma_congr_right e) =
    (prod_congr_right e).trans (sigma_equiv_prod α₁ β₂).symm :=
  by 
    ext ⟨a, b⟩ : 1
    simp 

/-- A variation on `equiv.prod_congr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simps (config := { fullyApplied := ff })]
def prod_shear {α₁ β₁ α₂ β₂ : Type _} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
  { toFun := fun x : α₁ × β₁ => (e₁ x.1, e₂ x.1 x.2),
    invFun := fun y : α₂ × β₂ => (e₁.symm y.1, (e₂$ e₁.symm y.1).symm y.2),
    left_inv :=
      by 
        rintro ⟨x₁, y₁⟩
        simp only [symm_apply_apply],
    right_inv :=
      by 
        rintro ⟨x₁, y₁⟩
        simp only [apply_symm_apply] }

end ProdCongr

namespace Perm

variable {α₁ β₁ β₂ : Type _} [DecidableEq α₁] (a : α₁) (e : perm β₁)

/-- `prod_extend_right a e` extends `e : perm β` to `perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
def prod_extend_right : perm (α₁ × β₁) :=
  { toFun := fun ab => if ab.fst = a then (a, e ab.snd) else ab,
    invFun := fun ab => if ab.fst = a then (a, e.symm ab.snd) else ab,
    left_inv :=
      by 
        rintro ⟨k', x⟩
        simp only 
        splitIfs with h <;> simp [h],
    right_inv :=
      by 
        rintro ⟨k', x⟩
        simp only 
        splitIfs with h <;> simp [h] }

@[simp]
theorem prod_extend_right_apply_eq (b : β₁) : prod_extend_right a e (a, b) = (a, e b) :=
  if_pos rfl

theorem prod_extend_right_apply_ne {a a' : α₁} (h : a' ≠ a) (b : β₁) : prod_extend_right a e (a', b) = (a', b) :=
  if_neg h

theorem eq_of_prod_extend_right_ne {e : perm β₁} {a a' : α₁} {b : β₁} (h : prod_extend_right a e (a', b) ≠ (a', b)) :
  a' = a :=
  by 
    contrapose! h 
    exact prod_extend_right_apply_ne _ h _

@[simp]
theorem fst_prod_extend_right (ab : α₁ × β₁) : (prod_extend_right a e ab).fst = ab.fst :=
  by 
    rw [prod_extend_right, coe_fn_mk]
    splitIfs with h
    ·
      rw [h]
    ·
      rfl

end Perm

section 

/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrow_prod_equiv_prod_arrow (α β γ : Type _) : (γ → α × β) ≃ (γ → α) × (γ → β) :=
  ⟨fun f => (fun c => (f c).1, fun c => (f c).2), fun p c => (p.1 c, p.2 c), fun f => funext$ fun c => Prod.mk.eta,
    fun p =>
      by 
        cases p 
        rfl⟩

open Sum

/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sum_arrow_equiv_prod_arrow (α β γ : Type _) : (Sum α β → γ) ≃ (α → γ) × (β → γ) :=
  ⟨fun f => (f ∘ inl, f ∘ inr), fun p => Sum.elim p.1 p.2,
    fun f =>
      by 
        ext ⟨⟩ <;> rfl,
    fun p =>
      by 
        cases p 
        rfl⟩

@[simp]
theorem sum_arrow_equiv_prod_arrow_apply_fst {α β γ} (f : Sum α β → γ) (a : α) :
  (sum_arrow_equiv_prod_arrow α β γ f).1 a = f (inl a) :=
  rfl

@[simp]
theorem sum_arrow_equiv_prod_arrow_apply_snd {α β γ} (f : Sum α β → γ) (b : β) :
  (sum_arrow_equiv_prod_arrow α β γ f).2 b = f (inr b) :=
  rfl

@[simp]
theorem sum_arrow_equiv_prod_arrow_symm_apply_inl {α β γ} (f : α → γ) (g : β → γ) (a : α) :
  ((sum_arrow_equiv_prod_arrow α β γ).symm (f, g)) (inl a) = f a :=
  rfl

@[simp]
theorem sum_arrow_equiv_prod_arrow_symm_apply_inr {α β γ} (f : α → γ) (g : β → γ) (b : β) :
  ((sum_arrow_equiv_prod_arrow α β γ).symm (f, g)) (inr b) = g b :=
  rfl

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sum_prod_distrib (α β γ : Sort _) : Sum α β × γ ≃ Sum (α × γ) (β × γ) :=
  ⟨fun p =>
      match p with 
      | (inl a, c) => inl (a, c)
      | (inr b, c) => inr (b, c),
    fun s =>
      match s with 
      | inl q => (inl q.1, q.2)
      | inr q => (inr q.1, q.2),
    fun p =>
      by 
        rcases p with ⟨_ | _, _⟩ <;> rfl,
    fun s =>
      by 
        rcases s with (⟨_, _⟩ | ⟨_, _⟩) <;> rfl⟩

@[simp]
theorem sum_prod_distrib_apply_left {α β γ} (a : α) (c : γ) : sum_prod_distrib α β γ (Sum.inl a, c) = Sum.inl (a, c) :=
  rfl

@[simp]
theorem sum_prod_distrib_apply_right {α β γ} (b : β) (c : γ) : sum_prod_distrib α β γ (Sum.inr b, c) = Sum.inr (b, c) :=
  rfl

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prod_sum_distrib (α β γ : Sort _) : α × Sum β γ ≃ Sum (α × β) (α × γ) :=
  calc α × Sum β γ ≃ Sum β γ × α := prod_comm _ _ 
    _ ≃ Sum (β × α) (γ × α) := sum_prod_distrib _ _ _ 
    _ ≃ Sum (α × β) (α × γ) := sum_congr (prod_comm _ _) (prod_comm _ _)
    

@[simp]
theorem prod_sum_distrib_apply_left {α β γ} (a : α) (b : β) : prod_sum_distrib α β γ (a, Sum.inl b) = Sum.inl (a, b) :=
  rfl

@[simp]
theorem prod_sum_distrib_apply_right {α β γ} (a : α) (c : γ) : prod_sum_distrib α β γ (a, Sum.inr c) = Sum.inr (a, c) :=
  rfl

/-- The product of an indexed sum of types (formally, a `sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigma_prod_distrib {ι : Type _} (α : ι → Type _) (β : Type _) : (Σi, α i) × β ≃ Σi, α i × β :=
  ⟨fun p => ⟨p.1.1, (p.1.2, p.2)⟩, fun p => (⟨p.1, p.2.1⟩, p.2.2),
    fun p =>
      by 
        rcases p with ⟨⟨_, _⟩, _⟩
        rfl,
    fun p =>
      by 
        rcases p with ⟨_, ⟨_, _⟩⟩
        rfl⟩

/-- The product `bool × α` is equivalent to `α ⊕ α`. -/
def bool_prod_equiv_sum (α : Type u) : Bool × α ≃ Sum α α :=
  calc Bool × α ≃ Sum Unit Unit × α := prod_congr bool_equiv_punit_sum_punit (Equiv.refl _)
    _ ≃ Sum (Unit × α) (Unit × α) := sum_prod_distrib _ _ _ 
    _ ≃ Sum α α := sum_congr (punit_prod _) (punit_prod _)
    

/-- The function type `bool → α` is equivalent to `α × α`. -/
@[simps]
def bool_arrow_equiv_prod (α : Type u) : (Bool → α) ≃ α × α :=
  { toFun := fun f => (f tt, f ff), invFun := fun p b => cond b p.1 p.2,
    left_inv := fun f => funext$ Bool.forall_bool.2 ⟨rfl, rfl⟩, right_inv := fun ⟨x, y⟩ => rfl }

end 

section 

open Sum Nat

/-- The set of natural numbers is equivalent to `ℕ ⊕ punit`. -/
def nat_equiv_nat_sum_punit : ℕ ≃ Sum ℕ PUnit.{u + 1} :=
  ⟨fun n =>
      match n with 
      | zero => inr PUnit.unit
      | succ a => inl a,
    fun s =>
      match s with 
      | inl n => succ n
      | inr PUnit.unit => zero,
    fun n =>
      by 
        cases n 
        repeat' 
          rfl,
    fun s =>
      by 
        cases' s with a u
        ·
          rfl
        ·
          cases u
          ·
            rfl⟩

/-- `ℕ ⊕ punit` is equivalent to `ℕ`. -/
def nat_sum_punit_equiv_nat : Sum ℕ PUnit.{u + 1} ≃ ℕ :=
  nat_equiv_nat_sum_punit.symm

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def int_equiv_nat_sum_nat : ℤ ≃ Sum ℕ ℕ :=
  by 
    refine' ⟨_, _, _, _⟩ <;>
      intro z <;>
        first |
          cases z <;> [left, right] <;> assumption|
          cases z <;> rfl

end 

/-- An equivalence between `α` and `β` generates an equivalence between `list α` and `list β`. -/
def list_equiv_of_equiv {α β : Type _} (e : α ≃ β) : List α ≃ List β :=
  { toFun := List.map e, invFun := List.map e.symm,
    left_inv :=
      fun l =>
        by 
          rw [List.map_mapₓ, e.symm_comp_self, List.map_id],
    right_inv :=
      fun l =>
        by 
          rw [List.map_mapₓ, e.self_comp_symm, List.map_id] }

/-- `fin n` is equivalent to `{m // m < n}`. -/
def fin_equiv_subtype (n : ℕ) : Finₓ n ≃ { m // m < n } :=
  ⟨fun x => ⟨x.1, x.2⟩, fun x => ⟨x.1, x.2⟩, fun ⟨a, b⟩ => rfl, fun ⟨a, b⟩ => rfl⟩

/-- If `α` is equivalent to `β`, then `unique α` is equivalent to `unique β`. -/
def unique_congr (e : α ≃ β) : Unique α ≃ Unique β :=
  { toFun := fun h => @Equiv.unique _ _ h e.symm, invFun := fun h => @Equiv.unique _ _ h e,
    left_inv := fun _ => Subsingleton.elimₓ _ _, right_inv := fun _ => Subsingleton.elimₓ _ _ }

/-- If `α` is equivalent to `β`, then `is_empty α` is equivalent to `is_empty β`. -/
theorem is_empty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β :=
  ⟨fun h => @Function.is_empty _ _ h e.symm, fun h => @Function.is_empty _ _ h e⟩

protected theorem IsEmpty (e : α ≃ β) [IsEmpty β] : IsEmpty α :=
  e.is_empty_congr.mpr ‹_›

section 

open Subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `perm.subtype_perm`. -/
def subtype_equiv {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) :
  { a : α // p a } ≃ { b : β // q b } :=
  ⟨fun x => ⟨e x, (h _).1 x.2⟩,
    fun y =>
      ⟨e.symm y,
        (h _).2
          (by 
            simp 
            exact y.2)⟩,
    fun ⟨x, h⟩ =>
      Subtype.ext_val$
        by 
          simp ,
    fun ⟨y, h⟩ =>
      Subtype.ext_val$
        by 
          simp ⟩

@[simp]
theorem subtype_equiv_refl {p : α → Prop} (h : ∀ a, p a ↔ p (Equiv.refl _ a) := fun a => Iff.rfl) :
  (Equiv.refl α).subtypeEquiv h = Equiv.refl { a : α // p a } :=
  by 
    ext 
    rfl

@[simp]
theorem subtype_equiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) :
  (e.subtype_equiv h).symm =
    e.symm.subtype_equiv
      fun a =>
        by 
          convert (h$ e.symm a).symm 
          exact (e.apply_symm_apply a).symm :=
  rfl

@[simp]
theorem subtype_equiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop} (e : α ≃ β) (f : β ≃ γ)
  (h : ∀ a : α, p a ↔ q (e a)) (h' : ∀ b : β, q b ↔ r (f b)) :
  (e.subtype_equiv h).trans (f.subtype_equiv h') = (e.trans f).subtypeEquiv fun a => (h a).trans (h'$ e a) :=
  rfl

@[simp]
theorem subtype_equiv_apply {p : α → Prop} {q : β → Prop} (e : α ≃ β) (h : ∀ a : α, p a ↔ q (e a)) (x : { x // p x }) :
  e.subtype_equiv h x = ⟨e x, (h _).1 x.2⟩ :=
  rfl

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps]
def subtype_equiv_right {p q : α → Prop} (e : ∀ x, p x ↔ q x) : { x // p x } ≃ { x // q x } :=
  subtype_equiv (Equiv.refl _) e

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtype_equiv_of_subtype {p : β → Prop} (e : α ≃ β) : { a : α // p (e a) } ≃ { b : β // p b } :=
  subtype_equiv e$
    by 
      simp 

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtype_equiv_of_subtype' {p : α → Prop} (e : α ≃ β) : { a : α // p a } ≃ { b : β // p (e.symm b) } :=
  e.symm.subtype_equiv_of_subtype.symm

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtype_equiv_prop {α : Type _} {p q : α → Prop} (h : p = q) : Subtype p ≃ Subtype q :=
  subtype_equiv (Equiv.refl α) fun a => h ▸ Iff.rfl

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
def subtype_subtype_equiv_subtype_exists {α : Type u} (p : α → Prop) (q : Subtype p → Prop) :
  Subtype q ≃ { a : α // ∃ h : p a, q ⟨a, h⟩ } :=
  ⟨fun ⟨⟨a, ha⟩, ha'⟩ => ⟨a, ha, ha'⟩,
    fun ⟨a, ha⟩ =>
      ⟨⟨a, ha.cases_on$ fun h _ => h⟩,
        by 
          cases ha 
          exact ha_h⟩,
    fun ⟨⟨a, ha⟩, h⟩ => rfl, fun ⟨a, h₁, h₂⟩ => rfl⟩

@[simp]
theorem subtype_subtype_equiv_subtype_exists_apply {α : Type u} (p : α → Prop) (q : Subtype p → Prop) a :
  (subtype_subtype_equiv_subtype_exists p q a : α) = a :=
  by 
    cases a 
    cases a_val 
    rfl

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
def subtype_subtype_equiv_subtype_inter {α : Type u} (p q : α → Prop) :
  { x : Subtype p // q x.1 } ≃ Subtype fun x => p x ∧ q x :=
  (subtype_subtype_equiv_subtype_exists p _).trans$ subtype_equiv_right$ fun x => exists_prop

@[simp]
theorem subtype_subtype_equiv_subtype_inter_apply {α : Type u} (p q : α → Prop) a :
  (subtype_subtype_equiv_subtype_inter p q a : α) = a :=
  by 
    cases a 
    cases a_val 
    rfl

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
def subtype_subtype_equiv_subtype {α : Type u} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
  { x : Subtype p // q x.1 } ≃ Subtype q :=
  (subtype_subtype_equiv_subtype_inter p _).trans$ subtype_equiv_right$ fun x => ⟨And.right, fun h₁ => ⟨h h₁, h₁⟩⟩

@[simp]
theorem subtype_subtype_equiv_subtype_apply {α : Type u} {p q : α → Prop} (h : ∀ x, q x → p x)
  (a : { x : Subtype p // q x.1 }) : (subtype_subtype_equiv_subtype h a : α) = a :=
  by 
    cases a 
    cases a_val 
    rfl

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symmApply]
def subtype_univ_equiv {α : Type u} {p : α → Prop} (h : ∀ x, p x) : Subtype p ≃ α :=
  ⟨fun x => x, fun x => ⟨x, h x⟩, fun x => Subtype.eq rfl, fun x => rfl⟩

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtype_sigma_equiv {α : Type u} (p : α → Type v) (q : α → Prop) :
  { y : Sigma p // q y.1 } ≃ Σx : Subtype q, p x.1 :=
  ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, fun ⟨⟨x, h⟩, y⟩ => rfl, fun ⟨⟨x, y⟩, h⟩ => rfl⟩

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigma_subtype_equiv_of_subset {α : Type u} (p : α → Type v) (q : α → Prop) (h : ∀ x, p x → q x) :
  (Σx : Subtype q, p x) ≃ Σx : α, p x :=
  (subtype_sigma_equiv p q).symm.trans$ subtype_univ_equiv$ fun x => h x.1 x.2

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigma_subtype_preimage_equiv {α : Type u} {β : Type v} (f : α → β) (p : β → Prop) (h : ∀ x, p (f x)) :
  (Σy : Subtype p, { x : α // f x = y }) ≃ α :=
  calc _ ≃ Σy : β, { x : α // f x = y } := sigma_subtype_equiv_of_subset _ p fun y ⟨x, h'⟩ => h' ▸ h x 
    _ ≃ α := sigma_preimage_equiv f
    

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigma_subtype_preimage_equiv_subtype {α : Type u} {β : Type v} (f : α → β) {p : α → Prop} {q : β → Prop}
  (h : ∀ x, p x ↔ q (f x)) : (Σy : Subtype q, { x : α // f x = y }) ≃ Subtype p :=
  calc
    (Σy : Subtype q, { x : α // f x = y }) ≃ Σy : Subtype q, { x : Subtype p // Subtype.mk (f x) ((h x).1 x.2) = y } :=
    by 
      apply sigma_congr_right 
      intro y 
      symm 
      refine' (subtype_subtype_equiv_subtype_exists _ _).trans (subtype_equiv_right _)
      intro x 
      exact ⟨fun ⟨hp, h'⟩ => congr_argₓ Subtype.val h', fun h' => ⟨(h x).2 (h'.symm ▸ y.2), Subtype.eq h'⟩⟩
    _ ≃ Subtype p := sigma_preimage_equiv fun x : Subtype p => (⟨f x, (h x).1 x.property⟩ : Subtype q)
    

-- error in Data.Equiv.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A sigma type over an `option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigma_option_equiv_of_some
{α : Type u}
(p : option α → Type v)
(h : p none → false) : «expr ≃ »(«exprΣ , »((x : option α), p x), «exprΣ , »((x : α), p (some x))) :=
begin
  have [ident h'] [":", expr ∀ x, p x → x.is_some] [],
  { intro [ident x],
    cases [expr x] [],
    { intro [ident n],
      exfalso,
      exact [expr h n] },
    { intro [ident s],
      exact [expr rfl] } },
  exact [expr (sigma_subtype_equiv_of_subset _ _ h').symm.trans (sigma_congr_left' (option_is_some_equiv α))]
end

/-- The `pi`-type `Π i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`sigma` type such that for all `i` we have `(f i).fst = i`. -/
def pi_equiv_subtype_sigma (ι : Type _) (π : ι → Type _) : (∀ i, π i) ≃ { f : ι → Σi, π i // ∀ i, (f i).1 = i } :=
  ⟨fun f => ⟨fun i => ⟨i, f i⟩, fun i => rfl⟩,
    fun f i =>
      by 
        rw [←f.2 i]
        exact (f.1 i).2,
    fun f => funext$ fun i => rfl,
    fun ⟨f, hf⟩ =>
      Subtype.eq$ funext$ fun i => Sigma.eq (hf i).symm$ eq_of_heq$ rec_heq_of_heq _$ rec_heq_of_heq _$ HEq.refl _⟩

/-- The set of functions `f : Π a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the set of functions `Π a, {b : β a // p a b}`. -/
def subtype_pi_equiv_pi {α : Sort u} {β : α → Sort v} {p : ∀ a, β a → Prop} :
  { f : ∀ a, β a // ∀ a, p a (f a) } ≃ ∀ a, { b : β a // p a b } :=
  ⟨fun f a => ⟨f.1 a, f.2 a⟩, fun f => ⟨fun a => (f a).1, fun a => (f a).2⟩,
    by 
      rintro ⟨f, h⟩
      rfl,
    by 
      rintro f 
      funext a 
      exact Subtype.ext_val rfl⟩

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtype_prod_equiv_prod {α : Type u} {β : Type v} {p : α → Prop} {q : β → Prop} :
  { c : α × β // p c.1 ∧ q c.2 } ≃ { a // p a } × { b // q b } :=
  ⟨fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩, fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl,
    fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl⟩

/-- A subtype of a `prod` is equivalent to a sigma type whose fibers are subtypes. -/
def subtype_prod_equiv_sigma_subtype {α β : Type _} (p : α → β → Prop) :
  { x : α × β // p x.1 x.2 } ≃ Σa, { b : β // p a b } :=
  { toFun := fun x => ⟨x.1.1, x.1.2, x.prop⟩, invFun := fun x => ⟨⟨x.1, x.2⟩, x.2.Prop⟩,
    left_inv :=
      fun x =>
        by 
          ext <;> rfl,
    right_inv := fun ⟨a, b, pab⟩ => rfl }

/-- The type `Π (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps]
def pi_equiv_pi_subtype_prod {α : Type _} (p : α → Prop) (β : α → Type _) [DecidablePred p] :
  (∀ i : α, β i) ≃ (∀ i : { x // p x }, β i) × ∀ i : { x // ¬p x }, β i :=
  { toFun := fun f => (fun x => f x, fun x => f x), invFun := fun f x => if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩,
    right_inv :=
      by 
        rintro ⟨f, g⟩
        ext1 <;>
          ·
            ext y 
            rcases y with ⟨⟩
            simp only [y_property, dif_pos, dif_neg, not_false_iff, Subtype.coe_mk]
            rfl,
    left_inv :=
      fun f =>
        by 
          ext x 
          byCases' h : p x <;>
            ·
              simp only [h, dif_neg, dif_pos, not_false_iff]
              rfl }

end 

section SubtypeEquivCodomain

variable {X : Type _} {Y : Type _} [DecidableEq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtype_equiv_codomain (f : { x' // x' ≠ x } → Y) : { g : X → Y // g ∘ coeₓ = f } ≃ Y :=
  (subtype_preimage _ f).trans$
    @fun_unique { x' // ¬x' ≠ x } _$
      show Unique { x' // ¬x' ≠ x } from
        @Equiv.unique _ _
          (show Unique { x' // x' = x } from { default := ⟨x, rfl⟩, uniq := fun ⟨x', h⟩ => Subtype.val_injective h })
          (subtype_equiv_right$ fun a => not_not)

@[simp]
theorem coe_subtype_equiv_codomain (f : { x' // x' ≠ x } → Y) :
  (subtype_equiv_codomain f : { g : X → Y // g ∘ coeₓ = f } → Y) = fun g => (g : X → Y) x :=
  rfl

@[simp]
theorem subtype_equiv_codomain_apply (f : { x' // x' ≠ x } → Y) (g : { g : X → Y // g ∘ coeₓ = f }) :
  subtype_equiv_codomain f g = (g : X → Y) x :=
  rfl

theorem coe_subtype_equiv_codomain_symm (f : { x' // x' ≠ x } → Y) :
  ((subtype_equiv_codomain f).symm : Y → { g : X → Y // g ∘ coeₓ = f }) =
    fun y =>
      ⟨fun x' => if h : x' ≠ x then f ⟨x', h⟩ else y,
        by 
          funext x' 
          dsimp 
          erw [dif_pos x'.2, Subtype.coe_eta]⟩ :=
  rfl

@[simp]
theorem subtype_equiv_codomain_symm_apply (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) :
  ((subtype_equiv_codomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
  rfl

@[simp]
theorem subtype_equiv_codomain_symm_apply_eq (f : { x' // x' ≠ x } → Y) (y : Y) :
  ((subtype_equiv_codomain f).symm y : X → Y) x = y :=
  dif_neg (not_not.mpr rfl)

theorem subtype_equiv_codomain_symm_apply_ne (f : { x' // x' ≠ x } → Y) (y : Y) (x' : X) (h : x' ≠ x) :
  ((subtype_equiv_codomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
  dif_pos h

end SubtypeEquivCodomain

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps apply]
noncomputable def of_bijective {α β} (f : α → β) (hf : bijective f) : α ≃ β :=
  { toFun := f, invFun := Function.surjInv hf.surjective, left_inv := Function.left_inverse_surj_inv hf,
    right_inv := Function.right_inverse_surj_inv _ }

theorem of_bijective_apply_symm_apply {α β} (f : α → β) (hf : bijective f) (x : β) :
  f ((of_bijective f hf).symm x) = x :=
  (of_bijective f hf).apply_symm_apply x

@[simp]
theorem of_bijective_symm_apply_apply {α β} (f : α → β) (hf : bijective f) (x : α) :
  (of_bijective f hf).symm (f x) = x :=
  (of_bijective f hf).symm_apply_apply x

section 

variable {α' β' : Type _} (e : perm α') {p : β' → Prop} [DecidablePred p] (f : α' ≃ Subtype p)

/--
Extend the domain of `e : equiv.perm α` to one that is over `β` via `f : α → subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `set.range f` fixed. For this use-case `equiv` given by `f` can
be constructed by `equiv.of_left_inverse'` or `equiv.of_left_inverse` when there is a known
inverse, or `equiv.of_injective` in the general case.`.
-/
def perm.extend_domain : perm β' :=
  (perm_congr f e).subtypeCongr (Equiv.refl _)

@[simp]
theorem perm.extend_domain_apply_image (a : α') : e.extend_domain f (f a) = f (e a) :=
  by 
    simp [perm.extend_domain]

theorem perm.extend_domain_apply_subtype {b : β'} (h : p b) : e.extend_domain f b = f (e (f.symm ⟨b, h⟩)) :=
  by 
    simp [perm.extend_domain, h]

theorem perm.extend_domain_apply_not_subtype {b : β'} (h : ¬p b) : e.extend_domain f b = b :=
  by 
    simp [perm.extend_domain, h]

@[simp]
theorem perm.extend_domain_refl : perm.extend_domain (Equiv.refl _) f = Equiv.refl _ :=
  by 
    simp [perm.extend_domain]

@[simp]
theorem perm.extend_domain_symm : (e.extend_domain f).symm = perm.extend_domain e.symm f :=
  rfl

theorem perm.extend_domain_trans (e e' : perm α') :
  (e.extend_domain f).trans (e'.extend_domain f) = perm.extend_domain (e.trans e') f :=
  by 
    simp [perm.extend_domain, perm_congr_trans]

end 

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtype_quotient_equiv_quotient_subtype (p₁ : α → Prop) [s₁ : Setoidₓ α] [s₂ : Setoidₓ (Subtype p₁)]
  (p₂ : Quotientₓ s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ («expr⟦ ⟧» a))
  (h : ∀ x y : Subtype p₁, @Setoidₓ.R _ s₂ x y ↔ (x : α) ≈ y) : { x // p₂ x } ≃ Quotientₓ s₂ :=
  { toFun :=
      fun a =>
        Quotientₓ.hrecOn a.1 (fun a h => «expr⟦ ⟧» ⟨a, (hp₂ _).2 h⟩)
          (fun a b hab =>
            hfunext
              (by 
                rw [Quotientₓ.sound hab])
              fun h₁ h₂ _ => heq_of_eq (Quotientₓ.sound ((h _ _).2 hab)))
          a.2,
    invFun :=
      fun a =>
        Quotientₓ.liftOn a (fun a => (⟨«expr⟦ ⟧» a.1, (hp₂ _).1 a.2⟩ : { x // p₂ x }))
          fun a b hab => Subtype.ext_val (Quotientₓ.sound ((h _ _).1 hab)),
    left_inv := fun ⟨a, ha⟩ => Quotientₓ.induction_on a (fun a ha => rfl) ha,
    right_inv := fun a => Quotientₓ.induction_on a fun ⟨a, ha⟩ => rfl }

section Swap

variable [DecidableEq α]

/-- A helper function for `equiv.swap`. -/
def swap_core (a b r : α) : α :=
  if r = a then b else if r = b then a else r

theorem swap_core_self (r a : α) : swap_core a a r = r :=
  by 
    unfold swap_core 
    splitIfs <;> cc

theorem swap_core_swap_core (r a b : α) : swap_core a b (swap_core a b r) = r :=
  by 
    unfold swap_core 
    splitIfs <;> cc

theorem swap_core_comm (r a b : α) : swap_core a b r = swap_core b a r :=
  by 
    unfold swap_core 
    splitIfs <;> cc

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : perm α :=
  ⟨swap_core a b, swap_core a b, fun r => swap_core_swap_core r a b, fun r => swap_core_swap_core r a b⟩

@[simp]
theorem swap_self (a : α) : swap a a = Equiv.refl _ :=
  ext$ fun r => swap_core_self r a

theorem swap_comm (a b : α) : swap a b = swap b a :=
  ext$ fun r => swap_core_comm r _ _

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
  rfl

@[simp]
theorem swap_apply_left (a b : α) : swap a b a = b :=
  if_pos rfl

@[simp]
theorem swap_apply_right (a b : α) : swap a b b = a :=
  by 
    byCases' h : b = a <;> simp [swap_apply_def, h]

-- error in Data.Equiv.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem swap_apply_of_ne_of_ne {a b x : α} : «expr ≠ »(x, a) → «expr ≠ »(x, b) → «expr = »(swap a b x, x) :=
by simp [] [] [] ["[", expr swap_apply_def, "]"] [] [] { contextual := tt }

@[simp]
theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = Equiv.refl _ :=
  ext$ fun x => swap_core_swap_core _ _ _

@[simp]
theorem symm_swap (a b : α) : (swap a b).symm = swap a b :=
  rfl

@[simp]
theorem swap_eq_refl_iff {x y : α} : swap x y = Equiv.refl _ ↔ x = y :=
  by 
    refine' ⟨fun h => (Equiv.refl _).Injective _, fun h => h ▸ swap_self _⟩
    rw [←h, swap_apply_left, h, refl_apply]

theorem swap_comp_apply {a b x : α} (π : perm α) :
  π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x :=
  by 
    cases π 
    rfl

theorem swap_eq_update (i j : α) : (Equiv.swap i j : α → α) = update (update id j i) i j :=
  funext$
    fun x =>
      by 
        rw [update_apply _ i j, update_apply _ j i, Equiv.swap_apply_def, id.def]

theorem comp_swap_eq_update (i j : α) (f : α → β) : f ∘ Equiv.swap i j = update (update f j (f i)) i (f j) :=
  by 
    rw [swap_eq_update, comp_update, comp_update, comp.right_id]

-- error in Data.Equiv.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem symm_trans_swap_trans
[decidable_eq β]
(a b : α)
(e : «expr ≃ »(α, β)) : «expr = »((e.symm.trans (swap a b)).trans e, swap (e a) (e b)) :=
equiv.ext (λ x, begin
   have [] [":", expr ∀
    a, «expr ↔ »(«expr = »(e.symm x, a), «expr = »(x, e a))] [":=", expr λ a, by { rw [expr @eq_comm _ (e.symm x)] [],
      split; intros []; simp [] [] [] ["*"] [] ["at", "*"] }],
   simp [] [] [] ["[", expr swap_apply_def, ",", expr this, "]"] [] [],
   split_ifs [] []; simp [] [] [] [] [] []
 end)

@[simp]
theorem trans_swap_trans_symm [DecidableEq β] (a b : β) (e : α ≃ β) :
  (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
  symm_trans_swap_trans a b e.symm

@[simp]
theorem swap_apply_self (i j a : α) : swap i j (swap i j a) = a :=
  by 
    rw [←Equiv.trans_apply, Equiv.swap_swap, Equiv.refl_apply]

/-- A function is invariant to a swap if it is equal at both elements -/
theorem apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) : v (swap i j k) = v k :=
  by 
    byCases' hi : k = i
    ·
      rw [hi, swap_apply_left, hv]
    byCases' hj : k = j
    ·
      rw [hj, swap_apply_right, hv]
    rw [swap_apply_of_ne_of_ne hi hj]

theorem swap_apply_eq_iff {x y z w : α} : swap x y z = w ↔ z = swap x y w :=
  by 
    rw [apply_eq_iff_eq_symm_apply, symm_swap]

theorem swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) :=
  by 
    byCases' hab : a = b
    ·
      simp [hab]
    byCases' hax : x = a
    ·
      simp [hax, eq_comm]
    byCases' hbx : x = b
    ·
      simp [hbx]
    simp [hab, hax, hbx, swap_apply_of_ne_of_ne]

namespace Perm

@[simp]
theorem sum_congr_swap_refl {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : α) :
  Equiv.Perm.sumCongr (Equiv.swap i j) (Equiv.refl β) = Equiv.swap (Sum.inl i) (Sum.inl j) :=
  by 
    ext x 
    cases x
    ·
      simp [Sum.map, swap_apply_def]
      splitIfs <;> rfl
    ·
      simp [Sum.map, swap_apply_of_ne_of_ne]

@[simp]
theorem sum_congr_refl_swap {α β : Sort _} [DecidableEq α] [DecidableEq β] (i j : β) :
  Equiv.Perm.sumCongr (Equiv.refl α) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) :=
  by 
    ext x 
    cases x
    ·
      simp [Sum.map, swap_apply_of_ne_of_ne]
    ·
      simp [Sum.map, swap_apply_def]
      splitIfs <;> rfl

end Perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def set_value (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
  (swap a (f.symm b)).trans f

@[simp]
theorem set_value_eq (f : α ≃ β) (a : α) (b : β) : set_value f a b a = b :=
  by 
    dsimp [set_value]
    simp [swap_apply_left]

end Swap

end Equiv

theorem Plift.eq_up_iff_down_eq {x : Plift α} {y : α} : x = Plift.up y ↔ x.down = y :=
  Equiv.plift.eq_symm_apply

theorem Function.Injective.map_swap {α β : Type _} [DecidableEq α] [DecidableEq β] {f : α → β}
  (hf : Function.Injective f) (x y z : α) : f (Equiv.swap x y z) = Equiv.swap (f x) (f y) (f z) :=
  by 
    convRHS => rw [Equiv.swap_apply_def]
    splitIfs with h₁ h₂
    ·
      rw [hf h₁, Equiv.swap_apply_left]
    ·
      rw [hf h₂, Equiv.swap_apply_right]
    ·
      rw [Equiv.swap_apply_of_ne_of_ne (mt (congr_argₓ f) h₁) (mt (congr_argₓ f) h₂)]

namespace Equiv

protected theorem exists_unique_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x}, p x ↔ q (f x)) :
  (∃!x, p x) ↔ ∃!y, q y :=
  by 
    split 
    ·
      rintro ⟨a, ha₁, ha₂⟩
      exact
        ⟨f a, h.1 ha₁,
          fun b hb =>
            f.symm_apply_eq.1
              (ha₂ (f.symm b)
                (h.2
                  (by 
                    simpa using hb)))⟩
    ·
      rintro ⟨b, hb₁, hb₂⟩
      exact
        ⟨f.symm b,
          h.2
            (by 
              simpa using hb₁),
          fun y hy => (eq_symm_apply f).2 (hb₂ _ (h.1 hy))⟩

protected theorem exists_unique_congr_left' {p : α → Prop} (f : α ≃ β) : (∃!x, p x) ↔ ∃!y, p (f.symm y) :=
  Equiv.exists_unique_congr f
    fun x =>
      by 
        simp 

protected theorem exists_unique_congr_left {p : β → Prop} (f : α ≃ β) : (∃!x, p (f x)) ↔ ∃!y, p y :=
  (Equiv.exists_unique_congr_left' f.symm).symm

protected theorem forall_congrₓ {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x}, p x ↔ q (f x)) :
  (∀ x, p x) ↔ ∀ y, q y :=
  by 
    split  <;> intro h₂ x
    ·
      rw [←f.right_inv x]
      apply h.mp 
      apply h₂ 
    apply h.mpr 
    apply h₂

protected theorem forall_congr' {p : α → Prop} {q : β → Prop} (f : α ≃ β) (h : ∀ {x}, p (f.symm x) ↔ q x) :
  (∀ x, p x) ↔ ∀ y, q y :=
  (Equiv.forall_congr f.symm fun x => h.symm).symm

universe ua1 ua2 ub1 ub2 ug1 ug2

variable {α₁ : Sort ua1} {α₂ : Sort ua2} {β₁ : Sort ub1} {β₂ : Sort ub2} {γ₁ : Sort ug1} {γ₂ : Sort ug2}

protected theorem forall₂_congr {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
  (h : ∀ {x y}, p x y ↔ q (eα x) (eβ y)) : (∀ x y, p x y) ↔ ∀ x y, q x y :=
  by 
    apply Equiv.forall_congr 
    intros 
    apply Equiv.forall_congr 
    intros 
    apply h

protected theorem forall₂_congr' {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
  (h : ∀ {x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) : (∀ x y, p x y) ↔ ∀ x y, q x y :=
  (Equiv.forall₂_congr eα.symm eβ.symm fun x y => h.symm).symm

protected theorem forall₃_congrₓ {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
  (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) : (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  by 
    apply Equiv.forall₂_congr 
    intros 
    apply Equiv.forall_congr 
    intros 
    apply h

protected theorem forall₃_congr' {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop} (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂)
  (eγ : γ₁ ≃ γ₂) (h : ∀ {x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
  (∀ x y z, p x y z) ↔ ∀ x y z, q x y z :=
  (Equiv.forall₃_congr eα.symm eβ.symm eγ.symm fun x y z => h.symm).symm

protected theorem forall_congr_left' {p : α → Prop} (f : α ≃ β) : (∀ x, p x) ↔ ∀ y, p (f.symm y) :=
  Equiv.forall_congr f
    fun x =>
      by 
        simp 

protected theorem forall_congr_left {p : β → Prop} (f : α ≃ β) : (∀ x, p (f x)) ↔ ∀ y, p y :=
  (Equiv.forall_congr_left' f.symm).symm

protected theorem exists_congr_left {α β} (f : α ≃ β) {p : α → Prop} : (∃ a, p a) ↔ ∃ b, p (f.symm b) :=
  ⟨fun ⟨a, h⟩ =>
      ⟨f a,
        by 
          simpa using h⟩,
    fun ⟨b, h⟩ => ⟨_, h⟩⟩

section 

variable (P : α → Sort w) (e : α ≃ β)

/--
Transport dependent functions through an equivalence of the base space.
-/
@[simps]
def Pi_congr_left' : (∀ a, P a) ≃ ∀ b, P (e.symm b) :=
  { toFun := fun f x => f (e.symm x),
    invFun :=
      fun f x =>
        by 
          rw [←e.symm_apply_apply x]
          exact f (e x),
    left_inv :=
      fun f =>
        funext$
          fun x =>
            eq_of_heq
              ((eq_rec_heqₓ _ _).trans
                (by 
                  dsimp 
                  rw [e.symm_apply_apply])),
    right_inv :=
      fun f =>
        funext$
          fun x =>
            eq_of_heq
              ((eq_rec_heqₓ _ _).trans
                (by 
                  rw [e.apply_symm_apply])) }

end 

section 

variable (P : β → Sort w) (e : α ≃ β)

/--
Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def Pi_congr_left : (∀ a, P (e a)) ≃ ∀ b, P b :=
  (Pi_congr_left' P e.symm).symm

end 

section 

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ a : α, W a ≃ Z (h₁ a))

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def Pi_congr : (∀ a, W a) ≃ ∀ b, Z b :=
  (Equiv.piCongrRight h₂).trans (Equiv.piCongrLeft _ h₁)

@[simp]
theorem coe_Pi_congr_symm : ((h₁.Pi_congr h₂).symm : (∀ b, Z b) → ∀ a, W a) = fun f a => (h₂ a).symm (f (h₁ a)) :=
  rfl

theorem Pi_congr_symm_apply (f : ∀ b, Z b) : (h₁.Pi_congr h₂).symm f = fun a => (h₂ a).symm (f (h₁ a)) :=
  rfl

@[simp]
theorem Pi_congr_apply_apply (f : ∀ a, W a) (a : α) : h₁.Pi_congr h₂ f (h₁ a) = h₂ a (f a) :=
  by 
    change cast _ ((h₂ (h₁.symm (h₁ a))) (f (h₁.symm (h₁ a)))) = (h₂ a) (f a)
    generalizeProofs hZa 
    revert hZa 
    rw [h₁.symm_apply_apply a]
    simp 

end 

section 

variable {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : ∀ b : β, W (h₁.symm b) ≃ Z b)

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def Pi_congr' : (∀ a, W a) ≃ ∀ b, Z b :=
  (Pi_congr h₁.symm fun b => (h₂ b).symm).symm

@[simp]
theorem coe_Pi_congr' : (h₁.Pi_congr' h₂ : (∀ a, W a) → ∀ b, Z b) = fun f b => h₂ b$ f$ h₁.symm b :=
  rfl

theorem Pi_congr'_apply (f : ∀ a, W a) : h₁.Pi_congr' h₂ f = fun b => h₂ b$ f$ h₁.symm b :=
  rfl

@[simp]
theorem Pi_congr'_symm_apply_symm_apply (f : ∀ b, Z b) (b : β) :
  (h₁.Pi_congr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) :=
  by 
    change cast _ ((h₂ (h₁ (h₁.symm b))).symm (f (h₁ (h₁.symm b)))) = (h₂ b).symm (f b)
    generalizeProofs hWb 
    revert hWb 
    generalize hb : h₁ (h₁.symm b) = b' 
    rw [h₁.apply_symm_apply b] at hb 
    subst hb 
    simp 

end 

end Equiv

theorem Function.Injective.swap_apply [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f)
  (x y z : α) : Equiv.swap (f x) (f y) (f z) = f (Equiv.swap x y z) :=
  by 
    byCases' hx : z = x
    ·
      simp [hx]
    byCases' hy : z = y
    ·
      simp [hy]
    rw [Equiv.swap_apply_of_ne_of_ne hx hy, Equiv.swap_apply_of_ne_of_ne (hf.ne hx) (hf.ne hy)]

theorem Function.Injective.swap_comp [DecidableEq α] [DecidableEq β] {f : α → β} (hf : Function.Injective f) (x y : α) :
  Equiv.swap (f x) (f y) ∘ f = f ∘ Equiv.swap x y :=
  funext$ fun z => hf.swap_apply _ _ _

/-- If both `α` and `β` are singletons, then `α ≃ β`. -/
def equivOfUniqueOfUnique [Unique α] [Unique β] : α ≃ β :=
  { toFun := fun _ => default β, invFun := fun _ => default α, left_inv := fun _ => Subsingleton.elimₓ _ _,
    right_inv := fun _ => Subsingleton.elimₓ _ _ }

/-- If `α` is a singleton, then it is equivalent to any `punit`. -/
def equivPunitOfUnique [Unique α] : α ≃ PUnit.{v} :=
  equivOfUniqueOfUnique

/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
def subsingletonProdSelfEquiv {α : Type _} [Subsingleton α] : α × α ≃ α :=
  { toFun := fun p => p.1, invFun := fun a => (a, a), left_inv := fun p => Subsingleton.elimₓ _ _,
    right_inv := fun p => Subsingleton.elimₓ _ _ }

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equivOfSubsingletonOfSubsingleton [Subsingleton α] [Subsingleton β] (f : α → β) (g : β → α) : α ≃ β :=
  { toFun := f, invFun := g, left_inv := fun _ => Subsingleton.elimₓ _ _, right_inv := fun _ => Subsingleton.elimₓ _ _ }

/-- A nonempty subsingleton type is (noncomputably) equivalent to `punit`. -/
noncomputable def Equiv.punitOfNonemptyOfSubsingleton {α : Sort _} [h : Nonempty α] [Subsingleton α] : α ≃ PUnit.{v} :=
  equivOfSubsingletonOfSubsingleton (fun _ => PUnit.unit) fun _ => h.some

/-- `unique (unique α)` is equivalent to `unique α`. -/
def uniqueUniqueEquiv : Unique (Unique α) ≃ Unique α :=
  equivOfSubsingletonOfSubsingleton (fun h => h.default)
    fun h => { default := h, uniq := fun _ => Subsingleton.elimₓ _ _ }

namespace Quot

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β) (eq : ∀ a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
  Quot ra ≃ Quot rb :=
  { toFun := Quot.map e fun a₁ a₂ => (Eq a₁ a₂).1,
    invFun :=
      Quot.map e.symm
        fun b₁ b₂ h => (Eq (e.symm b₁) (e.symm b₂)).2 ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h),
    left_inv :=
      by 
        rintro ⟨a⟩
        dunfold Quot.map 
        simp only [Equiv.symm_apply_apply],
    right_inv :=
      by 
        rintro ⟨a⟩
        dunfold Quot.map 
        simp only [Equiv.apply_symm_apply] }

@[simp]
theorem congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β) (eq : ∀ a₁ a₂ : α, ra a₁ a₂ ↔ rb (e a₁) (e a₂))
  (a : α) : Quot.congr e Eq (Quot.mk ra a) = Quot.mk rb (e a) :=
  rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {r r' : α → α → Prop} (eq : ∀ a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) : Quot r ≃ Quot r' :=
  Quot.congr (Equiv.refl α) Eq

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congr_left {r : α → α → Prop} (e : α ≃ β) : Quot r ≃ Quot fun b b' => r (e.symm b) (e.symm b') :=
  @Quot.congr α β r (fun b b' => r (e.symm b) (e.symm b')) e
    fun a₁ a₂ =>
      by 
        simp only [e.symm_apply_apply]

end Quot

namespace Quotientₓ

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : Setoidₓ α} {rb : Setoidₓ β} (e : α ≃ β)
  (eq : ∀ a₁ a₂, @Setoidₓ.R α ra a₁ a₂ ↔ @Setoidₓ.R β rb (e a₁) (e a₂)) : Quotientₓ ra ≃ Quotientₓ rb :=
  Quot.congr e Eq

@[simp]
theorem congr_mk {ra : Setoidₓ α} {rb : Setoidₓ β} (e : α ≃ β)
  (eq : ∀ a₁ a₂ : α, Setoidₓ.R a₁ a₂ ↔ Setoidₓ.R (e a₁) (e a₂)) (a : α) :
  Quotientₓ.congr e Eq (Quotientₓ.mk a) = Quotientₓ.mk (e a) :=
  rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {r r' : Setoidₓ α} (eq : ∀ a₁ a₂, @Setoidₓ.R α r a₁ a₂ ↔ @Setoidₓ.R α r' a₁ a₂) :
  Quotientₓ r ≃ Quotientₓ r' :=
  Quot.congrRight Eq

end Quotientₓ

namespace Function

theorem update_comp_equiv {α β α' : Sort _} [DecidableEq α'] [DecidableEq α] (f : α → β) (g : α' ≃ α) (a : α) (v : β) :
  update f a v ∘ g = update (f ∘ g) (g.symm a) v :=
  by 
    rw [←update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]

theorem update_apply_equiv_apply {α β α' : Sort _} [DecidableEq α'] [DecidableEq α] (f : α → β) (g : α' ≃ α) (a : α)
  (v : β) (a' : α') : update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
  congr_funₓ (update_comp_equiv f g a v) a'

end Function

