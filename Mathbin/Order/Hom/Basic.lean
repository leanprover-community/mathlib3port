/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module order.hom.basic
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Equiv.Option
import Mathbin.Order.RelIso.Basic
import Mathbin.Tactic.Monotonicity.Basic
import Mathbin.Tactic.AssertExists
import Mathbin.Order.Disjoint

/-!
# Order homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines order homomorphisms, which are bundled monotone functions. A preorder
homomorphism `f : α →o β` is a function `α → β` along with a proof that `∀ x y, x ≤ y → f x ≤ f y`.

## Main definitions

In this file we define the following bundled monotone maps:
 * `order_hom α β` a.k.a. `α →o β`: Preorder homomorphism.
    An `order_hom α β` is a function `f : α → β` such that `a₁ ≤ a₂ → f a₁ ≤ f a₂`
 * `order_embedding α β` a.k.a. `α ↪o β`: Relation embedding.
    An `order_embedding α β` is an embedding `f : α ↪ β` such that `a ≤ b ↔ f a ≤ f b`.
    Defined as an abbreviation of `@rel_embedding α β (≤) (≤)`.
* `order_iso`: Relation isomorphism.
    An `order_iso α β` is an equivalence `f : α ≃ β` such that `a ≤ b ↔ f a ≤ f b`.
    Defined as an abbreviation of `@rel_iso α β (≤) (≤)`.

We also define many `order_hom`s. In some cases we define two versions, one with `ₘ` suffix and
one without it (e.g., `order_hom.compₘ` and `order_hom.comp`). This means that the former
function is a "more bundled" version of the latter. We can't just drop the "less bundled" version
because the more bundled version usually does not work with dot notation.

* `order_hom.id`: identity map as `α →o α`;
* `order_hom.curry`: an order isomorphism between `α × β →o γ` and `α →o β →o γ`;
* `order_hom.comp`: composition of two bundled monotone maps;
* `order_hom.compₘ`: composition of bundled monotone maps as a bundled monotone map;
* `order_hom.const`: constant function as a bundled monotone map;
* `order_hom.prod`: combine `α →o β` and `α →o γ` into `α →o β × γ`;
* `order_hom.prodₘ`: a more bundled version of `order_hom.prod`;
* `order_hom.prod_iso`: order isomorphism between `α →o β × γ` and `(α →o β) × (α →o γ)`;
* `order_hom.diag`: diagonal embedding of `α` into `α × α` as a bundled monotone map;
* `order_hom.on_diag`: restrict a monotone map `α →o α →o β` to the diagonal;
* `order_hom.fst`: projection `prod.fst : α × β → α` as a bundled monotone map;
* `order_hom.snd`: projection `prod.snd : α × β → β` as a bundled monotone map;
* `order_hom.prod_map`: `prod.map f g` as a bundled monotone map;
* `pi.eval_order_hom`: evaluation of a function at a point `function.eval i` as a bundled
  monotone map;
* `order_hom.coe_fn_hom`: coercion to function as a bundled monotone map;
* `order_hom.apply`: application of a `order_hom` at a point as a bundled monotone map;
* `order_hom.pi`: combine a family of monotone maps `f i : α →o π i` into a monotone map
  `α →o Π i, π i`;
* `order_hom.pi_iso`: order isomorphism between `α →o Π i, π i` and `Π i, α →o π i`;
* `order_hom.subtyle.val`: embedding `subtype.val : subtype p → α` as a bundled monotone map;
* `order_hom.dual`: reinterpret a monotone map `α →o β` as a monotone map `αᵒᵈ →o βᵒᵈ`;
* `order_hom.dual_iso`: order isomorphism between `α →o β` and `(αᵒᵈ →o βᵒᵈ)ᵒᵈ`;
* `order_iso.compl`: order isomorphism `α ≃o αᵒᵈ` given by taking complements in a
  boolean algebra;

We also define two functions to convert other bundled maps to `α →o β`:

* `order_embedding.to_order_hom`: convert `α ↪o β` to `α →o β`;
* `rel_hom.to_order_hom`: convert a `rel_hom` between strict orders to a `order_hom`.

## Tags

monotone map, bundled morphism
-/


open OrderDual

variable {F α β γ δ : Type _}

#print OrderHom /-
/-- Bundled monotone (aka, increasing) function -/
structure OrderHom (α β : Type _) [Preorder α] [Preorder β] where
  toFun : α → β
  monotone' : Monotone to_fun
#align order_hom OrderHom
-/

-- mathport name: «expr →o »
infixr:25 " →o " => OrderHom

#print OrderEmbedding /-
/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_embedding (≤) (≤)`. -/
abbrev OrderEmbedding (α β : Type _) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)
#align order_embedding OrderEmbedding
-/

-- mathport name: «expr ↪o »
infixl:25 " ↪o " => OrderEmbedding

#print OrderIso /-
/-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_iso (≤) (≤)`. -/
abbrev OrderIso (α β : Type _) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)
#align order_iso OrderIso
-/

-- mathport name: «expr ≃o »
infixl:25 " ≃o " => OrderIso

section

#print OrderHomClass /-
/-- `order_hom_class F α b` asserts that `F` is a type of `≤`-preserving morphisms. -/
abbrev OrderHomClass (F : Type _) (α β : outParam (Type _)) [LE α] [LE β] :=
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop)
#align order_hom_class OrderHomClass
-/

#print OrderIsoClass /-
/-- `order_iso_class F α β` states that `F` is a type of order isomorphisms.

You should extend this class when you extend `order_iso`. -/
class OrderIsoClass (F : Type _) (α β : outParam (Type _)) [LE α] [LE β] extends
  EquivLike F α β where
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b
#align order_iso_class OrderIsoClass
-/

end

export OrderIsoClass (map_le_map_iff)

attribute [simp] map_le_map_iff

instance [LE α] [LE β] [OrderIsoClass F α β] : CoeTC F (α ≃o β) :=
  ⟨fun f => ⟨f, fun _ _ => map_le_map_iff f⟩⟩

#print OrderIsoClass.toOrderHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toOrderHomClass [LE α] [LE β] [OrderIsoClass F α β] :
    OrderHomClass F α β :=
  { EquivLike.toEmbeddingLike with map_rel := fun f a b => (map_le_map_iff f).2 }
#align order_iso_class.to_order_hom_class OrderIsoClass.toOrderHomClass
-/

namespace OrderHomClass

variable [Preorder α] [Preorder β] [OrderHomClass F α β]

protected theorem monotone (f : F) : Monotone (f : α → β) := fun _ _ => map_rel f
#align order_hom_class.monotone OrderHomClass.monotone

protected theorem mono (f : F) : Monotone (f : α → β) := fun _ _ => map_rel f
#align order_hom_class.mono OrderHomClass.mono

instance : CoeTC F (α →o β) :=
  ⟨fun f =>
    { toFun := f
      monotone' := OrderHomClass.mono _ }⟩

end OrderHomClass

section OrderIsoClass

section LE

variable [LE α] [LE β] [OrderIsoClass F α β]

@[simp]
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b ≤ a ↔ b ≤ f a := by
  convert(map_le_map_iff _).symm; exact (EquivLike.right_inv _ _).symm
#align map_inv_le_iff map_inv_le_iff

@[simp]
theorem le_map_inv_iff (f : F) {a : α} {b : β} : a ≤ EquivLike.inv f b ↔ f a ≤ b := by
  convert(map_le_map_iff _).symm; exact (EquivLike.right_inv _ _).symm
#align le_map_inv_iff le_map_inv_iff

end LE

variable [Preorder α] [Preorder β] [OrderIsoClass F α β]

include β

theorem map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)
#align map_lt_map_iff map_lt_map_iff

@[simp]
theorem map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a := by
  convert(map_lt_map_iff _).symm; exact (EquivLike.right_inv _ _).symm
#align map_inv_lt_iff map_inv_lt_iff

@[simp]
theorem lt_map_inv_iff (f : F) {a : α} {b : β} : a < EquivLike.inv f b ↔ f a < b := by
  convert(map_lt_map_iff _).symm; exact (EquivLike.right_inv _ _).symm
#align lt_map_inv_iff lt_map_inv_iff

end OrderIsoClass

namespace OrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →o β) fun _ => α → β :=
  ⟨OrderHom.toFun⟩

initialize_simps_projections OrderHom (toFun → coe)

protected theorem monotone (f : α →o β) : Monotone f :=
  f.monotone'
#align order_hom.monotone OrderHom.monotone

protected theorem mono (f : α →o β) : Monotone f :=
  f.Monotone
#align order_hom.mono OrderHom.mono

instance : OrderHomClass (α →o β) α β where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_rel f := f.Monotone

/- warning: order_hom.to_fun_eq_coe clashes with [anonymous] -> [anonymous]
Case conversion may be inaccurate. Consider using '#align order_hom.to_fun_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] {f : α →o β} : f.toFun = f :=
  rfl
#align order_hom.to_fun_eq_coe [anonymous]

@[simp]
theorem coe_fun_mk {f : α → β} (hf : Monotone f) : (mk f hf : α → β) = f :=
  rfl
#align order_hom.coe_fun_mk OrderHom.coe_fun_mk

-- See library note [partially-applied ext lemmas]
@[ext]
theorem ext (f g : α →o β) (h : (f : α → β) = g) : f = g :=
  FunLike.coe_injective h
#align order_hom.ext OrderHom.ext

/- warning: order_hom.coe_eq clashes with [anonymous] -> [anonymous]
Case conversion may be inaccurate. Consider using '#align order_hom.coe_eq [anonymous]ₓ'. -/
theorem [anonymous] (f : α →o β) : coe f = f := by ext <;> rfl
#align order_hom.coe_eq [anonymous]

/-- One can lift an unbundled monotone function to a bundled one. -/
instance : CanLift (α → β) (α →o β) coeFn Monotone where prf f h := ⟨⟨f, h⟩, rfl⟩

#print OrderHom.copy /-
/-- Copy of an `order_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →o β) (f' : α → β) (h : f' = f) : α →o β :=
  ⟨f', h.symm.subst f.monotone'⟩
#align order_hom.copy OrderHom.copy
-/

@[simp]
theorem coe_copy (f : α →o β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align order_hom.coe_copy OrderHom.coe_copy

theorem copy_eq (f : α →o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align order_hom.copy_eq OrderHom.copy_eq

#print OrderHom.id /-
/-- The identity function as bundled monotone function. -/
@[simps (config := { fullyApplied := false })]
def id : α →o α :=
  ⟨id, monotone_id⟩
#align order_hom.id OrderHom.id
-/

instance : Inhabited (α →o α) :=
  ⟨id⟩

/-- The preorder structure of `α →o β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance : Preorder (α →o β) :=
  @Preorder.lift (α →o β) (α → β) _ coeFn

instance {β : Type _} [PartialOrder β] : PartialOrder (α →o β) :=
  @PartialOrder.lift (α →o β) (α → β) _ coeFn ext

theorem le_def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl
#align order_hom.le_def OrderHom.le_def

@[simp, norm_cast]
theorem coe_le_coe {f g : α →o β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl
#align order_hom.coe_le_coe OrderHom.coe_le_coe

@[simp]
theorem mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g :=
  Iff.rfl
#align order_hom.mk_le_mk OrderHom.mk_le_mk

@[mono]
theorem apply_mono {f g : α →o β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  (h₁ x).trans <| g.mono h₂
#align order_hom.apply_mono OrderHom.apply_mono

/-- Curry/uncurry as an order isomorphism between `α × β →o γ` and `α →o β →o γ`. -/
def curry : (α × β →o γ) ≃o (α →o β →o γ)
    where
  toFun f :=
    ⟨fun x => ⟨Function.curry f x, fun y₁ y₂ h => f.mono ⟨le_rfl, h⟩⟩, fun x₁ x₂ h y =>
      f.mono ⟨h, le_rfl⟩⟩
  invFun f :=
    ⟨Function.uncurry fun x => f x, fun x y h => (f.mono h.1 x.2).trans <| (f y.1).mono h.2⟩
  left_inv f := by ext ⟨x, y⟩; rfl
  right_inv f := by ext (x y); rfl
  map_rel_iff' f g := by simp [le_def]
#align order_hom.curry OrderHom.curry

@[simp]
theorem curry_apply (f : α × β →o γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl
#align order_hom.curry_apply OrderHom.curry_apply

@[simp]
theorem curry_symm_apply (f : α →o β →o γ) (x : α × β) : curry.symm f x = f x.1 x.2 :=
  rfl
#align order_hom.curry_symm_apply OrderHom.curry_symm_apply

#print OrderHom.comp /-
/-- The composition of two bundled monotone functions. -/
@[simps (config := { fullyApplied := false })]
def comp (g : β →o γ) (f : α →o β) : α →o γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩
#align order_hom.comp OrderHom.comp
-/

@[mono]
theorem comp_mono ⦃g₁ g₂ : β →o γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →o β⦄ (hf : f₁ ≤ f₂) :
    g₁.comp f₁ ≤ g₂.comp f₂ := fun x => (hg _).trans (g₂.mono <| hf _)
#align order_hom.comp_mono OrderHom.comp_mono

#print OrderHom.compₘ /-
/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps (config := { fullyApplied := false })]
def compₘ : (β →o γ) →o (α →o β) →o α →o γ :=
  curry ⟨fun f : (β →o γ) × (α →o β) => f.1.comp f.2, fun f₁ f₂ h => comp_mono h.1 h.2⟩
#align order_hom.compₘ OrderHom.compₘ
-/

@[simp]
theorem comp_id (f : α →o β) : comp f id = f := by ext; rfl
#align order_hom.comp_id OrderHom.comp_id

@[simp]
theorem id_comp (f : α →o β) : comp id f = f := by ext; rfl
#align order_hom.id_comp OrderHom.id_comp

#print OrderHom.const /-
/-- Constant function bundled as a `order_hom`. -/
@[simps (config := { fullyApplied := false })]
def const (α : Type _) [Preorder α] {β : Type _} [Preorder β] : β →o α →o β
    where
  toFun b := ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' b₁ b₂ h x := h
#align order_hom.const OrderHom.const
-/

@[simp]
theorem const_comp (f : α →o β) (c : γ) : (const β c).comp f = const α c :=
  rfl
#align order_hom.const_comp OrderHom.const_comp

@[simp]
theorem comp_const (γ : Type _) [Preorder γ] (f : α →o β) (c : α) :
    f.comp (const γ c) = const γ (f c) :=
  rfl
#align order_hom.comp_const OrderHom.comp_const

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`order_hom`. -/
@[simps]
protected def prod (f : α →o β) (g : α →o γ) : α →o β × γ :=
  ⟨fun x => (f x, g x), fun x y h => ⟨f.mono h, g.mono h⟩⟩
#align order_hom.prod OrderHom.prod

@[mono]
theorem prod_mono {f₁ f₂ : α →o β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →o γ} (hg : g₁ ≤ g₂) :
    f₁.Prod g₁ ≤ f₂.Prod g₂ := fun x => Prod.le_def.2 ⟨hf _, hg _⟩
#align order_hom.prod_mono OrderHom.prod_mono

theorem comp_prod_comp_same (f₁ f₂ : β →o γ) (g : α →o β) :
    (f₁.comp g).Prod (f₂.comp g) = (f₁.Prod f₂).comp g :=
  rfl
#align order_hom.comp_prod_comp_same OrderHom.comp_prod_comp_same

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`order_hom`. This is a fully bundled version. -/
@[simps]
def prodₘ : (α →o β) →o (α →o γ) →o α →o β × γ :=
  curry ⟨fun f : (α →o β) × (α →o γ) => f.1.Prod f.2, fun f₁ f₂ h => prod_mono h.1 h.2⟩
#align order_hom.prodₘ OrderHom.prodₘ

/-- Diagonal embedding of `α` into `α × α` as a `order_hom`. -/
@[simps]
def diag : α →o α × α :=
  id.Prod id
#align order_hom.diag OrderHom.diag

#print OrderHom.onDiag /-
/-- Restriction of `f : α →o α →o β` to the diagonal. -/
@[simps (config := { simpRhs := true })]
def onDiag (f : α →o α →o β) : α →o β :=
  (curry.symm f).comp diag
#align order_hom.on_diag OrderHom.onDiag
-/

/-- `prod.fst` as a `order_hom`. -/
@[simps]
def fst : α × β →o α :=
  ⟨Prod.fst, fun x y h => h.1⟩
#align order_hom.fst OrderHom.fst

/-- `prod.snd` as a `order_hom`. -/
@[simps]
def snd : α × β →o β :=
  ⟨Prod.snd, fun x y h => h.2⟩
#align order_hom.snd OrderHom.snd

@[simp]
theorem fst_prod_snd : (fst : α × β →o α).Prod snd = id := by ext ⟨x, y⟩ : 2; rfl
#align order_hom.fst_prod_snd OrderHom.fst_prod_snd

@[simp]
theorem fst_comp_prod (f : α →o β) (g : α →o γ) : fst.comp (f.Prod g) = f :=
  ext _ _ rfl
#align order_hom.fst_comp_prod OrderHom.fst_comp_prod

@[simp]
theorem snd_comp_prod (f : α →o β) (g : α →o γ) : snd.comp (f.Prod g) = g :=
  ext _ _ rfl
#align order_hom.snd_comp_prod OrderHom.snd_comp_prod

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps]
def prodIso : (α →o β × γ) ≃o (α →o β) × (α →o γ)
    where
  toFun f := (fst.comp f, snd.comp f)
  invFun f := f.1.Prod f.2
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
  map_rel_iff' f g := forall_and.symm
#align order_hom.prod_iso OrderHom.prodIso

/-- `prod.map` of two `order_hom`s as a `order_hom`. -/
@[simps]
def prodMap (f : α →o β) (g : γ →o δ) : α × γ →o β × δ :=
  ⟨Prod.map f g, fun x y h => ⟨f.mono h.1, g.mono h.2⟩⟩
#align order_hom.prod_map OrderHom.prodMap

variable {ι : Type _} {π : ι → Type _} [∀ i, Preorder (π i)]

#print Pi.evalOrderHom /-
/-- Evaluation of an unbundled function at a point (`function.eval`) as a `order_hom`. -/
@[simps (config := { fullyApplied := false })]
def Pi.evalOrderHom (i : ι) : (∀ j, π j) →o π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩
#align pi.eval_order_hom Pi.evalOrderHom
-/

#print OrderHom.coeFnHom /-
/-- The "forgetful functor" from `α →o β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps (config := { fullyApplied := false })]
def coeFnHom : (α →o β) →o α → β where
  toFun f := f
  monotone' x y h := h
#align order_hom.coe_fn_hom OrderHom.coeFnHom
-/

#print OrderHom.apply /-
/-- Function application `λ f, f a` (for fixed `a`) is a monotone function from the
monotone function space `α →o β` to `β`. See also `pi.eval_order_hom`.  -/
@[simps (config := { fullyApplied := false })]
def apply (x : α) : (α →o β) →o β :=
  (Pi.evalOrderHom x).comp coeFnHom
#align order_hom.apply OrderHom.apply
-/

#print OrderHom.pi /-
/-- Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`. -/
@[simps]
def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
  ⟨fun x i => f i x, fun x y h i => (f i).mono h⟩
#align order_hom.pi OrderHom.pi
-/

/-- Order isomorphism between bundled monotone maps `α →o Π i, π i` and families of bundled monotone
maps `Π i, α →o π i`. -/
@[simps]
def piIso : (α →o ∀ i, π i) ≃o ∀ i, α →o π i
    where
  toFun f i := (Pi.evalOrderHom i).comp f
  invFun := pi
  left_inv f := by ext (x i); rfl
  right_inv f := by ext (x i); rfl
  map_rel_iff' f g := forall_swap
#align order_hom.pi_iso OrderHom.piIso

#print OrderHom.Subtype.val /-
/-- `subtype.val` as a bundled monotone function.  -/
@[simps (config := { fullyApplied := false })]
def Subtype.val (p : α → Prop) : Subtype p →o α :=
  ⟨Subtype.val, fun x y h => h⟩
#align order_hom.subtype.val OrderHom.Subtype.val
-/

#print OrderHom.unique /-
/-- There is a unique monotone map from a subsingleton to itself. -/
instance unique [Subsingleton α] : Unique (α →o α)
    where
  default := OrderHom.id
  uniq a := ext _ _ (Subsingleton.elim _ _)
#align order_hom.unique OrderHom.unique
-/

#print OrderHom.orderHom_eq_id /-
theorem orderHom_eq_id [Subsingleton α] (g : α →o α) : g = OrderHom.id :=
  Subsingleton.elim _ _
#align order_hom.order_hom_eq_id OrderHom.orderHom_eq_id
-/

#print OrderHom.dual /-
/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps]
protected def dual : (α →o β) ≃ (αᵒᵈ →o βᵒᵈ)
    where
  toFun f := ⟨OrderDual.toDual ∘ f ∘ OrderDual.ofDual, f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩
  left_inv f := ext _ _ rfl
  right_inv f := ext _ _ rfl
#align order_hom.dual OrderHom.dual
-/

#print OrderHom.dual_id /-
@[simp]
theorem dual_id : (OrderHom.id : α →o α).dual = OrderHom.id :=
  rfl
#align order_hom.dual_id OrderHom.dual_id
-/

@[simp]
theorem dual_comp (g : β →o γ) (f : α →o β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align order_hom.dual_comp OrderHom.dual_comp

#print OrderHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : OrderHom.dual.symm OrderHom.id = (OrderHom.id : α →o α) :=
  rfl
#align order_hom.symm_dual_id OrderHom.symm_dual_id
-/

@[simp]
theorem symm_dual_comp (g : βᵒᵈ →o γᵒᵈ) (f : αᵒᵈ →o βᵒᵈ) :
    OrderHom.dual.symm (g.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f) :=
  rfl
#align order_hom.symm_dual_comp OrderHom.symm_dual_comp

/-- `order_hom.dual` as an order isomorphism. -/
def dualIso (α β : Type _) [Preorder α] [Preorder β] : (α →o β) ≃o (αᵒᵈ →o βᵒᵈ)ᵒᵈ
    where
  toEquiv := OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' f g := Iff.rfl
#align order_hom.dual_iso OrderHom.dualIso

#print OrderHom.withBotMap /-
/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `with_bot α →o with_bot β`. -/
@[simps (config := { fullyApplied := false })]
protected def withBotMap (f : α →o β) : WithBot α →o WithBot β :=
  ⟨WithBot.map f, f.mono.withBot_map⟩
#align order_hom.with_bot_map OrderHom.withBotMap
-/

#print OrderHom.withTopMap /-
/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `with_top α →o with_top β`. -/
@[simps (config := { fullyApplied := false })]
protected def withTopMap (f : α →o β) : WithTop α →o WithTop β :=
  ⟨WithTop.map f, f.mono.withTop_map⟩
#align order_hom.with_top_map OrderHom.withTopMap
-/

end OrderHom

/-- Embeddings of partial orders that preserve `<` also preserve `≤`. -/
def RelEmbedding.orderEmbeddingOfLTEmbedding [PartialOrder α] [PartialOrder β]
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) : α ↪o β :=
  { f with map_rel_iff' := by intros ; simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }
#align rel_embedding.order_embedding_of_lt_embedding RelEmbedding.orderEmbeddingOfLTEmbedding

@[simp]
theorem RelEmbedding.orderEmbeddingOfLTEmbedding_apply [PartialOrder α] [PartialOrder β]
    {f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)} {x : α} :
    RelEmbedding.orderEmbeddingOfLTEmbedding f x = f x :=
  rfl
#align rel_embedding.order_embedding_of_lt_embedding_apply RelEmbedding.orderEmbeddingOfLTEmbedding_apply

namespace OrderEmbedding

variable [Preorder α] [Preorder β] (f : α ↪o β)

/-- `<` is preserved by order embeddings of preorders. -/
def ltEmbedding : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  { f with map_rel_iff' := by intros <;> simp [lt_iff_le_not_le, f.map_rel_iff] }
#align order_embedding.lt_embedding OrderEmbedding.ltEmbedding

@[simp]
theorem ltEmbedding_apply (x : α) : f.ltEmbedding x = f x :=
  rfl
#align order_embedding.lt_embedding_apply OrderEmbedding.ltEmbedding_apply

@[simp]
theorem le_iff_le {a b} : f a ≤ f b ↔ a ≤ b :=
  f.map_rel_iff
#align order_embedding.le_iff_le OrderEmbedding.le_iff_le

@[simp]
theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
  f.ltEmbedding.map_rel_iff
#align order_embedding.lt_iff_lt OrderEmbedding.lt_iff_lt

@[simp]
theorem eq_iff_eq {a b} : f a = f b ↔ a = b :=
  f.Injective.eq_iff
#align order_embedding.eq_iff_eq OrderEmbedding.eq_iff_eq

protected theorem monotone : Monotone f :=
  OrderHomClass.monotone f
#align order_embedding.monotone OrderEmbedding.monotone

protected theorem strictMono : StrictMono f := fun x y => f.lt_iff_lt.2
#align order_embedding.strict_mono OrderEmbedding.strictMono

protected theorem acc (a : α) : Acc (· < ·) (f a) → Acc (· < ·) a :=
  f.ltEmbedding.Acc a
#align order_embedding.acc OrderEmbedding.acc

protected theorem wellFounded :
    WellFounded ((· < ·) : β → β → Prop) → WellFounded ((· < ·) : α → α → Prop) :=
  f.ltEmbedding.WellFounded
#align order_embedding.well_founded OrderEmbedding.wellFounded

protected theorem isWellOrder [IsWellOrder β (· < ·)] : IsWellOrder α (· < ·) :=
  f.ltEmbedding.IsWellOrder
#align order_embedding.is_well_order OrderEmbedding.isWellOrder

/-- An order embedding is also an order embedding between dual orders. -/
protected def dual : αᵒᵈ ↪o βᵒᵈ :=
  ⟨f.toEmbedding, fun a b => f.map_rel_iff⟩
#align order_embedding.dual OrderEmbedding.dual

/-- A version of `with_bot.map` for order embeddings. -/
@[simps (config := { fullyApplied := false })]
protected def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β :=
  { f.toEmbedding.option_map with
    toFun := WithBot.map f
    map_rel_iff' := WithBot.map_le_iff f fun a b => f.map_rel_iff }
#align order_embedding.with_bot_map OrderEmbedding.withBotMap

/-- A version of `with_top.map` for order embeddings. -/
@[simps (config := { fullyApplied := false })]
protected def withTopMap (f : α ↪o β) : WithTop α ↪o WithTop β :=
  { f.dual.withBot_map.dual with toFun := WithTop.map f }
#align order_embedding.with_top_map OrderEmbedding.withTopMap

/-- To define an order embedding from a partial order to a preorder it suffices to give a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
def ofMapLEIff {α β} [PartialOrder α] [Preorder β] (f : α → β) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    α ↪o β :=
  RelEmbedding.ofMapRelIff f hf
#align order_embedding.of_map_le_iff OrderEmbedding.ofMapLEIff

@[simp]
theorem coe_ofMapLEIff {α β} [PartialOrder α] [Preorder β] {f : α → β} (h) :
    ⇑(ofMapLEIff f h) = f :=
  rfl
#align order_embedding.coe_of_map_le_iff OrderEmbedding.coe_ofMapLEIff

/-- A strictly monotone map from a linear order is an order embedding. -/
def ofStrictMono {α β} [LinearOrder α] [Preorder β] (f : α → β) (h : StrictMono f) : α ↪o β :=
  ofMapLEIff f fun _ _ => h.le_iff_le
#align order_embedding.of_strict_mono OrderEmbedding.ofStrictMono

@[simp]
theorem coe_ofStrictMono {α β} [LinearOrder α] [Preorder β] {f : α → β} (h : StrictMono f) :
    ⇑(ofStrictMono f h) = f :=
  rfl
#align order_embedding.coe_of_strict_mono OrderEmbedding.coe_ofStrictMono

/-- Embedding of a subtype into the ambient type as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def subtype (p : α → Prop) : Subtype p ↪o α :=
  ⟨Function.Embedding.subtype p, fun x y => Iff.rfl⟩
#align order_embedding.subtype OrderEmbedding.subtype

/-- Convert an `order_embedding` to a `order_hom`. -/
@[simps (config := { fullyApplied := false })]
def toOrderHom {X Y : Type _} [Preorder X] [Preorder Y] (f : X ↪o Y) : X →o Y
    where
  toFun := f
  monotone' := f.Monotone
#align order_embedding.to_order_hom OrderEmbedding.toOrderHom

end OrderEmbedding

section RelHom

variable [PartialOrder α] [Preorder β]

namespace RelHom

variable (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotone
is weakly monotone. -/
@[simps (config := { fullyApplied := false })]
def toOrderHom : α →o β where
  toFun := f
  monotone' := StrictMono.monotone fun x y => f.map_rel
#align rel_hom.to_order_hom RelHom.toOrderHom

end RelHom

theorem RelEmbedding.toOrderHom_injective
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) :
    Function.Injective (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop)).toOrderHom :=
  fun _ _ h => f.Injective h
#align rel_embedding.to_order_hom_injective RelEmbedding.toOrderHom_injective

end RelHom

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ]

instance : OrderIsoClass (α ≃o β) α β where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr
  map_le_map_iff f _ _ := f.map_rel_iff'

@[simp]
theorem toFun_eq_coe {f : α ≃o β} : f.toFun = f :=
  rfl
#align order_iso.to_fun_eq_coe OrderIso.toFun_eq_coe

-- See note [partially-applied ext lemmas]
@[ext]
theorem ext {f g : α ≃o β} (h : (f : α → β) = g) : f = g :=
  FunLike.coe_injective h
#align order_iso.ext OrderIso.ext

#print OrderIso.toOrderEmbedding /-
/-- Reinterpret an order isomorphism as an order embedding. -/
def toOrderEmbedding (e : α ≃o β) : α ↪o β :=
  e.toRelEmbedding
#align order_iso.to_order_embedding OrderIso.toOrderEmbedding
-/

@[simp]
theorem coe_toOrderEmbedding (e : α ≃o β) : ⇑e.toOrderEmbedding = e :=
  rfl
#align order_iso.coe_to_order_embedding OrderIso.coe_toOrderEmbedding

protected theorem bijective (e : α ≃o β) : Function.Bijective e :=
  e.toEquiv.Bijective
#align order_iso.bijective OrderIso.bijective

protected theorem injective (e : α ≃o β) : Function.Injective e :=
  e.toEquiv.Injective
#align order_iso.injective OrderIso.injective

protected theorem surjective (e : α ≃o β) : Function.Surjective e :=
  e.toEquiv.Surjective
#align order_iso.surjective OrderIso.surjective

@[simp]
theorem apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
  e.toEquiv.apply_eq_iff_eq
#align order_iso.apply_eq_iff_eq OrderIso.apply_eq_iff_eq

#print OrderIso.refl /-
/-- Identity order isomorphism. -/
def refl (α : Type _) [LE α] : α ≃o α :=
  RelIso.refl (· ≤ ·)
#align order_iso.refl OrderIso.refl
-/

@[simp]
theorem coe_refl : ⇑(refl α) = id :=
  rfl
#align order_iso.coe_refl OrderIso.coe_refl

@[simp]
theorem refl_apply (x : α) : refl α x = x :=
  rfl
#align order_iso.refl_apply OrderIso.refl_apply

#print OrderIso.refl_toEquiv /-
@[simp]
theorem refl_toEquiv : (refl α).toEquiv = Equiv.refl α :=
  rfl
#align order_iso.refl_to_equiv OrderIso.refl_toEquiv
-/

#print OrderIso.symm /-
/-- Inverse of an order isomorphism. -/
def symm (e : α ≃o β) : β ≃o α :=
  e.symm
#align order_iso.symm OrderIso.symm
-/

@[simp]
theorem apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x
#align order_iso.apply_symm_apply OrderIso.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
#align order_iso.symm_apply_apply OrderIso.symm_apply_apply

#print OrderIso.symm_refl /-
@[simp]
theorem symm_refl (α : Type _) [LE α] : (refl α).symm = refl α :=
  rfl
#align order_iso.symm_refl OrderIso.symm_refl
-/

theorem apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply
#align order_iso.apply_eq_iff_eq_symm_apply OrderIso.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq
#align order_iso.symm_apply_eq OrderIso.symm_apply_eq

@[simp]
theorem symm_symm (e : α ≃o β) : e.symm.symm = e := by ext; rfl
#align order_iso.symm_symm OrderIso.symm_symm

theorem symm_injective : Function.Injective (symm : α ≃o β → β ≃o α) := fun e e' h => by
  rw [← e.symm_symm, h, e'.symm_symm]
#align order_iso.symm_injective OrderIso.symm_injective

@[simp]
theorem toEquiv_symm (e : α ≃o β) : e.toEquiv.symm = e.symm.toEquiv :=
  rfl
#align order_iso.to_equiv_symm OrderIso.toEquiv_symm

#print OrderIso.trans /-
/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans]
def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  e.trans e'
#align order_iso.trans OrderIso.trans
-/

@[simp]
theorem coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e :=
  rfl
#align order_iso.coe_trans OrderIso.coe_trans

@[simp]
theorem trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl
#align order_iso.trans_apply OrderIso.trans_apply

@[simp]
theorem refl_trans (e : α ≃o β) : (refl α).trans e = e := by ext x; rfl
#align order_iso.refl_trans OrderIso.refl_trans

@[simp]
theorem trans_refl (e : α ≃o β) : e.trans (refl β) = e := by ext x; rfl
#align order_iso.trans_refl OrderIso.trans_refl

@[simp]
theorem symm_trans_apply (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ) :
    (e₁.trans e₂).symm c = e₁.symm (e₂.symm c) :=
  rfl
#align order_iso.symm_trans_apply OrderIso.symm_trans_apply

theorem symm_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
#align order_iso.symm_trans OrderIso.symm_trans

#print OrderIso.prodComm /-
/-- `prod.swap` as an `order_iso`. -/
def prodComm : α × β ≃o β × α where
  toEquiv := Equiv.prodComm α β
  map_rel_iff' a b := Prod.swap_le_swap
#align order_iso.prod_comm OrderIso.prodComm
-/

@[simp]
theorem coe_prodComm : ⇑(prodComm : α × β ≃o β × α) = Prod.swap :=
  rfl
#align order_iso.coe_prod_comm OrderIso.coe_prodComm

@[simp]
theorem prodComm_symm : (prodComm : α × β ≃o β × α).symm = prodComm :=
  rfl
#align order_iso.prod_comm_symm OrderIso.prodComm_symm

variable (α)

#print OrderIso.dualDual /-
/-- The order isomorphism between a type and its double dual. -/
def dualDual : α ≃o αᵒᵈᵒᵈ :=
  refl α
#align order_iso.dual_dual OrderIso.dualDual
-/

@[simp]
theorem coe_dualDual : ⇑(dualDual α) = toDual ∘ toDual :=
  rfl
#align order_iso.coe_dual_dual OrderIso.coe_dualDual

@[simp]
theorem coe_dualDual_symm : ⇑(dualDual α).symm = ofDual ∘ ofDual :=
  rfl
#align order_iso.coe_dual_dual_symm OrderIso.coe_dualDual_symm

variable {α}

@[simp]
theorem dualDual_apply (a : α) : dualDual α a = toDual (toDual a) :=
  rfl
#align order_iso.dual_dual_apply OrderIso.dualDual_apply

@[simp]
theorem dualDual_symm_apply (a : αᵒᵈᵒᵈ) : (dualDual α).symm a = ofDual (ofDual a) :=
  rfl
#align order_iso.dual_dual_symm_apply OrderIso.dualDual_symm_apply

end LE

open Set

section Le

variable [LE α] [LE β] [LE γ]

@[simp]
theorem le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y :=
  e.map_rel_iff
#align order_iso.le_iff_le OrderIso.le_iff_le

theorem le_symm_apply (e : α ≃o β) {x : α} {y : β} : x ≤ e.symm y ↔ e x ≤ y :=
  e.rel_symm_apply
#align order_iso.le_symm_apply OrderIso.le_symm_apply

theorem symm_apply_le (e : α ≃o β) {x : α} {y : β} : e.symm y ≤ x ↔ y ≤ e x :=
  e.symm_apply_rel
#align order_iso.symm_apply_le OrderIso.symm_apply_le

end Le

variable [Preorder α] [Preorder β] [Preorder γ]

protected theorem monotone (e : α ≃o β) : Monotone e :=
  e.toOrderEmbedding.Monotone
#align order_iso.monotone OrderIso.monotone

protected theorem strictMono (e : α ≃o β) : StrictMono e :=
  e.toOrderEmbedding.StrictMono
#align order_iso.strict_mono OrderIso.strictMono

@[simp]
theorem lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
  e.toOrderEmbedding.lt_iff_lt
#align order_iso.lt_iff_lt OrderIso.lt_iff_lt

/-- Converts an `order_iso` into a `rel_iso (<) (<)`. -/
def toRelIsoLT (e : α ≃o β) : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop) :=
  ⟨e.toEquiv, fun x y => lt_iff_lt e⟩
#align order_iso.to_rel_iso_lt OrderIso.toRelIsoLT

@[simp]
theorem toRelIsoLT_apply (e : α ≃o β) (x : α) : e.toRelIsoLT x = e x :=
  rfl
#align order_iso.to_rel_iso_lt_apply OrderIso.toRelIsoLT_apply

@[simp]
theorem toRelIsoLT_symm (e : α ≃o β) : e.toRelIsoLT.symm = e.symm.toRelIsoLT :=
  rfl
#align order_iso.to_rel_iso_lt_symm OrderIso.toRelIsoLT_symm

/-- Converts a `rel_iso (<) (<)` into an `order_iso`. -/
def ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : α ≃o β :=
  ⟨e.toEquiv, fun x y => by simp [le_iff_eq_or_lt, e.map_rel_iff]⟩
#align order_iso.of_rel_iso_lt OrderIso.ofRelIsoLT

@[simp]
theorem ofRelIsoLT_apply {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) (x : α) : ofRelIsoLT e x = e x :=
  rfl
#align order_iso.of_rel_iso_lt_apply OrderIso.ofRelIsoLT_apply

@[simp]
theorem ofRelIsoLT_symm {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) :
    (ofRelIsoLT e).symm = ofRelIsoLT e.symm :=
  rfl
#align order_iso.of_rel_iso_lt_symm OrderIso.ofRelIsoLT_symm

@[simp]
theorem ofRelIsoLT_toRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β) :
    ofRelIsoLT (toRelIsoLT e) = e := by ext; simp
#align order_iso.of_rel_iso_lt_to_rel_iso_lt OrderIso.ofRelIsoLT_toRelIsoLT

@[simp]
theorem toRelIsoLT_ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : toRelIsoLT (ofRelIsoLT e) = e := by
  ext; simp
#align order_iso.to_rel_iso_lt_of_rel_iso_lt OrderIso.toRelIsoLT_ofRelIsoLT

#print OrderIso.ofCmpEqCmp /-
/-- To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear orders,
    it suffices to prove `cmp a (g b) = cmp (f a) b`. -/
def ofCmpEqCmp {α β} [LinearOrder α] [LinearOrder β] (f : α → β) (g : β → α)
    (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
  have gf : ∀ a : α, a = g (f a) := by intro ; rw [← cmp_eq_eq_iff, h, cmp_self_eq_eq]
  { toFun := f
    invFun := g
    left_inv := fun a => (gf a).symm
    right_inv := by intro ; rw [← cmp_eq_eq_iff, ← h, cmp_self_eq_eq]
    map_rel_iff' := by intros ; apply le_iff_le_of_cmp_eq_cmp; convert(h _ _).symm; apply gf }
#align order_iso.of_cmp_eq_cmp OrderIso.ofCmpEqCmp
-/

/-- To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is enough to show
    that `g` is the inverse of `f`-/
def ofHomInv {F G : Type _} [OrderHomClass F α β] [OrderHomClass G β α] (f : F) (g : G)
    (h₁ : (f : α →o β).comp (g : β →o α) = OrderHom.id)
    (h₂ : (g : β →o α).comp (f : α →o β) = OrderHom.id) : α ≃o β
    where
  toFun := f
  invFun := g
  left_inv := FunLike.congr_fun h₂
  right_inv := FunLike.congr_fun h₁
  map_rel_iff' a b :=
    ⟨fun h => by replace h := map_rel g h;
      rwa [Equiv.coe_fn_mk, show g (f a) = (g : β →o α).comp (f : α →o β) a from rfl,
        show g (f b) = (g : β →o α).comp (f : α →o β) b from rfl, h₂] at h,
      fun h => (f : α →o β).Monotone h⟩
#align order_iso.of_hom_inv OrderIso.ofHomInv

/-- Order isomorphism between `α → β` and `β`, where `α` has a unique element. -/
@[simps toEquiv apply]
def funUnique (α β : Type _) [Unique α] [Preorder β] : (α → β) ≃o β
    where
  toEquiv := Equiv.funUnique α β
  map_rel_iff' f g := by simp [Pi.le_def, Unique.forall_iff]
#align order_iso.fun_unique OrderIso.funUnique

@[simp]
theorem funUnique_symm_apply {α β : Type _} [Unique α] [Preorder β] :
    ((funUnique α β).symm : β → α → β) = Function.const α :=
  rfl
#align order_iso.fun_unique_symm_apply OrderIso.funUnique_symm_apply

end OrderIso

namespace Equiv

variable [Preorder α] [Preorder β]

#print Equiv.toOrderIso /-
/-- If `e` is an equivalence with monotone forward and inverse maps, then `e` is an
order isomorphism. -/
def toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β :=
  ⟨e, fun x y => ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩
#align equiv.to_order_iso Equiv.toOrderIso
-/

@[simp]
theorem coe_toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    ⇑(e.toOrderIso h₁ h₂) = e :=
  rfl
#align equiv.coe_to_order_iso Equiv.coe_toOrderIso

@[simp]
theorem toOrderIso_toEquiv (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    (e.toOrderIso h₁ h₂).toEquiv = e :=
  rfl
#align equiv.to_order_iso_to_equiv Equiv.toOrderIso_toEquiv

end Equiv

namespace StrictMono

variable {α β} [LinearOrder α] [Preorder β]

variable (f : α → β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

/-- A strictly monotone function with a right inverse is an order isomorphism. -/
@[simps (config := { fullyApplied := False })]
def orderIsoOfRightInverse (g : β → α) (hg : Function.RightInverse g f) : α ≃o β :=
  { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f
    invFun := g
    left_inv := fun x => h_mono.Injective <| hg _
    right_inv := hg }
#align strict_mono.order_iso_of_right_inverse StrictMono.orderIsoOfRightInverse

end StrictMono

#print OrderIso.dual /-
/-- An order isomorphism is also an order isomorphism between dual orders. -/
protected def OrderIso.dual [LE α] [LE β] (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨f.toEquiv, fun _ _ => f.map_rel_iff⟩
#align order_iso.dual OrderIso.dual
-/

section LatticeIsos

theorem OrderIso.map_bot' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x ≤ x')
    (hy : ∀ y', y ≤ y') : f x = y := by refine' le_antisymm _ (hy _);
  rw [← f.apply_symm_apply y, f.map_rel_iff]; apply hx
#align order_iso.map_bot' OrderIso.map_bot'

theorem OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ≃o β) : f ⊥ = ⊥ :=
  f.map_bot' (fun _ => bot_le) fun _ => bot_le
#align order_iso.map_bot OrderIso.map_bot

theorem OrderIso.map_top' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x' ≤ x)
    (hy : ∀ y', y' ≤ y) : f x = y :=
  f.dual.map_bot' hx hy
#align order_iso.map_top' OrderIso.map_top'

theorem OrderIso.map_top [LE α] [PartialOrder β] [OrderTop α] [OrderTop β] (f : α ≃o β) : f ⊤ = ⊤ :=
  f.dual.map_bot
#align order_iso.map_top OrderIso.map_top

theorem OrderEmbedding.map_inf_le [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α) :
    f (x ⊓ y) ≤ f x ⊓ f y :=
  f.Monotone.map_inf_le x y
#align order_embedding.map_inf_le OrderEmbedding.map_inf_le

theorem OrderEmbedding.le_map_sup [SemilatticeSup α] [SemilatticeSup β] (f : α ↪o β) (x y : α) :
    f x ⊔ f y ≤ f (x ⊔ y) :=
  f.Monotone.le_map_sup x y
#align order_embedding.le_map_sup OrderEmbedding.le_map_sup

theorem OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α) :
    f (x ⊓ y) = f x ⊓ f y :=
  by
  refine' (f.to_order_embedding.map_inf_le x y).antisymm _
  apply f.symm.le_iff_le.1
  simpa using f.symm.to_order_embedding.map_inf_le (f x) (f y)
#align order_iso.map_inf OrderIso.map_inf

theorem OrderIso.map_sup [SemilatticeSup α] [SemilatticeSup β] (f : α ≃o β) (x y : α) :
    f (x ⊔ y) = f x ⊔ f y :=
  f.dual.map_inf x y
#align order_iso.map_sup OrderIso.map_sup

/-- Note that this goal could also be stated `(disjoint on f) a b` -/
theorem Disjoint.map_orderIso [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) (ha : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff_inf_le, ← f.map_inf, ← f.map_bot]; exact f.monotone ha.le_bot
#align disjoint.map_order_iso Disjoint.map_orderIso

/-- Note that this goal could also be stated `(codisjoint on f) a b` -/
theorem Codisjoint.map_orderIso [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) (ha : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff_le_sup, ← f.map_sup, ← f.map_top]; exact f.monotone ha.top_le
#align codisjoint.map_order_iso Codisjoint.map_orderIso

@[simp]
theorem disjoint_map_orderIso_iff [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) : Disjoint (f a) (f b) ↔ Disjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm, fun h =>
    h.map_orderIso f⟩
#align disjoint_map_order_iso_iff disjoint_map_orderIso_iff

@[simp]
theorem codisjoint_map_orderIso_iff [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) : Codisjoint (f a) (f b) ↔ Codisjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm, fun h =>
    h.map_orderIso f⟩
#align codisjoint_map_order_iso_iff codisjoint_map_orderIso_iff

namespace WithBot

/-- Taking the dual then adding `⊥` is the same as adding `⊤` then taking the dual.
This is the order iso form of `with_bot.of_dual`, as proven by `coe_to_dual_top_equiv_eq`.
-/
protected def toDualTopEquiv [LE α] : WithBot αᵒᵈ ≃o (WithTop α)ᵒᵈ :=
  OrderIso.refl _
#align with_bot.to_dual_top_equiv WithBot.toDualTopEquiv

@[simp]
theorem toDualTopEquiv_coe [LE α] (a : α) :
    WithBot.toDualTopEquiv ↑(toDual a) = toDual (a : WithTop α) :=
  rfl
#align with_bot.to_dual_top_equiv_coe WithBot.toDualTopEquiv_coe

@[simp]
theorem toDualTopEquiv_symm_coe [LE α] (a : α) :
    WithBot.toDualTopEquiv.symm (toDual (a : WithTop α)) = ↑(toDual a) :=
  rfl
#align with_bot.to_dual_top_equiv_symm_coe WithBot.toDualTopEquiv_symm_coe

@[simp]
theorem toDualTopEquiv_bot [LE α] : WithBot.toDualTopEquiv (⊥ : WithBot αᵒᵈ) = ⊥ :=
  rfl
#align with_bot.to_dual_top_equiv_bot WithBot.toDualTopEquiv_bot

@[simp]
theorem toDualTopEquiv_symm_bot [LE α] : WithBot.toDualTopEquiv.symm (⊥ : (WithTop α)ᵒᵈ) = ⊥ :=
  rfl
#align with_bot.to_dual_top_equiv_symm_bot WithBot.toDualTopEquiv_symm_bot

theorem coe_toDualTopEquiv_eq [LE α] :
    (WithBot.toDualTopEquiv : WithBot αᵒᵈ → (WithTop α)ᵒᵈ) = toDual ∘ WithBot.ofDual :=
  funext fun _ => rfl
#align with_bot.coe_to_dual_top_equiv_eq WithBot.coe_toDualTopEquiv_eq

end WithBot

namespace WithTop

/-- Taking the dual then adding `⊤` is the same as adding `⊥` then taking the dual.
This is the order iso form of `with_top.of_dual`, as proven by `coe_to_dual_bot_equiv_eq`. -/
protected def toDualBotEquiv [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _
#align with_top.to_dual_bot_equiv WithTop.toDualBotEquiv

@[simp]
theorem toDualBotEquiv_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv ↑(toDual a) = toDual (a : WithBot α) :=
  rfl
#align with_top.to_dual_bot_equiv_coe WithTop.toDualBotEquiv_coe

@[simp]
theorem toDualBotEquiv_symm_coe [LE α] (a : α) :
    WithTop.toDualBotEquiv.symm (toDual (a : WithBot α)) = ↑(toDual a) :=
  rfl
#align with_top.to_dual_bot_equiv_symm_coe WithTop.toDualBotEquiv_symm_coe

@[simp]
theorem toDualBotEquiv_top [LE α] : WithTop.toDualBotEquiv (⊤ : WithTop αᵒᵈ) = ⊤ :=
  rfl
#align with_top.to_dual_bot_equiv_top WithTop.toDualBotEquiv_top

@[simp]
theorem toDualBotEquiv_symm_top [LE α] : WithTop.toDualBotEquiv.symm (⊤ : (WithBot α)ᵒᵈ) = ⊤ :=
  rfl
#align with_top.to_dual_bot_equiv_symm_top WithTop.toDualBotEquiv_symm_top

theorem coe_toDualBotEquiv [LE α] :
    (WithTop.toDualBotEquiv : WithTop αᵒᵈ → (WithBot α)ᵒᵈ) = toDual ∘ WithTop.ofDual :=
  funext fun _ => rfl
#align with_top.coe_to_dual_bot_equiv_eq WithTop.coe_toDualBotEquiv

end WithTop

namespace OrderIso

variable [PartialOrder α] [PartialOrder β] [PartialOrder γ]

/-- A version of `equiv.option_congr` for `with_top`. -/
@[simps apply]
def withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β :=
  { e.toOrderEmbedding.withTop_map with toEquiv := e.toEquiv.optionCongr }
#align order_iso.with_top_congr OrderIso.withTopCongr

@[simp]
theorem withTopCongr_refl : (OrderIso.refl α).withTopCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.optionCongr_refl
#align order_iso.with_top_congr_refl OrderIso.withTopCongr_refl

@[simp]
theorem withTopCongr_symm (e : α ≃o β) : e.withTopCongr.symm = e.symm.withTopCongr :=
  RelIso.toEquiv_injective e.toEquiv.optionCongr_symm
#align order_iso.with_top_congr_symm OrderIso.withTopCongr_symm

@[simp]
theorem withTopCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    e₁.withTopCongr.trans e₂.withTopCongr = (e₁.trans e₂).withTopCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.optionCongr_trans e₂.toEquiv
#align order_iso.with_top_congr_trans OrderIso.withTopCongr_trans

/-- A version of `equiv.option_congr` for `with_bot`. -/
@[simps apply]
def withBotCongr (e : α ≃o β) : WithBot α ≃o WithBot β :=
  { e.toOrderEmbedding.withBot_map with toEquiv := e.toEquiv.optionCongr }
#align order_iso.with_bot_congr OrderIso.withBotCongr

@[simp]
theorem withBotCongr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _ :=
  RelIso.toEquiv_injective Equiv.optionCongr_refl
#align order_iso.with_bot_congr_refl OrderIso.withBotCongr_refl

@[simp]
theorem withBotCongr_symm (e : α ≃o β) : e.withBotCongr.symm = e.symm.withBotCongr :=
  RelIso.toEquiv_injective e.toEquiv.optionCongr_symm
#align order_iso.with_bot_congr_symm OrderIso.withBotCongr_symm

@[simp]
theorem withBotCongr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    e₁.withBotCongr.trans e₂.withBotCongr = (e₁.trans e₂).withBotCongr :=
  RelIso.toEquiv_injective <| e₁.toEquiv.optionCongr_trans e₂.toEquiv
#align order_iso.with_bot_congr_trans OrderIso.withBotCongr_trans

end OrderIso

section BoundedOrder

variable [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] (f : α ≃o β)

include f

theorem OrderIso.isCompl {x y : α} (h : IsCompl x y) : IsCompl (f x) (f y) :=
  ⟨h.1.map_orderIso _, h.2.map_orderIso _⟩
#align order_iso.is_compl OrderIso.isCompl

theorem OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsCompl (f x) (f y) :=
  ⟨f.IsCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.IsCompl h⟩
#align order_iso.is_compl_iff OrderIso.isCompl_iff

theorem OrderIso.complementedLattice [ComplementedLattice α] : ComplementedLattice β :=
  ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_is_compl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    refine' ⟨f y, f.symm.is_compl_iff.2 hy⟩⟩
#align order_iso.complemented_lattice OrderIso.complementedLattice

theorem OrderIso.complementedLattice_iff : ComplementedLattice α ↔ ComplementedLattice β :=
  ⟨by intro ; exact f.complemented_lattice, by intro ; exact f.symm.complemented_lattice⟩
#align order_iso.complemented_lattice_iff OrderIso.complementedLattice_iff

end BoundedOrder

end LatticeIsos

-- Developments relating order homs and sets belong in `order.hom.set` or later.
assert_not_exists Set.range

